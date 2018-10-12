{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE StandaloneDeriving   #-}
module Main where

import           Control.Monad ((<=<))
import           Data.SBV
import           Data.SBV.List ((.!!), (.++))
import qualified Data.SBV.List as SBVL
import           Prelude       as P hiding (concat)


data Ty
  = List Ty
  | IntTy
  | BoolTy

type family Concrete (ty :: Ty) :: *
type instance Concrete ('List a) = [Concrete a]
type instance Concrete 'IntTy    = Integer
type instance Concrete 'BoolTy   = Bool

type Suitable a = (Show (Concrete a), SymWord (Concrete a), Literal a)

data Expr ty where
  -- transducers
  ListCat  :: Suitable a
           => Expr ('List a) -> Expr ('List a) -> Expr ('List a)
  ListMap  :: Suitable a
           => (Expr a -> Expr b)
           ->                   Expr ('List a) -> Expr ('List b)

  -- producers / information
  -- TODO: use Suitable?
  ListInfo :: HasKind (Concrete a) => ListInfo a -> Expr ('List a)

  -- other
  Eq       :: (Eq (Concrete a), Suitable a)
           => Expr a         -> Expr a         -> Expr 'BoolTy
  Gt       :: Expr 'IntTy    -> Expr 'IntTy    -> Expr 'BoolTy
  Not      ::                   Expr 'BoolTy   -> Expr 'BoolTy
  BinOp    :: Fold a -> Expr a -> Expr a -> Expr a

  LitB     :: Concrete 'BoolTy                 -> Expr 'BoolTy
  LitI     :: Concrete 'IntTy                  -> Expr 'IntTy
  Sym      :: SBV (Concrete a)                 -> Expr a

instance Boolean (Expr 'BoolTy) where
  true  = LitB True
  false = LitB False
  bnot  = Not
  (&&&) = BinOp And

instance Num (Expr 'IntTy) where
  fromInteger = LitI
  (+)    = BinOp Add
  (*)    = error "not supported"
  (-)    = error "not supported"
  negate = error "not supported"
  abs    = error "not supported"
  signum = error "not supported"

data Fold a where
  And :: Fold 'BoolTy
  Add :: Fold 'IntTy

deriving instance Show (Fold a)

data ListInfo a where
  LitList      :: [SBV (Concrete a)]                     -> ListInfo a
  LenInfo      :: SBV Integer                            -> ListInfo a
  FoldInfo     :: (Expr a -> Expr b) -> Fold b -> Expr b -> ListInfo a
  AtInfo       :: Expr 'IntTy -> Expr a                  -> ListInfo a
  ContainsInfo :: Expr a                                 -> ListInfo a

pattern AllInfo :: (b ~ 'BoolTy) => (Expr a -> Expr b) -> ListInfo a
pattern AllInfo f <- FoldInfo f And (LitB True) where
  AllInfo f = FoldInfo f And  (LitB True)

instance HasKind (Concrete a) => Show (ListInfo a) where
  showsPrec p li = showParen (p > 10) $ case li of
    LitList l -> showString "LitList " . showsPrec 11 l
    LenInfo i -> showString "LenInfo " . showsPrec 11 i
    FoldInfo f fold empty' ->
        showString "FoldInfo "
      . showsPrec 11 (f (Sym (uninterpret "x")))
      . showString " "
      . showsPrec 11 fold
      . showString " "
      . showsPrec 11 empty'
    AtInfo i a ->
        showString "AtInfo "
      . showsPrec 11 i
      . showString " "
      . showsPrec 11 a
    ContainsInfo a -> showString "ContainsInfo " . showsPrec 11 a

instance Show (Expr ty) where
  showsPrec p expr = showParen (p > 10) $ case expr of
    ListCat a b ->
      showString "ListCat "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
    ListMap f as ->
        showString "ListMap "
      . showsPrec 11 (f (Sym (uninterpret "x")))
      . showString " "
      . showsPrec 11 as

    ListInfo i -> showString "ListInfo " . showsPrec 11 i
    LitB a     -> showString "LitB " . showsPrec 11 a
    LitI a     -> showString "LitI " . showsPrec 11 a

    Eq a b ->
        showString "Eq "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
    Gt a b ->
        showString "Gt "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
    BinOp op a b ->
        showString "BinOp "
      . showsPrec 11 op
      . showString " "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
    Not a -> showString "Not " . showsPrec 11 a
    Sym a -> showsPrec 11 a

class Literal a where
  lit :: Concrete a -> Expr a

instance Literal 'BoolTy where
  lit = LitB

instance Literal 'IntTy where
  lit = LitI

eval :: Expr ty -> Concrete ty
eval = \case
  ListCat a b        -> eval a <> eval b
  ListMap f as       -> eval . f . lit <$> eval as
  ListInfo _         -> error "cannot evaluate list info"

  Eq a b             -> eval a == eval b
  Gt a b             -> eval a >  eval b
  Not a              -> not (eval a)

  BinOp op a b -> case op of
    And -> eval a && eval b
    Add -> eval a +  eval b

  LitB a             -> a
  LitI a             -> a
  Sym _              -> error "canot evaluate symbolic value"

sEval :: SymWord (Concrete ty) => Expr ty -> SBV (Concrete ty)
sEval = \case
  ListCat a b    -> sEval a .++ sEval b
  ListMap{}      -> error "can't map with sbv lists"
  ListInfo{}     -> error "can't evaluate list info"

  Eq a b         -> sEval a .== sEval b
  Gt a b         -> sEval a .>  sEval b
  Not a          -> bnot (sEval a)

  BinOp op a b -> case op of
    And -> sEval a &&& sEval b
    Add -> sEval a +   sEval b

  LitB a         -> literal a
  LitI a         -> literal a
  Sym a          -> a

-- "My claim is that we should exploit a hypothesis not in terms of its
-- immediate consequences, but in terms of the leverage it exerts on an
-- arbitrary goal: we should give elimination a motive"

-- The motive for consuming a list of type @a@
data Motive a where
  MLength   :: Expr 'IntTy           -> Motive a
  MAt       :: Expr 'IntTy -> Expr a -> Motive a
  MFold
    -- consuming a list of a, where we operate on bs
    :: SymWord (Concrete b) => (Expr a -> Expr b)
    -- fold
    -> Fold b
    -- target
    -> Expr b
    -> Motive a

evalMotive
  :: forall a. (Show (Concrete a), SymWord (Concrete a))
  => Motive a -> Expr ('List a) -> Symbolic (SBV Bool)
evalMotive _ Sym{}    = error "can't motivate evaluation of symbolic value"

evalMotive (MLength len) (ListCat a b) = do
  [al, bl] <- sIntegers ["al", "bl"]
  let totalLen = al + bl .== sEval len
  aLen <- evalMotive (MLength (Sym al)) a
  bLen <- evalMotive (MLength (Sym bl)) b
  pure $ totalLen &&& aLen &&& bLen
evalMotive (MLength len) (ListMap _ lst) = evalMotive (MLength len) lst
evalMotive (MLength len) (ListInfo i) =
  let lenV = sEval len
  in case i of
       LenInfo len' -> pure $ len'                    .== lenV
       LitList l    -> pure $ fromIntegral (length l) .== lenV
       _            -> error $
         "sorry, can't help with this motive: " ++ show i

evalMotive (MFold mapping fold target) (ListCat a b) = do
  [targetA, targetB] <- mkExistVars 2
  let append = BinOp fold
  constrain $ sEval target .== sEval (Sym targetA `append` Sym targetB)
  (&&&)
    <$> evalMotive (MFold mapping fold (Sym targetA)) a
    <*> evalMotive (MFold mapping fold (Sym targetB)) b

evalMotive (MFold f And target) (ListInfo (FoldInfo g And i)) = do
  -- g is at least as strong an assumption as f.
  -- example:
  -- f: for all i: elements of the list, i > 0
  -- g: i need to know that for all i: elements of the list, i > -1
  j <- forall_
  let fEval = sEval $ f (Sym j) `Eq` target
      gEval = sEval $ g (Sym j) `Eq` i
  pure $ gEval ==> fEval

evalMotive (MFold f Add target) (ListInfo (FoldInfo g Add i)) = do
  j <- forall_
  let fEval = sEval $ f (Sym j) `Eq` target
      gEval = sEval $ g (Sym j) `Eq` i
  pure $ gEval ==> fEval

evalMotive (MFold mapping fold target) (ListInfo info) = case (fold, info) of
  (_, LenInfo len)
    | Just cLen <- unliteral len -> do
      vars <- mkExistVars (fromIntegral cLen)
      pure $
        sEval (foldr (BinOp fold) (empty fold) (fmap (mapping . Sym) vars))
        .==
        sEval target
    | otherwise -> error "TODO: folding non-literal length list"
  (_, LitList l) -> pure $
    sEval target
    .==
    sEval (foldr (BinOp fold) (empty fold) (fmap (mapping . Sym) l))
  _ -> error $ "sorry, can't help with this motive: " ++ show info
evalMotive (MFold mapping fold target) (ListMap g lst) =
  evalMotive (MFold (mapping . g) fold target) lst

evalMotive MFold{} _ = error "sorry, can't help with this motive"

evalMotive (MAt i a) (ListCat l1 l2) = do
    let l1' = sEval l1
        l2' = sEval l2
        i'  = sEval i
        a'  = sEval a
    pure $
      l1' .!! i'                     .== a' |||
      l2' .!! (i' - SBVL.length l1') .== a'
evalMotive (MAt i _) (ListMap _ lst) = evalMotive (MAt i (error "TODO")) lst
evalMotive (MAt i a) (ListInfo info) = case info of
  LitList litList -> pure $
    let iV = sEval i
        aV = sEval a
    in fromIntegral (length litList) .> iV &&&
       (SBVL.implode litList SBVL..!! iV) .== aV

  _ -> error "can't help with this motive"

evalMotive MLength{} BinOp{} = error "vacuous match"
evalMotive MAt{} BinOp{}     = error "vacuous match"

empty :: Fold a -> Expr a
empty = \case
  Add -> 0
  And -> true

gt0 :: Expr 'IntTy -> Expr 'BoolTy
gt0 x = Gt x 0

lte0 :: Expr 'IntTy -> Expr 'BoolTy
lte0 x = Not (Gt x 0)

mkAnyM :: (Expr a -> Expr 'BoolTy) -> Motive a
mkAnyM f = MFold (bnot . f) And false

main :: IO ()
main = do
  makeReport "any (> 0) [1, 2, 3] (expect good)" $ do
    let lst = ListInfo (LitList [1, 2, 3])
    constrain =<< evalMotive (mkAnyM gt0) lst

  makeReport "any (> 0) [-1, 2, 3] (expect good)" $ do
    let lst = ListInfo (LitList [-1, 2, 3])
    constrain =<< evalMotive (mkAnyM gt0) lst

  makeReport "any (> 0) [a, -1, 3] (expect good)" $ do
    a <- sInteger "a"
    let lst = ListInfo (LitList [a, -1, 3])
    constrain =<< evalMotive (mkAnyM gt0) lst

  makeReport "all (> 0) [a, -1, 3] (expect bad)" $ do
    a <- sInteger "a"
    let lst = ListInfo (LitList [a, -1, 3])
    constrain =<< evalMotive (MFold gt0 And true) lst

  makeReport "length [] == 0 (expect good)" $ do
    let lst = ListInfo (LenInfo 0) :: Expr ('List 'IntTy)
    constrain =<< evalMotive (MLength 0) lst

  makeReport "length (len 2) == 2 (expect good)" $ do
    let lst :: Expr ('List 'IntTy)
        lst = ListInfo (LenInfo 2)
    constrain =<< evalMotive (MLength 2) lst

  -- show that the result of a mapping is all positive
  makeReport "fmap (> 0) lst == true (expect good)" $ do
    let lst = ListInfo (AllInfo gt0) :: Expr ('List 'IntTy)
    constrain =<< evalMotive (MFold gt0 And true) lst

  let almostAllPos :: Expr ('List 'IntTy)
      almostAllPos = ListCat
        (ListInfo (AllInfo gt0))
        (ListCat
          (ListInfo (AllInfo (Eq 0)))
          (ListInfo (AllInfo gt0)))

  makeReport "fmap (> 0) almostAllPos == true (expect bad)" $
    constrain =<< evalMotive (MFold gt0 And true) almostAllPos

  makeReport "(and []) == true (expect good)" $
    constrain =<< evalMotive (MFold (Eq @'BoolTy true) And true) (ListInfo (LenInfo 0))

  makeReport "(not (and [])) == true (expect bad)" $ do
    x <- evalMotive (MFold (Eq @'BoolTy true) And true) (ListInfo (LenInfo 0))
    constrain $ bnot x

  let mkAnd :: SBV Bool -> ListInfo 'BoolTy
      mkAnd = AllInfo . Eq . Sym

  makeReport "(and [true]) == true (expect good)" $
    constrain <=< evalMotive (MFold (Eq true) And true) $ ListInfo $ mkAnd true -- AndInfo $ SAnd true

  makeReport "(and [false]) == true (expect bad)" $
    constrain =<< evalMotive
      (MFold (Eq true) And true)
      (ListInfo $ FoldInfo id And false)
      -- Lit [false]

  makeReport "and [false] /= true (expect good)" $
    constrain =<< evalMotive
      (MFold (Eq true) And false)
      (ListInfo (FoldInfo id And false))

  makeReport "all (> 0) => (not (any (> 0)) == false) (expect bad)" $
    constrain =<< evalMotive
      (MFold gt0 And false)
      (ListInfo (AllInfo gt0))

  makeReport "any (<= 0) => not (all (> 0)) (expect good)" $
    constrain =<< evalMotive
      (MFold gt0 And false)
      -- (ListInfo (FoldInfo lte0 Or true))
      -- <=>
      (ListInfo (FoldInfo (bnot . lte0) And false))

  makeReport "at 2 [1, 2, 3] == 3 (expect good)" $
    constrain =<< evalMotive
      (MAt (LitI 2) (LitI 3))
      (ListInfo $ LitList [1, 2, 3])

  makeReport "at 2 [1, 2, 3] == 2 (expect bad)" $
    constrain =<< evalMotive
      (MAt (LitI 2) (LitI 2))
      (ListInfo $ LitList [1, 2, 3])

  let sumTo7 :: Expr ('List 'IntTy)
      sumTo7 = ListCat
        (ListInfo (FoldInfo id Add 3))
        (ListInfo (FoldInfo id Add 4))

  makeReport "sum sumTo7 == 7 (expect good)" $
    constrain =<< evalMotive (MFold id Add 7) sumTo7

  makeReport "sum (map (const 1) [length 7]) == 7 (expect good)" $ do
    let lst :: Expr ('List 'IntTy)
        lst = ListInfo (LenInfo 7)
    constrain =<< evalMotive (MFold (const 1) Add 7) lst

makeReport :: String -> Symbolic () -> IO ()
makeReport header a = do
  putStrLn $ '\n' : header
  ThmResult provable <- prove a
  -- putStrLn $ "provable:    " ++ show provable
  -- SatResult satisfiable <- sat a
  -- putStrLn $ "satisfiable: " ++ show satisfiable
  vacuous <- isVacuous a
  -- putStrLn $ "vacuous:     " ++ show vacuous
  putStrLn $
    if vacuous
    then "bad (vacuous)"
    else case provable of
           Satisfiable{}   -> "bad (not vacuous)"
           Unsatisfiable{} -> "good"
           _               -> show $ ThmResult provable
