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
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
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
  -- list consumers
  ListLen  :: Suitable a
           => Expr ('List a)                   -> Expr 'IntTy
  ListAnd  :: Expr ('List 'BoolTy)             -> Expr 'BoolTy
  ListOr   :: Expr ('List 'BoolTy)             -> Expr 'BoolTy

  ListAll  :: Suitable a
           => (Expr a -> Expr 'BoolTy)
           -> Expr ('List a)                   -> Expr 'BoolTy
  ListAny  :: Suitable a
           => (Expr a -> Expr 'BoolTy)
           -> Expr ('List a)                   -> Expr 'BoolTy

  ListEq   :: Suitable a
           => Expr ('List a) -> Expr ('List a) -> Expr 'BoolTy
  ListAt   :: Expr ('List a) -> Expr 'IntTy    -> Expr a
  ListContains
           :: Suitable a
           => Expr ('List a) -> Expr a         -> Expr 'BoolTy

  -- transducers
  ListCat  :: Suitable a
           => Expr ('List a) -> Expr ('List a) -> Expr ('List a)
  ListMap  :: Suitable a
           => (Expr a -> Expr b)
           ->                   Expr ('List a) -> Expr ('List b)

  -- producers
  -- TODO: use Suitable?
  ListInfo :: HasKind (Concrete a) => ListInfo a -> Expr ('List a)

  -- other
  Eq       :: (Eq (Concrete a), Suitable a)
           => Expr a         -> Expr a         -> Expr 'BoolTy
  Gt       :: Expr 'IntTy    -> Expr 'IntTy    -> Expr 'BoolTy
  And      :: Expr 'BoolTy   -> Expr 'BoolTy   -> Expr 'BoolTy
  Or       :: Expr 'BoolTy   -> Expr 'BoolTy   -> Expr 'BoolTy
  Not      ::                   Expr 'BoolTy   -> Expr 'BoolTy

  LitB     :: Concrete 'BoolTy                 -> Expr 'BoolTy
  LitI     :: Concrete 'IntTy                  -> Expr 'IntTy
  Sym      :: SBV (Concrete a)                 -> Expr a

data ListInfo a where
  LitList :: [SBV (Concrete a)]            -> ListInfo a
  LenInfo :: SBV Integer                   -> ListInfo a
  AnyInfo :: (Expr a      -> Expr 'BoolTy) -> ListInfo a
  AllInfo :: (Expr a      -> Expr 'BoolTy) -> ListInfo a
  SumInfo :: (Expr 'IntTy -> Expr 'BoolTy) -> ListInfo 'IntTy

instance HasKind (Concrete a) => Show (ListInfo a) where
  showsPrec p li = showParen (p > 10) $ case li of
    LitList l -> showString "LitList " . showsPrec 11 l
    LenInfo i -> showString "LenInfo " . showsPrec 11 i
    AnyInfo f -> showString "AnyInfo " . showsPrec 11 (f (Sym (uninterpret "x")))
    AllInfo f -> showString "AllInfo " . showsPrec 11 (f (Sym (uninterpret "x")))
    SumInfo f -> showString "SumInfo " . showsPrec 11 (f (Sym (uninterpret "x")))

instance Show (Expr ty) where
  showsPrec p expr = showParen (p > 10) $ case expr of
    ListLen l          -> showString "ListLen " . showsPrec 11 l
    ListAnd l          -> showString "ListAnd " . showsPrec 11 l
    ListAll f l        ->
      showString "ListAll " .
      showsPrec 11 (f (Sym (uninterpret "x"))) .
      showsPrec 11 l
    ListAny f l        ->
      showString "ListAny " .
      showsPrec 11 (f (Sym (uninterpret "x"))) .
      showsPrec 11 l
    ListOr  l          -> showString "ListOr " . showsPrec 11 l
    ListEq  a b        -> showString "ListEq " . showsPrec 11 a . showsPrec 11 b
    ListAt lst i       ->
      showString "ListAt " .
      showsPrec 11 lst .
      showString " " .
      showsPrec 11 i
    ListContains lst a ->
      showString "ListContains " .
      showsPrec 11 lst .
      showString " " .
      showsPrec 11 a

    ListCat a b        ->
      showString "ListCat " .
      showsPrec 11 a .
      showString " " .
      showsPrec 11 b
    ListMap _ as     ->
      showString "ListMap _ " .
      showsPrec 11 as
    ListInfo i         -> showString "ListInfo " . showsPrec 11 i

    LitB a             -> showString "LitB " . showsPrec 11 a
    LitI a             -> showString "LitI " . showsPrec 11 a
    Eq a b             ->
      showString "Eq " .
      showsPrec 11 a .
      showString " " .
      showsPrec 11 b
    Gt a b             ->
      showString "Gt " .
      showsPrec 11 a .
      showString " " .
      showsPrec 11 b
    And a b            ->
      showString "And " .
      showsPrec 11 a .
      showString " " .
      showsPrec 11 b
    Or a b             ->
      showString "Or " .
      showsPrec 11 a .
      showString " " .
      showsPrec 11 b
    Not a              -> showString "Not" . showsPrec 11 a
    Sym a -> showsPrec 11 a

class Literal a where
  lit :: Concrete a -> Expr a

instance Literal 'BoolTy where
  lit = LitB

instance Literal 'IntTy where
  lit = LitI

eval :: Expr ty -> Concrete ty
eval = \case
  ListLen l          -> fromIntegral $ length $ eval l
  ListAnd l          -> and $ eval l
  ListOr  l          -> or  $ eval l
  ListAll f l        -> and $ fmap (eval . f . lit) $ eval l
  ListAny f l        -> or  $ fmap (eval . f . lit) $ eval l
  ListEq  a b        -> eval a == eval b
  ListAt lst i       -> eval lst !! fromIntegral (eval i)
  ListContains lst a -> eval a `elem` eval lst

  ListCat a b        -> eval a <> eval b
  ListMap f as       -> eval . f . lit <$> eval as
  ListInfo _         -> error "cannot evaluate list info"

  Eq a b             -> eval a == eval b
  Gt a b             -> eval a >  eval b
  And a b            -> eval a && eval b
  Or a b             -> eval a || eval b
  Not a              -> not (eval a)

  LitB a             -> a
  LitI a             -> a
  Sym _              -> error "canot evaluate symbolic value"

sEval :: SymWord (Concrete ty) => Expr ty -> SBV (Concrete ty)
sEval = \case
  ListLen l      -> SBVL.length $ sEval l
  ListAnd _      -> error "can't fold with sbv lists"
  ListOr  _      -> error "can't fold with sbv lists"
  ListAll{}      -> error "can't fold with sbv lists"
  ListAny{}      -> error "can't fold with sbv lists"
  ListEq  a b    -> sEval a .== sEval b
  ListAt lst i   -> sEval lst .!! sEval i
  ListContains{} -> error "can't contains with sbv lists"

  ListCat a b    -> sEval a .++ sEval b
  ListMap{}      -> error "can't map with sbv lists"
  ListInfo _     -> error "can't evaluate list info"

  Eq a b         -> sEval a .== sEval b
  Gt a b         -> sEval a .>  sEval b
  And a b        -> sEval a &&& sEval b
  Or a b         -> sEval a ||| sEval b
  Not a          -> bnot (sEval a)
  LitB a         -> literal a
  LitI a         -> literal a
  Sym a          -> a

-- "My claim is that we should exploit a hypothesis not in terms of its
-- immediate consequences, but in terms of the leverage it exerts on an
-- arbitrary goal: we should give elimination a motive"

-- The motive for consuming a list of type @a@
data Motive a where
  MLength   :: Expr 'IntTy                   -> Motive a
  MAt       :: Expr 'IntTy -> Expr a         -> Motive a
  MNegate   :: Motive a                      -> Motive a

  MAll      :: (Expr a      -> Expr 'BoolTy) -> Motive a
  MAny      :: (Expr a      -> Expr 'BoolTy) -> Motive a
  MSum      :: (Expr 'IntTy -> Expr 'BoolTy) -> Motive 'IntTy
  -- MFold

evalMotive
  :: forall a. (Show (Concrete a), SymWord (Concrete a))
  => Motive a -> Expr ('List a) -> Symbolic (SBV Bool)
evalMotive _ ListAt{} = error "nested lists not allowed"
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

evalMotive (MAll f) (ListCat a b) = (&&&)
  <$> evalMotive (MAll f) a
  <*> evalMotive (MAll f) b
evalMotive (MAll f) (ListMap g lst) = evalMotive (MAll (f . g)) lst
evalMotive (MAll f) (ListInfo i) = case i of
  AllInfo g -> do
    j <- forall_
    -- g is at least as strong an assumption as f.
    -- example:
    -- f: for all i: elements of the list, i > 0
    -- g: i need to know that for all i: elements of the list, i > -1
    let fEval = sEval $ f $ Sym j
        gEval = sEval $ g $ Sym j
    pure $ gEval ==> fEval
  LenInfo len
    | Just 0 <- unliteral len -> pure true
    | otherwise -> error "TODO"
  LitList l -> pure $ foldr (&&&) true (fmap (sEval . f . Sym) l)
  _ -> error $ "sorry, can't help with this motive: " ++ show i

evalMotive (MAny f) (ListCat a b) = (|||)
  <$> evalMotive (MAny f) a
  <*> evalMotive (MAny f) b
evalMotive (MAny f) (ListMap g lst) = evalMotive (MAny (f . g)) lst
evalMotive (MAny f) (ListInfo info) = case info of
  AnyInfo g -> do
    j <- exists_
    let fEval = sEval $ f $ Sym j
        gEval = sEval $ g $ Sym j
    pure $ gEval ==> fEval
  LenInfo len
    | Just 0 <- unliteral len -> pure false
    | otherwise -> error "TODO"
  LitList l -> pure $ foldr (|||) false (fmap (sEval . f . Sym) l)
  _ -> error $ "sorry, can't help with this motive: " ++ show info

evalMotive (MSum f) (ListCat a b) = do
  [aV, bV] <- sIntegers ["aV", "bV"]
  constrain $ sEval $ f $ Sym $ aV + bV
  (&&&)
    <$> evalMotive (MSum (Eq (Sym aV))) a
    <*> evalMotive (MSum (Eq (Sym bV))) b
evalMotive (MSum f) (ListInfo info) = case info of
  SumInfo g -> do
    j <- exists_
    let fEval = sEval $ f $ Sym j
        gEval = sEval $ g $ Sym j
    pure $ gEval ==> fEval
  _ -> error $ "sorry, can't help with this motive: " ++ show info

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

evalMotive (MNegate (MAll f)) lst = evalMotive (MAny (Not . f)) lst
evalMotive (MNegate (MAny f)) lst = evalMotive (MAll (Not . f)) lst

l0 :: Expr 'IntTy
l0 = LitI 0

gt0 :: Expr 'IntTy -> Expr 'BoolTy
gt0 x = Gt x l0

lte0 :: Expr 'IntTy -> Expr 'BoolTy
lte0 x = Not (Gt x l0)

main :: IO ()
main = do
  makeReport "any (> 0) [1, 2, 3] (expect good)" $ do
    let lst = ListInfo (LitList [1, 2, 3])
    constrain =<< evalMotive (MAny gt0) lst

  makeReport "any (> 0) [-1, 2, 3] (expect good)" $ do
    let lst = ListInfo (LitList [-1, 2, 3])
    constrain =<< evalMotive (MAny gt0) lst

  makeReport "any (> 0) [a, -1, 3] (expect good)" $ do
    a <- sInteger "a"
    let lst = ListInfo (LitList [a, -1, 3])
    constrain =<< evalMotive (MAny gt0) lst

  makeReport "all (> 0) [a, -1, 3] (expect bad)" $ do
    a <- sInteger "a"
    let lst = ListInfo (LitList [a, -1, 3])
    constrain =<< evalMotive (MAll gt0) lst

  makeReport "length [] == 0 (expect good)" $ do
    let lst = ListInfo (LenInfo 0) :: Expr ('List 'IntTy)
    constrain =<< evalMotive (MLength l0) lst

  makeReport "length (len 2) == 2 (expect good)" $ do
    let lst :: Expr ('List 'IntTy)
        lst = ListInfo (LenInfo 2)
    constrain =<< evalMotive (MLength (LitI 2)) lst

  -- show that the result of a mapping is all positive
  makeReport "fmap (> 0) lst == true (expect good)" $ do
    let lst = ListInfo (AllInfo gt0) :: Expr ('List 'IntTy)
    constrain =<< evalMotive (MAll gt0) lst

  let almostAllPos :: Expr ('List 'IntTy)
      almostAllPos = ListCat
        (ListInfo (AllInfo gt0))
        (ListCat
          (ListInfo (AllInfo (Eq l0)))
          (ListInfo (AllInfo gt0)))

  makeReport "fmap (> 0) almostAllPos == true (expect bad)" $ do
    constrain =<< evalMotive (MAll gt0) almostAllPos

  makeReport "(and []) == true (expect good)" $
    constrain <=< evalMotive (MAll (Eq true')) $ ListInfo $ LenInfo 0

  makeReport "(not (and [])) == true (expect bad)" $ do
    x <- evalMotive (MAll (Eq true')) $ ListInfo $ LenInfo 0
    constrain $ bnot x

  let mkAnd :: SBV Bool -> ListInfo 'BoolTy
      mkAnd = AllInfo . Eq . Sym

  makeReport "(and [true]) == true (expect good)" $
    constrain <=< evalMotive (MAll (Eq true')) $ ListInfo $ mkAnd true -- AndInfo $ SAnd true
      -- Lit [true]

  makeReport "(and [false]) == true (expect bad)" $
    constrain <=< evalMotive (MAll (Eq true')) $ ListInfo $ mkAnd false -- AndInfo $ SAnd false
      -- Lit [false]

  makeReport "and [false] /= true (expect good)" $ do
    constrain <=< evalMotive (MAll (Eq true')) $
      ListInfo $ mkAnd false -- AndInfo $ SAnd false
      -- Lit [false]

  makeReport "not (any (> 0) (all [> 0])) == false (expect bad)" $ do
    constrain <=< evalMotive (MNegate (MAny gt0)) $ ListInfo $ AllInfo gt0

  makeReport "not (all (> 0) (any [<= 0])) == true (expect good)" $ do
    constrain <=< evalMotive (MNegate (MAll gt0)) $ ListInfo $ AnyInfo lte0

  makeReport "at 2 [1, 2, 3] == 3 (expect good)" $ do
    constrain <=< evalMotive (MAt (LitI 2) (LitI 3)) $ ListInfo $ LitList
      [1, 2, 3]

  makeReport "at 2 [1, 2, 3] == 2 (expect bad)" $ do
    constrain <=< evalMotive (MAt (LitI 2) (LitI 2)) $ ListInfo $ LitList
      [1, 2, 3]

  let sumTo7 :: Expr ('List 'IntTy)
      sumTo7 = ListCat
        (ListInfo (SumInfo (Eq (LitI 3))))
        (ListInfo (SumInfo (Eq (LitI 4))))

  makeReport "sum almostAllPos == 7 (expect good)" $ do
    constrain =<< evalMotive (MSum (Eq (LitI 7))) sumTo7

true', false' :: Expr 'BoolTy
true'  = LitB true
false' = LitB false

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
