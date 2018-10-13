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

import           Data.SBV
import           Data.SBV.List ((.!!), (.++))
import qualified Data.SBV.List as SBVL
import           EasyTest
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

empty :: Fold a -> Expr a
empty = \case
  Add -> 0
  And -> true

-- "My claim is that we should exploit a hypothesis not in terms of its
-- immediate consequences, but in terms of the leverage it exerts on an
-- arbitrary goal: we should give elimination a motive"

data ListInfo a where
  LitList      :: [SBV (Concrete a)]                     -> ListInfo a
  LenInfo      :: Expr 'IntTy                            -> ListInfo a
  FoldInfo     :: SymWord (Concrete b)
    -- consuming a list of a, where we operate on bs
    => (Expr a -> Expr b)
    -- fold
    -> Fold b
    -- result
    -> Expr b
    -> ListInfo a
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

forAll' :: (SymWord (Concrete a), Provable t) => (Expr a -> t) -> Predicate
forAll' f = forAll_ $ f . Sym

evalMotive
  :: forall a. Suitable a
  => ListInfo a -> Expr ('List a) -> Symbolic (SBV Bool)
evalMotive _ Sym{} = error "can't motivate evaluation of symbolic value"

evalMotive (LitList l1) l2'@(ListMap f l2) = pure $
  SBVL.implode l1 .== sEval l2'

evalMotive (LenInfo len) (ListCat a b) = do
  [al, bl] <- sIntegers ["al", "bl"]
  let totalLen = al + bl .== sEval len
  aLen <- evalMotive (LenInfo (Sym al)) a
  bLen <- evalMotive (LenInfo (Sym bl)) b
  pure $ totalLen &&& aLen &&& bLen
evalMotive (LenInfo len) (ListMap _ lst) = evalMotive (LenInfo len) lst
evalMotive (LenInfo len) (ListInfo i) =
  let lenV = sEval len
  in case i of
       LenInfo len' -> pure $ sEval len'              .== lenV
       LitList l    -> pure $ fromIntegral (length l) .== lenV
       _            -> error $
         "sorry, can't help with this motive: " ++ show i

evalMotive (FoldInfo mapping fold target) (ListCat a b) = do
  [targetA, targetB] <- mkExistVars 2
  let append = BinOp fold
  constrain $ sEval target .== sEval (Sym targetA `append` Sym targetB)
  (&&&)
    <$> evalMotive (FoldInfo mapping fold (Sym targetA)) a
    <*> evalMotive (FoldInfo mapping fold (Sym targetB)) b

-- g is at least as strong an assumption as f.
-- example:
-- f: for all i: elements of the list, i > 0
-- g: i need to know that for all i: elements of the list, i > -1
evalMotive (FoldInfo f And target) (ListInfo (FoldInfo g And lst))
  = forAll' $ \j ->
    sEval (f j `Eq` target)
    ==>
    sEval (g j `Eq` lst)
evalMotive (FoldInfo f Add target) (ListInfo (FoldInfo g Add lst))
  = forAll' $ \j ->
    sEval (f j `Eq` target)
    ==>
    sEval (g j `Eq` lst)

evalMotive (FoldInfo mapping fold target) (ListInfo info) = case (fold, info) of
  (_, LenInfo len)
    | Just cLen <- unliteral (sEval len) -> do
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
evalMotive (FoldInfo mapping fold target) (ListMap g lst) =
  evalMotive (FoldInfo (mapping . g) fold target) lst

evalMotive FoldInfo{} _ = error "sorry, can't help with this motive"

evalMotive (AtInfo i a) (ListCat l1 l2) = do
    let l1' = sEval l1
        l2' = sEval l2
        i'  = sEval i
        a'  = sEval a
    pure $
      l1' .!! i'                     .== a' |||
      l2' .!! (i' - SBVL.length l1') .== a'
evalMotive (AtInfo i _) (ListMap _ lst) = evalMotive (AtInfo i (error "TODO")) lst
evalMotive (AtInfo i a) (ListInfo info) = case info of
  LitList litList -> pure $
    let iV = sEval i
        aV = sEval a
    in fromIntegral (length litList) .> iV &&&
       (SBVL.implode litList SBVL..!! iV) .== aV

  _ -> error "can't help with this motive"

evalMotive LenInfo{} BinOp{} = error "vacuous match"
evalMotive AtInfo{}  BinOp{} = error "vacuous match"

gt0 :: Expr 'IntTy -> Expr 'BoolTy
gt0 x = Gt x 0

lte0 :: Expr 'IntTy -> Expr 'BoolTy
lte0 x = Not (Gt x 0)

mkAnyM :: (Expr a -> Expr 'BoolTy) -> ListInfo a
mkAnyM f = FoldInfo (bnot . f) And false

mkTest
  :: forall a. Suitable a
  => Validity -> ListInfo a -> Symbolic (Expr ('List a)) -> Test ()
mkTest expectValid motive expr = do
  (valid, vacuous) <- io $ do
    let constraints = constrain =<< evalMotive motive =<< expr
    (,) <$> isTheorem constraints <*> isVacuous constraints

  expect $ if expectValid == Valid
    then valid
    else (not valid || vacuous)

data Validity = Valid | Invalid
  deriving Eq

main :: IO ()
main = do
  let almostAllPos :: Expr ('List 'IntTy)
      almostAllPos = ListCat
        (ListInfo (AllInfo gt0))
        (ListCat
          (ListInfo (AllInfo (Eq 0)))
          (ListInfo (AllInfo gt0)))

      sumTo7 :: Expr ('List 'IntTy)
      sumTo7 = ListCat
        (ListInfo (FoldInfo id Add 3))
        (ListInfo (FoldInfo id Add 4))

  run $ tests
    [ scope "any (> 0) [1, 2, 3]" $
        mkTest Valid (mkAnyM gt0) $ pure $ ListInfo $ LitList [1, 2, 3]
    , scope "any (> 0) [-1, 2, 3]" $
        mkTest Valid (mkAnyM gt0) $ pure $ ListInfo $ LitList [-1, 2, 3]

    , scope "any (> 0) [a, -1, 3]" $ do
        mkTest Valid (mkAnyM gt0) $ do
          a <- sInteger "a"
          pure $ ListInfo $ LitList [a, -1, 3]

    , scope "all (> 0) [a, -1, 3]" $
      mkTest Invalid (FoldInfo gt0 And true) $ do
        a <- sInteger "a"
        pure $ ListInfo $ LitList [a, -1, 3]

    , scope "length [] == 0" $ do
        let lst = ListInfo (LenInfo 0) :: Expr ('List 'IntTy)
        mkTest Valid (LenInfo 0) $ pure lst

    , scope "length (len 2) == 2" $ do
        let lst :: Expr ('List 'IntTy)
            lst = ListInfo (LenInfo 2)
        mkTest Valid (LenInfo 2) $ pure lst

      -- show that the result of a mapping is all positive
    , scope "fmap (> 0) lst == true" $ do
        let lst = ListInfo (AllInfo gt0) :: Expr ('List 'IntTy)
        mkTest Valid (FoldInfo gt0 And true) $ pure lst

    , scope "fmap (> 0) almostAllPos == true" $
        mkTest Invalid (FoldInfo gt0 And true) $ pure almostAllPos

    , scope "(and []) == true" $
        mkTest Valid (FoldInfo (Eq @'BoolTy true) And true)
          $ pure $ ListInfo $ LenInfo 0

    , scope "all (eq true) [] /= false" $ do
        mkTest Invalid (FoldInfo (Eq @'BoolTy true) And false)
          $ pure $ ListInfo $ LenInfo 0

    , scope "(and [true]) == true" $
        mkTest @'BoolTy Valid (FoldInfo (Eq true) And true)
          $ pure $ ListInfo $ AllInfo $ Eq $ Sym true

    , scope "(and [false]) == true" $
        mkTest Invalid
          (FoldInfo (Eq true) And true)
          $ pure $ ListInfo $ FoldInfo id And false

    , scope "and [false] /= true" $
        mkTest Valid
          (FoldInfo (Eq true) And false)
          $ pure $ ListInfo $ FoldInfo id And false

    , scope "all (> 0) => (not (any (> 0)) == false)" $
        mkTest Invalid
          (FoldInfo gt0 And false)
          $ pure $ ListInfo $ AllInfo gt0

    , scope "any (<= 0) => not (all (> 0))" $
        mkTest Valid
          (FoldInfo gt0 And false)
          $ pure $ ListInfo $ FoldInfo (bnot . lte0) And false

    , scope "at 2 [1, 2, 3] == 3" $
        mkTest Valid
          (AtInfo (LitI 2) (LitI 3))
          $ pure $ ListInfo $ LitList [1, 2, 3]

    , scope "at 2 [1, 2, 3] == 2" $
        mkTest Invalid
          (AtInfo (LitI 2) (LitI 2))
          $ pure $ ListInfo $ LitList [1, 2, 3]

    , scope "sum sumTo7 == 7" $
        mkTest Valid (FoldInfo id Add 7) $ pure sumTo7

    , scope "sum (map (const 1) [length 7]) == 7" $ do
        let lst :: Expr ('List 'IntTy)
            lst = ListInfo (LenInfo 7)
        mkTest Valid (FoldInfo (const 1) Add 7) $ pure lst
    ]
