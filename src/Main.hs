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
  FoldInfo :: SymWord (Concrete b)
    -- consuming a list of a, where we operate on bs
    => (Expr a -> Expr b)
    -- fold
    -> Fold b
    -- result
    -> Expr b
    -> ListInfo a
  AtInfo       :: Expr 'IntTy -> Expr a                  -> ListInfo a
  ContainsInfo :: Expr a                                 -> ListInfo a
  ListCat      ::              ListInfo a -> ListInfo a  -> ListInfo a
  MapInfo      :: (Expr a -> Expr b) -> ListInfo b


pattern AllInfo :: (Expr a -> Expr b) -> ListInfo 'BoolTy
pattern AllInfo f = FoldInfo f And (LitB True)

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

    ListCat a b ->
      showString "ListCat "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
    MapInfo f fold as ->
        showString "MapInfo "
      . showsPrec 11 (f (Sym (uninterpret "x")))
      . showString " "
      . showsPrec 11 as

instance Show (Expr ty) where
  showsPrec p expr = showParen (p > 10) $ case expr of
    ListInfo i -> showString "ListInfo " . showsPrec 11 i
    LitB a     -> showString "LitB "     . showsPrec 11 a
    LitI a     -> showString "LitI "     . showsPrec 11 a

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
  ListInfo i -> case i of
    -- ListCat a b  -> eval a <> eval b
    -- MapInfo f as -> eval . f . lit <$> eval as
    _            -> error "cannot evaluate list info"

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
  ListInfo i -> case i of
    -- ListCat a b    -> sEval a .++ sEval b
    MapInfo{}      -> error "can't map with sbv lists"
    _              -> error "can't evaluate list info"

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
  :: forall a b. Suitable a
  => ListInfo b -> (Expr a -> Expr b) -> ListInfo a -> Symbolic (SBV Bool)
evalMotive l1'@(LitList l1) g (MapInfo f l2) =
  evalMotive l1' (g . f) l2
  -- pure $ SBVL.implode l1 .== sEval l2'

evalMotive (LenInfo len) f (ListCat a b) = do
  [al, bl] <- sIntegers ["al", "bl"]
  let totalLen = al + bl .== sEval len
  aLen <- evalMotive (LenInfo (Sym al)) f a
  bLen <- evalMotive (LenInfo (Sym bl)) f b
  pure $ totalLen &&& aLen &&& bLen
evalMotive (LenInfo len) f (MapInfo g lst)
  -- we won't evaluate f / g but we have to pass them through so the types
  -- align
  = evalMotive (LenInfo len) (f . g) lst
evalMotive (LenInfo len) _f (LenInfo len')
  = pure $ sEval len' .== sEval len

evalMotive (LenInfo len) _f (LitList l)
  = pure $ fromIntegral (length l) .== sEval len

evalMotive (FoldInfo fold target) f (ListCat a b) = do
  [targetA, targetB] <- mkExistVars 2
  let append = BinOp fold
  constrain $ sEval target .== sEval (Sym targetA `append` Sym targetB)
  (&&&)
    <$> evalMotive (FoldInfo fold (Sym targetA)) f a
    <*> evalMotive (FoldInfo fold (Sym targetB)) f b

-- g is at least as strong an assumption as f.
-- example:
-- f: for all i: elements of the list, i > 0
-- g: i need to know that for all i: elements of the list, i > -1
evalMotive (FoldInfo And target) f (FoldInfo And lst)
  = forAll' $ \j ->
    sEval (j `Eq` target)
    ==>
    sEval (j `Eq` lst)
evalMotive (FoldInfo Add target) f (FoldInfo Add lst)
  = forAll' $ \j ->
    sEval (j `Eq` target)
    ==>
    sEval (j `Eq` lst)

evalMotive (FoldInfo fold target) f (LenInfo len)
  | Just cLen <- unliteral (sEval len) = do
    vars <- mkExistVars (fromIntegral cLen)
    pure $
      sEval (foldr (BinOp fold) (empty fold) (f . Sym <$> vars))
      .==
      sEval target
  | otherwise = error "TODO: folding non-literal length list"

evalMotive (FoldInfo fold target) f (LitList l) = pure $
    sEval target
    .==
    sEval (foldr (BinOp fold) (empty fold) (f . Sym <$> l))
evalMotive (FoldInfo fold target) f (MapInfo g lst) =
  evalMotive (FoldInfo fold target) (f . g) lst

evalMotive FoldInfo{} _f _ = error "sorry, can't help with this motive"

evalMotive (AtInfo i a) f (ListCat l1 l2) = do
  case1 <- evalMotive (AtInfo i a) f l1
  error "TODO"
  -- let l1' = sEval l1
  --     i'  = sEval i
  -- case2 <- evalMotive (AtInfo (Sym (i' - SBVL.length l1')) a) f l2
  -- pure $ case1 ||| case2

evalMotive m@AtInfo{} f (MapInfo g lst) = evalMotive m (f . g) lst
evalMotive (AtInfo i a) f (LitList litList) = pure $
  let iV = sEval i
      aV = sEval a
  in fromIntegral (length litList) .> iV &&&
     (SBVL.implode (fmap (error "TODO") litList) SBVL..!! iV) .== aV


gt0 :: Expr 'IntTy -> Expr 'BoolTy
gt0 x = Gt x 0

lte0 :: Expr 'IntTy -> Expr 'BoolTy
lte0 x = Not (Gt x 0)

pattern AnyM :: (Expr a -> Expr 'BoolTy) -> ListInfo a
pattern AnyM f = FoldInfo (MapInfo f) And (LitB False)

mkTest
  :: forall a b. Suitable a
  => Validity -> ListInfo b -> (Expr a -> Expr b) -> Symbolic (ListInfo a) -> Test ()
mkTest expectValid motive f expr = do
  (valid, vacuous) <- io $ do
    let constraints = constrain =<< evalMotive motive f =<< expr
    (,) <$> isTheorem constraints <*> isVacuous constraints

  expect $ if expectValid == Valid
    then valid
    else (not valid || vacuous)

data Validity = Valid | Invalid
  deriving Eq

main :: IO ()
main = do
  let almostAllPos :: ListInfo 'IntTy
      almostAllPos = ListCat
        (AllInfo gt0)
        (ListCat
          (AllInfo (Eq 0))
          (AllInfo gt0))

      sumTo7 :: ListInfo 'IntTy
      sumTo7 = ListCat
        (FoldInfo Add 3)
        (FoldInfo Add 4)

  run $ tests
    [ scope "any (> 0) [1, 2, 3]" $
        mkTest Valid AnyM (bnot . gt0) $ pure $ ListInfo $ LitList [1, 2, 3]
    , scope "any (> 0) [-1, 2, 3]" $
        mkTest Valid AnyM (bnot . gt0) $ pure $ ListInfo $ LitList [-1, 2, 3]

    , scope "any (> 0) [a, -1, 3]" $ do
        mkTest Valid AnyM (bnot . gt0) $ do
          a <- sInteger "a"
          pure $ ListInfo $ LitList [a, -1, 3]

    , scope "all (> 0) [a, -1, 3]" $
      mkTest Invalid (FoldInfo And true) gt0 $ do
        a <- sInteger "a"
        pure $ ListInfo $ LitList [a, -1, 3]

    , scope "length [] == 0" $ do
        let lst = ListInfo (LenInfo 0) :: Expr ('List 'IntTy)
        mkTest Valid (LenInfo 0) id $ pure lst

    , scope "length (len 2) == 2" $ do
        let lst :: Expr ('List 'IntTy)
            lst = ListInfo (LenInfo 2)
        mkTest Valid (LenInfo 2) id $ pure lst

      -- show that the result of a mapping is all positive
    , scope "fmap (> 0) lst == true" $ do
        let lst = ListInfo (AllInfo gt0) :: Expr ('List 'IntTy)
        mkTest Valid (FoldInfo And true) gt0 $ pure lst

    , scope "fmap (> 0) almostAllPos == true" $
        mkTest Invalid (FoldInfo And true) gt0 $ pure almostAllPos

    , scope "(and []) == true" $
        mkTest Valid (FoldInfo And true) (Eq @'BoolTy true)
          $ pure $ ListInfo $ LenInfo 0

    , scope "all (eq true) [] /= false" $ do
        mkTest Invalid (FoldInfo And false) (Eq @'BoolTy true)
          $ pure $ ListInfo $ LenInfo 0

    , scope "(and [true]) == true" $
        mkTest @'BoolTy Valid (FoldInfo And true) (Eq true)
          $ pure $ ListInfo $ AllInfo $ Eq $ Sym true

    , scope "(and [false]) == true" $
        mkTest Invalid
          (FoldInfo And true) (Eq true)
          $ pure $ ListInfo $ FoldInfo id And false

    , scope "and [false] /= true" $
        mkTest Valid
          (FoldInfo And false) (Eq true)
          $ pure $ ListInfo $ FoldInfo id And false

    , scope "all (> 0) => (not (any (> 0)) == false)" $
        mkTest Invalid
          (FoldInfo And false) gt0
          $ pure $ ListInfo $ AllInfo gt0

    , scope "any (<= 0) => not (all (> 0))" $
        mkTest Valid
          (FoldInfo And false) gt0
          $ pure $ ListInfo $ FoldInfo (bnot . lte0) And false

    , scope "at 2 [1, 2, 3] == 3" $
        mkTest Valid
          (AtInfo (LitI 2) (LitI 3)) id
          $ pure $ ListInfo $ LitList [1, 2, 3]

    , scope "at 2 [1, 2, 3] == 2" $
        mkTest Invalid
          (AtInfo (LitI 2) (LitI 2)) id
          $ pure $ ListInfo $ LitList [1, 2, 3]

    , scope "sum sumTo7 == 7" $
        mkTest Valid (FoldInfo Add 7) id $ pure sumTo7

    , scope "sum (map (const 1) [length 7]) == 7" $ do
        let lst :: Expr ('List 'IntTy)
            lst = ListInfo (LenInfo 7)
        mkTest Valid (FoldInfo Add 7) (const 1) $ pure lst
    ]
