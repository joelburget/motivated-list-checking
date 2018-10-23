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

import Data.Foldable (foldrM)
import Control.Monad.Except
import           Data.SBV
import           Data.SBV.List ((.++))
import           EasyTest
import           Prelude       as P hiding (concat, init)
import Data.List (find)
import           Data.Type.Equality           ((:~:) (Refl), apply)


data Ty
  = List Ty
  | IntTy
  | BoolTy
  deriving Show

data SingTy :: Ty -> * where
  SList :: SingTy a -> SingTy ('List a)
  SInt  ::             SingTy 'IntTy
  SBool ::             SingTy 'BoolTy

singEq :: SingTy a -> SingTy b -> Maybe (a :~: b)
singEq (SList a) (SList b) = apply Refl <$> singEq a b
singEq SInt      SInt      = Just Refl
singEq SBool     SBool     = Just Refl

instance Show (SingTy ty) where
  showsPrec p = \case
    SList a -> showParen (p > 10) $ showString "SList " . showsPrec 11 a
    SInt    -> showString "SInt"
    SBool   -> showString "SBool"

type family Concrete (ty :: Ty) where
  Concrete ('List a) = [Concrete a]
  Concrete 'IntTy    = Integer
  Concrete 'BoolTy   = Bool

data Existential where
  Exists :: SingTy ty -> Expr ty -> Existential

example :: Existential
example = Exists (SList SInt) (ListInfo (LitList [1, 2, 3]))

class Sing ty where
  sing :: SingTy ty

instance Sing 'BoolTy where
  sing = SBool

instance Sing 'IntTy where
  sing = SInt

instance Sing a => Sing ('List a) where
  sing = SList sing

data Expr (ty :: Ty) where
  -- transducers
  ListCat      :: SingTy a -> Expr ('List a)     -> Expr ('List a) -> Expr ('List a)
  ListMap      :: SingTy a -> (Expr a -> Expr b) -> Expr ('List a) -> Expr ('List b)

  ListLen      ::                                             Expr ('List a) -> Expr 'IntTy
  ListFold     :: SingTy a -> (Expr a -> Expr b) -> Fold b -> Expr ('List a) -> Expr b
  ListAt       ::                              Expr 'IntTy -> Expr ('List a) -> Expr a
  ListContains ::                       SingTy a -> Expr a -> Expr ('List a) -> Expr 'BoolTy

  -- other
  Eq           :: SingTy a -> Expr a -> Expr a -> Expr 'BoolTy
  Gt           ::  Expr 'IntTy -> Expr 'IntTy  -> Expr 'BoolTy
  Not          ::                 Expr 'BoolTy -> Expr 'BoolTy
  BinOp        ::   Fold a -> Expr a -> Expr a -> Expr a

  LitB         :: Concrete 'BoolTy -> Expr 'BoolTy
  LitI         :: Concrete 'IntTy  -> Expr 'IntTy

  SymB         :: SBV Bool    -> Expr 'BoolTy
  SymI         :: SBV Integer -> Expr 'IntTy

  ListInfo     :: ListInfo a -> Expr ('List a)

symOf :: SingTy ty -> SBV (Concrete ty) -> Expr ty
symOf (SList _) _ = error "we don't support symbolic lists"
symOf SInt  s     = SymI s
symOf SBool s     = SymB s

litOf :: SingTy ty -> Concrete ty -> Expr ty
litOf (SList ty) l = ListInfo $ LitList $ litOf ty <$> l
litOf SInt       i = LitI i
litOf SBool      b = LitB b

varOf :: SingTy ty -> String -> Expr ty
varOf (SList _) _ = error "we don't support list variables"
varOf SInt      v = symOf SInt  (uninterpret v)
varOf SBool     v = symOf SBool (uninterpret v)

eqOf :: SingTy ty -> Concrete ty -> Concrete ty -> Bool
eqOf (SList ty) a b = length a == length b && and (zipWith (eqOf ty) a b)
eqOf SInt       a b = a == b
eqOf SBool      a b = a == b

forAllOf :: Provable t => SingTy ty -> (Expr ty -> t) -> Predicate
forAllOf = undefined

lit :: Sing ty => Concrete ty -> Expr ty
lit = litOf sing

sym :: Sing ty => SBV (Concrete ty) -> Expr ty
sym = symOf sing

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

foldOp :: Fold a -> Concrete a -> Concrete a -> Concrete a
foldOp = \case
  Add -> (+)
  And -> (&&)

sFoldOp :: Fold a -> SBV (Concrete a) -> SBV (Concrete a) -> SBV (Concrete a)
sFoldOp = \case
  Add -> (+)
  And -> (&&&)

-- "My claim is that we should exploit a hypothesis not in terms of its
-- immediate consequences, but in terms of the leverage it exerts on an
-- arbitrary goal: we should give elimination a motive"

data ListInfo (ty :: Ty) where
  LitList      :: [Expr a]    -> ListInfo a
  LenInfo      :: Expr 'IntTy -> ListInfo a
  FoldInfo
    :: SingTy a
    -> SingTy b
    -- consuming a list of a, where we operate on bs
    -> (Expr a -> Expr b)
    -- fold
    -> Fold b
    -- result
    -> Expr b
    -> ListInfo a

  AtInfo       :: Expr 'IntTy -> Expr a -> ListInfo a
  ContainsInfo :: Expr a                -> ListInfo a

  MapInfo :: SingTy a -> SingTy b -> (Expr a -> Expr b) -> Expr b -> ListInfo a

allInfo :: (Sing a, b ~ 'BoolTy) => (Expr a -> Expr b) -> ListInfo a
allInfo f = FoldInfo sing SBool f And (LitB True)

instance Show (ListInfo ty) where
  showsPrec p li = showParen (p > 10) $ case li of
    LitList l -> showString "LitList " . showsPrec 11 l
    LenInfo i -> showString "LenInfo " . showsPrec 11 i
    FoldInfo a b f fold result ->
        showString "FoldInfo "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
      . showString " "
      . showsPrec 11 (f (varOf a "x"))
      . showString " "
      . showsPrec 11 fold
      . showString " "
      . showsPrec 11 result
    AtInfo i a ->
        showString "AtInfo "
      . showsPrec 11 i
      . showString " "
      . showsPrec 11 a
    ContainsInfo a -> showString "ContainsInfo " . showsPrec 11 a
    MapInfo a b f bs ->
        showString "MapInfo "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
      . showString " "
      . showsPrec 11 (f (varOf a "x"))
      . showString " "
      . showsPrec 11 bs

instance Show (Expr ty) where
  showsPrec p expr = showParen (p > 10) $ case expr of
    ListCat ty a b ->
      showString "ListCat "
      . showsPrec 11 ty
      . showString " "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
    ListMap a f as ->
        showString "ListMap "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 (f (varOf a "x"))
      . showString " "
      . showsPrec 11 as
    ListLen as ->
        showString "ListLen "
      . showsPrec 11 as
    ListFold a f fempty as ->
        showString "ListFold "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 (f (varOf a "x"))
      . showString " "
      . showsPrec 11 fempty
      . showString " "
      . showsPrec 11 as
    ListAt i a ->
        showString "ListAt "
      . showsPrec 11 i
      . showString " "
      . showsPrec 11 a
    ListContains tyA a as ->
        showString "ListAt "
      . showsPrec 11 tyA
      . showString " "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 as

    LitB a     -> showString "LitB "     . showsPrec 11 a
    LitI a     -> showString "LitI "     . showsPrec 11 a
    ListInfo i -> showString "ListInfo " . showsPrec 11 i

    Eq ty a b ->
        showString "Eq "
      . showsPrec 11 ty
      . showString " "
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

    SymB a -> showsPrec 11 a
    SymI a -> showsPrec 11 a

eval :: Expr ty -> Concrete ty
eval = \case
  ListCat _ a b      -> eval a <> eval b
  ListMap a f as     -> eval . f . litOf a <$> eval as
  ListLen l          -> fromIntegral $ length $ eval l
  ListFold a f fold l  -> foldr
    (foldOp fold)
    (eval (empty fold))
    (fmap (eval . f . litOf a) (eval l))
  ListAt i l         -> eval l !! fromIntegral (eval i)
  ListContains ty a as -> case find (eqOf ty (eval a)) (eval as) of
    Just _  -> True
    Nothing -> False
  Eq ty a b -> eqOf ty (eval a) (eval b)
  Gt a b    -> eval a > eval b
  Not a     -> not (eval a)

  BinOp op a b       -> foldOp op (eval a) (eval b)

  LitB a             -> a
  LitI a             -> a
  ListInfo i -> case i of
    LitList l -> fmap eval l
    _         -> error "can't evaluate non-literal list"

  SymB _ -> error "canot evaluate symbolic value"
  SymI _ -> error "canot evaluate symbolic value"

forceRight :: Either a b -> b
forceRight (Left _) = error "unexpected left"
forceRight (Right b) = b

sEval
  :: Expr ty -> ExceptT String Symbolic (SBV (Concrete ty))
sEval = \case
  ListCat SBool a b     -> (.++) <$> sEval a <*> sEval b
  ListCat SInt  a b     -> (.++) <$> sEval a <*> sEval b
  ListCat (SList _) a b -> throwError "nested lists not allowed"
  ListMap{}             -> throwError "can't map with sbv lists"

  ListLen (ListInfo (LenInfo len)) -> sEval len

  ListFold _a f fold (ListInfo (LitList l)) ->  do
    init  <- sEval (empty fold)
    elems <- traverse (sEval . f) l
    foldrM
      (\x y -> pure $ sFoldOp fold x y)
      init
      elems

  ListFold a1 f And (ListInfo (FoldInfo a2 _b g And result)) ->
    case singEq a1 a2 of
      Nothing   -> throwError "can't compare folds of different types"
      Just Refl -> do
        -- init <- sEval (empty And)

        -- lift $ forAllOf a1 $ \i ->
        --   fmap forceRight (runExceptT (sEval (f i `eq` sym init)))
        --   ==>
        --   fmap forceRight (runExceptT (sEval (g i `eq` result)))

        sEval result

  ListFold a1 f Add (ListInfo (FoldInfo a2 _b g Add result)) ->
    case singEq a1 a2 of
      Nothing   -> throwError "can't compare folds of different types"
      -- XXX: f and g must be equal
      Just Refl -> sEval result

  ListFold a f fold (ListCat _ l1 l2) -> sFoldOp fold
    <$> sEval (ListFold a f fold l1)
    <*> sEval (ListFold a f fold l2)

  ListFold _ _ fold (ListInfo (LenInfo len)) -> do
    len' <- sEval len
    case unliteral len' of
      Just 0  -> sEval $ empty fold
      Just _  -> throwError "can't determine fold of this list"
      Nothing -> throwError "can't determine fold of this list"

  ListAt i (ListInfo (AtInfo j v)) -> do
    i' <- sEval i
    j' <- sEval j
    case (unliteral i', unliteral j') of
      (Just i'', Just j'') -> if i'' == j'' then sEval v else throwError ""

  ListAt i (ListInfo (LitList l)) -> do
    i' <- sEval i
    case unliteral i' of
      Just i'' ->
        if length l > fromIntegral i''
        then sEval $ l !! fromIntegral i''
        else throwError "indexing beyond the end of the list"

  -- ListContains a as  -> eval a `elem` eval as

  Eq ty a b -> (.==) <$> sEval a <*> sEval b
  Gt a b    -> (.>)  <$> sEval a <*> sEval b
  Not a     -> bnot  <$> sEval a

  BinOp op a b -> case op of
    And -> (&&&) <$> sEval a <*> sEval b
    Add -> (+)   <$> sEval a <*> sEval b

  LitB a -> pure $ literal a
  LitI a -> pure $ literal a
  SymB a -> pure $ a
  SymI a -> pure $ a

-- forAll' :: (SymWord (Concrete a), Provable t) => (Expr a -> t) -> Predicate
-- forAll' f = forAll_ $ f . sym

-- evalMotive
--   :: forall a. Suitable a
--   => ListInfo a -> Expr ('List a) -> Maybe (Symbolic (SBV (Concrete a)))
-- evalMotive (LenInfo len) (ListLen lst) = Just $ pure $ sEval len

-- evalMotive _ Sym{} = error "can't motivate evaluation of symbolic value"

-- evalMotive (LitList l1) l2'@(ListMap f l2) = pure $
--   SBVL.implode l1 .== sEval l2'

-- evalMotive (LenInfo len) (ListCat a b) = do
--   [al, bl] <- sIntegers ["al", "bl"]
--   let totalLen = al + bl .== sEval len
--   aLen <- evalMotive (LenInfo (Sym al)) a
--   bLen <- evalMotive (LenInfo (Sym bl)) b
--   pure $ totalLen &&& aLen &&& bLen
-- evalMotive (LenInfo len) (ListMap _ lst) = evalMotive (LenInfo len) lst
-- evalMotive (LenInfo len) (ListLen lst)
--   = pure $ sEval len .== sEval len'
-- evalMotive (LenInfo len) (LitList l)
--   = pure $ fromIntegral (length l) .== sEval len

-- evalMotive (FoldInfo mapping fold target) (ListCat a b) = do
--   [targetA, targetB] <- mkExistVars 2
--   let append = BinOp fold
--   constrain $ sEval target .== sEval (Sym targetA `append` Sym targetB)
--   (&&&)
--     <$> evalMotive (FoldInfo mapping fold (Sym targetA)) a
--     <*> evalMotive (FoldInfo mapping fold (Sym targetB)) b

-- -- g is at least as strong an assumption as f.
-- -- example:
-- -- f: for all i: elements of the list, i > 0
-- -- g: i need to know that for all i: elements of the list, i > -1
-- evalMotive (FoldInfo f And target) (ListFold g And lst)
--   = forAll' $ \j ->
--     sEval (f j `Eq` target)
--     ==>
--     sEval (g j `Eq` lst)
-- evalMotive (FoldInfo f Add target) (ListFold g Add lst)
--   = forAll' $ \j ->
--     sEval (f j `Eq` target)
--     ==>
--     sEval (g j `Eq` lst)

-- evalMotive (FoldInfo mapping fold target) (LenInfo len)
--   | Just cLen <- unliteral (sEval len) = do
--     vars <- mkExistVars (fromIntegral cLen)
--     pure $
--       sEval (foldr (BinOp fold) (empty fold) (fmap (mapping . Sym) vars))
--       .==
--       sEval target
--   | otherwise = error "TODO: folding non-literal length list"
-- evalMotive (FoldInfo mapping fold target) (LitList l)
--   = pure $
--     sEval target
--     .==
--     sEval (foldr (BinOp fold) (empty fold) (fmap (mapping . Sym) l))
-- evalMotive (FoldInfo mapping fold target) (ListMap g lst) =
--   evalMotive (FoldInfo (mapping . g) fold target) lst

-- evalMotive FoldInfo{} _ = error "sorry, can't help with this motive"

-- evalMotive (AtInfo i a) (ListCat l1 l2) = do
--     let l1' = sEval l1
--         l2' = sEval l2
--         i'  = sEval i
--         a'  = sEval a
--     pure $
--       l1' .!! i'                     .== a' |||
--       l2' .!! (i' - SBVL.length l1') .== a'
-- evalMotive (AtInfo i _) (ListMap _ lst) = evalMotive (AtInfo i (error "TODO")) lst
-- evalMotive (AtInfo i a) (LitList litList) = pure $
--     let iV = sEval i
--         aV = sEval a
--     in fromIntegral (length litList) .> iV &&&
--        (SBVL.implode litList SBVL..!! iV) .== aV

-- evalMotive LenInfo{} BinOp{} = error "vacuous match"
-- evalMotive AtInfo{}  BinOp{} = error "vacuous match"

gt0 :: Expr 'IntTy -> Expr 'BoolTy
gt0 x = Gt x 0

lte0 :: Expr 'IntTy -> Expr 'BoolTy
lte0 x = Not (Gt x 0)

mkTest :: Validity -> Symbolic (Expr 'BoolTy) -> Test ()
mkTest expectValid expr = do
  (valid, vacuous) <- io $ do
    let constraints = do
          expr'  <- expr
          result <- runExceptT $ sEval expr'
          case result of
            Left msg      -> error msg
            Right result' -> constrain result'
    (,) <$> isTheorem constraints <*> isVacuous constraints

  expect $ if expectValid == Valid
    then valid
    else (not valid || vacuous)

data Validity = Valid | Invalid
  deriving Eq

mkAny
  :: Sing a
  => (Expr a -> Expr 'BoolTy) -> ListInfo a -> Expr 'BoolTy
mkAny f = ListFold sing (bnot . f) And . ListInfo

mkAll
  :: Sing a
  => (Expr a -> Expr 'BoolTy) -> ListInfo a -> Expr 'BoolTy
mkAll f = ListFold sing f And . ListInfo

mkAnd :: ListInfo 'BoolTy -> Expr 'BoolTy
mkAnd = mkAll id

eq
  :: Sing a
  => Expr a -> Expr a -> Expr 'BoolTy
eq = Eq sing

mkFoldInfo
  :: (Sing a, Sing b)
  => (Expr a -> Expr b) -> Fold b -> Expr b -> ListInfo a
mkFoldInfo = FoldInfo sing sing

mkFold
  :: Sing a
  => (Expr a -> Expr b) -> Fold b -> Expr ('List a) -> Expr b
mkFold = ListFold sing

main :: IO ()
main = do
  let almostAllPos :: Expr ('List 'IntTy)
      almostAllPos = ListCat SInt
        (ListInfo (allInfo gt0))
        (ListCat SInt
          (ListInfo (allInfo (Eq SInt 0)))
          (ListInfo (allInfo gt0)))

      sumTo7 :: Expr ('List 'IntTy)
      sumTo7 = ListCat SInt
        (ListInfo (mkFoldInfo id Add 3))
        (ListInfo (mkFoldInfo id Add 4))

  run $ tests
    [ scope "any (> 0) [1, 2, 3]" $
        mkTest Valid $ pure $ mkAny gt0 $ LitList [1, 2, 3]

    , scope "any (> 0) [-1, 2, 3]" $
        mkTest Valid $ pure $ mkAny gt0 $ LitList [lit (-1), 2, 3]

    , scope "any (> 0) [a, -1, 3]" $ do
        mkTest Valid $ do
          a <- sInteger "a"
          pure $ mkAny gt0 $ LitList [sym a, lit (-1), 3]

    , scope "all (> 0) [a, -1, 3]" $
      mkTest Invalid  $ do
        a <- sInteger "a"
        pure $ mkAll gt0 $ LitList [sym a, lit (-1), 3]

    , scope "length [] == 0" $
        mkTest Valid $ pure $ ListLen (ListInfo (LenInfo 0)) `eq` 0

    , scope "length (len 2) == 2" $
        mkTest Valid $ pure $ ListLen (ListInfo (LenInfo 2)) `eq` 2

      -- show that the result of a mapping is all positive
    , scope "fmap (> 0) lst == true" $
        mkTest Valid $ pure $
          mkAll gt0 $ allInfo gt0

    , scope "fmap (> 0) almostAllPos == true" $
        mkTest Invalid $ pure $
          mkFold gt0 And almostAllPos

    , scope "(and []) == true" $
        mkTest Valid $ pure $
          mkAnd $ LenInfo 0

    , scope "all (eq true) [] /= false" $ do
        mkTest Invalid $ pure $ Not $
          mkAnd $ LenInfo 0

    , scope "(and [true]) == true" $
        mkTest Valid $ pure $
          mkAnd $ allInfo $ eq true

    , scope "(and [false]) == true" $
        mkTest Invalid $ pure $
          mkAnd $ mkFoldInfo id And false

    , scope "and [false] /= true" $
        mkTest Valid $ pure $
          mkAnd $ mkFoldInfo id And false

    , scope "all (> 0) => (not (any (> 0)) == false)" $
        mkTest Invalid $ pure $
          bnot $ mkAny gt0 $ allInfo gt0

    , scope "any (<= 0) => not (all (> 0))" $
        mkTest Valid $ pure $
          mkAll gt0 $ mkFoldInfo (bnot . lte0) And false

    , scope "at 2 [1, 2, 3] == 3" $
        mkTest Valid $ pure $
          ListAt 2 (ListInfo (LitList [1, 2, 3])) `eq` LitI 3

    , scope "at 2 [1, 2, 3] == 2" $
        mkTest Invalid $ pure $
          ListAt 2 (ListInfo (LitList [1, 2, 3])) `eq` LitI 2

    , scope "sum sumTo7 == 7" $
        mkTest Valid $ pure $
          mkFold id Add sumTo7
          `eq`
          7

    , scope "sum (map (const 1) [length 7]) == 7" $ do
        let lst :: Expr ('List 'IntTy)
            lst = ListInfo (LenInfo 7)
        mkTest Valid $ pure $
          mkFold (const 1) Add lst
          `eq`
          7
    ]
