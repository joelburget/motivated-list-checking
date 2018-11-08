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
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE Rank2Types           #-}
module Main where

import Control.Applicative ((<|>))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldrM)
import Control.Monad.Except
import           Data.SBV
import           Data.SBV.List ((.++))
import           EasyTest
import           Prelude       as P hiding (concat, init)
import Data.List (find)
import           Data.Type.Equality           ((:~:) (Refl), apply)
import Data.Constraint (withDict, Dict(Dict))
import Control.Monad.Loops
import Control.Lens hiding (List, Fold, (.>), op)


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
singEq _         _         = Nothing

instance Show (SingTy ty) where
  showsPrec p = \case
    SList a -> showParen (p > 10) $ showString "SList " . showsPrec 11 a
    SInt    -> showString "SInt"
    SBool   -> showString "SBool"

type family Concrete (ty :: Ty) where
  Concrete ('List a) = [Concrete a]
  Concrete 'IntTy    = Integer
  Concrete 'BoolTy   = Bool

data ETy where
  ETy :: SingTy ty -> ETy

instance Show ETy where
  showsPrec p (ETy ty) = showParen (p > 10) $
      showString "ETy "
    . showsPrec 11 ty

data Existential tm where
  Exists :: SingTy ty -> tm ty -> Existential tm

type EExpr = Existential Expr

instance Show EExpr where
  showsPrec p (Exists ty expr) = showParen (p > 10) $
      showString "Exists "
    . showsPrec 11 ty
    . showString " "
    . showsPrec 11 expr

type ELI = Existential ListInfo

instance Show ELI where
  showsPrec p (Exists ty info) = showParen (p > 10) $
      showString "Exists "
    . showsPrec 11 ty
    . showString " "
    . showsPrec 11 info

newtype ConcreteList ty = ConcreteList [Expr ty]
  deriving Show

type EConcreteList = Existential ConcreteList

instance Show EConcreteList where
  showsPrec p (Exists ty list) = showParen (p > 10) $
      showString "Exists "
    . showsPrec 11 ty
    . showString " "
    . showsPrec 11 list

example :: EExpr
example = Exists (SList SInt) (ListInfo sing (LitList [1, 2, 3]))

class Sing ty where
  sing :: SingTy ty

instance Sing 'BoolTy where
  sing = SBool

instance Sing 'IntTy where
  sing = SInt

instance Sing a => Sing ('List a) where
  sing = SList sing

withEq :: forall a r. SingTy a -> (Eq (Concrete a) => r) -> r
withEq ty = withDict dict
  where dict :: Dict (Eq (Concrete a))
        dict = case ty of
          SInt    -> Dict
          SBool   -> Dict
          SList a -> withEq a $ Dict

withSymWord :: forall a r. SingTy a -> (SymWord (Concrete a) => r) -> r
withSymWord ty f = case ty of
  SInt    -> withDict (Dict :: Dict (SymWord (Concrete a))) f
  SBool   -> withDict (Dict :: Dict (SymWord (Concrete a))) f
  SList _ -> error "bad"

data Expr (ty :: Ty) where
  -- transducers
  ListCat
    :: SingTy a -> Expr ('List a)     -> Expr ('List a) -> Expr ('List a)
  ListMap
    :: SingTy a -> (Expr a -> Expr b) -> Expr ('List a) -> Expr ('List b)

  ListLen      ::                       Expr ('List a) -> Expr 'IntTy
  ListAt       ::        Expr 'IntTy -> Expr ('List a) -> Expr a
  ListContains :: SingTy a -> Expr a -> Expr ('List a) -> Expr 'BoolTy
  ListFold
    :: SingTy a -> SingTy b
    -> (Expr a -> Expr b) -> Fold b -> Expr ('List a) -> Expr b

  -- other
  Eq           :: SingTy a -> Expr a -> Expr a -> Expr 'BoolTy
  Gt           ::  Expr 'IntTy -> Expr 'IntTy  -> Expr 'BoolTy
  Not          ::                 Expr 'BoolTy -> Expr 'BoolTy
  BinOp        ::   Fold a -> Expr a -> Expr a -> Expr a

  LitB         :: Concrete 'BoolTy -> Expr 'BoolTy
  LitI         :: Concrete 'IntTy  -> Expr 'IntTy

  SymB         :: SBV Bool    -> Expr 'BoolTy
  SymI         :: SBV Integer -> Expr 'IntTy

  Var :: SingTy a -> String -> Expr a

  -- re ListInfo vs NormalListInfo: ListInfo is provided for convenience, but
  -- we normalize to NormalListInfo
  ListInfo       :: SingTy a -> ListInfo a -> Expr ('List a)
  NormalListInfo :: SingTy a -> Int -> Expr ('List a)

normalizeExpr :: Expr a -> StateT Int (Writer (Map Int ELI)) (Expr a)
normalizeExpr tm = case tm of
  ListCat ty a b -> ListCat ty <$> normalizeExpr a <*> normalizeExpr b
  ListMap ty f a -> ListMap ty f <$> normalizeExpr a
  ListLen a -> ListLen <$> normalizeExpr a
  ListAt a b -> ListAt <$> normalizeExpr a <*> normalizeExpr b
  ListContains ty a b -> ListContains ty <$> normalizeExpr a <*> normalizeExpr b
  ListFold ty1 ty2 g f a -> ListFold ty1 ty2 g f <$> normalizeExpr a
  Eq ty a b -> Eq ty <$> normalizeExpr a <*> normalizeExpr b
  Gt a b -> Gt <$> normalizeExpr a <*> normalizeExpr b
  Not a -> Not <$> normalizeExpr a
  BinOp f a b -> BinOp f <$> normalizeExpr a <*> normalizeExpr b
  LitB{} -> pure tm
  LitI{} -> pure tm
  SymB{} -> pure tm
  SymI{} -> pure tm
  Var{} -> pure tm
  NormalListInfo{} -> pure tm
  ListInfo ty i -> do
    pos <- id <<+= 1
    tell $ Map.singleton pos $ Exists ty i
    pure $ NormalListInfo ty pos

mergeConcreteReps
  :: [ELI]
  -> [(Either (ETy, Int) EConcreteList)]
  -> [ELI]
mergeConcreteReps elis econs = zipWith
  (\eli@(Exists ty1 li) econ -> case econ of
    Left _ -> eli -- we haven't started concretizing this list yet
    Right (Exists ty2 (ConcreteList list)) -> case singEq ty1 ty2 of
      Nothing   -> error "impossible"
      Just Refl -> Exists ty1 (AndInfo li (LitList list)))
  elis econs

mkVars
  :: SingTy ty -> Int -> Int
  -> ([Expr ty], [(String, ETy)], Symbolic (Map String EExpr))
mkVars ty listIx len =
  let varName exprIx = "var_" ++ show listIx ++ "_" ++ show exprIx
      exprs     = Var ty    . varName <$> [0..len]
      typedVars = (,ETy ty) . varName <$> [0..len]
      env = fmap Map.fromList $ forM [0..len] $ \exprIx ->
        let name = varName exprIx
        in (name,) <$> case ty of
             SInt  -> Exists ty . SymI <$> sInteger name
             SBool -> Exists ty . SymB <$> sBool name
             _     -> error "unsupported var type"
  in (exprs, typedVars, env)

extractVars :: Modelable a => a -> [(String, ETy)] -> Map String EExpr
extractVars model names
  = let f = \case
          (name, ETy SInt)  -> (name, Exists SInt  . LitI <$> getModelValue name model)
          (name, ETy SBool) -> (name, Exists SBool . LitB <$> getModelValue name model)
          _                 -> error "unexpected type"
    in Map.fromList $
        concatMap (\case { (name, Just x) -> [(name, x)];  _ -> [] }) $
        fmap f names

existentialTy :: Existential tm -> ETy
existentialTy (Exists ty _) = ETy ty

symOf :: SingTy ty -> SBV (Concrete ty) -> Expr ty
symOf (SList _) _ = error "we don't support symbolic lists"
symOf SInt  s     = SymI s
symOf SBool s     = SymB s

litOf :: SingTy ty -> Concrete ty -> Expr ty
litOf (SList ty) l = ListInfo ty $ LitList $ litOf ty <$> l
litOf SInt       i = LitI i
litOf SBool      b = LitB b

symVarOf :: SingTy ty -> String -> Expr ty
symVarOf (SList _) _ = error "we don't support list variables"
symVarOf SInt      v = symOf SInt  (uninterpret v)
symVarOf SBool     v = symOf SBool (uninterpret v)

eqOf :: SingTy ty -> Concrete ty -> Concrete ty -> Bool
eqOf (SList ty) a b = length a == length b && and (zipWith (eqOf ty) a b)
eqOf SInt       a b = a == b
eqOf SBool      a b = a == b

forAllOf :: SingTy ty -> (Expr ty -> Symbolic (SBV Bool)) -> Predicate
forAllOf SInt f      = forAll_ $ f . sym
forAllOf SBool f     = forAll_ $ f . sym
forAllOf (SList _) _ = error "i don't know what to do in this case"

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

data ListInfo (ty :: Ty) where
  LitList :: [Expr a] -> ListInfo a
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

  AtInfo :: Expr 'IntTy -> Expr a -> ListInfo a
  LenGt :: Int -> ListInfo a

  OrInfo  :: ListInfo a -> ListInfo a -> ListInfo a
  AndInfo :: ListInfo a -> ListInfo a -> ListInfo a

extractConcreteList :: ListInfo ty -> Maybe (Either [Expr ty] Int)
extractConcreteList = \case
  LitList lst -> Just (Left lst)
  FoldInfo{}  -> Nothing
  AtInfo{}    -> Nothing
  LenGt len   -> Just (Right len)
  OrInfo{}    -> Nothing
  AndInfo a b -> extractConcreteList a `choose` extractConcreteList b

  -- prefer left over right, otherwise take either Just
  where choose (Just l@Left{}) _               = Just l
        choose _               (Just l@Left{}) = Just l
        choose x               y               = x <|> y

allInfo :: (Sing a, b ~ 'BoolTy) => (Expr a -> Expr b) -> ListInfo a
allInfo f = FoldInfo sing SBool f And (LitB True)

instance Show (ListInfo ty) where
  showsPrec p li = showParen (p > 10) $ case li of
    LitList l -> showString "LitList " . showsPrec 11 l
    FoldInfo a b f fold result ->
        showString "FoldInfo "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
      . showString " "
      . showsPrec 11 (f (symVarOf a "x"))
      . showString " "
      . showsPrec 11 fold
      . showString " "
      . showsPrec 11 result
    AtInfo i a ->
        showString "AtInfo "
      . showsPrec 11 i
      . showString " "
      . showsPrec 11 a
    LenGt i ->
        showString "LenGt "
      . showsPrec 11 i
    OrInfo a b ->
        showString "OrInfo "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
    AndInfo a b ->
        showString "AndInfo "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b

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
      . showsPrec 11 (f (symVarOf a "x"))
      . showString " "
      . showsPrec 11 as
    ListLen as ->
        showString "ListLen "
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
    ListFold a b f fempty as ->
        showString "ListFold "
      . showsPrec 11 a
      . showString " "
      . showsPrec 11 b
      . showString " "
      . showsPrec 11 (f (symVarOf a "x"))
      . showString " "
      . showsPrec 11 fempty
      . showString " "
      . showsPrec 11 as

    LitB a     -> showString "LitB "     . showsPrec 11 a
    LitI a     -> showString "LitI "     . showsPrec 11 a
    ListInfo ty i ->
        showString "ListInfo "
      . showsPrec 11 ty
      . showString " "
      . showsPrec 11 i
    NormalListInfo ty i ->
        showString "NormalListInfo "
      . showsPrec 11 ty
      . showString " "
      . showsPrec 11 i

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

    Var ty a ->
        showString "Var "
      . showsPrec 11 ty
      . showString " "
      . showsPrec 11 a

eval :: Expr ty -> Concrete ty
eval = \case
  ListCat _ a b      -> eval a <> eval b
  ListMap a f as     -> eval . f . litOf a <$> eval as
  ListLen l          -> fromIntegral $ length $ eval l
  ListFold a _b f fold l -> foldr
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
  ListInfo _ty i -> case i of
    LitList l -> fmap eval l
    _         -> error "can't evaluate non-literal list"

  NormalListInfo _ _ -> error "cannot evaluate normal list info"
  SymB _  -> error "cannot evaluate symbolic value"
  SymI _  -> error "cannot evaluate symbolic value"
  Var _ _ -> error "cannot evaluate variable"

forceRight :: Either a b -> b
forceRight (Left _) = error "unexpected left"
forceRight (Right b) = b

sEval'
 :: Map String EExpr
 -> [ELI]
 -> Expr ty
 -> Symbolic (SBV (Concrete ty))
sEval' vars infos x
  = forceRight <$> runReaderT (runExceptT (sEval x)) (vars, infos)

type SEval ty = ExceptT String
  (ReaderT (Map String EExpr, [ELI])
  Symbolic) ty

viewInfo :: SingTy a -> Int -> SEval (ListInfo a)
viewInfo ty pos = do
  (_, infos) <- ask
  case infos !! pos of
    Exists ty' li -> case singEq ty ty' of
      Nothing   -> throwError "got list info of wrong type"
      Just Refl -> pure li

undetermined :: SingTy ty -> SEval (SBV (Concrete ty))
undetermined ty = withSymWord ty $ lift $ lift free_

sEval :: forall ty. Expr ty -> SEval (SBV (Concrete ty))
sEval = \case
  ListCat SBool a b     -> (.++) <$> sEval a <*> sEval b
  ListCat SInt  a b     -> (.++) <$> sEval a <*> sEval b
  ListCat (SList _) _ _ -> throwError "nested lists not allowed"
  ListMap{}             -> throwError "can't map with sbv lists"

  ListLen (NormalListInfo ty pos) -> do
    li <- viewInfo ty pos
    sEval $ ListLen $ ListInfo ty li
  ListFold tyA tyB f fold (NormalListInfo ty pos) -> do
    li <- viewInfo ty pos
    sEval $ ListFold tyA tyB f fold $ ListInfo ty li
  ListAt i (NormalListInfo ty pos) -> do
    li <- viewInfo ty pos
    sEval $ ListAt i $ ListInfo ty li

  -- ListContains i (NormalListInfo _ pos)

  ListLen (ListInfo ty (OrInfo a b)) -> do
    x  <- lift $ lift free_
    a' <- sEval $ ListLen $ ListInfo ty a
    b' <- sEval $ ListLen $ ListInfo ty b
    lift $ lift $ constrain $ x .== a' ||| x .== b'
    pure x

  ListLen (ListInfo ty (AndInfo a b)) -> do
    a' <- sEval $ ListLen $ ListInfo ty a
    b' <- sEval $ ListLen $ ListInfo ty b
    lift $ lift $ constrain $ a' .== b'
    pure a'

  ListLen (ListInfo _ (LitList l)) -> pure $ literal $ fromIntegral $ length l
  ListLen (ListInfo _ (LenGt len)) -> do
    x <- lift $ lift free_
    lift $ lift $ constrain $ x .> fromIntegral len
    pure x

  ListFold tyA tyB f fold (ListInfo ty (OrInfo a b)) -> withSymWord tyB $ do
    x <- lift $ lift free_
    a' <- sEval $ ListFold tyA tyB f fold $ ListInfo ty a
    b' <- sEval $ ListFold tyA tyB f fold $ ListInfo ty b
    lift $ lift $ constrain $ x .== a' ||| x .== b'
    pure x

  ListFold tyA tyB f fold (ListInfo ty (AndInfo a b)) -> do
    a' <- sEval $ ListFold tyA tyB f fold $ ListInfo ty a
    b' <- sEval $ ListFold tyA tyB f fold $ ListInfo ty b
    lift $ lift $ constrain $ a' .== b'
    pure a'

  ListFold _a _b f fold (ListInfo _ (LitList l)) ->  do
    init  <- sEval (empty fold)
    elems <- traverse (sEval . f) l
    foldrM
      (\x y -> pure $ sFoldOp fold x y)
      init
      elems

  ListFold a1 _b1 f And (ListInfo _ (FoldInfo a2 _b2 g And result)) ->
    case singEq a1 a2 of
      Nothing   -> throwError "can't compare folds of different types"
      Just Refl -> do
        -- show that our knowledge is at least as strong as the assumption
        (vars, infos) <- ask
        precondition <- lift $ lift $ forAllOf a1 $ \someA -> do
          knowledge  <- sEval' vars infos $ g someA
          assumption <- sEval' vars infos $ f someA
          pure $ knowledge ==> assumption
        lift $ lift $ constrain precondition

        sEval result

  ListFold a1 _b1 f Add (ListInfo _ (FoldInfo a2 _b2 g Add result)) -> do
    case singEq a1 a2 of
      Nothing   -> throwError "can't compare folds of different types"
      Just Refl -> do
        -- The function we know about and the function we're asking about must
        -- be extensionally equal
        (vars, infos) <- ask
        precondition <- lift $ lift $ forAllOf a1 $ \someA -> do
          knowledge  <- sEval' vars infos $ g someA
          assumption <- sEval' vars infos $ f someA
          pure $ knowledge .== assumption
        lift $ lift $ constrain precondition

        sEval result

  ListFold a b f fold (ListCat _ l1 l2) -> do
    sFoldOp fold
      <$> sEval (ListFold a b f fold l1)
      <*> sEval (ListFold a b f fold l2)

  ListAt i (ListInfo _ (AtInfo j v)) -> do
    i' <- sEval i
    j' <- sEval j
    case (unliteral i', unliteral j') of
      (Just i'', Just j'') -> if i'' == j'' then sEval v else throwError $
        -- TODO: we should recover from this failure
        "mismatched at indices: " ++ show i'' ++ " vs " ++ show j''
        -- TODO: we should recover from this failure as well
      _ -> throwError "couldn't get literal form of both list indices"

  ListFold _ tyB _ _ (ListInfo _ (AtInfo _ _))         -> undetermined tyB
  ListFold _ tyB _ _ (ListInfo _ (LenGt _))            -> undetermined tyB
  ListFold _ tyB _ _ (ListInfo _ (FoldInfo _ _ _ _ _)) -> undetermined tyB

  ListAt i (ListInfo _ (LitList l)) -> do
    i' <- sEval i
    case unliteral i' of
      Just i'' ->
        if length l > fromIntegral i''
        then sEval $ l !! fromIntegral i''
        else throwError "indexing beyond the end of the list"
      Nothing -> throwError "couldn't get literal list index"

  -- ListContains a as  -> eval a `elem` eval as

  Eq _ty a b -> (.==) <$> sEval a <*> sEval b
  Gt a b     -> (.>)  <$> sEval a <*> sEval b
  Not a      -> bnot  <$> sEval a

  BinOp op a b -> case op of
    And -> (&&&) <$> sEval a <*> sEval b
    Add -> (+)   <$> sEval a <*> sEval b

  LitB a -> pure $ literal a
  LitI a -> pure $ literal a
  SymB a -> pure $ a
  SymI a -> pure $ a
  Var ty1 a -> do
    (vars, _) <- ask
    case Map.lookup a vars of
      Nothing -> throwError $ "couldn't find variable " ++ a
      Just (Exists ty2 expr) -> case singEq ty1 ty2 of
        Just Refl -> sEval expr
        Nothing -> throwError $ "variable of wrong type. expected: " ++
          show ty1 ++ ", found: " ++ show ty2

  other -> error $ "todo: " ++ show other

gt0 :: Expr 'IntTy -> Expr 'BoolTy
gt0 x = Gt x 0

lte0 :: Expr 'IntTy -> Expr 'BoolTy
lte0 x = Not (Gt x 0)

mkTest
  :: Validity -> Expr 'BoolTy -> Test ()
mkTest expectValid expr = mkTest' expectValid expr (pure Map.empty)

runNormalize :: Expr a -> (Expr a, [ELI])
runNormalize expr =
  let (expr', infos) = runWriter $ evalStateT (normalizeExpr expr) 0
      maxIx = maximum $ Map.keys infos
      infos' = [0..maxIx] <&> \pos -> infos Map.! pos
  in (expr', infos')

type SearchEnv =
  ( [Either (ETy, Int) EConcreteList]
  , Map String EExpr
  )

searchListSkeletons :: Lens' SearchEnv [Either (ETy, Int) EConcreteList]
searchListSkeletons = _1

searchVariableMapping :: Lens' SearchEnv (Map String EExpr)
searchVariableMapping = _2

mkConstraints
  :: Symbolic (Map String EExpr)
  -> [ELI]
  -> Expr 'BoolTy
  -> Map String EExpr
  -> Symbolic (SBV Bool)
mkConstraints sEnv infos expr concreteVars = do
  env <- sEnv
  ifor_ concreteVars $ \name (Exists (ty :: SingTy ty) concreteExpr) ->
    case env ^. singular (ix name) of
      Exists ty' envExpr -> case singEq ty ty' of
        Nothing -> (error "bad" :: Symbolic ())
        Just Refl -> do
          concreteValue <-
            runReaderT (runExceptT (sEval concreteExpr)) (env, infos)
          envValue <-
            runReaderT (runExceptT (sEval envExpr)) (env, infos)
          case (concreteValue, envValue) of
            (Right concreteValue', Right envValue') ->
              constrain $ concreteValue' .== envValue'
            _ -> error "bad"
  result <- runReaderT (runExceptT (sEval expr)) (env, infos)
  case result of
    Left msg      -> error msg
    Right result' -> pure result'

mkTest'
  :: Validity -> Expr 'BoolTy -> Symbolic (Map String EExpr) -> Test ()
mkTest' expectValid expr sEnv = do
  let (expr', infos)     = runNormalize expr
      initialAssignments = Map.empty
      constraints0       = mkConstraints sEnv infos expr' initialAssignments

  valid   <- io $ isTheorem constraints0
  vacuous <- io $ isVacuous constraints0

  expect $ if expectValid == Valid
    then valid && not vacuous
    else not valid || vacuous

  -- for each list info:
  --   if it doesn't already have a concrete representation:
  --     iteratively try every concrete list rep until we find one that
  --     produces a falsifying model
  --
  -- optimization 1: exponentially increasing search, then binary search
  -- 0 ... 1 ... 2 ... 4 ... 8 ... 16 ... 32 ... 64 ... 128 <- found example
  --                                                ^^^ binary search here
  --
  -- optimization 2 (done): extract falsifying model, feed in entirety of
  -- previously found model as constraints for new model

  -- Either index to start search at or concrete (skeleton of) counterexample
  let listSkeletons :: [Either (ETy, Int) EConcreteList]
      listSkeletons = infos <&> \(Exists ty li) -> case extractConcreteList li of
        Nothing            -> Left (ETy ty, 0)
        Just (Right start) -> Left (ETy ty, start)
        Just (Left xs)     -> Right $ Exists ty $ ConcreteList xs
      initialState       = (listSkeletons, initialAssignments)
      numLists           = length listSkeletons

  concreteResults <- io $
    flip execStateT initialState $ forM_ [0..numLists - 1] $ \listIx ->
      whileM_ (isn't _Right <$> use (singular (searchListSkeletons . ix listIx))) $ do
        rep <- use $ singular $ searchListSkeletons . ix listIx
        case rep of
          Right{} -> error "impossible"
          Left (ETy ty, startingLen) -> do
            variableMapping <- use searchVariableMapping

            let (vars, typedVars, varEnv) = mkVars ty listIx startingLen
                listElemVars = Exists ty $ ConcreteList vars
                constraints = mkConstraints sEnv infos expr' variableMapping

            (valid', vacuous') <- liftIO $
              (,) <$> isTheorem constraints <*> isVacuous constraints

            if valid' && not vacuous'

            -- we failed to find a falsifying model at this length -- try a
            -- longer list
            then
              if startingLen < 50
              then modify $ searchListSkeletons . ix listIx .~ Left (ETy ty, succ startingLen)
              else error "we probably should have found a model by now"

            -- we found a model
            else do
              let listSkeletons' = listSkeletons
                    & ix listIx .~ Right listElemVars
                  sEnv'  = Map.union <$> sEnv <*> varEnv

                  -- merge in learned concretizations
                  infos' = mergeConcreteReps infos listSkeletons'

                  constraints' = mkConstraints sEnv' infos' expr' variableMapping
              searchListSkeletons .= listSkeletons'

              -- for each variable in the list we just found, extract its
              -- concrete rep
              extractedVars <- liftIO $ do
                result <- prove constraints'
                -- print result
                -- putStrLn $ "typedVars: " ++ show typedVars
                pure $ extractVars result typedVars
              liftIO $ putStrLn $ "extractedVars: " ++ show extractedVars
              searchVariableMapping <>= extractedVars

  -- liftIO $ print (fst concreteResults :: [Either (ETy, Int) EConcreteList])
  pure ()

data Validity = Valid | Invalid
  deriving Eq

mkAny
  :: Sing a
  => (Expr a -> Expr 'BoolTy) -> ListInfo a -> Expr 'BoolTy
mkAny f = bnot . ListFold sing sing (bnot . f) And . ListInfo sing

mkAll
  :: Sing a
  => (Expr a -> Expr 'BoolTy) -> ListInfo a -> Expr 'BoolTy
mkAll f = ListFold sing sing f And . ListInfo sing

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
  :: (Sing a, Sing b)
  => (Expr a -> Expr b) -> Fold b -> Expr ('List a) -> Expr b
mkFold = ListFold sing sing

pattern VarI :: String -> Expr 'IntTy
pattern VarI name = Var SInt name

pattern VarB :: String -> Expr 'BoolTy
pattern VarB name = Var SBool name

main :: IO ()
main = do
  let almostAllPos :: Expr ('List 'IntTy)
      almostAllPos = ListCat SInt
        (ListInfo sing (allInfo gt0))
        (ListCat SInt
          (ListInfo sing (allInfo (Eq SInt 0)))
          (ListInfo sing (allInfo gt0)))

      sumTo7 :: Expr ('List 'IntTy)
      sumTo7 = ListCat SInt
        (ListInfo sing (mkFoldInfo id Add 3))
        (ListInfo sing (mkFoldInfo id Add 4))

  run $ tests
    -- [ scope "any (> 0) [1, 2, 3]" $
    --     mkTest Valid $ pure $ mkAny gt0 $ LitList [1, 2, 3]

    -- , scope "any (> 0) [-1, 2, 3]" $
    --     mkTest Valid $ pure $ mkAny gt0 $ LitList [lit (-1), 2, 3]

    -- , scope "any (> 0) [a, -1, 3]" $ do
    --     mkTest Valid $ do
    --       a <- sInteger "a"
    --       pure $ mkAny gt0 $ LitList [sym a, lit (-1), 3]

    -- , scope "all (> 0) [a, 1, 3]" $
    --   mkTest Invalid  $ do
    --     a <- sInteger "a"
    --     pure $ mkAll gt0 $ LitList [sym a, lit 1, 3]

    -- , scope "length [] == 0" $
    --     mkTest Valid $ pure $ ListLen (ListInfo sing (LitList [])) `eq` 0

    -- , scope "length (len 2) == 2" $
    --     mkTest Valid $ do
    --       [a, b] <- sIntegers ["a", "b"]
    --       let lst :: Expr ('List 'IntTy)
    --           lst = ListInfo sing $ LitList [sym a, sym b]
    --       pure $ ListLen lst `eq` 2

    --   -- show that the result of a mapping is all positive
    -- , scope "fmap (> 0) lst == true" $
    --     mkTest Valid $ pure $
    --       mkAll gt0 $ allInfo gt0

    -- , scope "fmap (> 0) almostAllPos == true" $
    --     mkTest Invalid $ pure $
    --       mkFold gt0 And almostAllPos

    -- , scope "(and []) == true" $
    --     mkTest Valid $ pure $
    --       mkAnd $ LitList []

    -- , scope "all (eq true) [] /= false" $ do
    --     mkTest Invalid $ pure $ Not $
    --       mkAnd $ LitList []

    -- , scope "(and [true]) == true" $
    --     mkTest Valid $ pure $
    --       mkAnd $ allInfo $ eq true

    -- , scope "(and [false]) == true" $
    --     mkTest Invalid $ pure $
    --       mkAnd $ mkFoldInfo id And false

    -- , scope "and [false] /= true" $
    --     mkTest Valid $ pure $ bnot $
    --       mkAnd (mkFoldInfo id And false) `eq` true

    -- , scope "all (> 0) => (not (any (> 0)) == false)" $
    --     mkTest Invalid $ pure $
    --       bnot $ mkAny gt0 $ allInfo gt0

    -- , scope "any (<= 0) => not (all (> 0))" $
    --     mkTest Valid $ pure $ bnot $
    --       mkAll gt0 $ mkFoldInfo (bnot . lte0) And false

    -- , scope "at 2 [1, 2, 3] == 3" $
    --     mkTest Valid $ pure $
    --       ListAt 2 (ListInfo sing (LitList [1, 2, 3])) `eq` LitI 3

    -- , scope "at 2 [1, 2, 3] == 2" $
    --     mkTest Invalid $ pure $
    --       ListAt 2 (ListInfo sing (LitList [1, 2, 3])) `eq` LitI 2

    -- , scope "sum sumTo7 == 7" $
    --     mkTest Valid $ pure $
    --       mkFold id Add sumTo7
    --       `eq`
    --       7

    -- , scope "sum (map (const 1) [length 7]) == 7" $
    --     mkTest Valid $ do
    --       elems <- sIntegers ["a", "b", "c", "d", "e", "f", "g"]
    --       let lst :: Expr ('List 'IntTy)
    --           lst = ListInfo sing $ LitList $ sym <$> elems
    --       pure $
    --         mkFold (const 1) Add lst
    --         `eq`
    --         7

    -- , scope "sum (map (const 1) [length 3 || length 4] > 2" $
    --     mkTest Valid $ do
    --       [a, b, c, d, e, f, g] <- sIntegers ["a", "b", "c", "d", "e", "f", "g"]
    --       let lst :: Expr ('List 'IntTy)
    --           lst = ListInfo sing $ OrInfo
    --             (LitList $ sym <$> [a, b, c])
    --             (LitList $ sym <$> [d, e, f, g])
    --       pure $
    --         mkFold (const 1) Add lst
    --         `Gt`
    --         2

    -- , scope "sum (map (const 1) [length 3 && at 2 == 1000] == 3" $
    --     mkTest' Valid $ do
    --       [ai, bi, ci] <- sIntegers ["a", "b", "c"]
    --       let lst :: Expr ('List 'IntTy)
    --           lst = ListInfo sing $ AndInfo
    --             (LitList [VarI "a", VarI "b", VarI "c"])
    --             (AtInfo 2 1000)
    --           m = Map.fromList
    --             [ ("a", Exists SInt $ SymI ai)
    --             , ("b", Exists SInt $ SymI bi)
    --             , ("c", Exists SInt $ SymI ci)
    --             ]
    --           expr = mkFold (const 1) Add lst
    --             `eq`
    --             3

    --       pure (m, expr)

    [ scope "sum [length 3 && at 2 == 1000] == 3" $
        mkTest' Invalid
          (let lst :: Expr ('List 'IntTy)
               lst = ListInfo sing $ AndInfo
                 (LitList [VarI "a", VarI "b", VarI "c"])
                 (AtInfo 2 1000)
           in mkFold id Add lst `eq` 3) $ do
          [ai, bi, ci] <- sIntegers ["a", "b", "c"]
          pure $ Map.fromList
            [ ("a", Exists SInt $ SymI ai)
            , ("b", Exists SInt $ SymI bi)
            , ("c", Exists SInt $ SymI ci)
            ]

    , scope "sum [at 2 == 1000 && len > 3] == 3" $
        mkTest Invalid $
          let lst :: Expr ('List 'IntTy)
              lst = ListInfo sing $ AndInfo
                (AtInfo 2 1000)
                (LenGt 3)
              expr = mkFold id Add lst
                `eq`
                3

          in expr

    , scope "sum [all (eq 1)] == 21" $
        mkTest Invalid $
          let lst :: Expr ('List 'IntTy)
              lst = ListInfo sing $ FoldInfo SInt SBool (`eq` 1) And true

              -- AndInfo
              --   (AtInfo 2 1000)
              --   (LenGt 3)
              expr = mkFold id Add lst
                `eq`
                21

          in expr
    ]
