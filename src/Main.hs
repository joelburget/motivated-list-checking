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


-- A list represented as the result of a fold
newtype FoldedList a = FoldedList { unFoldedList :: a }
  deriving (Show, Functor)

newtype SListLength = SListLength { unSListLength :: SBV Integer }
  deriving Show

instance Semigroup SListLength where
  SListLength x <> SListLength y = SListLength $ x + y

instance Monoid SListLength where
  mempty = SListLength 0

-- Just use SOr if you need a boolean predicate
data SAny a = SAny (Expr a -> Expr 'BoolTy)

instance HasKind (Concrete a) => Show (SAny a) where
  show (SAny f) = show (f (Sym (uninterpret "x")))

-- Just use SAnd if you need a boolean predicate
data SAll a = SAll (Expr a -> Expr 'BoolTy)

instance HasKind (Concrete a) => Show (SAll a) where
  show (SAll f) = show (f (Sym (uninterpret "x")))

newtype SOr = SOr { unSOr :: SBV Bool }
  deriving Show

instance Semigroup SOr where
  SOr x <> SOr y = SOr (x &&& y)

instance Monoid SOr where
  mempty = SOr true

newtype SAnd = SAnd { unSAnd :: SBV Bool }
  deriving Show

instance Semigroup SAnd where
  SAnd x <> SAnd y = SAnd (x ||| y)

instance Monoid SAnd where
  mempty = SAnd false

data SCmp = SCmp (SBV Integer -> SBV Bool) -- Ordering (SBV Integer)

instance Show SCmp where
  show _ = "SCmp"

-- TODO: contains monoid

cons :: Monoid a => a -> FoldedList a -> FoldedList a
cons a (FoldedList f) = FoldedList $ a <> f

snoc :: Monoid a => FoldedList a -> a -> FoldedList a
snoc (FoldedList f) a = FoldedList $ f <> a

concat :: Monoid a => FoldedList a -> FoldedList a -> FoldedList a
concat (FoldedList a) (FoldedList a') = FoldedList $ a <> a'

implode :: Monoid a => [a] -> FoldedList a
implode = FoldedList . mconcat

singleton :: Monoid a => a -> FoldedList a
singleton = FoldedList

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
  ListInfo :: ListInfo a                       -> Expr ('List a)

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
  LitList :: [SBV (Concrete a)] -> ListInfo a
  LenInfo :: SListLength        -> ListInfo a
  AnyInfo :: SAny 'IntTy        -> ListInfo 'IntTy
  AllInfo :: SAll 'IntTy        -> ListInfo 'IntTy
  OrInfo  :: SOr                -> ListInfo 'BoolTy
  AndInfo :: SAnd               -> ListInfo 'BoolTy
  CmpInfo :: SCmp               -> ListInfo 'IntTy

instance Show (ListInfo a) where
  showsPrec p li = showParen (p > 10) $ case li of
    LitList l -> showString "LitList " . showsPrec 11 l
    LenInfo i -> showString "LenInfo " . showsPrec 11 i
    AnyInfo i -> showString "AnyInfo " . showsPrec 11 i
    AllInfo i -> showString "AllInfo " . showsPrec 11 i
    OrInfo  i -> showString "OrInfo "  . showsPrec 11 i
    AndInfo i -> showString "AndInfo " . showsPrec 11 i
    CmpInfo i -> showString "CmpInfo " . showsPrec 11 i

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
  Length    :: Expr 'IntTy              -> Motive a
  MAll      :: (Expr a -> Expr 'BoolTy) -> Motive a
  MAny      :: (Expr a -> Expr 'BoolTy) -> Motive a
  MEq       :: Expr ('List a)           -> Motive a
  MAt       :: Expr 'IntTy -> Expr a    -> Motive a
  MContains :: Expr a                   -> Motive a
  -- MFold

evalMotive
  :: forall a. (Show (Concrete a), SymWord (Concrete a))
  => Motive a -> Expr ('List a) -> Symbolic (SBV Bool)
evalMotive (Length len) = \case
  ListCat a b -> do
    [al, bl] <- sIntegers ["al", "bl"]
    let totalLen = al + bl .== sEval len
    aLen <- evalMotive (Length (Sym al)) a
    bLen <- evalMotive (Length (Sym bl)) b
    pure $ totalLen &&& aLen &&& bLen
  ListMap _ lst -> evalMotive (Length len) lst
  ListAt{} -> error "nested lists not allowed"
  ListInfo i -> case i of
    LenInfo (SListLength len') -> pure $ len' .== sEval len
    _                          -> error $ "sorry, can't help with this motive: " ++ show i
  Sym{} -> error "can't motivate evaluation of symbolic value"
evalMotive (MAll f) = \case
  ListCat a b -> (&&&)
    <$> evalMotive (MAll f) a
    <*> evalMotive (MAll f) b
  ListMap g lst -> evalMotive (MAll (f . g)) lst
  ListAt{} -> error "nested lists not allowed"
  ListInfo i -> case i of
    AndInfo (SAnd b) -> pure $ sEval $ f $ Sym b
    AllInfo (SAll g) -> do
      j <- forall_
      let fEval = sEval $ f $ Sym j
          gEval = sEval $ g $ Sym j
      pure $ gEval ==> fEval
    CmpInfo (SCmp g) -> do
      -- g is at least as strong an assumption as f.
      -- example:
      -- f: for all i: elements of the list, i > 0
      -- g: i need to know that for all i: elements of the list, i > -1
      j <- forall_
      let fEval = sEval $ f $ Sym j
          gEval =         g       j
      pure $ gEval ==> fEval
    LenInfo (SListLength len)
      | Just 0 <- unliteral len -> pure true
      | otherwise -> error "TODO"
    _ -> error $ "sorry, can't help with this motive: " ++ show i
  Sym{} -> error "can't motivate evaluation of symbolic value"
evalMotive (MAny f) = \case
  ListCat a b -> (|||)
    <$> evalMotive (MAny f) a
    <*> evalMotive (MAny f) b
  ListMap g lst -> evalMotive (MAny (f . g)) lst
  ListAt{} -> error "nested lists not allowed"
  ListInfo info -> case info of
    OrInfo  (SOr b) -> pure $ sEval $ f $ Sym b -- TODO: right?
    AnyInfo (SAny g) -> do
      j <- exists_
      let fEval = sEval $ f $ Sym j
          gEval = sEval $ g $ Sym j
      pure $ gEval ==> fEval
    LenInfo (SListLength len)
      | Just 0 <- unliteral len -> pure false
      | otherwise -> error "TODO"
    _ -> error $ "sorry, can't help with this motive: " ++ show info
  Sym{} -> error "can't motivate evaluation of symbolic value"
evalMotive (MEq lst) = \case
  ListCat a b -> pure $ sEval a .++ sEval b .== sEval lst
  ListMap{} -> error "XXX tricky"
  ListAt{} -> error "nested lists not allowed"
  ListInfo litLst  -> error "TODO"
    -- do
    -- ifor_ litLst $ \i val -> constrain $
    --   sEval lst .!! fromIntegral i .== literal val
  Sym{} -> error "can't motivate evaluation of symbolic value"
evalMotive (MAt i a) = \case
  ListCat l1 l2 -> do
    let l1' = sEval l1
        l2' = sEval l2
        i'  = sEval i
        a'  = sEval a
    pure $
      l1' .!! i'                     .== a' |||
      l2' .!! (i' - SBVL.length l1') .== a'
  ListMap{} -> error "XXX tricky 3"
  ListAt{} -> error "nested lists not allowed"
  ListInfo litLst -> error "TODO"
  -- ifor_ litLst $ \j val -> constrain $
  --   fromIntegral j .== i ==> literal val .== a
  Sym{} -> error "can't motivate evaluation of symbolic value"
evalMotive motive@(MContains a) = \case
  ListCat l1 l2 -> (|||)
    <$> evalMotive motive l1
    <*> evalMotive motive l2
  ListMap{} -> error "XXX tricky 4"
  ListAt{} -> error "nested lists not allowed"
  ListInfo litLst -> error "TODO"
  -- for_ litLst $ \val -> constrain $
  --   literal val .== a
  Sym{} -> error "can't motivate evaluation of symbolic value"

main :: IO ()
main = do

  -- print <=< prove $
  makeReport "(len 2) + (len 4) == len 6 (expect good)" $ do
    let len = unSListLength $ unFoldedList $
          FoldedList (SListLength 2) `concat` FoldedList (SListLength 4)
    constrain $ len .== 6

  makeReport "true (expect good)"  $
    constrain true

  makeReport "false (expect bad)" $
    constrain false

  {-
  print <=< prove $ unSAll $ unFoldedList $
    implode $ SOr . (.> 0) <$> [ 1, 2, 3 :: SBV Integer ]

  print <=< prove $ unSAll $ unFoldedList $
    implode $ SOr . (.> 0) <$> [ -1, 2, 3 :: SBV Integer ]

  print <=< prove $ do
    a <- sInteger "a"
    pure $ unSAll $ unFoldedList $
      implode $ SOr . (.> 0) <$> [ a, 2, 3 :: SBV Integer ]
  -}

  -- TODO
  -- print <=< prove $ do
  --   let l :: Expr ('List 'IntTy)
  --       l = ListInfo (LenInfo (SListLength 2))
  --   pure $ sEval $ Eq (LitI 2) (ListLen l)

  makeReport "length [] == 0 (expect good)" $ do
    let lst = ListInfo (LenInfo (SListLength 0)) :: Expr ('List 'IntTy)
    constrain =<< evalMotive (Length (LitI 0)) lst

  -- show that the result of a mapping is all positive
  makeReport "fmap (> 0) lst == true (expect good)" $ do
    let lst = ListInfo (CmpInfo (SCmp (.> 0))) :: Expr ('List 'IntTy)

    constrain =<< evalMotive (MAll (\x -> (Gt x (LitI 0)))) lst

  let almostAllPos :: Expr ('List 'IntTy)
      almostAllPos = ListCat
        (ListInfo (CmpInfo (SCmp (.> 0))))
        (ListCat
          (ListInfo (CmpInfo (SCmp (.== 0))))
          (ListInfo (CmpInfo (SCmp (.> 0)))))
  makeReport "fmap (> 0) almostAllPos == true (expect bad)" $ do
    constrain =<< evalMotive (MAll (\x -> (Gt x (LitI 0)))) almostAllPos

  makeReport "(and []) == true (expect good)" $
    constrain <=< evalMotive (MAll (Eq true')) $ ListInfo $ LenInfo $ SListLength 0

  makeReport "(not (and [])) == true (expect bad)" $ do
    x <- evalMotive (MAll (Eq true')) $ ListInfo $ LenInfo $ SListLength 0
    constrain $ bnot x

  makeReport "(and [true]) == true (expect good)" $
    constrain <=< evalMotive (MAll (Eq true')) $ ListInfo $ AndInfo $ SAnd true
      -- Lit [true]

  makeReport "(and [false]) == true (expect bad)" $
    constrain <=< evalMotive (MAll (Eq true')) $ ListInfo $ AndInfo $ SAnd false
      -- Lit [false]

  makeReport "(not (and [false])) == true (expect good)" $ do
    x <- evalMotive (MAll (Eq true')) $ ListInfo $ AndInfo $ SAnd false
    constrain $ bnot x
      -- Lit [false]

  makeReport "fmap (> 0) (all [> 0]) == true (expect good)" $ do
    constrain <=< evalMotive (MAll (\x -> Gt x (LitI 0))) $ ListInfo $ AllInfo $
      SAll (\x -> Gt x (LitI 0))

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
