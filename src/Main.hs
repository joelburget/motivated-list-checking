{-# language ConstraintKinds    #-}
{-# language TypeOperators    #-}
{-# language ScopedTypeVariables    #-}
{-# language FlexibleContexts    #-}
{-# language LambdaCase    #-}
{-# language KindSignatures    #-}
{-# language TypeFamilies    #-}
{-# language DataKinds    #-}
{-# language GADTs    #-}
{-# language DeriveFunctor    #-}
{-# language NamedFieldPuns    #-}
{-# language OverloadedStrings #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
module Main where

import Prelude as P hiding (concat)
import Control.Monad
import Data.SBV
import           Data.SBV.List ((.++), (.!!))
import qualified Data.SBV.List as SBVL


-- A list represented as the result of a fold
newtype FoldedList a = FoldedList { unFoldedList :: a }
  deriving (Show, Functor)

newtype SListLength = SListLength { unSListLength :: SBV Integer }
  deriving Show

instance Semigroup SListLength where
  SListLength x <> SListLength y = SListLength $ x + y

instance Monoid SListLength where
  mempty = SListLength 0

newtype SOr = SOr { unSAll :: SBV Bool }
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

data SCmp = SCmp Ordering (SBV Integer)
  deriving Show

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

type Suitable a = (Show (Concrete a), SymWord (Concrete a))

data Expr ty where
  -- list consumers
  ListLen  :: Suitable a
           => Expr ('List a)                   -> Expr 'IntTy
  ListAnd  :: Expr ('List 'BoolTy)             -> Expr 'BoolTy
  ListOr   :: Expr ('List 'BoolTy)             -> Expr 'BoolTy
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
           => (     Concrete a  ->      Concrete b)
           -> (SBV (Concrete a) -> SBV (Concrete b))
           ->                   Expr ('List a) -> Expr ('List b)

  -- producers
  ListInfo :: ListInfo a                       -> Expr a

  -- other
  LitB     :: Concrete 'BoolTy                 -> Expr 'BoolTy
  LitI     :: Concrete 'IntTy                  -> Expr 'IntTy
  Eq       :: (Eq (Concrete a), Suitable a)
           => Expr a         -> Expr a         -> Expr 'BoolTy
  Gt       :: Expr 'IntTy    -> Expr 'IntTy    -> Expr 'BoolTy
  And      :: Expr 'BoolTy   -> Expr 'BoolTy   -> Expr 'BoolTy
  Or       :: Expr 'BoolTy   -> Expr 'BoolTy   -> Expr 'BoolTy
  Not      ::                   Expr 'BoolTy   -> Expr 'BoolTy

data ListInfo a where
  LitList :: [SBV (Concrete a)] -> ListInfo a
  LenInfo :: SListLength        -> ListInfo a
  OrInfo  :: SOr                -> ListInfo a
  AndInfo :: SAnd               -> ListInfo a
  CmpInfo :: SCmp               -> ListInfo a
  deriving Show

instance Show (Expr ty) where
  showsPrec p expr = showParen (p > 10) $ case expr of
    ListLen l          -> showString "ListLen" . showsPrec 10 l
    ListAnd l          -> showString "ListAnd" . showsPrec 10 l
    ListOr  l          -> showString "ListOr" . showsPrec 10 l
    ListEq  a b        -> showString "ListEq" . showsPrec 10 a . showsPrec 10 b
    ListAt lst i       ->
      showString "ListAt " .
      showsPrec 10 lst .
      showString " " .
      showsPrec 10 i
    ListContains lst a ->
      showString "ListContains " .
      showsPrec 10 lst .
      showString " " .
      showsPrec 10 a

    ListCat a b        ->
      showString "ListCat " .
      showsPrec 10 a .
      showString " " .
      showsPrec 10 b
    ListMap _ _ as     ->
      showString "ListMap _ _ " .
      showsPrec 10 as
    ListInfo i         -> showString "ListInfo " . showsPrec 10 i

    LitB a             -> showString "LitB" . showsPrec 10 a
    LitI a             -> showString "LitI" . showsPrec 10 a
    Eq a b             ->
      showString "Eq " .
      showsPrec 10 a .
      showString " " .
      showsPrec 10 b
    Gt a b             ->
      showString "Gt" .
      showsPrec 10 a .
      showString " " .
      showsPrec 10 b
    And a b            ->
      showString "And" .
      showsPrec 10 a .
      showString " " .
      showsPrec 10 b
    Or a b             ->
      showString "Or" .
      showsPrec 10 a .
      showString " " .
      showsPrec 10 b
    Not a              -> showString "Not" . showsPrec 10 a

eval :: Expr ty -> Concrete ty
eval = \case
  ListLen l          -> fromIntegral $ length $ eval l
  ListAnd l          -> and $ eval l
  ListOr  l          -> or $ eval l
  ListEq  a b        -> eval a == eval b
  ListAt lst i       -> eval lst !! fromIntegral (eval i)
  ListContains lst a -> eval a `elem` eval lst

  ListCat a b        -> eval a <> eval b
  ListMap f _ as     -> f <$> eval as
  ListInfo _         -> error "cannot evaluate list info"

  Eq a b             -> eval a == eval b
  Gt a b             -> eval a >  eval b
  And a b            -> eval a && eval b
  Or a b             -> eval a || eval b
  Not a              -> not (eval a)
  LitB a             -> a
  LitI a             -> a

sEval :: SymWord (Concrete ty) => Expr ty -> SBV (Concrete ty)
sEval = \case
  ListLen l      -> SBVL.length $ sEval l
  ListAnd _      -> error "can't fold with sbv lists"
  ListOr  _      -> error "can't fold with sbv lists"
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

-- "My claim is that we should exploit a hypothesis not in terms of its
-- immediate consequences, but in terms of the leverage it exerts on an
-- arbitrary goal: we should give elimination a motive"

-- The motive for consuming a list of type @a@
data Motive a where
  Length    :: SBV (Concrete 'IntTy)                        -> Motive a
  MAnd      :: (SBV (Concrete a) -> SBV (Concrete 'BoolTy)) -> Motive a
  MOr       :: (SBV (Concrete a) -> SBV (Concrete 'BoolTy)) -> Motive a
  MEq       :: Expr ('List a)                               -> Motive a
  MAt       :: SBV (Concrete 'IntTy) -> SBV (Concrete a)    -> Motive a
  MContains ::                          SBV (Concrete a)    -> Motive a
  -- MFold

evalMotive'
  :: forall a. (Show (Concrete a), SymWord (Concrete a))
  => Motive a -> Expr ('List a) -> Symbolic ()
evalMotive' (Length len) = \case
  ListCat a b -> do
    [al, bl] <- sIntegers ["al", "bl"]
    constrain $ al + bl .== len
    evalMotive' (Length al) a
    evalMotive' (Length bl) b
  ListMap _ _ lst -> evalMotive' (Length len) lst
  ListAt{} -> error "nested lists not allowed"
  ListInfo i -> case i of
    LenInfo (SListLength len') -> constrain $ len' .== len
    _                          -> error $ "sorry, can't help with this motive: " ++ show i
evalMotive' (MAnd f) = \case
  ListCat a b -> do
    evalMotive' (MAnd f) a
    evalMotive' (MAnd f) b
  ListMap _ g lst -> evalMotive' (MAnd (f . g)) lst
  ListAt{} -> error "nested lists not allowed"
  ListInfo i -> case i of
    OrInfo (SOr b) -> constrain $ error "TODO"
    -- constrain $ foldr (&&&) true (f . literal <$> lst)
    -- traverse (constrain . f . literal) lst >> pure ()
    _ -> error $ "sorry, can't help with this motive: " ++ show i
evalMotive' (MOr f) = \case
  ListCat a b -> do
    evalMotive' (MOr f) a
    evalMotive' (MOr f) b
  ListMap _ g lst -> evalMotive' (MOr (f . g)) lst
  ListAt{} -> error "nested lists not allowed"
  ListInfo lst  -> error "TODO"
    -- constrain $ foldr (|||) false (f . literal <$> lst)
evalMotive' (MEq lst) = \case
  ListCat a b -> constrain $ sEval a .++ sEval b .== sEval lst
  ListMap{} -> error "XXX tricky"
  ListAt{} -> error "nested lists not allowed"
  ListInfo litLst  -> error "TODO"
    -- do
    -- ifor_ litLst $ \i val -> constrain $
    --   sEval lst .!! fromIntegral i .== literal val
evalMotive' (MAt i a) = \case
  ListCat l1 l2 -> do
    let l1' = sEval l1
        l2' = sEval l2
    constrain $
      l1' .!! i                     .== a |||
      l2' .!! (i - SBVL.length l1') .== a
  ListMap{} -> error "XXX tricky 3"
  ListAt{} -> error "nested lists not allowed"
  ListInfo litLst -> error "TODO"
  -- ifor_ litLst $ \j val -> constrain $
  --   fromIntegral j .== i ==> literal val .== a
evalMotive' motive@(MContains a) = \case
  ListCat l1 l2 -> do
    evalMotive' motive l1
    evalMotive' motive l2
  ListMap{} -> error "XXX tricky 4"
  ListAt{} -> error "nested lists not allowed"
  ListInfo litLst -> error "TODO"
  -- for_ litLst $ \val -> constrain $
  --   literal val .== a

evalMotive :: Suitable ty => SBV (Concrete ty) -> Expr ty -> Symbolic ()
evalMotive motive = \case
  ListLen lst        -> evalMotive' (Length motive) lst
  ListAnd lst        -> evalMotive' (MAnd (.== motive)) lst
  ListOr  lst        -> evalMotive' (MOr  (.== motive)) lst
  ListEq a b         -> evalMotive' (MEq a) b -- XXX use motive
  ListAt lst i       -> evalMotive' (MAt (sEval i) motive) lst
  ListContains lst a -> evalMotive' (MContains (sEval a)) lst

  -- XXX map not
  Not (ListAnd lst)  -> evalMotive motive (ListOr  (ListMap not bnot lst))
  Not (ListOr  lst)  -> evalMotive motive (ListAnd (ListMap not bnot lst))
  other -> error $ show other

main :: IO ()
main = do

  print <=< prove $
    let len = unSListLength $ unFoldedList $
          FoldedList (SListLength 2) `concat` FoldedList (SListLength 4)
    in len .== 6

  print <=< prove $
    let len = unSListLength $ unFoldedList $
          concat (FoldedList (SListLength 2)) (FoldedList (SListLength 4))
    in len .== 6

  print <=< prove $ unSAll $ unFoldedList $
    implode $ SOr . (.> 0) <$> [ 1, 2, 3 :: SBV Integer ]

  print <=< prove $ unSAll $ unFoldedList $
    implode $ SOr . (.> 0) <$> [ -1, 2, 3 :: SBV Integer ]

  print <=< prove $ do
    a <- sInteger "a"
    pure $ unSAll $ unFoldedList $
      implode $ SOr . (.> 0) <$> [ a, 2, 3 :: SBV Integer ]

  print <=< prove $ do
    [a, b] <- sIntegers ["a", "b"]
    let l :: Expr ('List 'IntTy)
        l = ListInfo (LenInfo (SListLength 2))
    pure $ sEval $ Eq (LitI 2) (ListLen l)

  makeReport "length [] == 0 (expect good)" $ do
    let lst = ListInfo (LenInfo (SListLength 0)) :: Expr ('List 'IntTy)
    evalMotive 0 (ListLen lst)

  -- proveWith z3 {verbose=True}

  -- show that the result of a mapping is all positive
  makeReport "fmap (> 0) lst == true (expect good)" $ do
    let expr  = ListInfo (CmpInfo (SCmp GT 0)) :: Expr ('List 'IntTy)
        expr' = ListAnd (ListMap (> 0) (.> 0) expr)

    evalMotive true expr'

--   -- should falsify the assertion
--   makeReport "fmap (> 0) lst == true (false)" $ do
--     lst <- sList "lst"

--     i <- forall "i"
--     constrain $
--       i .>= 0
--       ==>
--       ite (i .== 10)
--         (lst .!! i .== 0)
--         (lst .!! i .>  0)

--     let expr  = Sym lst :: Expr ('List 'IntTy)
--         expr' = ListAnd (ListMap (> 0) (.> 0) expr)

--     evalMotive true expr'

  makeReport "(and []) == true (expect good)" $
    evalMotive true $       ListAnd $ ListInfo $ LenInfo $ SListLength 0

  makeReport "(not (and [])) == true (expect bad)" $
    evalMotive true $ Not $ ListAnd $ ListInfo $ LenInfo $ SListLength 0

  makeReport "(and [true]) == true (expect good)" $
    evalMotive true $       ListAnd $ ListInfo $ OrInfo $ SOr true
      -- Lit [true]

  makeReport "(and [false]) == true (expect bad)" $
    evalMotive true $       ListAnd $ ListInfo $ OrInfo $ SOr false
      -- Lit [false]

  makeReport "(not (and [false])) == true (expect good)" $
    evalMotive true $ Not $ ListAnd $ ListInfo $ OrInfo $ SOr false
      -- Lit [false]

  makeReport "true (expect good)"  $
    constrain true

  makeReport "false (expect bad)" $
    constrain false

makeReport :: String -> Symbolic () -> IO ()
makeReport header a = do
  putStrLn $ '\n' : header
  -- provable <- prove a
  -- putStrLn $ "provable:    " ++ show provable
  SatResult satisfiable <- sat a
  -- putStrLn $ "satisfiable: " ++ show satisfiable
  vacuous <- isVacuous a
  -- putStrLn $ "vacuous:     " ++ show vacuous
  putStrLn $
    if vacuous
    then "vacuous"
    else case satisfiable of
           Satisfiable{}   -> "good"
           Unsatisfiable{} -> "bad"
           _               -> show $ SatResult satisfiable
