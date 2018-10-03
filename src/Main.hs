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
import Data.Foldable (for_)
import Control.Lens hiding (List, (.>))
import Control.Monad
import Data.SBV
import           Data.SBV.List ((.++), (.!!))
import qualified Data.SBV.List as SBVL


-- A list represented as the result of a fold
newtype FoldedList a = FoldedList { unFoldedList :: a }
  deriving Functor

newtype SListLength = SListLength { unSListLength :: SBV Integer }

instance Semigroup SListLength where
  SListLength x <> SListLength y = SListLength $ x + y

instance Monoid SListLength where
  mempty = SListLength 0

newtype SAll = SAll { unSAll :: SBV Bool }

instance Semigroup SAll where
  SAll x <> SAll y = SAll (x &&& y)

instance Monoid SAll where
  mempty = SAll true

newtype SAny = SAny { unSAny :: SBV Bool }

instance Semigroup SAny where
  SAny x <> SAny y = SAny (x ||| y)

instance Monoid SAny where
  mempty = SAny false

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
  ListLen :: Suitable a
          => Expr ('List a)                   -> Expr 'IntTy
  ListAnd :: Expr ('List 'BoolTy)             -> Expr 'BoolTy
  ListOr  :: Expr ('List 'BoolTy)             -> Expr 'BoolTy
  ListEq  :: Suitable a
          => Expr ('List a) -> Expr ('List a) -> Expr 'BoolTy
  ListAt  :: Expr ('List a) -> Expr 'IntTy    -> Expr a
  ListContains
          :: Suitable a
          => Expr ('List a) -> Expr a    -> Expr 'BoolTy

  -- transducers
  ListCat :: Suitable a
          => Expr ('List a) -> Expr ('List a) -> Expr ('List a)
  ListMap :: Suitable a
          => (     Concrete a  ->      Concrete b)
          -> (SBV (Concrete a) -> SBV (Concrete b))
          ->                   Expr ('List a) -> Expr ('List b)

  -- producers
  Lit     :: Concrete a                       -> Expr a
  Sym     :: SBV (Concrete a)                 -> Expr a

  -- other
  Eq      :: (Eq (Concrete a), Suitable a)
          => Expr a         -> Expr a         -> Expr 'BoolTy
  Gt      :: Expr 'IntTy    -> Expr 'IntTy    -> Expr 'BoolTy
  And     :: Expr 'BoolTy   -> Expr 'BoolTy   -> Expr 'BoolTy
  Or      :: Expr 'BoolTy   -> Expr 'BoolTy   -> Expr 'BoolTy
  Not     ::                   Expr 'BoolTy   -> Expr 'BoolTy

instance Show (Expr ty) where
  show = \case
    ListLen l          -> "ListLen"
    ListAnd l          -> "ListAnd"
    ListOr  l          -> "ListOr"
    ListEq  a b        -> "ListEq"
    ListAt lst i       -> "ListAt"
    ListContains lst a -> "ListContains"

    ListCat a b        -> "ListCat"
    ListMap f _ as     -> "ListMap"

    Eq a b             -> "Eq"
    Gt a b             -> "Gt"
    And a b            -> "And"
    Or a b             -> "Or"
    Not a              -> "Not"
    Lit a              -> "Lit"
    Sym _              -> "Sym"

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

  Eq a b             -> eval a == eval b
  Gt a b             -> eval a >  eval b
  And a b            -> eval a && eval b
  Or a b             -> eval a || eval b
  Not a              -> not (eval a)
  Lit a              -> a
  Sym _              -> error "cannot evaluate symbolic value"

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

  Eq a b         -> sEval a .== sEval b
  Gt a b         -> sEval a .>  sEval b
  And a b        -> sEval a &&& sEval b
  Or a b         -> sEval a ||| sEval b
  Not a          -> bnot (sEval a)
  Lit a          -> literal a
  Sym a          -> a

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
  Lit lst     -> constrain $ fromIntegral (length lst) .== len
  Sym lst     -> constrain $ SBVL.length lst .== len
evalMotive' (MAnd f) = \case
  ListCat a b -> do
    evalMotive' (MAnd f) a
    evalMotive' (MAnd f) b
  ListMap _ g lst -> evalMotive' (MAnd (f . g)) lst
  ListAt{} -> error "nested lists not allowed"
  Lit lst  ->
    constrain $ foldr (&&&) true (f . literal <$> lst)
    -- traverse (constrain . f . literal) lst >> pure ()
  Sym lst -> do
    i <- forall_
    constrain $ i .>= 0 &&& i .< SBVL.length lst ==> f (lst .!! i)
evalMotive' (MOr f) = \case
  ListCat a b -> do
    evalMotive' (MOr f) a
    evalMotive' (MOr f) b
  ListMap _ g lst -> evalMotive' (MOr (f . g)) lst
  ListAt{} -> error "nested lists not allowed"
  Lit lst  -> constrain $ foldr (|||) false (f . literal <$> lst)
  Sym lst -> do
    i <- exists_
    constrain $ i .>= 0 &&& i .< SBVL.length lst ==> f (lst .!! i)
evalMotive' (MEq lst) = \case
  ListCat a b -> constrain $ sEval a .++ sEval b .== sEval lst
  ListMap{} -> error "XXX tricky"
  ListAt{} -> error "nested lists not allowed"
  Lit litLst  -> do
    ifor_ litLst $ \i val -> constrain $
      sEval lst .!! fromIntegral i .== literal val
  Sym _       -> error "can't eliminate a symbolic list 2"
evalMotive' (MAt i a) = \case
  ListCat l1 l2 -> do
    let l1' = sEval l1
        l2' = sEval l2
    constrain $
      l1' .!! i                     .== a |||
      l2' .!! (i - SBVL.length l1') .== a
  ListMap{} -> error "XXX tricky 3"
  ListAt{} -> error "nested lists not allowed"
  Lit litLst -> ifor_ litLst $ \j val -> constrain $
    fromIntegral j .== i ==> literal val .== a
  Sym _ -> error "can't eliminate a symbolic list 3"
evalMotive' motive@(MContains a) = \case
  ListCat l1 l2 -> do
    evalMotive' motive l1
    evalMotive' motive l2
  ListMap{} -> error "XXX tricky 4"
  ListAt{} -> error "nested lists not allowed"
  Lit litLst -> for_ litLst $ \val -> constrain $
    literal val .== a
  Sym _ -> error "TODO"

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
    implode $ SAll . (.> 0) <$> [ 1, 2, 3 :: SBV Integer ]

  print <=< prove $ unSAll $ unFoldedList $
    implode $ SAll . (.> 0) <$> [ -1, 2, 3 :: SBV Integer ]

  print <=< prove $ do
    a <- sInteger "a"
    pure $ unSAll $ unFoldedList $
      implode $ SAll . (.> 0) <$> [ a, 2, 3 :: SBV Integer ]

  print <=< prove $ do
    [a, b] <- sIntegers ["a", "b"]
    let l :: Expr ('List 'IntTy)
        l = Sym (SBVL.implode [a, b])
    pure $ sEval $ Eq (Lit 2) (ListLen l)

  makeReport "length [] == 0 (expect good)" $ do
    let lst = Lit [] :: Expr ('List 'IntTy)
    evalMotive 0 (ListLen lst)

  -- proveWith z3 {verbose=True}

  -- show that the result of a mapping is all positive
  makeReport "fmap (> 0) lst == true (expect good)" $ do
    lst <- sList "lst"

    -- the real test is removing this constraint
    -- constrain $ SBVL.length lst .< 10

    i <- forall "i"
    constrain $ i .>= 0 ==> lst .!! i .> 0

    let expr  = Sym lst :: Expr ('List 'IntTy)
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
    evalMotive true $       ListAnd $ Lit []

  makeReport "(not (and [])) == true (expect bad)" $
    evalMotive true $ Not $ ListAnd $ Lit []

  makeReport "(and [true]) == true (expect good)" $
    evalMotive true $       ListAnd $ Lit [true]

  makeReport "(and [false]) == true (expect bad)" $
    evalMotive true $       ListAnd $ Lit [false]

  makeReport "(not (and [false])) == true (expect good)" $
    evalMotive true $ Not $ ListAnd $ Lit [false]

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
