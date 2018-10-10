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

data SAny a = SAny (Expr a -> Expr 'BoolTy)

instance HasKind (Concrete a) => Show (SAny a) where
  show (SAny f) = show (f (Sym (uninterpret "x")))

-- Just use SAnd if you need a boolean predicate
data SAll a = SAll (Expr a -> Expr 'BoolTy)

instance HasKind (Concrete a) => Show (SAll a) where
  show (SAll f) = show (f (Sym (uninterpret "x")))

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
  LitList :: [SBV (Concrete a)] -> ListInfo a
  LenInfo :: SListLength        -> ListInfo a
  AnyInfo :: SAny 'IntTy        -> ListInfo 'IntTy
  AllInfo :: SAll a             -> ListInfo a

instance HasKind (Concrete a) => Show (ListInfo a) where
  showsPrec p li = showParen (p > 10) $ case li of
    LitList l -> showString "LitList " . showsPrec 11 l
    LenInfo i -> showString "LenInfo " . showsPrec 11 i
    AnyInfo i -> showString "AnyInfo " . showsPrec 11 i
    AllInfo i -> showString "AllInfo " . showsPrec 11 i

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
  MLength   :: Expr 'IntTy              -> Motive a
  MAt       :: Expr 'IntTy -> Expr a    -> Motive a
  MNegate   :: Motive a                 -> Motive a

  MAll      :: (Expr a -> Expr 'BoolTy) -> Motive a
  MAny      :: (Expr a -> Expr 'BoolTy) -> Motive a
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
       LenInfo (SListLength len') -> pure $ len'                    .== lenV
       LitList l                  -> pure $ fromIntegral (length l) .== lenV
       _                          -> error $
         "sorry, can't help with this motive: " ++ show i

evalMotive (MAll f) (ListCat a b) = (&&&)
  <$> evalMotive (MAll f) a
  <*> evalMotive (MAll f) b
evalMotive (MAll f) (ListMap g lst) = evalMotive (MAll (f . g)) lst
evalMotive (MAll f) (ListInfo i) = case i of
  AllInfo (SAll g) -> do
    j <- forall_
    -- g is at least as strong an assumption as f.
    -- example:
    -- f: for all i: elements of the list, i > 0
    -- g: i need to know that for all i: elements of the list, i > -1
    let fEval = sEval $ f $ Sym j
        gEval = sEval $ g $ Sym j
    pure $ gEval ==> fEval
  LenInfo (SListLength len)
    | Just 0 <- unliteral len -> pure true
    | otherwise -> error "TODO"
  _ -> error $ "sorry, can't help with this motive: " ++ show i

evalMotive (MAny f) (ListCat a b) = (|||)
  <$> evalMotive (MAny f) a
  <*> evalMotive (MAny f) b
evalMotive (MAny f) (ListMap g lst) = evalMotive (MAny (f . g)) lst
evalMotive (MAny f) (ListInfo info) = case info of
  AnyInfo (SAny g) -> do
    j <- exists_
    let fEval = sEval $ f $ Sym j
        gEval = sEval $ g $ Sym j
    pure $ gEval ==> fEval
  LenInfo (SListLength len)
    | Just 0 <- unliteral len -> pure false
    | otherwise -> error "TODO"
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
  -- ifor_ litLst $ \j val -> constrain $
  --   fromIntegral j .== i ==> literal val .== a

evalMotive (MNegate (MAll f)) lst = evalMotive (MAny (Not . f)) lst
evalMotive (MNegate (MAny f)) lst = evalMotive (MAll (Not . f)) lst

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

  let l0 :: Expr 'IntTy
      l0 = LitI 0

      gt0 :: Expr 'IntTy -> Expr 'BoolTy
      gt0 x = Gt x l0

      lte0 :: Expr 'IntTy -> Expr 'BoolTy
      lte0 x = Not (Gt x l0)

  makeReport "length [] == 0 (expect good)" $ do
    let lst = ListInfo (LenInfo (SListLength 0)) :: Expr ('List 'IntTy)
    constrain =<< evalMotive (MLength l0) lst

  -- show that the result of a mapping is all positive
  makeReport "fmap (> 0) lst == true (expect good)" $ do
    let lst = ListInfo (AllInfo (SAll gt0)) :: Expr ('List 'IntTy)

    constrain =<< evalMotive (MAll gt0) lst

  let almostAllPos :: Expr ('List 'IntTy)
      almostAllPos = ListCat
        (ListInfo (AllInfo (SAll gt0)))
        (ListCat
          (ListInfo (AllInfo (SAll (Eq l0))))
          (ListInfo (AllInfo (SAll gt0))))
  makeReport "fmap (> 0) almostAllPos == true (expect bad)" $ do
    constrain =<< evalMotive (MAll gt0) almostAllPos

  makeReport "(and []) == true (expect good)" $
    constrain <=< evalMotive (MAll (Eq true')) $ ListInfo $ LenInfo $ SListLength 0

  makeReport "(not (and [])) == true (expect bad)" $ do
    x <- evalMotive (MAll (Eq true')) $ ListInfo $ LenInfo $ SListLength 0
    constrain $ bnot x

  let mkAnd :: SBV Bool -> ListInfo 'BoolTy
      mkAnd = AllInfo . SAll . Eq . Sym

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
    constrain <=< evalMotive (MNegate (MAny gt0)) $ ListInfo $ AllInfo $
      SAll gt0

  makeReport "not (all (> 0) (any [<= 0])) == true (expect good)" $ do
    constrain <=< evalMotive (MNegate (MAll gt0)) $ ListInfo $ AnyInfo $
      SAny lte0

  makeReport "at 2 [1, 2, 3] == 3 (expect good)" $ do
    constrain <=< evalMotive (MAt (LitI 2) (LitI 3)) $ ListInfo $ LitList
      [1, 2, 3]

  makeReport "at 2 [1, 2, 3] == 2 (expect bad)" $ do
    constrain <=< evalMotive (MAt (LitI 2) (LitI 2)) $ ListInfo $ LitList
      [1, 2, 3]

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
