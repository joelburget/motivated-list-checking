{-# language NamedFieldPuns    #-}
{-# language OverloadedStrings #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
module Main where

import Prelude as P
-- import Control.Lens
import Data.SBV
import qualified Data.SBV.String as SBVS

class SymbolicMonoid a where
  sempty :: a
  (.<>)  :: SBV a -> SBV a -> SBV a

instance SymbolicMonoid Integer where
  sempty = 0
  (.<>)  = (+)

instance SymbolicMonoid String where
  sempty = ""
  (.<>)  = SBVS.concat

newtype SListLength = SListLength (SBV Integer)

instance Semigroup SListLength where
  SListLength x <> SListLength y = SListLength $ x + y

instance Monoid SListLength where
  mempty = SListLength 0

-- A list represented as the result of a fold
newtype FoldedList a = FoldedList (SBV a)

cons :: SymbolicMonoid a => SBV a -> FoldedList a -> FoldedList a
cons a (FoldedList f) = FoldedList $ a .<> f

concat :: SymbolicMonoid a => FoldedList a -> FoldedList a -> FoldedList a
concat (FoldedList a) (FoldedList a') = FoldedList $ a .<> a'

main :: IO ()
main = putStrLn "Hello, Haskell!"
