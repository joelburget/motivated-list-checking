
data BoundedArray a = BoundedArray
  { start :: SBV Integer
  , len   :: SBV Integer
  -- TODO: maybe SFunArray?
  , values :: SArray Integer a
  }

newBoundedArray :: HasKind a => SBV Integer -> Symbolic (BoundedArray a)
newBoundedArray len = do
  arr <- newArray_ Nothing
  pure $ BoundedArray 0 len arr

length :: BoundedArray a -> SBV Integer
length BoundedArray{len} = len

null :: BoundedArray a -> SBV Bool
null BoundedArray{len} = len .== 0

head :: BoundedArray a -> SBV a
head BoundedArray{start, values} = readArray values start

tail :: BoundedArray a -> BoundedArray a
tail arr@BoundedArray{start} = arr{start=start+1}

singleton :: SymWord a => SBV a -> Symbolic (BoundedArray a)
singleton val = do
  arr <- newArray_ Nothing
  let arr' = writeArray arr 0 val
  pure $ BoundedArray 0 1 arr'

implode :: SymWord a => [SBV a] -> Symbolic (BoundedArray a)
implode vals = do
  let len = P.length vals
  arr <- newArray_ Nothing
  pure $ BoundedArray 0 (fromIntegral len) $ ifoldl
    (\i arr' val -> writeArray arr' (fromIntegral i) val)
    arr
    vals

concat :: BoundedArray a -> BoundedArray a -> BoundedArray a
concat = undefined

map
  :: SymWord b
  => (SBV a -> SBV b) -> BoundedArray a -> Symbolic (BoundedArray b)
map f (BoundedArray start len arrA) = do
  arrB <- newArray_ Nothing
  i    <- forall_
  constrain $ start .<= i
  constrain $ i     .<  len
  pure $ BoundedArray start len $ writeArray arrB i $ f $ readArray arrA i

-- XXX this is trouble
filter :: (SBV a -> SBV Bool) -> BoundedArray a -> BoundedArray a
filter = undefined

foldr :: (SBV a -> SBV b -> SBV b) -> SBV b -> BoundedArray a -> BoundedArray b
foldr = undefined

foldl :: (SBV b -> SBV a -> SBV b) -> SBV b -> BoundedArray a -> BoundedArray b
foldl = undefined
