module Data.Vec

import Data.IOArray.Prims

%default total

-- Need this since otherwise we get an unwanted `Erased` in the `make-vector`
-- arguments.
data ArrayDataErased : Type where [external]

%inline
unsafeCoerceArrayType : ArrayDataErased -> ArrayData a
unsafeCoerceArrayType = believe_me

%foreign "scheme:make-vector"
export
prim__newArrayUninit : Int -> PrimIO (ArrayDataErased)

export
record IOVec a where
  constructor MkIOVec 
  array : ArrayData a
  len : Int
  cap : Int

export
withCapacity : HasIO io => Int -> io (IOVec a)
withCapacity cap = pure (MkIOVec (unsafeCoerceArrayType !(primIO (prim__newArrayUninit cap))) 0 cap)

export %inline
new : HasIO io => io (IOVec a)
new = withCapacity 0

public export %inline
inBounds : IOVec a -> Int -> Bool
inBounds vec idx = 0 <= idx && idx < vec.len

export
partial
unsafeGet : HasIO io => IOVec a -> Int -> io a
unsafeGet vec idx = pure !(primIO (prim__arrayGet vec.array idx))

export
unsafeGet' : IOVec a -> Int -> a
unsafeGet' vec idx = unsafePerformIO $ primIO $ prim__arrayGet vec.array idx

export
partial
unsafeSet : HasIO io => IOVec a -> Int -> a -> io ()
unsafeSet vec idx x = primIO (prim__arraySet vec.array idx x)

-- TODO: is returning a () here bad? could the compiler just pretend this fn does
--       nothing and always return a () immediately?
--       we could return the vec itself perhaps?
export
partial
unsafeSet' : IOVec a -> Int -> a -> ()
unsafeSet' vec idx x = unsafePerformIO $ primIO $ prim__arraySet vec.array idx x

export
get : HasIO io => IOVec a -> Int -> io (Maybe a)
get vec idx = if inBounds vec idx
              then map Just $ unsafeGet vec idx
              else pure Nothing

export
get' : IOVec a -> Int -> Maybe a
get' vec idx = if inBounds vec idx
               then Just $ unsafeGet' vec idx
               else Nothing

export
partial
set : HasIO io => IOVec a -> Int -> a -> io ()
set vec idx x = case inBounds vec idx of
                     True => unsafeSet vec idx x

export
partial
set' : IOVec a -> Int -> a -> ()
set' vec idx x = case inBounds vec idx of
                      True => unsafeSet' vec idx x

export
push : HasIO io => IOVec a -> a -> io (IOVec a)
push vec x = do
  -- vec <- if vec.len == vec.cap
  --        then ?todo -- resize
  --        else pure vec
  unsafeSet vec vec.len x
  pure $ { len := vec.len + 1 } vec

fromList : HasIO io => List a -> io (IOVec a)
fromList list = do
  let len = cast (length list)
  vec <- Vec.withCapacity len
  go list vec
    where
      go : List a -> IOVec a -> io (IOVec a)
      go [] vec = pure vec
      go (x :: xs) vec = go xs !(push vec x)

export
Show a => Show (IOVec a) where
  show vec = "[" ++ (unsafePerformIO (go 0 "" vec)) ++ "]"
    where
      go : Int -> String -> IOVec a -> IO (String)
      go idx acc vec =
        if idx < (vec.len - 1) then assert_total $
          go (idx + 1) (acc ++ show !(unsafeGet vec idx) ++ ", ") vec
        else if idx < vec.len then pure $
          acc ++ show !(unsafeGet vec idx)
        else
          pure acc
