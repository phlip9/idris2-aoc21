module Data.Vec

import Data.IOArray.Prims

%default total

export
data I61 : Type where [external]

namespace I61
  %foreign "scheme:(lambda (x y) (if (fx= x y) 1 0))"
  export %inline
  prim__eq_I61 : I61 -> I61 -> Bool

  %foreign "scheme:(lambda (x y) (if (fx< x y) 1 0))"
  export %inline
  prim__lt_I61 : I61 -> I61 -> Bool

  %foreign "scheme:(lambda (x y) (if (fx<= x y) 1 0))"
  export %inline
  prim__lte_I61 : I61 -> I61 -> Bool

  %foreign "scheme:(lambda (x y) (if (fx> x y) 1 0))"
  export %inline
  prim__gt_I61 : I61 -> I61 -> Bool

  %foreign "scheme:(lambda (x y) (if (fx>= x y) 1 0))"
  export %inline
  prim__gte_I61 : I61 -> I61 -> Bool

  %foreign "scheme:fx+"
  export %inline
  prim__add_I61 : I61 -> I61 -> I61

  %foreign "scheme:fx*"
  export %inline
  prim__mul_I61 : I61 -> I61 -> I61

  -- will panic if Integer is out-of-bounds
  %foreign "scheme:(lambda (x) (fx+ x 0))"
  export %inline
  prim__cast_Integer_I61 : Integer -> I61

  %foreign "scheme:fx-"
  export %inline
  prim__neg_I61 : I61 -> I61

  %foreign "scheme:fx-"
  export %inline
  prim__sub_I61 : I61 -> I61 -> I61

  %foreign "scheme:fxabs"
  export %inline
  prim__abs_I61 : I61 -> I61

  %foreign "scheme:fxdiv"
  export %inline
  partial
  prim__div_I61 : I61 -> I61 -> I61

  %foreign "scheme:fxmod"
  export %inline
  partial
  prim__mod_I61 : I61 -> I61 -> I61

public export
Eq I61 where
  (==) = prim__eq_I61

public export
Ord I61 where
  (<) = prim__lt_I61
  (<=) = prim__lte_I61
  (>) = prim__gt_I61
  (>=) = prim__gte_I61

%inline
public export
Num I61 where
  (+) = prim__add_I61
  (*) = prim__mul_I61
  fromInteger = prim__cast_Integer_I61

%inline
public export
Neg I61 where
  negate = prim__neg_I61
  (-) = prim__sub_I61

public export
Abs I61 where
  abs = prim__abs_I61

public export
Integral I61 where
  div = prim__div_I61
  mod = prim__mod_I61

Cast Integer I61 where
  cast = prim__cast_Integer_I61

Cast Nat I61 where
  cast x = cast {to=I61} (cast {to=Integer} x)

Cast I61 Integer where
  cast = believe_me

Show I61 where
  showPrec d x = showPrec d (cast {to=Integer} x)

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

namespace IOVec
  export
  withCapacity : HasIO io => Int -> io (IOVec a)
  withCapacity cap = pure (MkIOVec (unsafeCoerceArrayType !(primIO (prim__newArrayUninit cap))) 0 cap)

  export %inline
  new : HasIO io => io (IOVec a)
  new = withCapacity 0

  export
  replicate : HasIO io => Int -> a -> io (IOVec a)
  replicate n x = pure (MkIOVec !(primIO (prim__newArray n x)) n n)

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

  public export %inline
  unsafeGet'' : IOVec a -> Int -> a
  unsafeGet'' vec idx = unsafePerformIO $ primIO $ prim__arrayGet vec.array idx

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

  -- what do we want to benchmark (to decide how to structure this module)
  -- placing unsafePerformIO deep inside vs only at the outer-most layer?
  -- first, let's try a read-only bench like sum'ing a big IOVec

  export
  sum : HasIO io => Num a => IOVec a -> io a
  sum xs = go xs 0 0
    where
      go : IOVec a -> Int -> a -> io a
      go xs idx s = if idx < xs.len
                       then assert_total $ go xs (idx + 1) (s + !(unsafeGet xs idx))
                       else pure s

  export
  sum' : Num a => IOVec a -> a
  sum' xs = go xs 0 0
    where
      go : IOVec a -> Int -> a -> a
      go xs idx s = if idx < xs.len
                       then assert_total $ go xs (idx + 1) (s + (unsafeGet' xs idx))
                       else s

  export
  sum'' : IOVec Int32 -> Int32
  sum'' xs = go xs 0 0
    where
      go : IOVec Int32 -> Int -> Int32 -> Int32
      go xs idx s = if idx < xs.len
                       then assert_total $ go xs (idx + 1) (s + (unsafeGet' xs idx))
                       else s

  export
  sum''' : IOVec Int32 -> Int32
  sum''' xs = go xs 0 0
    where
      go : IOVec Int32 -> Int -> Int32 -> Int32
      go xs idx s = if idx < xs.len
                       then assert_total $ go xs (idx + 1) (s + (unsafeGet'' xs idx))
                       else s

  public export %inline
  unsafeGet4 : IOVec Int32 -> Int -> Int32
  unsafeGet4 vec idx = unsafePerformIO $ primIO $ prim__arrayGet vec.array idx

  export
  sum4 : IOVec Int32 -> Int32
  sum4 xs = go xs 0 0
    where
      go : IOVec Int32 -> Int -> Int32 -> Int32
      go xs idx s = if idx < xs.len
                       then assert_total $ go xs (idx + 1) (s + (unsafeGet4 xs idx))
                       else s

  export
  fromList : HasIO io => List a -> io (IOVec a)
  fromList list = do
    let len = cast (length list)
    vec <- IOVec.withCapacity len
    foldlM (\vec, x => push vec x) vec list

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

  export
  test : IO ()
  test = do
    xs <- IOVec.withCapacity 5
    xs <- IOVec.push xs 1
    xs' <- IOVec.push xs 9
    printLn xs
    printLn xs'
    ys <- IOVec.push xs 2
    printLn xs
    printLn xs'
    printLn ys

export
record Vec a where
  constructor MkVec
  array : ArrayData a
  len : Int
  cap : Int

namespace Vec
  -- we need these funky lambdas to drop the Erased argument which idris leaves
  -- in for some reason...

  %foreign "scheme:(lambda (_ cap) (make-vector cap))"
  %inline
  prim__newArrayUninit' : Int -> ArrayData a

  %foreign "scheme:(lambda (_ xs idx) (vector-ref xs idx))"
  %inline
  prim__arrayGet' : ArrayData a -> Int -> a

  %foreign "scheme:(lambda (_ xs idx x) (vector-set! xs idx x) xs)"
  %inline
  prim__arraySet' : ArrayData a -> Int -> a -> ArrayData a

  export %inline
  withCapacity : Int -> Vec a
  withCapacity cap = MkVec (prim__newArrayUninit' cap) 0 cap

  export %inline
  new : Vec a
  new = withCapacity 0

  export %inline
  unsafeGet : Vec a -> Int -> a
  unsafeGet vec idx = prim__arrayGet' vec.array idx

  export %inline
  unsafeSet : Vec a -> Int -> a -> Vec a
  unsafeSet vec idx x = { array := prim__arraySet' vec.array idx x } vec

  export %inline
  push : Vec a -> a -> Vec a
  push vec x = { array := prim__arraySet' vec.array vec.len x
               , len := vec.len + 1 } vec
    -- vec <- if vec.len == vec.cap
    --        then ?todo -- resize
    --        else pure vec
  
  export
  fromList : List a -> Vec a
  fromList list
    = let len = cast (length list)
          vec = Vec.withCapacity len in
          foldl Vec.push vec list

  export
  sum : Vec Int32 -> Int32
  sum xs = go xs 0 0
    where
      go : Vec Int32 -> Int -> Int32 -> Int32
      go xs idx s = if idx < xs.len
                       then assert_total $ go xs (idx + 1) (s + (Vec.unsafeGet xs idx))
                       else s

  export
  Show a => Show (Vec a) where
    show vec = "[" ++ (go 0 "" vec) ++ "]"
      where
        go : Int -> String -> Vec a -> String
        go idx acc vec =
          if idx < (vec.len - 1) then assert_total $
            go (idx + 1) (acc ++ show (unsafeGet vec idx) ++ ", ") vec
          else if idx < vec.len then
            acc ++ show (unsafeGet vec idx)
          else
            acc

data FXVector : Type where [external]

export
record I61Vec where
  constructor MkI61Vec
  array : FXVector
  len : I61
  cap : I61

namespace I61Vec
  -- we need these funky lambdas to drop the Erased argument which idris leaves
  -- in for some reason...

  %foreign "scheme:make-fxvector"
  %inline
  prim__newArrayUninit' : I61 -> FXVector

  %foreign "scheme:fxvector-ref"
  %inline
  prim__arrayGet' : FXVector -> I61 -> I61

  %foreign "scheme:(lambda (vec idx val) (fxvector-set! vec idx val) vec)"
  %inline
  prim__arraySet' : FXVector -> I61 -> I61 -> FXVector

  export %inline
  withCapacity : I61 -> I61Vec
  withCapacity cap = MkI61Vec (I61Vec.prim__newArrayUninit' cap) 0 cap

  export %inline
  new : I61Vec
  new = withCapacity 0

  export %inline
  unsafeGet : I61Vec -> I61 -> I61
  unsafeGet vec idx = I61Vec.prim__arrayGet' vec.array idx

  export %inline
  unsafeSet : I61Vec -> I61 -> I61 -> I61Vec
  unsafeSet vec idx x = { array := I61Vec.prim__arraySet' vec.array idx x } vec

  export %inline
  push : I61Vec -> I61 -> I61Vec
  push vec x = { array := I61Vec.prim__arraySet' vec.array vec.len x
               , len := vec.len + 1 } vec
    -- vec <- if vec.len == vec.cap
    --        then ?todo -- resize
    --        else pure vec
  
  export
  fromList : List I61 -> I61Vec
  fromList list
    = let len = cast (length list)
          vec = I61Vec.withCapacity len in
          foldl I61Vec.push vec list

  export
  sum : I61Vec -> I61
  sum xs = go xs 0 0
    where
      go : I61Vec -> I61 -> I61 -> I61
      go xs idx s = if idx < xs.len
                       then assert_total $ go xs (idx + 1) (s + (I61Vec.unsafeGet xs idx))
                       else s

  export
  test : I61 -> (I61Vec, I61Vec)
  test x = let xs = I61Vec.withCapacity 4
               xs = I61Vec.push xs 1
               xs = I61Vec.push xs 2
               xs = I61Vec.push xs 3 in
               (I61Vec.push xs 4, I61Vec.push xs x)

  export
  Show I61Vec where
    show vec = "[" ++ (go 0 "" vec) ++ "]"
      where
        go : I61 -> String -> I61Vec -> String
        go idx acc vec =
          if idx < (vec.len - 1) then assert_total $
            go (idx + 1) (acc ++ show (I61Vec.unsafeGet vec idx) ++ ", ") vec
          else if idx < vec.len then
            acc ++ show (I61Vec.unsafeGet vec idx)
          else
            acc
