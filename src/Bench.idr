module Bench

import Data.List
import Data.List1
import Data.String
import Data.Vec
import Scratch
import System.Clock
import System.Random

%default total

dbg : Show a => String -> a -> a
dbg label val = unsafePerformIO $ do
  putStrLn "\{label}: \{show val}"
  pure val

||| Clamp `x` to the range `[min, max]`. Assumes `min <= max`.
clamp : Ord a => (min : a) -> (max : a) -> (x : a) -> a
clamp min max x = if x > max then max
                  else if x < min then min
                  else x

||| Linearly interpolate between `x0` and `x1` according to the scale parameter `t`.
||| For example, `lerp` returns `x0` when `t = 0` and `x1` when `t = 1`.
lerp : Num a => Neg a => (x0 : a) -> (x1 : a) -> (t : a) -> a
lerp x0 x1 t = (1 - t) * x0 + (t * x1)

||| Linearly interpolate between `x0` and `x1` then clamp in the range `[x0, x1]`.
||| Useful for handling scale parameters `t ∉ [0, 1]`
lerpClamp : Ord a => Num a => Neg a => (x0 : a) -> (x1 : a) -> (t : a) -> a
lerpClamp x0 x1 t = clamp x0 x1 (lerp x0 x1 t)

||| Truncate a float number returning the whole part. Truncate works
||| correctly on negative numbers, unlike `floor`.
||| For example, `trunc 3.58 == 3.0` and `trunc (-4.9) == (-4.0)`
trunc : F64 -> F64
trunc x = cast {to=F64} $ cast {to=Integer} x

||| Return the fractional part of a float number.
||| For example, `frac 3.58 == 0.58` and `fract (-4.9) == (-0.9)`
fract : F64 -> F64
fract x = x - trunc x

data Interval a
  = OpenAbove a -- [a ..)
  | OpenBelow a -- (.. a]
  | Closed a a -- [a .. b]

||| Return the fractional index of a list as an `Interval` of the adjacent integer
||| number entries. A negative index will result in an `OpenBelow` interval while
||| an index greater than the largest integer index will result in an `OpenAbove`
||| interval.
fractIndex : (xs : List1 a) -> (idx : F64) -> Interval a
fractIndex (x ::: xs) idx = if idx < 0.0 then OpenBelow x
                            else go x xs (cast idx)
where
  go : a -> List a -> Nat -> Interval a
  go x [] idx = OpenAbove x
  go x (y :: _) 0 = Closed x y
  go _ (y :: ys) (S idx) = go y ys idx

||| Return the empirical quantile, interpolating between the two adjacent integer
||| number entries.
||| Assumes `xs` is sorted. Handles `q ∉ [0, 1]` by returning the min or max
||| respectively.
empiricalQuantile : (xs : List1 F64) -> (q : F64) -> F64
empiricalQuantile xs q
  = let n = cast {to=F64} $ length xs
        idx = (n * q) - 1
        t = fract idx in
        case fractIndex xs idx of
             OpenAbove x => x
             OpenBelow x => x
             Closed x y => lerpClamp x y t

namespace Maybe
  ||| Assert that a `Maybe` must be `Just`.
  export
  partial
  unwrap : Maybe a -> a
  unwrap m = case m of
                  Just x => x

namespace List1
  export
  sort : Ord a => List1 a -> List1 a
  sort xs = let sorted = List.sort (forget xs) in
                -- Proving that List.sort doesn't change the length is tedious
                -- so just assert_total here...
                assert_total $ Maybe.unwrap $ List1.fromList sorted

namespace Clock
  export
  fromMillis : Cast a Integer => a -> Clock Duration
  fromMillis ms
    = let ms = cast {to=Integer} ms
          ns = ms `mod` 1000000
          s = if ms > 0 then ms `div` 1000000
                        else 0 in
          makeDuration s ns
  
  export
  fromSecs : Cast a Integer => a -> Clock Duration
  fromSecs s = makeDuration (cast s) 0

||| Replace elements below/above `q`/`1-q` quantile with the `q`/`1-q` quantile
||| respectively. Reduces impact of outliers without changing the number of samples.
|||
||| Note: assumes xs is sorted
||| See: https://en.wikipedia.org/wiki/Winsorising
||| 
||| ### Example
|||
||| ```idris2
||| > winsorize [1.0,2,3,4,5,6,7,8,9,10] 0.25
||| [2.5 2.5, 3.0, 4.0, 5.0, 6.0, 7.0, 7.5, 7.5, 7.5]
||| ```
winsorize : (xs : List1 F64) -> (q : F64) -> List1 F64
winsorize xs q
  = let q = clamp 0.0 1.0 q
        q = if q > 0.5 then 1.0 - q else q
        lo = empiricalQuantile xs q
        hi = empiricalQuantile xs (1.0 - q) in
        map (clamp lo hi) xs

winsorizeUnsorted : (xs : List1 F64) -> (q : F64) -> List1 F64
winsorizeUnsorted xs q = winsorize (sort xs) q

||| Computes the Median Absolute Deviation multiplied by a constant `c = 1.4826`.
||| Note: assumes `xs` is sorted and roughly normal
||| See: https://www.wikiwand.com/en/Median_absolute_deviation
|||  and https://www.rdocumentation.org/packages/stats/versions/3.6.2/topics/mad
median_abs_dev : (xs : List1 F64) -> (p50 : F64) -> {default 1.4826 c : F64} -> F64
median_abs_dev xs p50
  = let abs_devs = List1.sort $ map (\x => abs (p50 - x)) xs
        p50' = empiricalQuantile abs_devs 0.50 in
        c * p50'

record Summary where
  constructor MkSummary
  min : F64
  max : F64
  p50 : F64
  median_abs_dev : F64

namespace Summary
  ||| assumes `samples` is sorted
  export
  fromList1 : (samples : List1 F64) -> Summary
  fromList1 samples
    = let min = foldl1 min samples
          max = foldl1 max samples
          p50 = empiricalQuantile samples 0.50
          mad = median_abs_dev samples p50 in
          MkSummary min max p50 mad

fmtNanosF64 : F64 -> String
fmtNanosF64 = fmtDuration . fromNanos

implementation Show Summary where
    show s = """
             Summary { \
             min := \{fmtNanosF64 s.min}, \
             max := \{fmtNanosF64 s.max}, \
             p50 := \{fmtNanosF64 s.p50}, \
             median_abs_dev := \{fmtNanosF64 s.median_abs_dev} \
             }
             """

collectSample : (k : Integer) -> (prog : IO a) -> IO Integer
collectSample k prog = do
  start <- clockTime Monotonic
  for_ [1..k] $ \_ => prog
  end <- clockTime Monotonic

  let nsElapsed = toNanos end - toNanos start
  pure nsElapsed

||| Progressively double the number of samples until the absolute error stabilizes.
||| Stop sampling if this bench takes too long (>3 seconds).
bIterInner : Integer -> Clock Duration -> IO a -> IO Summary
bIterInner samplesPerIter totalDuration prog = do
  loopStart <- clockTime Monotonic

  samples <- for (rangeTo (50 - 1)) $ \_ => do
    ns <- collectSample samplesPerIter prog
    pure $ (cast {to=F64} ns) / (cast {to=F64} samplesPerIter)

  let samples = winsorizeUnsorted samples 0.05
  let summary = Summary.fromList1 samples

  let samplesPerIter' = 5 * samplesPerIter

  samples' <- for (rangeTo (50 - 1)) $ \_ => do
    ns <- collectSample (samplesPerIter') prog
    pure $ (cast {to=F64} ns) / (cast {to=F64} samplesPerIter')

  let samples' = winsorizeUnsorted samples' 0.05
  let summary' = Summary.fromList1 samples'

  loopEnd <- clockTime Monotonic
  let loopDuration = timeDifference loopEnd loopStart
  let totalDuration = addDuration totalDuration loopDuration

  if loopDuration > Clock.fromMillis 100
       && (summary.median_abs_dev / summary.p50) < 0.02
       && abs (summary.p50 - summary'.p50) < summary'.median_abs_dev
    then pure (summary')
    else if totalDuration > Clock.fromSecs 3
      then pure (summary')
      -- This loop terminates since the clock is monotonic and we double the
      -- amount of work each iteration.
      else assert_total $ bIterInner (samplesPerIter * 2) totalDuration prog

safeDiv1 : Integral a => Ord a => a -> a -> a
safeDiv1 x y = x `div` (max 1 y)

export
bIter : (prog : IO a) -> IO Summary
bIter prog = do
  -- to start, let's estimate the number of iterations needed to hit a minimum
  -- target time of 1 ms
  nsSingle <- collectSample 1 prog
  let nsTarget = 1000000 -- 1 ms
  let samplesPerIter = max 1 (nsTarget `safeDiv1` nsSingle)

  bIterInner samplesPerIter (Clock.fromSecs 0) prog

export
data Benchmark
  = Single String (IO Summary)
  | Group String (List Benchmark)

export
bench : String -> IO Summary -> Benchmark
bench = Single

export
benchGroup : String -> List Benchmark -> Benchmark
benchGroup = Group

withPrefix : String -> Benchmark -> Benchmark
withPrefix preLabel (Single label prog) = Single (preLabel ++ "/" ++ label) prog
withPrefix preLabel (Group label benches) = Group (preLabel ++ "/" ++ label) benches

runBenchmark : Benchmark -> IO ()
runBenchmark (Single label benchProg) = do
  let prefixStr = "bench   \{label}: "
  putStr prefixStr

  summary <- benchProg

  let medianStr = padLeft 9 ' ' $ fmtNanosF64 summary.p50
  let padding = 40 `minus` (length prefixStr)
  let deviationStr = fmtNanosF64 $ 0.5 * (summary.max - summary.min)
  let resultStr = indent padding "\{medianStr} (± \{deviationStr})"

  putStrLn resultStr

runBenchmark (Group label benches) = do
  let header = "Bench Group: \{label}"
  putStrLn header
  putStrLn $ replicate (length header) '━'
  for_ benches $ \bench => do
    assert_total $ runBenchmark $ withPrefix label bench
  putStrLn ""

-- TODO(phlip9): CLI options & benchmark filtering
export
benchMain : List Benchmark -> IO ()
benchMain benches = for_ benches runBenchmark

benchListSum'' : IO Summary
benchListSum'' = do
  xs <- pure (the (List Int32) [1..10000])
  bIter $ pure (sum xs)

benchListSum4 : IO Summary
benchListSum4 = do
  xs <- for [1..10000] $ \_ => randomRIO {a=Int32} (0, 10000)
  bIter $ pure (sum xs)

export
main : IO ()
main = benchMain
  [ benchGroup "sum List"
      [ bench "inline" $ do
          let xs : List Int32 = [1..10000]
          bIter $ pure (sum xs)
      ]
  , benchGroup "sum IOVec"
      [ bench "IO" $ do
          xs <- IOVec.fromList {a=Int32} [1..10000]
          bIter $ IOVec.sum xs
      , bench "unsafeIO" $ do
          xs <- IOVec.fromList {a=Int32} [1..10000]
          bIter $ pure (IOVec.sum' xs)
      , bench "unsafeIO spec" $ do
          xs <- IOVec.fromList {a=Int32} [1..10000]
          bIter $ pure (IOVec.sum'' xs)
      , bench "unsafeIO spec,inl" $ do
          xs <- IOVec.fromList {a=Int32} [1..10000]
          bIter $ pure (IOVec.sum''' xs)
      , bench "unsafeIO spec,inl,get" $ do
          xs <- IOVec.fromList {a=Int32} [1..10000]
          bIter $ pure (IOVec.sum4 xs)
      ]
  , benchGroup "sum IOVec"
      [ bench "pure spec,inl" $ do
          let xs = Vec.fromList {a=Int32} [1..10000]
          bIter $ pure $ Vec.sum xs
      ]
  , benchGroup "sum I61Vec"
      [ bench "pure spec,inl" $ do
          let xs = I61Vec.fromList [1..10000]
          bIter $ pure $ I61Vec.sum xs
      ]
  ]
