module AOC.Day3

import Data.Bits
import Data.DPair
import Data.Fin
import Data.List
import Data.List1
import Data.Nat
import Data.String
import Data.Vect
import Scratch
import System.ReadExt

%default total

namespace Vect
  public export
  foldlWithIndex : {0 acc : Type} ->
                   {0 elem : Type} ->
                   {len : Nat} ->
                   (acc -> elem -> Subset Nat (`LT` len) -> acc) ->
                   acc ->
                   Vect len elem ->
                   acc
  foldlWithIndex {len = Z} f acc [] = acc
  foldlWithIndex {len = S k} f acc (x :: xs)
    = let accNext = (f acc x (Element Z ltZero)) in
          foldlWithIndex {len = k} (\acc, elem, (Element n prf) => f acc elem (Element (S n) (LTESucc prf))) accNext xs

public export %inline
bitToChar : Bool -> Char
bitToChar False = '0'
bitToChar True = '1'

parseBitsVect : String -> Maybe (p ** Vect p Bool)
parseBitsVect s = go (0 ** []) $ unpack (trim s)
where
  go : (p ** Vect p Bool) -> List Char -> Maybe (q ** Vect q Bool)
  go acc [] = Just acc
  go (p ** bits) (c :: cs) = do
    bit <- case c of
                '0' => Just False
                '1' => Just True
                _ => Nothing
    go (1 + p ** bit :: bits) cs

export
interface FiniteBits a => NonDegenFinBits a where
  0 prf : 2 `LTE` bitSize {a}

gte2 : {n : Nat} -> 2 `LTE` (S (S n))
gte2 = LTESucc $ LTESucc LTEZero

export NonDegenFinBits Bits8 where prf = gte2
export NonDegenFinBits Bits16 where prf = gte2
export NonDegenFinBits Bits32 where prf = gte2
export NonDegenFinBits Bits64 where prf = gte2

namespace NonDegenFinBits
  public export %inline
  zeroIndex : NonDegenFinBits a => Index {a}
  zeroIndex = bitsToIndex {a} (Element 0 (transitive (LTESucc LTEZero) prf))

  public export %inline
  oneIndex : NonDegenFinBits a => Index {a}
  oneIndex = bitsToIndex {a} (Element 1 prf)

  public export %inline
  boolToBits : NonDegenFinBits a => Bool -> a
  boolToBits False = zeroBits
  boolToBits True = bit zeroIndex

  public export %inline
  shiftLOne : NonDegenFinBits a => a -> a
  shiftLOne x = shiftL x oneIndex

  export %inline
  bitIndexes : NonDegenFinBits a => Vect (bitSize {a}) (Index {a})
  bitIndexes = tabulate {len=bitSize} bitsToIndex

  ||| returns a Vect from LSB -> MSB
  export
  unpackBits : NonDegenFinBits a => a -> Vect (bitSize {a}) Bool
  unpackBits x = tabulate {len=bitSize} (\idx => testBit x (bitsToIndex idx))

  public export
  boolBit : NonDegenFinBits a => Index {a} -> Bool -> a
  boolBit idx True = bit idx
  boolBit idx False = zeroBits

  ||| takes an unpacked bits Vect (from LSB -> MSB) and packs into bits
  export
  packBits : NonDegenFinBits a => Vect (bitSize {a}) Bool -> a
  packBits xs = foldlWithIndex (\acc, elem, idx => acc .|. boolBit (bitsToIndex idx) elem) zeroBits xs

bitsVectToBits : NonDegenFinBits a => {n : Nat} -> Vect n Bool -> Maybe a
bitsVectToBits {n} xs
  with (n <= bitSize {a})
    _ | False = Nothing
    bitsVectToBits {n=Z} [] | True = Nothing
    bitsVectToBits {n} xs | True = Just (go zeroBits bitIndexes xs)
  where go : a -> Vect m (Index {a}) -> Vect k Bool -> a
        go acc [] _ = acc
        go acc _ [] = acc
        go acc (idx :: idxs) (True :: bs) = go (acc .|. bit idx) idxs bs
        go acc (_ :: idxs) (False :: bs) = go acc idxs bs

export
parseBits : NonDegenFinBits a => String -> Maybe a
parseBits s = do
  (_ ** bitsVect) <- parseBitsVect s
  bitsVectToBits bitsVect

export
showBits : NonDegenFinBits a => a -> String
showBits x = reverse $ pack $ toList $ map bitToChar (unpackBits x)

parse : List String -> List Bits16
parse lines = mapMaybe parseBits lines

record State where
  constructor MkState
  parityCounts : Vect 12 (Integer, Integer)

emptyState : State
emptyState = MkState $ replicate 12 (0, 0)

toBits12 : Bits16 -> Vect 12 Bool
toBits12 b = take 12 (unpackBits b)

fromBits12 : Vect 12 Bool -> Bits16
fromBits12 xs = packBits (xs ++ replicate 4 False)

updateState : State -> Bits16 -> State
updateState s b = { parityCounts := zipWith zipper (toBits12 b) s.parityCounts } s
  where
    zipper : Bool -> (Integer, Integer) -> (Integer, Integer)
    zipper b (nZ, nO) = if b then (nZ, nO + 1) else (nZ + 1, nO)

-- tie-breaks to True
mostCommonBit : (Integer, Integer) -> Bool
mostCommonBit (nZ, nO) = if nO >= nZ then True else False

-- tie-breaks to False
leastCommonBit : (Integer, Integer) -> Bool
leastCommonBit (nZ, nO) = if nZ <= nO then False else True

gamma : State -> Bits16
gamma s = fromBits12 $ map mostCommonBit s.parityCounts

epsilon : State -> Bits16
epsilon s = fromBits12 $ map leastCommonBit s.parityCounts

part1 : List Bits16 -> Bits32
part1 xs = let state = foldl updateState emptyState xs
               gamma = cast {to=Bits32} $ gamma state
               epsilon = cast {to=Bits32} $ epsilon state in
               gamma * epsilon

countBitsIndex : Index {a=Bits16} -> List Bits16 -> (Integer, Integer)
countBitsIndex idx xs = foldl (folder idx) (0, 0) xs
  where
    folder : Index {a=Bits16} -> (Integer, Integer) -> Bits16 -> (Integer, Integer)
    folder idx (nZ, nO) x = if (testBit x idx) then (nZ, nO + 1) else (nZ + 1, nO)

diagnostic : Nat -> ((Integer, Integer) -> Bool) -> List Bits16 -> Bits16
diagnostic prec decider xs = let idxs = reverse $ take prec $ toList (bitIndexes {a=Bits16}) in
                                 go decider idxs xs
  where
    go : ((Integer, Integer) -> Bool) -> List (Index {a=Bits16}) -> List Bits16 -> Bits16
    go _ _ [] = zeroBits
    go _ _ (x :: []) = x
    go _ [] (x :: _) = x
    go decider (idx :: idxs) xs = let b = decider $ countBitsIndex idx xs
                                      xs = filter (\x => testBit x idx == b) xs in
                                      go decider idxs xs

oxygen : List Bits16 -> Bits16
oxygen xs = diagnostic 12 mostCommonBit xs

co2 : List Bits16 -> Bits16
co2 xs = diagnostic 12 leastCommonBit xs

part2 : List Bits16 -> Bits32
part2 xs = let oxygen = cast {to=Bits32} (oxygen xs)
               co2 = cast {to=Bits32} (co2 xs) in 
               oxygen * co2

export
day3 : String -> IO ()
day3 inputFilename = do
  (Right lines) <- readFileWithLimit inputFilename
  | Left err => putStrLn ("Error reading data: " ++ show err)

  let xs = parse lines

  part "Part 1" $ part1 xs
  part "Part 2" $ part2 xs
