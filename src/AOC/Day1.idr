module AOC.Day1

import Data.List
import Data.Vect
import Data.String

import Scratch
import System.ReadExt

%default total

export
windows2 : List a -> List (a, a)
windows2 [] = []
windows2 (x :: []) = []
windows2 (x1 :: x2 :: xs) = (x1, x2) :: windows2 (x2 :: xs)

windows3 : List a -> List (a, a, a)
windows3 [] = []
windows3 (x :: []) = []
windows3 (x1 :: x2 :: []) = []
windows3 (x1 :: x2 :: x3 :: xs) = (x1, x2, x3) :: windows3 (x2 :: x3 :: xs)

export
dt : List Integer -> List Integer
dt xs = map (\(x, y) => y - x) (windows2 xs)

dt'' : List Integer -> List Integer
dt'' xs = map (\[x, y] => y - x) (windowsL 2 xs)

part1 : List Integer -> Integer
part1 xs = cast $ length $ filter (>0) (dt xs)

part1'' : List Integer -> Integer
part1'' xs = cast $ length $ filter (>0) (dt'' xs)

part2 : List Integer -> Integer
part2 xs = part1 $ map (\(x, y, z) => x + y + z) (windows3 xs)

part1' : List Integer -> Integer
part1'        [] = 0
part1' (x :: xs) = fst $ foldl foldCount (0, x) xs
  where
    foldCount : (Integer, Integer) -> Integer -> (Integer, Integer)
    foldCount (count, prev) next = let inc : Integer = if next > prev then 1 else 0 in
                                       (count + inc, next)

part2' : List Integer -> Integer
part2' [] = 0
part2' (x1 :: []) = 0
part2' (x1 :: x2 :: []) = 0
part2' (x1 :: x2 :: x3 :: xs) = fst $ foldl foldCount (0, x1 + x2 + x3, x2, x1) xs
  where
    foldCount : (Integer, Integer, Integer, Integer) -> Integer -> (Integer, Integer, Integer, Integer)
    foldCount (count, prevSum, prev2, prev1) next
      = let nextSum = prev2 + prev1 + next
            inc : Integer = if nextSum > prevSum then 1 else 0 in
            (count + inc, nextSum, prev1, next)

export
day1 : String -> IO ()
day1 inputFilename = do
  Right lines <- readFileWithLimit inputFilename
  | Left err => putStrLn ("Error reading data: " ++ show err)
  let xs = parse lines
  part "Part 1" $ part1 xs
  part "Part 1'" $ part1' xs
  part "Part 1''" $ part1'' xs
  part "Part 2" $ part2 xs
  part "Part 2'" $ part2' xs

  Right (n ** lines) <- readFileWithLimit' "data/01"
  | Left err => putStrLn ("Error reading data: " ++ show err)
  putStrLn "Read \{show n} lines"
  let (m ** xs) = parse' lines
  putStrLn "\{show m} lines after parsing"

  part "Part 1V" $ part1V xs
  part "Part 1V'" $ part1V' xs
  part "Part 1V''" $ part1V'' xs
  part "Part 1V'''" $ part1V''' xs

  where
    parse : List String -> List Integer
    parse lines = mapMaybe parseInteger lines

    parse' : Vect n String -> (m ** Vect m Integer)
    parse' lines = mapMaybe parseInteger lines

    part1V : Vect n Integer -> Integer
    part1V        [] = 0
    part1V (x :: xs) = fst $ foldl foldCount (0, x) xs
      where
        foldCount : (Integer, Integer) -> Integer -> (Integer, Integer)
        foldCount (count, prev) next = let inc : Integer = if next > prev then 1 else 0 in
                                           (count + inc, next)

    dtV : {n : Nat} -> Vect n Integer -> Vect (n `minus` 1) Integer
    dtV xs = map (\[x, y] => y - x) (windows 2 xs)

    part1V' : {n : Nat} -> Vect n Integer -> Integer
    part1V' xs = foldl (\count, x => if x > 0 then count + 1 else count) 0 $ dtV xs

    part1V'' : {n : Nat} -> Vect n Integer -> Integer
    part1V'' xs = cast $ count (>0) $ dtV xs

    part1V''' : {n : Nat} -> Vect n Integer -> Integer
    part1V''' xs = cast $ fst $ filter (>0) $ dtV xs
