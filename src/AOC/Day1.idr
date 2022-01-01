module AOC.Day1

import Data.List
import Data.String

import Scratch
import System.ReadExt

%default total

parse : List String -> List Integer
parse lines = mapMaybe parseInteger lines

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

part1 : List Integer -> Integer
part1 xs = cast $ length $ filter (>0) (dt xs)

part2 : List Integer -> Integer
part2 xs = part1 $ map (\(x, y, z) => x + y + z) (windows3 xs)

part1' : List Integer -> Integer
part1'        [] = 0
part1' (x :: xs) = fst $ foldl foldCount (0, x) xs
  where
    foldCount : (Integer, Integer) -> Integer -> (Integer, Integer)
    foldCount (count, prev) next = let inc = if next > prev then 1 else 0 in
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
            inc = if nextSum > prevSum then 1 else 0 in
            (count + inc, nextSum, prev1, next)

export
day1 : IO ()
day1
  = do Right lines <- readFileWithLimit "data/01"
             | Left err => putStrLn ("Error reading data: " ++ show err)
       let xs = parse lines
       part "Part 1" $ part1 xs
       part "Part 1'" $ part1' xs
       part "Part 2" $ part2 xs
       part "Part 1'" $ part2' xs
  where
    part : String -> Lazy Integer -> IO ()
    part label thunk = do out <- timeit label $ delay (pure (force thunk))
                          putStrLn (label ++ ":  out: " ++ show out ++ "\n")

