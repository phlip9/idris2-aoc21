module AOC.Day1

import Data.List
import Data.String

import System.ReadExt

%default total

parse : List String -> List Integer
parse lines = mapMaybe parseInteger lines

export
windows2 : List a -> List (a, a)
windows2 [] = []
windows2 (x :: []) = []
windows2 (x1 :: (x2 :: xs)) = (x1, x2) :: windows2 (x2 :: xs)

windows3 : List a -> List (a, a, a)
windows3 [] = []
windows3 (x :: []) = []
windows3 (x1 :: (x2 :: [])) = []
windows3 (x1 :: (x2 :: (x3 :: xs))) = (x1, x2, x3) :: windows3 (x2 :: x3 :: xs)

export
dt : List Integer -> List Integer
dt xs = map (\(x, y) => y - x) (windows2 xs)

part1 : List Integer -> Integer
part1 xs = cast $ length $ filter (>0) (dt xs)

part2 : List Integer -> Integer
part2 xs = part1 $ map (\(x, y, z) => x + y + z) (windows3 xs)

-- part1v2 : List Integer -> Integer
-- part1v2 xs = foldl1 (\x, y => y - x) xs

export
day1 : IO ()
day1
  = do Right lines <- readFileWithLimit "data/01"
             | Left err => putStrLn ("Error reading data: " ++ show err)
       let xs = parse lines
       putStrLn ("Part 1: " ++ show (part1 xs))
       -- putStrLn ("Part 1 (v2): " ++ show (part1v2 xs))
       putStrLn ("Part 2: " ++ show (part2 xs))
