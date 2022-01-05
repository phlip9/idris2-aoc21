module AOC.Day4

import Scratch
import System.ReadExt

%default total

export
day4 : String -> IO ()
day4 inputFilename = do
  (Right lines) <- readFileWithLimit inputFilename
  | Left err => putStrLn ("Error reading data: " ++ show err)

  pure ()

  -- let xs = parse lines
  -- 
  -- part "Part 1" $ part1 xs
  -- part "Part 2" $ part2 xs
