module Main

import AOC.Day1
import AOC.Day2
import AOC.Day3
import Data.Either
import Data.List
import Data.String
import System

Day : Type
Day = (String -> IO ())

days : List Day
days = [day1, day2, day3]

record Args where
  constructor MkArgs
  day : Day
  inputFilename : String

namespace List
  export
  get : Nat -> List a -> Maybe a
  get idx xs with (inBounds idx xs)
    _ | Yes (ok) = Just $ index idx xs {ok}
    _ | No (_) = Nothing

usage : String
usage = """
aoc21 [option ...] day input
"""

parseDay : String -> Maybe Day
parseDay dayIdx = do
  (S dayIdx) <- parsePositive dayIdx
  | 0 => Nothing
  List.get dayIdx days

parseArgs : List String -> Either String Args
parseArgs [dayIdx, input] = do
  day <- maybeToEither "invalid day" (parseDay dayIdx)
  Right $ MkArgs day input
parseArgs _ = Left $ "invalid number of arguments" ++ "\n\n" ++ usage

main : IO ()
main = do
  args <- getArgs
  Right args <- pure $ parseArgs (drop 1 args)
  | Left err => putStrLn ("error parsing arguments: " ++ err)
  args.day args.inputFilename
