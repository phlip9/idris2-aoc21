module Main

import AOC.Day1
import AOC.Day2
import AOC.Day3
import AOC.Day4
import Bench
import Data.Either
import Data.List
import Data.String
import System

Day : Type
Day = (String -> IO ())

days : List Day
days = [day1, day2, day3, day4]

data Command
  = RunDay Day String
  | Bench

namespace Command
  export
  run : Command -> IO ()
  run (RunDay day filename) = day filename
  run (Bench) = Bench.main

namespace List
  export
  get : Nat -> List a -> Maybe a
  get idx xs with (inBounds idx xs)
    _ | Yes (ok) = Just $ index idx xs {ok}
    _ | No (_) = Nothing

usage : String
usage = """
aoc21 [option ...] subcommand

· aoc21 day day file - run a day
· aoc21 bench - run the benchmarks
"""

parseDay : String -> Maybe Day
parseDay dayIdx = do
  (S dayIdx) <- parsePositive dayIdx
  | 0 => Nothing
  List.get dayIdx days

parseError : String -> Either String a
parseError err = Left $ err ++ "\n\n" ++ usage

parseRunDay : List String -> Either String Command
parseRunDay [dayIdx, input] = do
  day <- maybeToEither "invalid day" (parseDay dayIdx)
  Right $ RunDay day input
parseRunDay _ = parseError "day: invalid number of arguments"

parseBench : List String -> Either String Command
parseBench [] = Right $ Bench
parseBench _ = parseError "bench: invalid number of arguments"

parseCommand : List String -> Either String Command
parseCommand (cmd :: rest) = case cmd of
                                  "day" => parseRunDay rest
                                  "bench" => parseBench rest
                                  _ => parseError "unknown subcommand"
parseCommand [] = parseError "invalid arguments: expected subcommand"

main : IO ()
main = do
  args <- getArgs
  Right cmd <- pure $ parseCommand (drop 1 args)
  | Left err => putStrLn ("error parsing arguments: " ++ err)

  Command.run cmd
