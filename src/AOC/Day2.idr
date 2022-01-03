module AOC.Day2

import Data.List
import Data.String
import Scratch
import System.ReadExt

%default total

data Heading
  = Forward
  | Down
  | Up

Show Heading where
  show Forward = "forward"
  show Down = "down"
  show Up = "up"

parseHeading : String -> Maybe Heading
parseHeading "forward" = Just Forward
parseHeading "down" = Just Down
parseHeading "up" = Just Up
parseHeading _ = Nothing

record Command where
  constructor MkCommand
  heading : Heading
  units : Integer

Show Command where
  show cmd = "\{show cmd.heading} \{show cmd.units}"

parseCommand : String -> Maybe Command
parseCommand s = do
  let (heading, units) = break (== ' ') s
  heading <- parseHeading heading
  units <- parsePositive units
  Just $ MkCommand heading units

parseCommands : List String -> List Command
parseCommands lines = mapMaybe parseCommand lines

part1 : List Command -> Integer
part1 cmds = let (horiz, depth) = foldl go (0, 0) cmds in
                 horiz * depth
  where
    go : (Integer, Integer) -> Command -> (Integer, Integer)
    go (horiz, depth) cmd = case cmd.heading of
                                 Forward => (horiz + cmd.units, depth)
                                 Down => (horiz, depth + cmd.units)
                                 Up => (horiz, depth - cmd.units)

part2 : List Command -> Integer
part2 cmds = let (horiz, depth, _) = foldl go (0, 0, 0) cmds in
                 horiz * depth
  where
    go : (Integer, Integer, Integer) -> Command -> (Integer, Integer, Integer)
    go (horiz, depth, aim) cmd = case cmd.heading of
                                      Forward => (horiz + cmd.units, depth + (cmd.units * aim), aim)
                                      Down => (horiz, depth, aim + cmd.units)
                                      Up => (horiz, depth, aim - cmd.units)

export
day2 : String -> IO ()
day2 inputFilename = do
  Right lines <- readFileWithLimit inputFilename
  | Left err => putStrLn ("Error reading data: " ++ show err)

  -- putStrLn "===="
  -- putStrLn $ fastUnlines $ map show $ parseCommands lines
  -- putStrLn "===="
  
  let cmds = parseCommands lines

  part "Part 1" $ part1 cmds
  part "Part 2" $ part2 cmds
