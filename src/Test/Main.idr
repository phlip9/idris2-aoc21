module Test.Main

import AOC.Day1
import Data.Vect
import System

assertEq : Eq a => Show a => a -> a -> IO ()
assertEq x y = if x == y
               then pure ()
               else do putStrLn """
                         assertion failure: left == right
                           left: \{show x}
                          right: \{show y}
                         """
                       exitFailure

testWindows2 : IO ()
testWindows2 = assertEq (windows2 [1, 2, 3]) [(1, 2), (2, 3)]

testDt : IO ()
testDt = assertEq (dt [1, 5, 2, 3]) [4, -3, 1]

testTakeM : IO ()
testTakeM = do assertEq (takeM 2 [1, 2, 3, 4]) (Just [1, 2])
               assertEq (takeM 4 [1, 2, 3, 4]) (Just [1, 2, 3, 4])
               assertEq (takeM 5 [1, 2, 3, 4]) Nothing
               assertEq (takeM 0 [1, 2, 3, 4]) (Just [])

testSplitAtM : IO ()
testSplitAtM = do assertEq (splitAtM 2 [1, 2, 3, 4]) (Just ([1, 2], [3, 4]))
                  assertEq (splitAtM 4 [1, 2, 3, 4]) (Just ([1, 2, 3, 4], []))
                  assertEq (splitAtM 5 [1, 2, 3, 4]) Nothing
                  assertEq (splitAtM 0 [1, 2, 3, 4]) (Just ([], [1, 2, 3, 4]))

testReverse' : IO ()
testReverse' = do assertEq (reverse' [1, 2, 3]) [3, 2, 1]

main : IO ()
main = do testWindows2
          testDt
          testTakeM
          testSplitAtM
          testReverse'
          putStrLn "ran tests"
