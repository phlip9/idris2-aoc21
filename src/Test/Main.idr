module Test.Main

import AOC.Day1
import Control.Monad.Identity
import Data.List
import Data.SOP
import Data.String
import Data.Vect
import Hedgehog
import Scratch

ints : List Integer -> List Integer
ints = the (List Integer)

testWindows2 : Test ()
testWindows2 = windows2 (ints [3, 2, 1]) === [(3, 2), (2, 1)]

testTakeM : Test ()
testTakeM = do takeM 2 (ints [1, 2, 3, 4]) === Just [1, 2]
               takeM 4 (ints [1, 2, 3, 4]) === Just [1, 2, 3, 4]
               takeM 5 (ints [1, 2, 3, 4]) === Nothing
               takeM 0 (ints [1, 2, 3, 4]) === Just []

testSplitAtM : Test ()
testSplitAtM = do splitAtM 2 (ints [1, 2, 3, 4]) === Just ([1, 2], [3, 4])
                  splitAtM 4 (ints [1, 2, 3, 4]) === Just ([1, 2, 3, 4], [])
                  splitAtM 5 (ints [1, 2, 3, 4]) === Nothing
                  splitAtM 0 (ints [1, 2, 3, 4]) === Just ([], [1, 2, 3, 4])

testDt : Test ()
testDt = dt [1, 5, 2, 3] === [4, -3, 1]

vectGen : Hedgehog.Range Nat -> Gen a -> Gen (p ** Vect p a)
vectGen range gen = do len <- nat range
                       v <- vect len gen
                       pure (len ** v)

propReverse : Property
propReverse = let int20 = int $ linear 0 20 in
                  property $ do (_ ** xs) <- forAll (vectGen (linear 0 10) int20)
                                xs === reverse' (reverse' xs)

test1 : Test () -> Property
test1 t = withTests 1 . property $ test t

main : IO ()
main = test [MkGroup "Tests"
                      [ ("testWindows2", test1 testWindows2)
                      , ("testTakeM", test1 testTakeM)
                      , ("testSplitAtM", test1 testSplitAtM)
                      , ("testDt", test1 testDt)
                      , ("propReverse", propReverse)
                      ]]
