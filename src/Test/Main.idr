module Test.Main

import AOC.Day1
import AOC.Day3
import Control.Monad.Identity
import Data.Bits
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
vectGen range gen = do
  len <- nat range
  v <- vect len gen
  pure (len ** v)

propReverse : Property
propReverse = let int20 = int $ linear 0 20 in
                  property $ do (_ ** xs) <- forAll (vectGen (linear 0 10) int20)
                                xs === reverse' (reverse' xs)

interface Arbitrary a where
  any : Gen a

Arbitrary Bits8 where any = bits8 (linear 0 oneBits)
Arbitrary Bits16 where any = bits16 (linear 0 oneBits)
Arbitrary Bits32 where any = bits32 (linear 0 oneBits)
Arbitrary Bits64 where any = bits64 (linear 0 oneBits)

bitsStrGen : Hedgehog.Range Nat -> Gen String
bitsStrGen range = do
  bits <- list range binit
  pure $ pack bits

propShowParseIdemp : NonDegenFinBits a => Property
propShowParseIdemp = property $ do
  bitsStr <- forAll $ bitsStrGen (linear 1 (bitSize {a}))
  Just (padLeft (bitSize {a}) '0' bitsStr) === map (showBits {a}) (parseBits bitsStr)

propParseShowIdemp : NonDegenFinBits a => Arbitrary a => Show a => Eq a => Property
propParseShowIdemp = property $ do
  bs <- forAll $ any {a}
  Just (bs) === (parseBits {a} $ showBits {a} bs)

propPackUnpackIdemp : NonDegenFinBits a => Arbitrary a => Show a => Eq a => Property
propPackUnpackIdemp = property $ do
  bs <- forAll $ any {a}
  bs === (packBits (unpackBits bs))

test1 : Test () -> Property
test1 t = withTests 1 . property $ test t

main : IO ()
main = test [ MkGroup "Tests"
                      [ ("testWindows2", test1 testWindows2)
                      , ("testTakeM", test1 testTakeM)
                      , ("testSplitAtM", test1 testSplitAtM)
                      , ("testDt", test1 testDt)
                      , ("propReverse", propReverse)
                      ]
            , MkGroup "propShowParseIdemp"
                      [ ("Bits8", propShowParseIdemp {a=Bits8})
                      , ("Bits16", propShowParseIdemp {a=Bits16})
                      , ("Bits32", propShowParseIdemp {a=Bits32})
                      , ("Bits64", propShowParseIdemp {a=Bits64})
                      ]
            , MkGroup "propParseShowIdemp"
                      [ ("Bits8", propParseShowIdemp {a=Bits8})
                      , ("Bits16", propParseShowIdemp {a=Bits16})
                      , ("Bits32", propParseShowIdemp {a=Bits32})
                      , ("Bits64", propParseShowIdemp {a=Bits64})
                      ]
            , MkGroup "propPackUnpackIdemp"
                      [ ("Bits8", propPackUnpackIdemp {a=Bits8})
                      , ("Bits16", propPackUnpackIdemp {a=Bits16})
                      , ("Bits32", propPackUnpackIdemp {a=Bits32})
                      , ("Bits64", propPackUnpackIdemp {a=Bits64})
                      ]
            ]
