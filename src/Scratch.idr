module Scratch

import Data.List
import Data.Nat
import Data.Vect

%default total

plusOneEqSuccLeft : (right : Nat) -> 1 + right = S right
plusOneEqSuccLeft _ = Refl

plusOneEqSuccRight : (left : Nat) -> left + 1 = S left
plusOneEqSuccRight Z = Refl
plusOneEqSuccRight (S k) = cong S (plusOneEqSuccRight k)

-- snoc_ext : (xs : Vect n a) -> n = m -> Vect.length xs = m
-- snoc_ext xs prf = rewrite lengthCorrect xs in prf

snoc' : Vect n a -> a -> Vect (S n) a
snoc' [] v = [v]
snoc' xs  v = rewrite sym (plusOneEqSuccRight n) in (xs ++ [v])

export
reverse' : Vect n a -> Vect n a
reverse' [] = []
reverse' (x :: xs) = snoc' (reverse' xs) x

filter' : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter' pred []         = (0 ** [])
filter' pred (x :: xs)  = let (q ** xs') = filter' pred xs in
                              if pred x
                              then (S q ** x :: xs')
                              else (q ** xs')

filter'' : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter'' pred [] = (0 ** [])
filter'' pred (x :: xs) with (filter'' pred xs)
  filter'' pred (x :: xs) | (q ** xs') = if (pred x) then (S q ** x :: xs') else (q ** xs')

data Parity : Nat -> Type where
  Even : {n : _} -> Parity (n + n)
  Odd  : {n : _} -> Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S k) = case parity k of
                    Even => Odd
                    Odd {n = j} => rewrite plusSuccRightSucc j j in
                                           Even {n = S j}
-- parity : (n : Nat) -> Parity n
-- parity Z = Even {n = Z}
-- parity (S Z) = Odd {n = Z}
-- parity (S (S k)) with (parity k)
--   parity (S (S (j + j)))     | Even = rewrite plusSuccRightSucc j j in Even {n = S j}
--   parity (S (S (S (j + j)))) | Odd = rewrite plusSuccRightSucc j j in Odd {n = S j}



-- windowsN' n xs = let (window, rest) = splitAt n xs in
--                      window :: ?test -- windowsN n ((drop 1 window) :: rest)

-- takeM' : Nat -> Maybe (List a) -> List a -> Maybe (List a)
-- takeM' _ Nothing _ = Nothing
-- takeM' 0 (Just acc) _ = Just acc
-- takeM' (S n) _ [] = Nothing
-- takeM' (S n) (Just acc) (x :: xs) = takeM' n (Just (x :: acc)) xs

splitAtM' : Nat -> Maybe (List a) -> List a -> Maybe ((List a, List a))
splitAtM' _     Nothing     _           = Nothing
splitAtM' 0     (Just acc)  xs          = Just (acc, xs)
splitAtM' (S n) _           []          = Nothing
splitAtM' (S n) (Just acc)  (x :: xs)   = splitAtM' n (Just (x :: acc)) xs

export
splitAtM : Nat -> List a -> Maybe ((List a, List a))
splitAtM n xs = map (mapFst List.reverse) (splitAtM' n (Just []) xs)

export
takeM : Nat -> List a -> Maybe (List a)
takeM n xs = map fst (splitAtM n xs)

-- windowsN : (n : Nat) -> List a -> List (List a)
-- windowsN n xs = case splitAtM n xs of
--                      Nothing => []
--                      -- Just ([], _) => []
--                      Just (window, rest) => (windowsN n rest)

-- windowsN : (n : Nat) -> Vect m a -> List (Vect n a)
-- windowsN n xs = if n > length xs
--                 then []
--                 else windowsN' n xs

-- windowsN' : (n : Nat) -> (m : Nat) -> Vect (n + m) a -> List (Vect n a)
-- windowsN' Z _ _ = []
-- windowsN' _ Z _ = []
-- windowsN' n m xs = let (window, rest) = splitAt n xs in
