module Scratch

import Control.Monad.Maybe
import Data.List
import Data.List1
import Data.Maybe
import Data.Nat
import Data.String
import Data.Vect
import System.Clock

%default total

public export %inline
U64 : Type
U64 = Bits64

public export %inline
F64 : Type
F64 = Double

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

reverse'' : Vect len a -> Vect len a
reverse'' xs = rewrite sym $ plusZeroRightNeutral len in go xs []
  where go : Vect n a -> Vect m a -> Vect (n + m) a
        go {n=Z}   {m} []        ys = rewrite plusZeroLeftNeutral m in ys
        go {n=S n} {m} (x :: xs) ys = rewrite plusSuccRightSucc n m in go xs (x :: ys)

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

filter''' : (p : a -> Bool) -> List a -> List (x : a ** p x === True)
filter''' p [] = []
filter''' p (x :: xs) with (p x) proof eq 
  _ | True = (x ** eq) :: filter''' p xs
  _ | False = filter''' p xs


filter4 : (p : a -> Bool) -> Vect n a -> (m ** Vect m (x : a ** p x === True))
filter4 p [] = (0 ** [])
filter4 p (x :: xs) with (p x) proof eq 
  _ | True = let (m ** xs') = filter4 p xs in
                 (S m ** ((x ** eq) :: xs'))
  _ | False = filter4 p xs

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

-- plusMinusOne : (k : Nat) -> (k `minus` 1) `plus` 1 = S (k `minus` 1)
-- plusMinusOne k = rewrite plusOneEqSuccRight (k `minus` 1) in Refl

-- export
-- windowsNStep : (n : Nat) -> (xs : Vect ((S n) + m) a) -> (Vect (S n) a, Vect (n + m) a)
-- windowsNStep n xs = let (window, rest) = splitAt (S n) xs
--                         suffix = tail xs in
--                         (window, suffix)

-- inductive step when guaranteed (i.e., we always have room for at least one window)?

-- export
-- windowsNStep : (n : Nat) -> (xs : Vect (n + (S m)) a) -> (Vect n a, Vect (n + m) a)
-- windowsNStep n xs = let (window, rest) = splitAt n xs
--                         suffix = tail (rewrite plusSuccRightSucc n m in xs) in
--                         (window, suffix)


||| (n + m) - n = m
plusMinusCancel : (n : Nat) -> (m : Nat) -> (n + m) `minus` n = m
plusMinusCancel Z     Z = Refl
plusMinusCancel Z     m = rewrite plusZeroLeftNeutral m in
                          rewrite minusZeroRight m in
                                  Refl
plusMinusCancel n     Z = rewrite plusZeroRightNeutral n in
                          rewrite minusZeroN n in
                                  Refl
plusMinusCancel (S k) m = rewrite plusMinusCancel k m in
                                  Refl

||| n <= m ==> n + (m - n) = m
plusMinusLeftLte : (n, m : Nat) -> n `LTE` m -> n + (m `minus` n) = m
plusMinusLeftLte n m ltePrf = rewrite plusCommutative n (m `minus` n) in
                                      plusMinusLte n m ltePrf

||| n <= m ==> n - m = 0
minusLTE : n `LTE` m -> n `minus` m = 0
minusLTE LTEZero = Refl
minusLTE (LTESucc lte) = minusLTE lte

||| n < m ==> n <= m - 1
ltImpliesLTEMinusOne : {m : Nat} -> n `LT` m -> n `LTE` (m `minus` 1)
ltImpliesLTEMinusOne {m=S k} (LTESucc lte) = rewrite minusZeroRight k in lte

||| n < m ==> n - (m - 1) = 0
minusLTMinusOneEqZ : {m : Nat} -> n `LT` m -> n `minus` (m `minus` 1) = 0
minusLTMinusOneEqZ lt = let lte = ltImpliesLTEMinusOne {m=m} lt in 
                            minusLTE lte

||| intermediate proof goal
windows_rw : (j : Nat) -> (k : Nat) -> minus (S j + k) (minus (S j) 1) = S k
windows_rw j k = rewrite plusMinusCancel 1 j in
                 rewrite plusSuccRightSucc j k in
                 rewrite plusMinusCancel j (S k) in
                         Refl

windowsInductiveStep : (n : Nat) -> (xs : Vect (n + m) a) -> (Vect n a, Vect ((n + m) `minus` 1) a)
windowsInductiveStep n xs = let window = take n xs
                                suffix = drop' 1 xs in
                                (window, suffix)

||| non degenerate cases (where n <= length xs)
windowsNonDegen : {m : Nat} -> (n : Nat) -> (xs : Vect (n + m) a) -> Vect ((n + m) `minus` (n `minus` 1)) (Vect n a)
windowsNonDegen {m=Z} Z xs
  = []
windowsNonDegen {m=m} Z xs
  = rewrite plusZeroLeftNeutral m in
    rewrite minusZeroRight m in
            replicate m []
windowsNonDegen {m=Z} (S j) xs
  = rewrite plusZeroRightNeutral (S j) in
    rewrite minusZeroRight j in
    rewrite sym $ minusOneSuccN j in
    rewrite sym $ plusZeroRightNeutral j in
            [xs]
windowsNonDegen {m=S k} (S j) xs
  = let (window, suffix) = windowsInductiveStep (S j) xs -- in
        induction = windowsNonDegen {m=k} (S j) (rewrite (plusSuccRightSucc j k) in
                                                 rewrite (sym $ minusZeroRight (j + (S k))) in suffix) in
        -- WTB lean simp tactic :<
        (rewrite (minusZeroRight j) in
         rewrite (plusSuccRightSucc j (S k)) in
         rewrite (plusMinusCancel j (S (S k))) in
         rewrite (sym $ windows_rw j k) in
                 (window :: induction))

export
windows : {m : Nat} -> (n : Nat) -> (xs : Vect m a) -> Vect (m `minus` (n `minus` 1)) (Vect n a)
windows n xs with (isLTE n m)
  _ | Yes (lte) = let xs = (rewrite plusMinusLeftLte n m lte in xs)
                      out = windowsNonDegen {m=m `minus` n} n xs
                      out = (rewrite (sym $ plusMinusLeftLte n m lte) in out) in
                      out
  _ | No (notLTE) = let lt = notLTEImpliesGT notLTE in
                        (rewrite minusLTMinusOneEqZ lt in [])

export
windowsL : (n : Nat) -> (xs : List a) -> List (Vect n a)
windowsL n xs = toList $ windows n (fromList xs)

-- data MaybeT' : (m : Type -> Type) -> (a : Type) -> Type where
--   MkMaybeT' : m (Maybe a) -> MaybeT' m a
-- 
-- runMaybeT' : MaybeT' m a -> m (Maybe a)
-- runMaybeT' (MkMaybeT' x) = x
-- 
-- isNothingT' : Functor m => MaybeT' m a -> m (Bool)
-- isNothingT' = map isNothing . runMaybeT'
-- 
-- isJustT' : Functor m => MaybeT' m a -> m (Bool)
-- isJustT' = map isJust . runMaybeT'
-- 
-- maybeT' : Monad m => m b -> (a -> m b) -> MaybeT' m a -> m b
-- maybeT' v g x = (runMaybeT' x) >>= (maybe v g)

-- v : m b
-- g : a -> m b
-- x : MaybeT' m a
-- maybe : Lazy (m b) -> Lazy (a -> m b) -> Maybe a -> b
-- maybe v g : Maybe a -> m b
-- runMaybeT' x : m (Maybe a)
-- (>>=) : m a -> (a -> m b) -> m b
-- (>>=) (runMaybeT' x) : (Maybe a -> m b) -> m b

-- readUser : MaybeT IO String
-- readUser = do
--   putStrLn "Enter username: "
--   str <- getLine
--   if length str > 5
--      then just str
--      else nothing
-- 
-- readPass : MaybeT IO String
-- readPass = do
--   putStrLn "Enter password: "
--   str <- getLine
--   if length str <= 5
--      then just str
--      else nothing
-- 
-- login : IO ()
-- login = do
--   maybeCreds <- runMaybeT $ do
--     user <- readUser
--     pass <- readPass
--     pure (user, pass)
--   case maybeCreds of 
--        Nothing => putStrLn "Bad credentials!"
--        Just (user, _) => putStrLn ("Logged in as " ++ user)

-- [0..end] inclusive
export
rangeTo : Range a => Neg a => Eq a => (end : a) -> List1 a
rangeTo end = if end == 0
                then List1.singleton 0
                else (end ::: [0..end - 1])

export
toNanos : Clock type -> Integer
toNanos (MkClock seconds nanoseconds) =
  let scale = 1000000000
   in scale * seconds + nanoseconds

export
fromNanos : Cast a Integer => (ns : a) -> Clock Duration
fromNanos ns =
  let scale = 1000000000
      seconds = (cast ns) `div` scale
      nanoseconds = (cast ns) `mod` scale
   in MkClock seconds nanoseconds

export
fmtDuration : Clock Duration -> String
fmtDuration dur
  = let (s, ns) = (seconds dur, nanoseconds dur) in
        if      ns == 0       then show s ++ " s"
        else if s > 0         then showD ((cast s) + ((cast ns) * 1.0e-9)) ++ " s"
        else if ns >= 1000000 then showD ((cast ns) * 1.0e-6) ++ " ms"
        else if ns >= 1000    then showD ((cast ns) * 1.0e-3) ++ " µs"
        else                       show ns ++ " ns"
  where
    trimDecimal : Nat -> String -> String
    trimDecimal prec dec
      = let (prefix_, suffix) = span (/= '.') dec in
            prefix_ ++ substr 0 (prec + 1) suffix
    showD : Double -> String
    showD = trimDecimal 2 . show

export
timeit : String -> Lazy (IO a) -> IO a
timeit label thunk
  = do start <- clockTime Monotonic
       val <- force thunk
       now <- clockTime Monotonic
       dt <- pure (timeDifference now start)
       putStrLn (label ++ ": time: " ++ fmtDuration dt)
       pure val

export
part : Show a => String -> Lazy a -> IO ()
part label thunk = do out <- timeit label $ delay (pure (force thunk))
                      putStrLn (label ++ ":  out: " ++ show out ++ "\n")

-- Vect' : (n : Nat) -> a -> (p ** (p, List a))

-- data Vect = (Nat, List a)

-- namespace Vect'
--   data View : Nat -> List a -> Type where
--     Nil : View Z []
--     (::) : (x : a) -> (xs : View n xs_) -> View (S n) (x :: xs_)
-- 
--   view : List a 

public export
data LenListT : (len : Nat) -> (a : Type) -> Type where
  LenList : (len : Nat) -> (xs : List a) -> LenListT len a

-- data LenListT Nat a = LenList (List a)
-- data LenList : a -> (len : Nat) -> (xs : List a) -> Type
-- LenList : a -> (Nat, List a)

namespace LenListT
  public export
  Nil : LenListT 0 a
  Nil = LenList 0 []

  public export
  (::) : (x : a) -> LenListT n a -> LenListT (S n) a
  (::) x (LenList n xs) = LenList (S n) (x :: xs)

  public export
  toList : LenListT len a -> List a
  toList (LenList len xs) = xs

  public export
  length : LenListT len a -> Nat
  length (LenList len _) = len

public export
data VLenListT : (len : Nat) -> (a : Type) -> Type where
  -- VLenList : (ll : LenListT len a) -> (prf : List.length (toList ll) = length ll) -> VLenListT len a
  VLenList : (ll : LenListT len a) -> {0 prf : List.length (toList ll) = length ll} -> VLenListT len a

namespace VLenListT
  public export
  Nil : VLenListT 0 a
  Nil = VLenList (LenList 0 []) {prf=Refl}

  public export
  (::) : (x : a) -> VLenListT n a -> VLenListT (S n) a
  (::) x (VLenList (LenList n xs) {prf=prf}) = VLenList (LenList (S n) (x :: xs)) {prf=cong S prf}

-- public export
-- VLenList : (ll : LenListT len a) -> (List.) -> VLenListT len a

-- export
-- data VLenListT a = VLenList (LenListT a ** ?help)

-- data Vect'' = ((Nat, List a) ** (\(len, xs) => List.length xs = len))

public export
record Vect' (len : Nat) (a : Type) where
  constructor MkVect'
  list : List a
  {0 prf : List.length list = len}

namespace Vect'
  public export
  Nil : Vect' 0 a
  Nil = MkVect' [] {prf=Refl}

  public export
  (::) : (x : a) -> Vect' n a -> Vect' (S n) a
  (::) x vect = { list := (x :: vect.list)
                , prf := cong S vect.prf
                } vect

  export
  toList : Vect' _ a -> List a
  toList vect = vect.list

  export
  fromList : (xs : List a) -> Vect' (List.length xs) a
  fromList xs with (List.length xs) proof prf
    _ | len = MkVect' xs {prf}

  export
  length : {n : Nat} -> Vect' n a -> Nat
  length _ = n

export
testVect' : Vect' 3 Integer
testVect' = [1, 2, 3]

-- failVect' : Vect' Integer
-- failVect' = MkVect' 5 [1,2,3] Refl

infixl 1 |>

||| pipeline operator
public export
(|>) : a -> (f : (a -> b)) -> b
(|>) x f = f x
