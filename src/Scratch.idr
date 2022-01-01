module Scratch

import Control.Monad.Maybe
import Data.List
import Data.Maybe
import Data.Nat
import Data.String
import Data.Vect
import System.Clock

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


windowsN_rw : (j : Nat) -> (k : Nat) -> minus (S j + k) (minus (S j) 1) = S k
windowsN_rw j k = rewrite plusMinusCancel 1 j in
                  rewrite plusSuccRightSucc j k in
                  rewrite plusMinusCancel j (S k) in
                          Refl

export
windowsNStep : (n : Nat) -> (xs : Vect (n + m) a) -> (Vect n a, Vect ((n + m) `minus` 1) a)
windowsNStep n xs = let window = take n xs
                        suffix = drop' 1 xs in
                        (window, suffix)

export
windowsN : {m : Nat} -> (n : Nat) -> (xs : Vect (n + m) a) -> Vect ((n + m) `minus` (n `minus` 1)) (Vect n a)
windowsN {m=Z} Z xs
  = []
windowsN {m=m} Z xs
  = rewrite plusZeroLeftNeutral m in
    rewrite minusZeroRight m in
            replicate m []
windowsN {m=Z} (S j) xs
  = rewrite plusZeroRightNeutral (S j) in
    rewrite minusZeroRight j in
    rewrite sym $ minusOneSuccN j in
    rewrite sym $ plusZeroRightNeutral j in
            [xs]
windowsN {m=S k} (S j) xs
  = let (window, suffix) = windowsNStep (S j) xs -- in
        induction = windowsN {m=k} (S j) (rewrite (plusSuccRightSucc j k) in
                                          rewrite (sym $ minusZeroRight (j + (S k))) in suffix) in
        -- WTB lean simp tactic :<
        (rewrite (minusZeroRight j) in
         rewrite (plusSuccRightSucc j (S k)) in
         rewrite (plusMinusCancel j (S (S k))) in
         rewrite (sym $ windowsN_rw j k) in
                 (window :: induction))

-- windowsN n Z xs = rewrite plusZeroRightNeutral n in
--                   rewrite _ in [xs]
-- windowsN n (S k) xs = ?help2

-- windowsN : (n : Nat) -> (m : Nat) -> (xs : Vect (n + (S m)) a) -> Vect (n + (S m)) (Vect n a)
-- windowsN n Z xs = ?help
-- windowsN n (S k) xs = ?help2

-- minusSuccOfMinus : (n : Nat) -> (m : Nat) -> S (n `minus` m) = (S n) `minus` m
-- minusSuccOfMinus Z Z = Refl
-- minusSuccOfMinus Z m = Refl
-- minusSuccOfMinus _ _ = ?help3

-- minusSuccOfMinusSucc : (n : Nat) -> (m : Nat) -> S (n `minus` (S m)) = n `minus` m
-- minusSuccOfMinusSucc Z Z = Refl
-- minusSuccOfMinusSucc n m = ?help2

-- windowsN : (n : Nat) -> (m : Nat) -> (xs : Vect ((S n) + m) a) -> Vect (S (m `minus` (S n))) (Vect (S n) a)
-- windowsN : (n : Nat) -> (m : Nat) -> (xs : Vect ((S n) + m) a) -> Vect (m `minus` n) (Vect (S n) a)
-- windowsN n Z xs = [] -- rewrite sym $ plusZeroRightNeutral n in [xs]
-- windowsN n (S k) xs with (cmp n k)
--   windowsN n (S k) xs | CmpLT _ = ?help1
--   windowsN n (S k) xs | CmpEQ = ?help2
--   windowsN n (S k) xs | CmpGT _ = ?help3
-- windowsN n (S k) xs = ?help2
-- windowsN n (S k) xs = let (window, suffix) = windowsNStep n xs in ?help
-- windowsN n (S k) xs = let (window, suffix) = windowsNStep n xs
                          -- induction = windowsN n k suffix in
                          -- induction = windowsN n k (rewrite (plusSuccRightSucc n k) in suffix) in 
                          -- ?help
                          -- (window :: induction)
                          -- suffix = (rewrite sym $ plusSuccRightSucc n k in suffix)
                            -- let induction = windowsN n k suffix in
                          -- rewrite plusSuccRightSucc n k in
                                  -- ?help


-- windowsN : (n : Nat) -> (m : Nat) -> (xs : Vect ((S n) + m) a) -> Vect (S ((S m) `minus` n)) (Vect (S n) a)
-- windowsN n m xs with ()


-- length xs = S (n `plus` m)
-- S (minus m (S n)) = 1 + (m - (1 + n))


-- windowsNStep : (n : Nat) -> (xs : Vect (n + m) a) -> (Vect n a, Vect ((n + m) `minus` 1) a)
-- windowsNStep n xs = let (window, rest) = splitAt n xs
--                         suffix = drop' 1 xs in -- ?help
--                         (window, suffix)
                        -- rewrite plusMinusOne (n `plus` m) in ?help -- (window, suffix)

                        -- plus n m 
                        -- S (minus (plus n m) 1)
                        -- let k = plus n m
                        -- S (minus k 1) = plus (minus k 1) 1

                        -- case k = 0 => plus (minus 0 1) 1 = plus 0 1 = S 0 = S (minus 0 1)
                        -- case k = 1 => plus (minus 1 1) 1 = plus 0 1 = S 0 = S (minus 1 1)
                        -- case k = 2 => plus (minus 2 1) 1 = plus 1 1 = S 1 = S (minus 2 1)
                        -- ...

-- windowsN' : (n : Nat) -> (m : Nat) -> Vect (n + m) a -> List (Vect n a)
-- windowsN' Z _ _ = []
-- windowsN' _ Z _ = []
-- windowsN' n m xs = let (window, rest) = splitAt n xs in

-- windowsN' n xs = let (window, rest) = splitAt n xs in
--                      window :: ?test -- windowsN n ((drop 1 window) :: rest)


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

readUser : MaybeT IO String
readUser = do
  putStrLn "Enter username: "
  str <- getLine
  if length str > 5
     then just str
     else nothing

readPass : MaybeT IO String
readPass = do
  putStrLn "Enter password: "
  str <- getLine
  if length str <= 5
     then just str
     else nothing

login : IO ()
login = do
  maybeCreds <- runMaybeT $ do
    user <- readUser
    pass <- readPass
    pure (user, pass)
  case maybeCreds of 
       Nothing => putStrLn "Bad credentials!"
       Just (user, _) => putStrLn ("Logged in as " ++ user)

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
