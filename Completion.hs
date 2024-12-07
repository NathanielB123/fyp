{-# OPTIONS -Wall #-}
{-# LANGUAGE BlockArguments #-}


-- Attempts at implementing ground completion (will be used for dealing with
-- neutral equations)
-- Ordering rewrites based on lexicographic order appears to *just work*
-- Equivalence classes of terms *feels* nicer, but my implementation currently
-- gets stuck in loops a lot.

import Prelude hiding (lookup)
import Data.List (findIndex, nub)
import Data.Maybe (maybeToList, mapMaybe)
import Test.QuickCheck 
  (Gen, Arbitrary (arbitrary), within, Property, quickCheck, verbose)

data Tm = Var Int | App Tm Tm
  deriving (Eq, Show)

spLen :: Tm -> Int
spLen (Var _)   = 0
spLen (App _ t) = 1 + spLen t

instance Ord Tm where
  compare t u = case compare (spLen t) (spLen u) of
    LT -> LT
    GT -> GT
    EQ -> case (t, u) of
      (Var i, Var j) -> compare i j
      (App t1 t2, App u1 u2) -> case compare t1 u1 of
        LT -> LT
        GT -> GT
        EQ -> compare t2 u2
      _ -> error "Impossible"
    

type EqClass = ([Tm], [Int])

varMember :: Int -> EqClass -> Bool
varMember i (_, js) = i `elem` js

-- TODO: Is the lexicographic comparison here sound?
member :: [EqClass] -> Tm -> EqClass -> Bool
member eqs t (us, _) = any (\u -> t > u && checkEqDesc eqs t u) us

lookupVar :: [EqClass] -> Int -> Maybe Int
lookupVar eqs i = findIndex (varMember i) eqs

lookup :: [EqClass] -> Tm -> Maybe Int
lookup eqs (Var i) = lookupVar eqs i
lookup eqs t       = findIndex (member eqs t) eqs

justEq :: Eq a => Maybe a -> Maybe a -> Bool
justEq (Just x) (Just y) = x == y
justEq _        _        = False

checkEqDesc :: [EqClass] -> Tm -> Tm -> Bool
checkEqDesc eqs (Var i) (Var j)
  = i == j || justEq (lookupVar eqs i) (lookupVar eqs j)
checkEqDesc eqs (App t1 t2) (App u1 u2)
  = checkEq eqs t1 u1 && checkEq eqs t2 u2
checkEqDesc _ _ _ = False

checkEq :: [EqClass] -> Tm -> Tm -> Bool
checkEq eqs t u = checkEqDesc eqs t u || justEq (lookup eqs t) (lookup eqs u)

data Rw = Tm :-> Tm
  deriving (Show, Eq)

rwDesc :: Rw -> Tm -> Tm
rwDesc lr (App t u) = App (rw lr t) (rw lr u)
rwDesc _  (Var i)   = Var i

rw :: Rw -> Tm -> Tm
rw (l :-> r) t
  | l == t = r
  | otherwise = rwDesc (l :-> r) t


rwAll :: [Rw] -> Tm -> Tm
rwAll lrs t = foldr rw t lrs

iterFix :: Eq a => (a -> a) -> a -> a
iterFix f x = let x' = f x in if x == x' then x else iterFix f x'

rwFix :: [Rw] -> Tm -> Tm
rwFix lrs = iterFix (rwAll lrs)

checkRwEq :: [Rw] -> Tm -> Tm -> Bool
checkRwEq lrs t u = rwFix lrs t == rwFix lrs u

data TmEq = Tm := Tm
  deriving (Show)

merge :: EqClass -> EqClass -> EqClass
merge (ts, is) (us, js) = (ts ++ us, is ++ js)

insert :: Tm -> EqClass -> EqClass
insert (Var i) (ts, is) = (ts, i : is)
insert t       (ts, is) = (t : ts, is)

buildEqs :: [TmEq] -> [EqClass]
buildEqs (t := u : eqs) = case (i, j) of
  (Just i', Just j') -> if i' == j'
                        then built
                        else merge (built !! i') (built !! j') : built'
  (Just i', Nothing) -> insert u (built !! i') : built'
  (Nothing, Just j') -> insert t (built !! j') : built'
  (Nothing, Nothing) -> insert t (insert u mempty) : built
  where built = buildEqs eqs
        i = lookup built t
        j = lookup built u
        ij = maybeToList i ++ maybeToList j
        built' = fmap fst (filter (not . (`elem` ij) . snd) (zip built [0..]))
buildEqs [] = []

mkRw :: Tm -> Tm -> Maybe Rw
mkRw t u
  | t < u     = pure (u :-> t)
  | u < t     = pure (t :-> u)
  | otherwise = Nothing

rwRw :: [Rw] -> Rw -> Maybe Rw
rwRw rws (l :-> r) = mkRw (rwFix rws l) (rwFix rws r)

-- TODO: Can we add rw' to the accumulator and make this tail-recursive?
rwWrtRws :: [Rw] -> [Rw] -> [Rw]
rwWrtRws _   []         = []
rwWrtRws acc (lr : lrs) = maybeToList rw' ++ rwWrtRws (lr : acc) lrs
  where rw' = rwRw (acc ++ lrs) lr

rwRwsFix :: [Rw] -> [Rw]
rwRwsFix = iterFix (nub . rwWrtRws [])

buildRws :: [TmEq] -> [Rw]
buildRws eqs = rwRwsFix (nub (mapMaybe (\(t := u) -> mkRw t u) eqs))

genVar :: Gen Int
genVar = do
  (b2, b1) <- arbitrary @(Bool, Bool)
  pure (2 * fromEnum b2 + fromEnum b1)

instance Arbitrary Tm where
  arbitrary = do
    b <- arbitrary @Bool
    if b
    then do Var <$> genVar
    else do t <- arbitrary @Tm
            u <- arbitrary @Tm
            pure (App t u)

instance Arbitrary TmEq where
  arbitrary = do
    (t, u) <- arbitrary @(Tm, Tm)
    pure (t := u)

cmpStrats :: [TmEq] -> Tm -> Tm -> Bool
cmpStrats eqs t u = checkEq cls t u == checkRwEq rws t u
  where cls = buildEqs eqs
        rws = buildRws eqs

cmpStratsSafe :: [TmEq] -> Tm -> Tm -> Property
cmpStratsSafe eqs t u = within 50000 (cmpStrats eqs t u)

fuzz :: IO ()
fuzz = quickCheck cmpStratsSafe

fuzzVerbose :: IO ()
fuzzVerbose = quickCheck (verbose cmpStratsSafe)

{-
Example Failure Cases:]

[Var 1 := Var 2,App (App (Var 3) (App (Var 3) (Var 1))) (Var 1) := Var 3]
App (App (Var 1) (App (Var 3) (App (App (Var 1) (Var 3)) (Var 1)))) (Var 2)
Var 1
-}