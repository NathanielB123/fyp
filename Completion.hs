{-# OPTIONS -Wall #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}


-- Attempts at implementing ground completion (will be used for dealing with
-- neutral equations)
-- Includes a naive rewriting-based approach and a WIP E-graph impl

import Prelude hiding (lookup)
import Data.Maybe (maybeToList, mapMaybe)
import Test.QuickCheck
  (Gen, Arbitrary (arbitrary), Property, quickCheck, verbose, discardAfter)
import Control.Monad.State (State, MonadState (..), gets, execState)
import Data.IntMap (IntMap, insert, partition, toList, (!))

data Tm = Var Int | App Tm Tm
  deriving (Eq, Show)

spLen :: Tm -> Int
spLen (Var _)   = 0
spLen (App _ t) = 1 + spLen t

instance Ord Tm where
  compare :: Tm -> Tm -> Ordering
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

justEq :: Eq a => Maybe a -> Maybe a -> Bool
justEq (Just x) (Just y) = x == y
justEq _        _        = False

invSing :: IntMap a -> Maybe (Int, a)
invSing m = case toList m of
  [x] -> Just x
  _   -> Nothing

findInMap :: (a -> Bool) -> IntMap a -> Maybe (Int, a)
findInMap p m = invSing m'
  where (m', _) = partition p m

-- Rewriting to completion

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

type EqClass = ([Tm], [Int])

mkRw :: Tm -> Tm -> Maybe Rw
mkRw t u
  | t < u     = pure (u :-> t)
  | u < t     = pure (t :-> u)
  | otherwise = Nothing

rwRw :: [Rw] -> Rw -> Maybe Rw
rwRw rws (l :-> r) = mkRw (rwFix rws l) (rwFix rws r)

rwWrtRws :: [Rw] -> [Rw] -> [Rw]
rwWrtRws acc []         = acc
rwWrtRws acc (lr : lrs) = rwWrtRws (acc ++ maybeToList rw') lrs
  where rw' = rwRw (acc ++ lrs) lr

rwRwsFix :: [Rw] -> [Rw]
rwRwsFix = iterFix (rwWrtRws [])

buildRws :: [TmEq] -> [Rw]
buildRws eqs = rwRwsFix (mapMaybe (\(t := u) -> mkRw t u) eqs)

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

-- E-Graphs

data EClass = Cls {
  vars :: [Int],
  apps :: [(Int, Int)]
} | Ptr Int
  deriving (Show)

data EGraph = Graph {
  classes :: IntMap EClass,
  size    :: Int
}
  deriving (Show)

-- Pre-condition: 'f' should not create new EClass entries
modifyClasses :: (IntMap EClass -> IntMap EClass) -> State EGraph ()
modifyClasses f = do
  Graph cs s <- get
  put (Graph (f cs) s)

chase :: Int -> EClass -> IntMap EClass -> (Int, [Int], [(Int, Int)])
chase _ (Ptr j)     cs = chase j (cs ! j) cs
chase i (Cls vs as) _  = (i, vs, as)

findCls :: ([Int] -> [(Int, Int)] -> Bool) -> IntMap EClass 
        -> Maybe (Int, EClass)
findCls p = findInMap \case Cls vs as -> p vs as
                            Ptr _     -> False

addCls :: EClass -> State EGraph Int
addCls c = do
  Graph cs s <- get
  put (Graph (insert s c cs) (s + 1))
  pure s

chaseEq :: Int -> Int -> IntMap EClass -> Bool
chaseEq i j cs = i' == j'
  where (i', _, _) = chase i (cs ! i) cs
        (j', _, _) = chase j (cs ! j) cs

lookupEVar :: Int -> IntMap EClass -> Maybe (Int, EClass)
lookupEVar i = findCls (\vs _ -> i `elem` vs)

lookupEApp :: Int -> Int -> IntMap EClass -> Maybe (Int, EClass)
lookupEApp i j cs 
  = findCls (\_ as -> any (\(k, l) -> chaseEq i k cs && chaseEq j l cs) as) cs

lookupETm :: Tm -> IntMap EClass -> Maybe (Int, EClass)
lookupETm (Var i)   cs = lookupEVar i cs
lookupETm (App t u) cs = do
  (i, _) <- lookupETm t cs
  (j, _) <- lookupETm u cs
  lookupEApp i j cs

singClass :: Tm -> State EGraph EClass
singClass (Var i)   = pure (Cls [i] [])
singClass (App t u) = do
  (i, _) <- addTm t
  (j, _) <- addTm u
  pure (Cls [] [(i, j)])

addTm :: Tm -> State EGraph (Int, EClass)
addTm t = do
  g <- gets classes
  case lookupETm t g of
    Just e -> pure e
    Nothing -> do
      c <- singClass t
      (, c) <$> addCls c

mergeECls :: Int -> Int -> EClass -> EClass -> State EGraph ()
mergeECls i j c1 c2
  = modifyClasses \cs -> let (i', vs1, as1) = chase i c1 cs
                             (j', vs2, as2) = chase j c2 cs
                          in insert j' (Ptr i')
                           $ insert i' (Cls (vs1 <> vs2) (as1 <> as2)) cs

addEq :: TmEq -> State EGraph ()
addEq (t := u) = do
  (i, c1) <- addTm t
  (j, c2) <- addTm u
  cs <- gets classes
  if chaseEq i j cs
    then pure ()
    else mergeECls i j c1 c2

buildEGraph :: [TmEq] -> EGraph
buildEGraph = foldr (execState . addEq) (Graph mempty 0)

checkEGraphEqRec :: Tm -> Tm -> EGraph -> Bool
checkEGraphEqRec (App t1 t2) (App u1 u2) g 
  = checkEGraphEq t1 u1 g && checkEGraphEq t2 u2 g
checkEGraphEqRec (Var i)     (Var j)     _ = i == j
checkEGraphEqRec _           _           _ = False

checkEGraphEq :: Tm -> Tm -> EGraph -> Bool
checkEGraphEq t u g@(Graph cs _)
  =  checkEGraphEqRec t u g 
  || justEq (fst <$> lookupETm t cs) (fst <$> lookupETm u cs)


cmpStrats2 :: [TmEq] -> Tm -> Tm -> Bool
cmpStrats2 eqs t u = checkEGraphEq t u g == checkRwEq rws t u
  where g   = buildEGraph eqs
        rws = buildRws eqs

cmpStratsSafe2 :: [TmEq] -> Tm -> Tm -> Property
cmpStratsSafe2 eqs t u = discardAfter 500000 (cmpStrats2 eqs t u)

fuzz2 :: IO ()
fuzz2 = quickCheck cmpStratsSafe2

fuzzVerbose2 :: IO ()
fuzzVerbose2 = quickCheck (verbose cmpStratsSafe2)

-- Counter-examples
{-
[Var 3 := Var 1,Var 1 := Var 0,App (Var 0) (Var 3) := Var 0,App (App (Var 3) (App (Var 1) (Var 1))) (Var 0) := App (Var 1) (Var 1)]
Var 0
App (Var 1) (Var 3)
-}