{-# OPTIONS -Wall #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

-- Attempts at implementing ground completion (will be used for dealing with
-- neutral equations)

-- Includes a naive rewriting-based approach and e-graph implementation

-- The e-graph is current extremely slow, but I'm currently not bothering 
-- trying to keep the union-find balanced, or even doing hash-consing, so I
-- expect it could get a LOT faster.

import Prelude hiding (lookup)
import Data.Maybe (maybeToList, mapMaybe, isJust)
import Test.QuickCheck
  (Gen, Arbitrary (arbitrary), Property, quickCheck, verbose, discardAfter)
import Control.Monad.State (State, MonadState (..), gets, execState)
import Data.IntMap (IntMap, insert, partition, toList, (!))
import Data.Foldable (traverse_)
import Data.Kind (Type)
import Data.Containers.ListUtils (nubOrd)
import Data.Functor (($>))
import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad (unless)

-- Utilities

type Reader = (->)

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

maybeM :: Monad m => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM y f x = x >>= maybe y f

boolToMaybe :: Bool -> a -> Maybe a
boolToMaybe True  = Just
boolToMaybe False = const Nothing

whenNothing :: Applicative f => Maybe a -> f (Maybe a) -> f (Maybe a)
whenNothing (Just x) _ = pure (Just x)
whenNothing Nothing  f = f

findJustM :: (Foldable f, Monad m) => (a -> m (Maybe b)) -> f a -> m (Maybe b)
findJustM f = foldr (\x -> (>>= flip whenNothing (f x)))
                    (pure Nothing)

findM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m (Maybe a)
findM f = findJustM (\x -> flip boolToMaybe x <$> f x)

anyM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m Bool
anyM f = fmap isJust . findM f

-- Terms

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

data TmEq = Tm := Tm
  deriving (Show)

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

-- E-Graphs

data ETmSort = Branch | Leaf

type ETmData :: ETmSort -> Type
data ETmData s where
  EVar :: Int -> ETmData Leaf
  -- We want to be flexible to support other branching (application-like) terms
  -- (e.g. constructor or eliminator-headed), but for now we only have 'EApp'
  EApp :: Int -> Int -> ETmData Branch

deriving instance Show (ETmData s)
deriving instance Eq (ETmData Leaf)

type EBranch = ETmData Branch
type ELeaf   = ETmData Leaf

data ETm = L ELeaf | B EBranch

data EClassSort = Root | Child

type EClassData :: EClassSort -> Type
data EClassData s where
  Cls :: {
    vars    :: [ELeaf],
    apps    :: [EBranch],
    parents :: [(Int, EBranch)]
  } -> EClassData Root
  Ptr :: Int -> EClassData Child

deriving instance Show (EClassData s)

data EClass = forall s. E (EClassData s)

deriving instance Show EClass

pattern ECls :: () => ()
             => [ELeaf] -> [EBranch] -> [(Int, EBranch)] -> EClass
pattern EPtr :: () => () => Int -> EClass

pattern ECls vs as ps = E (Cls vs as ps)
pattern EPtr i        = E (Ptr i)

{-# COMPLETE ECls, EPtr #-}

type EClassRoot = EClassData Root

data EGraph = Graph {
  classes :: IntMap EClass,
  size    :: Int,
  wlist   :: [Int]
}
  deriving (Show)

-- Pre-condition: 'f' should not create new EClass entries
modifyClasses :: (IntMap EClass -> (IntMap EClass, a)) -> State EGraph a
modifyClasses f = do
  Graph cs s w <- get
  let (cs', x) = f cs
  put (Graph cs' s w)
  pure x

workListPush :: Int -> State EGraph ()
workListPush i = do
  Graph cs s w <- get
  put (Graph cs s (i : w))

chase :: Int -> Reader (IntMap EClass) (Int, EClassRoot)
chase i = do
  cs <- ask
  case cs ! i of
    EPtr j        -> chase j
    ECls vs as ps -> pure (i, Cls vs as ps)

findCls :: ([ELeaf] -> [EBranch] -> Reader (IntMap EClass) Bool)
        -> Reader (IntMap EClass) (Maybe (Int, EClass))
findCls p = do
  cs <- asks toList
  findM (\case (_, ECls vs as _) -> p vs as
               (_, EPtr _)       -> pure False) cs

-- Todo: Tidy these up with a 'chaseAdjust' helper
addParent :: Int -> EBranch -> Int -> IntMap EClass -> IntMap EClass
addParent i c j cs = insert j' (ECls vs as ((i, c):ps)) cs
  where (j', Cls vs as ps) = chase j cs

addParents :: Int -> [(Int, EBranch)] -> State EGraph ()
addParents i ps = do
  Graph cs s w <- get
  let cs' = foldr (\(j, c) -> addParent j c i) cs ps
  put (Graph cs' s w)

setParents :: Int -> [(Int, EBranch)] -> State EGraph ()
setParents i ps = do
  Graph cs s w <- get

  let (i', Cls vs as _) = chase i cs
      cs' = insert i' (ECls vs as ps) cs

  put (Graph cs' s w)

singClass :: ETm -> EClass
singClass (L i) = ECls [i] [] []
singClass (B t) = ECls [] [t] []

children :: EBranch -> [Int]
children (EApp i j) = [i, j]

addSingCls :: ETm -> State EGraph (Int, EClass)
addSingCls t = do
  Graph cs s w <- get
  let c   = singClass t
      cs' = case t of
        L _  -> cs
        B t' -> foldr (addParent s t') cs (children t')

  put (Graph (insert s c cs') (s + 1) w)
  pure (s, c)

chaseEq :: Int -> Int -> Reader (IntMap EClass) Bool
chaseEq i j = do
  (i', _) <- chase i
  (j', _) <- chase j
  pure (i' == j')

lookupELeaf :: ELeaf -> Reader (IntMap EClass) (Maybe (Int, EClass))
lookupELeaf i = findCls \vs _ -> pure (i `elem` vs)

branchEq :: EBranch -> EBranch -> Reader (IntMap EClass) Bool
branchEq (EApp i j) (EApp i' j') = (&&) <$> chaseEq i i' <*> chaseEq j j'

lookupEBranch :: EBranch -> Reader (IntMap EClass) (Maybe (Int, EClass))
lookupEBranch t = findCls (const (anyM (branchEq t)))

lookupEBranch' :: Foldable f => EBranch -> f (Int, EBranch)
               -> Reader (IntMap EClass) (Maybe Int)
lookupEBranch' t = findJustM \(i, u) -> do
  b <- branchEq t u
  pure (boolToMaybe b i)

lookupETm :: Tm -> Reader (IntMap EClass) (Maybe (Int, EClass))
lookupETm (Var i)   cs = lookupELeaf (EVar i) cs
lookupETm (App t u) cs = do
  (i, _) <- lookupETm t cs
  (j, _) <- lookupETm u cs
  lookupEBranch (EApp i j) cs

toETm :: Tm -> State EGraph ETm
toETm (Var i)   = pure (L (EVar i))
toETm (App t u) = do
  (i, _) <- addTm t
  (j, _) <- addTm u
  pure (B (EApp i j))

addTm :: Tm -> State EGraph (Int, EClass)
addTm t = do
  g <- gets classes
  case lookupETm t g of
    Just e -> pure e
    Nothing -> do
      t' <- toETm t
      addSingCls t'

mergeECls :: Int -> Int -> State EGraph ()
mergeECls i j = do
  Graph cs s w <- get
  let (i', Cls vs1 as1 ps1) = chase i cs
      (j', Cls vs2 as2 ps2) = chase j cs

  unless (i' == j') do
    let cs' = insert j' (EPtr i')
             (insert i' (ECls (vs1 <> vs2) (as1 <> as2) (ps1 <> ps2)) cs)
    put (Graph cs' s w)
    workListPush i'

addEq :: TmEq -> State EGraph ()
addEq (t := u) = do
  (i, _) <- addTm t
  (j, _) <- addTm u
  mergeECls i j

buildEGraph :: [TmEq] -> EGraph
buildEGraph = execState rebuild . foldr (execState . addEq) (Graph mempty 0 [])

checkEGraphEqRec :: Tm -> Tm -> EGraph -> Bool
checkEGraphEqRec (App t1 t2) (App u1 u2) g
  = checkEGraphEq t1 u1 g && checkEGraphEq t2 u2 g
checkEGraphEqRec (Var i)     (Var j)     _ = i == j
checkEGraphEqRec _           _           _ = False

checkEGraphEq :: Tm -> Tm -> EGraph -> Bool
checkEGraphEq t u g@(Graph cs _ _)
  =  checkEGraphEqRec t u g
  || justEq (fst <$> lookupETm t cs) (fst <$> lookupETm u cs)

workListPop :: (Int -> State EGraph ()) -> State EGraph ()
workListPop f = do
  Graph cs s w <- get
  case w of
    []   -> pure ()
    i:is -> do
      put (Graph cs s is)
      f i

repair :: Int -> State EGraph ()
repair i = do  
  cs <- gets classes

  -- We know the root e-class will always get added to the work list, so we can
  -- ignore non-root e-classes
  case cs ! i of
    EPtr _      -> pure ()
    ECls _ _ ps -> do
      setParents i []
      ps' <- go [] ps
      addParents i ps'
  where go :: [(Int, EBranch)] -> [(Int, EBranch)]
           -> State EGraph [(Int, EBranch)]
        go ts []           = pure ts
        go ts ((j, t):ps') = do
          cs  <- gets classes
          ts' <- case lookupEBranch' t ts cs of
            Just j' -> mergeECls j j' $> ts
            Nothing -> pure ((j, t):ts)
          go ts' ps'

rebuild :: State EGraph ()
rebuild = do
  Graph cs s w <- get
  let w' = nubOrd (fmap (\i -> fst (chase i cs)) w)

  put (Graph cs s [])
  
  traverse_ repair w'

  w'' <- gets wlist
  unless (null w'') rebuild

-- Fuzzing

genVar :: Gen Int
genVar = do
  (b4, b2, b1) <- arbitrary @(Bool, Bool, Bool)
  pure (4 * fromEnum b4 + 2 * fromEnum b2 + fromEnum b1)

instance Arbitrary Tm where
  arbitrary :: Gen Tm
  arbitrary = do
    b <- arbitrary @Bool
    if b
    then Var <$> genVar
    else do t <- arbitrary @Tm
            u <- arbitrary @Tm
            pure (App t u)

instance Arbitrary TmEq where
  arbitrary :: Gen TmEq
  arbitrary = do
    (t, u) <- arbitrary @(Tm, Tm)
    pure (t := u)

cmpStrats :: [TmEq] -> Tm -> Tm -> Bool
cmpStrats eqs t u = checkEGraphEq t u g == checkRwEq rws t u
  where g   = buildEGraph eqs
        rws = buildRws eqs

cmpStratsSafe :: [TmEq] -> Tm -> Tm -> Property
cmpStratsSafe eqs t u = discardAfter 500000 (cmpStrats eqs t u)

fuzz :: IO ()
fuzz = quickCheck cmpStratsSafe

fuzzVerbose :: IO ()
fuzzVerbose = quickCheck (verbose cmpStratsSafe)
