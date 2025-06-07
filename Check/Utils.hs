{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ApplicativeDo #-}

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Check.Utils where

import Data.Kind (Type)
import Data.Foldable (Foldable(..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Data ((:~:) (..))
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)

-- I don't like punning
type Pair a b = (a, b)
type List a   = [a]

type data Nat = Z | S Nat

type family n + m where
  Z   + m = m
  S n + m = S (n + m)

data SNat n where
  SS :: SNat n -> SNat (S n)
  SZ :: SNat Z

data Fin n where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)
deriving instance Eq (Fin n)

finToInt :: Fin g -> Int
finToInt FZ     = 0
finToInt (FS i) = finToInt i + 1

instance Show (Fin g) where
  show i = show $ finToInt i

vLookup :: Fin g -> Vec g a -> a
vLookup FZ     (_ :< t) = t
vLookup (FS i) (r :< _) = vLookup i r

tLookup :: (Sing SNat (g + d), PshThin c) => Fin g -> Tele c d g -> c (g + d)
tLookup @g @d FZ (_ :+ a)
  | SS n <- fill @SNat @(g + d)
  , Ev   <- recoverNat n
  = thin wkTh a
tLookup @g @d (FS i) (g :+ _) 
  | SS n <- fill @SNat @(g + d) 
  , Ev   <- recoverNat n
  = thin wkTh (tLookup i g)

-- Open type families are cringe, but additional typeclasses are also cringe
type Ap :: f -> a -> Type
type family Ap f a = r | r -> f a

data Dict c = c => Ev

class Sing s i where
  fill :: Ap s i

type instance Ap SNat n = SNat n

instance Sing SNat Z where
  fill = SZ

instance Sing SNat n => Sing SNat (S n) where
  fill = SS fill

parens :: String -> String
parens s = "(" <> s <> ")"

quotes :: String -> String
quotes s = "'" <> s <> "'"

-- I would prefer to flip the indices/parameters here, but we need the type
-- argument to come last to fit the requirements of 'Functor' etc...
data Vec g a where
  Emp  :: Vec Z a
  (:<) :: Vec g a -> a -> Vec (S g) a

pattern (:>) :: () => (g ~ S d) => a -> Vec d a -> Vec g a
pattern x :> xs = xs :< x

{-# COMPLETE Emp, (:>) #-}

deriving instance Eq a => Eq (Vec g a)
deriving instance Functor (Vec g)
deriving instance Foldable (Vec g)
deriving instance Traversable (Vec g)

data Thin d g where
  Eps  :: Thin Z Z
  Keep :: Thin d g -> Thin (S d) (S g)
  Drop :: Thin d g -> Thin (S d) g

idTh :: SNat g -> Thin g g
idTh SZ     = Eps
idTh (SS n) = Keep (idTh n)

wkTh :: Sing SNat g => Thin (S g) g
wkTh = Drop (idTh fill)

comTh :: Thin d g -> Thin x d -> Thin x g
comTh Eps       s2        = s2
comTh (Keep s1) (Keep s2) = Keep (comTh s1 s2)
comTh (Drop s1) (Keep s2) = Drop (comTh s1 s2)
comTh s1        (Drop s2) = Drop (comTh s1 s2)

-- Presheaves on the category of thinnings
class PshThin f where
  thin :: Thin d g -> f g -> f d

fThin :: (Functor f, PshThin c) => Thin d g -> f (c g) -> f (c d)
fThin = fmap . thin

instance Show a => Show (Vec g a) where
  show xs = show (toList xs)

pass :: Applicative f => f ()
pass = pure ()

passI :: Applicative f => f (IUnit i)
passI = pure IUnit

discard :: Applicative f => f a -> f ()
discard x = x *> pass

insert :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insert k v kvs 
  | k `elem` map fst kvs = fmap (\p -> if k == fst p then (k, v) else p) kvs
  | otherwise            = (k, v) : kvs

vLen :: Vec g a -> SNat g
vLen Emp      = SZ
vLen (r :< _) = SS (vLen r)

pattern Single :: () => (g ~ S Z) => a -> Vec g a
pattern Single x = Emp :< x

pattern Cons2 :: () => (g ~ S (S d)) => a -> a -> Vec d a -> Vec g a
pattern Cons2 x y zs = zs :< y :< x

{-# COMPLETE Emp, Single, Cons2 #-}

data Compose f g a = Comp (f (g a))

data Tele c d g where 
  Nil  :: Tele c d Z
  (:+) :: Tele c d g -> c (g + d) -> Tele c d (S g)

pattern (:.) :: () => (d ~ S g) => Tele c Z g -> c g -> Tele c Z d
pattern xs :. x <- xs :+ (transp plusZero -> x)
  where xs :. x = xs :+ transpInv plusZero x

plusZero :: n + Z :~: n
plusZero = unsafeCoerce Refl

transp :: x :~: y -> p x -> p y
transp Refl = id

transpInv :: x :~: y -> p y -> p x
transpInv Refl = id

tLookupZ :: (Sing SNat g, PshThin c) => Fin g -> Tele c Z g -> c g
tLookupZ @g i xs | Refl <- plusZero @g = tLookup i xs

recoverNat :: SNat n -> Dict (Sing SNat n)
recoverNat SZ     = Ev
recoverNat (SS n)
  | Ev <- recoverNat n
  = Ev

addNat :: SNat n -> SNat m -> SNat (n + m)
addNat SZ     m = m
addNat (SS n) m = SS $ addNat n m

data IUnit i = IUnit

asVec :: (forall n. Vec n a -> r) -> [a] -> r
asVec f []       = f Emp
asVec f (x : xs) = asVec (\xs' -> f (x :> xs')) xs

pattern One :: a -> NonEmpty a
pattern One x = x :| []

pattern (:||) :: a -> NonEmpty a -> NonEmpty a
pattern x :|| ys <- x :| (nonEmpty -> Just ys)

{-# COMPLETE One, (:||) #-}

asNonEmpVec :: (forall n. Vec (S n) a -> r) -> NonEmpty a -> r
asNonEmpVec f (One x)    = f (Single x)
asNonEmpVec f (x :|| xs) = asNonEmpVec (\xs' -> f (x :> xs')) xs

instance PshThin Fin where
  thin (Keep _) FZ     = FZ
  thin (Drop s) i      = FS (thin s i)
  thin (Keep s) (FS i) = FS (thin s i)
  thin Eps      i      = case i of
