{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DataKinds #-}

module Check.Utils where
import Data.Kind (Type)
import Data.Foldable (Foldable(..))
  
-- I don't like punning
type Pair a b = (a, b)
type List a   = [a]

data Nat = Z | S Nat

type family n + m where
  Z   + m = m
  S n + m = S (n + m)

data SNat n where
  SS :: SNat n -> SNat (S n)
  SZ :: SNat Z

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

-- I would prefer to flip the indices/parameters here, but I also really want 
-- 'Vec' to be 'Functor'
data Vec g a where
  Emp  :: Vec Z a
  (:<) :: Vec g a -> a -> Vec (S g) a

deriving instance Eq a => Eq (Vec g a)

instance Functor (Vec g) where
  fmap _ Emp       = Emp
  fmap f (xs :< x) = fmap f xs :< f x

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

instance Foldable (Vec g) where
  foldMap _ Emp       = mempty
  foldMap f (xs :< x) = foldMap f xs <> f x

instance Show a => Show (Vec g a) where
  show xs = show (toList xs)

pass :: Applicative f => f ()
pass = pure ()

discard :: Applicative f => f a -> f ()
discard x = x *> pass

insert :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insert k v kvs 
  | k `elem` map fst kvs = fmap (\p -> if k == fst p then (k, v) else p) kvs
  | otherwise            = (k, v) : kvs
