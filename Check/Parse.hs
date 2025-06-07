{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-orphans #-}

module Check.Parse where

import Prelude hiding (repeat, last, init)
import Text.Gigaparsec (($>), Parsec, (<|>), many, atomic)
import Text.Gigaparsec.Char (string, spaces, letter)
import Data.String (IsString(..))

import Check.Syntax
import Check.Utils hiding (parens)
import Data.List.NonEmpty (NonEmpty (..), init)
import Text.Gigaparsec.Combinator.NonEmpty (sepBy1)
import Data.Foldable1 (Foldable1(..))

token :: String -> Parsec ()
token s = atomic (string s) *> spaces

parens :: Parsec a -> Parsec a
parens p = "(" *> p <* ")"

brackets :: Parsec a -> Parsec a
brackets p = "[" *> p <* "]"

braces :: Parsec a -> Parsec a
braces p = "{" *> p <* "}"

instance a ~ () => IsString (Parsec a) where
  fromString = token

sepByExactly :: SNat n -> Parsec a -> Parsec () -> Parsec (Vec n a)
sepByExactly SZ     _ _ = pure Emp
sepByExactly (SS n) p s = flip (:<) <$> p <*> (s *> sepByExactly n p s)

optional :: Parsec a -> Parsec (Maybe a)
optional p = fmap Just p <|> pure Nothing

pair :: Parsec a -> Parsec () -> Parsec b -> Parsec (a, b)
pair p s q = (,) <$> p <*> (s *> q)

-- Smart constructors
bindGen :: (Parsec (Var, a) -> Parsec () -> Parsec r) -> Parsec Var -> Parsec a 
      -> Parsec r
-- Note there is some danger of ambiguity with pairs here. I think we can
-- resolve this by ensuring the parser for types doesn't accept outermost
-- ","s (because "," is not a type former, after all...)
bindGen repSep v a = repSep ((,) <$> v <*> a) "," <* "."

pBody :: Sing SNat a => Parsec Var -> Parsec t -> Parsec Tm -> Parsec (Body a t)
pBody v a b = (:|-) <$> bindGen (sepByExactly fill) v a <*> b

bindSome :: Parsec Var -> Parsec t -> Parsec (NonEmpty (Var, t))
bindSome = bindGen (\b s -> fmap (uncurry (,)) <$> sepBy1 b s)

pVar :: Parsec Var
pVar = (pure <$> letter) <* spaces

pApp :: Parsec Tm -> Parsec Tm -> Parsec Tm
pApp l r = buildApps <$> l <*> many r
  where buildApps = foldl' App

lamSym :: Parsec ()
lamSym = "λ" <|> "\\"

pLam :: Parsec Var -> Parsec Tm -> Parsec Tm -> Parsec Tm 
pLam v a t 
  =   "\\" *> (asNonEmpVec (\bs -> Lam . (bs :|-)) 
  <$> bindSome v (optional $ ":" *> a) <*> t)

piSym :: Parsec ()
piSym = "Π" <|> "forall"

pPi :: Parsec Var -> Parsec Tm -> Parsec Tm -> Parsec Tm
pPi v a b
  =   piSym *> (asNonEmpVec (\bs -> Pi . (bs :|-)) 
  <$> bindSome v (":" *> a) <*> b)

arrow :: Tm -> Tm -> Tm
arrow a b = Pi (Single ("_", a) :|- b)

pArrow :: Parsec Tm -> Parsec Tm -> Parsec Tm
pArrow l r = buildArrows <$> l <*> many (("→" <|> "->") *> r)
  where buildArrows a bs = foldr arrow (last as) (init as)
          where as = a :| bs

pIf :: Parsec (Motive (S Z)) -> Parsec Tm -> Parsec Tm -> Parsec Tm 
    -> Parsec Tm
pIf m t u v = "if" *> (If <$> m <*> t <*> ("then" *> u) <*> ("else" *> v))

pSmrtIf :: Parsec (Motive Z) -> Parsec Tm -> Parsec Tm -> Parsec Tm -> Parsec Tm
pSmrtIf m t u v 
  = "sif" *> (SmrtIf <$> m <*> t <*> ("then" *> u) <*> ("else" *> v))

pExpl :: Parsec (Motive Z) -> Parsec Tm -> Parsec Tm
pExpl m p = "explode" *> (Expl <$> m <*> p)

pU :: Parsec Tm
pU = "U" $> U

pB :: Parsec Tm
pB = "B" $> B

pTT :: Parsec Tm
pTT = "True" $> TT

pFF :: Parsec Tm
pFF = "False" $> FF

pId :: Parsec Tm -> Parsec Tm -> Parsec Tm -> Parsec Tm
pId a x y = "Id" *> (Id <$> a <*> x <*> y)

pRfl :: Parsec Tm
pRfl = "Rfl" $> Rfl Nothing

pRflAnn :: Parsec Tm -> Parsec Tm
pRflAnn x = "Rfl" *> (Rfl <$> optional (braces x))

pBot :: Parsec Tm
pBot = ("𝟘" <|> "Empty") $> Bot

pAbsrd :: Parsec Tm
pAbsrd = "!" $> Absrd

pTransp :: Parsec (Motive (S Z)) -> Parsec Tm -> Parsec Tm -> Parsec Tm
pTransp m p t = "transp" *> (Transp <$> m <*> p <*> t)

pMotive :: Sing SNat a => Parsec (Motive a)
pMotive @a
  | SZ   <- fill @_ @a = optional $ braces pTm
  | SS _ <- fill @_ @a = braces $ pBody pVar pass pTm

pCommonTm :: Parsec Tm
pCommonTm
  =   parens pTm
  <|> pU <|> pB <|> pBot
  <|> pTT <|> pFF
  <|> (Var <$> pVar)

pParensTm :: Parsec Tm
pParensTm 
  =   pRfl
  <|> pCommonTm

pTm :: Parsec Tm
pTm = pSmrtIf pMotive pParensTm pParensTm pParensTm
  <|> pExpl pMotive pParensTm
  <|> pIf pMotive pParensTm pParensTm pParensTm
  <|> pTransp pMotive pParensTm pParensTm
  <|> pId pParensTm pParensTm pParensTm
  <|> pRflAnn pParensTm
  <|> pLam pVar pTm pTm
  <|> pPi pVar pTm pTm
  <|> pArrow (pApp pParensTm pParensTm) (pApp pParensTm pParensTm)
  <|> pCommonTm
