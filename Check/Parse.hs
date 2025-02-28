{-# LANGUAGE OverloadedStrings #-}

module Check.Parse where

import Prelude hiding (repeat)
import Text.Gigaparsec (($>), Parsec, (<|>))
import Text.Gigaparsec.Char (string, spaces, satisfy)
import Data.Char (ord)
import Data.String (IsString(..))

import Check.Syntax
import Check.Utils

token :: String -> Parsec ()
token s = string s *> spaces

parens :: Parsec a -> Parsec a
parens p = "(" *> p <* ")"

brackets :: Parsec a -> Parsec a
brackets p = "[" *> p <* "]"

instance a ~ () => IsString (Parsec a) where
  fromString = token

repeat :: Parsec a -> Parsec [a]
repeat p = repeatSep p pass

repeatBeginSep :: Parsec () -> Parsec a -> Parsec () -> Parsec [a]
repeatBeginSep b p s = b *> ((:) <$> p <*> repeatBeginSep s p s) <|> pure []

repeatSep :: Parsec a -> Parsec () -> Parsec [a]
repeatSep p s = repeatBeginSep pass p s

pair :: Parsec a -> Parsec () -> Parsec b -> Parsec (a, b)
pair p s q = (,) <$> p <*> (s *> q)

-- Smart constructors

pMotive :: Nat -> Parsec Var -> Parsec Tm -> Parsec Motive
pMotive Z     _   ty = ([] :|-) <$> ty
pMotive (S n) var ty = _

pVar :: Parsec Var
pVar = (pure <$> satisfy (\c -> ord 'a' <= ord c && ord c <= ord 'z')) <* spaces

pVars :: Parsec Var -> Parsec [Var]
pVars var = repeatSep var "," <* "."

pAnnVars :: Parsec Var -> Parsec Tm -> Parsec [(Var, Tm)]
-- Note there is some danger of ambiguity with pairs here. I think we can
-- resolve this by ensuring the parser for types doesn't accept outermost
-- ","s (because "," is not a type former, after all...)
pAnnVars var ty = repeatSep (pair var ":" ty) "," <* "."

pApp :: Parsec Tm -> Parsec Tm -> Parsec Tm
pApp lhs rhs = buildApps <$> lhs <*> repeat rhs
  where buildApps = foldl App

pLam :: Parsec Var -> Parsec Tm -> Parsec Tm -> Parsec Tm 
pLam var ty body = token "\\" *> (buildLams <$> pAnnVars var ty <*> body)
  where buildLams xs t = foldr (uncurry Lam) t xs

-- pIf :: Parsec Tm -> Parsec Tm -> Parsec Tm -> Parsec Tm 
--     -> Parsec Tm
-- pIf m t u v = _
--   where buildIf

pTT :: Parsec Tm
pTT = "True" $> TT

pFF :: Parsec Tm
pFF = "False" $> FF


-- var :: Parsec String
-- var = (pure <$> satisfy (\c -> ord 'a' <= ord c && ord c <= ord 'z')) <* spaces

-- parseVars :: Parsec [String]
-- parseVars
--  =   (token "." $> [])
--  <|> ((:) <$> var <*> parseVars)


-- buildLams :: [v] -> Tm v -> Tm v
-- buildLams xs t = foldr Lam t xs

-- buildApps :: Tm v -> [Tm v] -> Tm v
-- buildApps = foldl App

-- parens :: Parsec a -> Parsec a
-- parens p = token "(" *> p <* token ")"

-- repeat :: Parsec a -> Parsec [a]
-- repeat p = ((:) <$> p <*> repeat p) <|> pure []

-- lhs :: Parsec (Tm String)
-- lhs =   parens parseTm
--     <|> (token "\\" *> (buildLams <$> parseVars <*> parseTm))
--     <|> (Var <$> var)

-- parseTm :: Parsec (Tm String)
-- parseTm = buildApps <$> lhs <*> repeat lhs


-- parseTm :: Parsec Tm
-- parseTm = _ <|> _
--   where pTT :: Parsec Tm
--         pTT = token "TT" $> TT
--         pFF = token "FF" $> FF

