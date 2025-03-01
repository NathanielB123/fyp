{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Check.Pipeline where

import Text.Gigaparsec (Parsec, parse)
import Text.Gigaparsec qualified as P

import Check.Common 
import Check.Parse (pTm)
import Check.Utils
import Check.Model
import qualified Check.Sanity as Sanity
import qualified Check.Check as Check
import qualified Check.Syntax as Pre

runParser :: Parsec a -> String -> TCM a
runParser p s
  | P.Success x <- parse @String p s = Success x
  | P.Failure e <- parse @String p s = Failure e


infer :: String -> TCM (VTy Z)
infer t = do
  t'     <- runParser (pTm <* "\n") t
  Ex t'' <- Sanity.check [] t'
  a      <- Check.infer Nil (Emp, []) t''
  pure a

check :: String -> String -> TCM ()
check t a = do
  t'     <- runParser (pTm <* "\n") t
  a'     <- runParser (pTm <* "\n") a
  Ex t'' <- Sanity.check [] t'
  a''    <- Sanity.checkOfSort [] SU a'
  Check.check Nil (Emp, []) a'' t''

parseTest :: String -> TCM (Pre.Tm)
parseTest = runParser (pTm <* "\n")

main :: IO ()
main = do
  l <- getLine
  case infer l of
    Success a -> putStrLn $ "Successfully inferred type: " <> show a
    Failure e -> putStrLn $ "Failed :(\n" <> e


