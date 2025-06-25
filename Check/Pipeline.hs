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
import Check.Check (coeTM)

runParser :: Parsec a -> String -> TCM a
runParser p s
  | P.Success x <- parse @String p s = Success x
  | P.Failure e <- parse @String p s = Failure e

infer :: String -> TCM (VTy Z)
infer t = do
  t'     <- runParser (pTm <* "\n") (t <> "\n")
  Ex t'' <- Sanity.check [] t'
  a      <- Check.infer Nil (Emp, []) t''
  pure a

check :: String -> Ty Z -> TCM (UnkTm Z)
check t a = do
  t'     <- runParser (pTm <* "\n") (t <> "\n")
  Ex t'' <- Sanity.check [] t'
  Check.check Nil (Emp, []) a t''
  pure $ Ex t''

eval :: String -> String -> TCM String
eval t a = do
  t'     <- runParser (pTm <* "\n") (t <> "\n")
  a'     <- runParser (pTm <* "\n") (a <> "\n")
  Ex t'' <- Sanity.check [] t'
  a''    <- Sanity.checkOfSort [] SU a'
  Check.check Nil (Emp, []) a'' t''
  pure $ show $ Check.eval @Z (Emp, []) t''

parseTest :: String -> TCM (Pre.Tm)
parseTest = runParser (pTm <* "\n")

main :: IO ()
main = do
  putStrLn "Enter type:"
  l1 <- getLine
  case check l1 U of
    Failure e -> putStrLn $ "Invalid Type :(\n" <> e
    Success (Ex a) -> do
      putStrLn "Enter term:"
      l2 <- getLine
      -- TODO: We could easily clean up the API a bit here and allow passing
      -- an expected 'SSort' to 'check'
      -- Honestly I am somewhat convinced that scrapping 'Sort's entirely would
      -- be reasonable though
      case check l2 (coeTM a) of
        Success a -> putStrLn $ "Success!"
        Failure e -> putStrLn $ "Failed :(\n" <> e

  -- putStrLn "Enter proof term:"
  -- l <- (<> "\n") <$> getLine
  -- case infer l of
  --   Success a -> putStrLn $ "Successfully inferred type: " <> show a
  --   Failure e -> putStrLn $ "Failed :(\n" <> e


boolLemmaTy = "forall f: B -> B, b : B. Id B (f b) (f (f (f b))) \n"
boolLemmaTm = "\\f, b. sif b then (sif (f TT) then Rfl else (sif (f FF) then Rfl else Rfl)) else (sif (f FF) then (sif (f TT) then Rfl else Rfl) else Rfl) \n"
-- >>> check boolLemmaTm boolLemmaTy
-- Success: ()

boolLemmaSpecTy = "forall f: B -> B. Id B (f TT) (f (f (f TT))) \n"
boolLemmaSpecTm = "\\f. sif (f TT) then Rfl else (sif (f FF) then Rfl else Rfl) \n"
-- >>> check boolLemmaSpecTm boolLemmaSpecTy
-- Success: ()

absrdTy = "B -> B \n"
absrdTm = "\\b : B. sif { B } (sif b then TT else FF) then (sif b then TT else !) else FF \n"
-- >>> check absrdTm absrdTy
-- Success: ()

-- >>> infer absrdTm
-- Success: Π (𝔹) (𝔹)

-- >>> eval absrdTm absrdTy
-- Success: "\955 sif (sif (`0) then (TT) else (FF))) then (sif (`0) then (TT) else (!))) else (FF))"
