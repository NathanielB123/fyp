{-# LANGUAGE PatternSynonyms #-}

module Check.Common where

type Error = String

throw :: Error -> TCM a
throw = Failure

orThrow :: Bool -> Error -> TCM ()
orThrow True  _ = pure ()
orThrow False e = throw e

justOrThrow :: Error -> Maybe a -> TCM a
justOrThrow _ (Just x) = Success x
justOrThrow e Nothing  = Failure e

guardThrow :: Bool -> Error -> TCM ()
guardThrow True  _ = pure ()
guardThrow False e = throw e

newtype TCM a = TCM (Either Error a)
  deriving (Functor, Applicative, Monad)

pattern Failure :: Error -> TCM a
pattern Failure e = TCM (Left e)
pattern Success :: a -> TCM a
pattern Success a = TCM (Right a)
{-# COMPLETE Failure, Success #-}

instance Show a => Show (TCM a) where
  show (Failure e)  = "Failed with: " <> e
  show (Success x) = "Success: " <> show x

appendError :: String -> TCM a -> TCM a
appendError _ (Success x) = Success x
appendError s (Failure e) = Failure (s <> "\n  - " <> e)

__IMPOSSIBLE__ :: a
__IMPOSSIBLE__ = error "ICE: Something went wrong!"
