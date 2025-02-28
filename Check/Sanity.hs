{-# LANGUAGE GADTs #-}

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE DataKinds #-}

-- Sanity checks (i.e. well-scopedness, no ill-typed redexes)
module Check.Sanity where

import Check.Utils
import qualified Check.Syntax as Pre
import Check.Model
import Check.Common
import Data.Bifunctor (Bifunctor(..))
import Control.Monad ((>=>))

type Ctx g = [(Pre.Var, Var g)]

bind :: Pre.Var -> Ctx g -> Ctx (S g)
bind i g = insert i VZ $ fmap (second VS) g

bindMany :: Vec a (Pre.Var) -> Ctx g -> Ctx (a + g)
bindMany Emp       g = g
bindMany (is :< i) g = bind i $ bindMany is g

-- TODO: Maybe a neater way to deal with this is have a function that returns
-- the 'SParSort q' of the term or a proof it is coercible to any sort, and then
-- just compare 'SParSort's
coeSort :: SParSort q -> Tm r g -> Maybe (Tm q g)
coeSort _    (El Rdx m t) = pure $ El Rdx m t
coeSort SPi  (Lam a t)    = pure $ Lam a t
coeSort SPi  _            = Nothing
coeSort SB   TT           = pure $ TT
coeSort SB   FF           = pure $ FF
coeSort SB   _            = Nothing
coeSort SU   U            = pure $ U
coeSort SU   B            = pure $ B
coeSort SU   Bot          = pure $ Bot
coeSort SU   (Pi a b)     = pure $ Pi a b
coeSort SU   (Id a x y)   = pure $ Id a x y
coeSort SU   _            = Nothing
coeSort SId  (Rfl x)      = pure $ Rfl x
coeSort SId  _            = Nothing
coeSort SBot _            = Nothing

wrongSortErr :: (Show a, Show b) => a -> b -> Error
wrongSortErr a t
   = quotes (show t) <> " does not have type " <> quotes (show a) <> "."

checkSort :: SParSort q -> Tm r g -> TCM (Tm q g)
checkSort a t
  | Just t' <- coeSort a t = pure t'
  | Nothing <- coeSort a t = throw $ wrongSortErr a t

checkBody :: Ctx g -> Pre.Body a -> TCM (UnkTm (a + g))
checkBody g (vs Pre.:|- t) = check (bindMany vs g) t

check :: Ctx g -> Pre.Tm -> TCM (UnkTm g)
check g (Pre.Var i)
  | Just i' <- lookup i g = pure $ Ex $ Var $ i'
  | Nothing <- lookup i g = throw $ "Variable " <> quotes i <> " not in scope!"
check g (Pre.App t u) = do
  t'    <- (check g >=> runUnk (checkSort SPi)) t
  Ex u' <- check g u
  pure $ Ex $ App t' u'
check g (Pre.Lam x a t) = do
  let g' = bind x g
  a'    <- (check g >=> runUnk (checkSort SU)) a
  Ex t' <- check g' t
  pure $ Ex $ Lam a' (Inc t')
check g (Pre.If m t u v) = do
  m' <- (checkBody g >=> runUnk (checkSort SU)) m
  pure $ Ex $ If (Inc m') _ _ _
check _ Pre.TT = pure $ Ex TT
check _ Pre.FF = pure $ Ex FF

