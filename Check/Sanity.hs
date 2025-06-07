{-# LANGUAGE GADTs #-}

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE BlockArguments #-}

-- Sanity checks (i.e. well-scopedness, no ill-typed redexes)
module Check.Sanity where

import Prelude hiding (unzip)
import Data.Bifunctor (Bifunctor(..))
import Data.Data ((:~:) (..))
import Check.Utils
import qualified Check.Syntax as Pre
import Check.Model
import Check.Common

type Ctx g = [(Pre.Var, Var g)]

bind :: Pre.Var -> Ctx g -> Ctx (S g)
bind i g = insert i VZ $ fmap (second VS) g

bindMany :: Vec a (Pre.Var) -> Ctx g -> Ctx (a + g)
bindMany Emp       g = g
bindMany (is :< i) g = bind i $ bindMany is g

coeSort :: SParSort q -> Tm r g -> TCM (Tm q g)
coeSort q t
  | Left  t'  <- sortOf t = pure t'
  | Right r   <- sortOf t = if
    | Just Refl <- q ~? r -> pure t
    | Nothing   <- q ~? r -> throw $ wrongSortErr t r q

sortOf :: Tm q g -> Either (forall r. Tm r g) (SParSort q)
sortOf (El Rdx m t) = Left $ El Rdx m t
sortOf (Lam _ _)    = pure SPi
sortOf (Pi _ _)     = pure SU
sortOf (Id _ _ _)   = pure SU
sortOf U            = pure SU
sortOf B            = pure SU
sortOf Bot          = pure SU
sortOf TT           = pure SB
sortOf FF           = pure SB
sortOf (Rfl _)      = pure SId
sortOf Absrd        = pure SAbsrd

(~?) :: SParSort q -> SParSort r -> Maybe (q :~: r)
SU     ~? SU     = pure Refl
SPi    ~? SPi    = pure Refl
SBot   ~? SBot   = pure Refl
SB     ~? SB     = pure Refl
SId    ~? SId    = pure Refl
SAbsrd ~? SAbsrd = pure Refl
_      ~? _      = Nothing

wrongSortErr :: (Show a, Show b, Show c) => a -> b -> c -> Error
wrongSortErr t a b
   =  quotes (show t) <> " is an intro form of type " <> quotes (show a) 
   <> " but expected term of type " <> quotes (show b) <> "."

checkOfSort :: Ctx g -> SParSort q -> Pre.Tm -> TCM (Tm q g)
checkOfSort g q t = do
  Ex t' <- check g t
  coeSort q t'

checkTele :: (forall x. Ctx x -> t -> TCM (r x)) -> Ctx g -> Vec d (Pre.Var, t) 
          -> TCM (Ctx (d + g), Tele r g d)
checkTele _ g Emp            = pure (g, Nil)
checkTele f g (bs :< (i, a)) = do
  (g', as') <- checkTele f g bs
  a'        <- f g' a
  pure (bind i g', as' :+ a')

checkBody :: (forall x. Ctx x -> t -> TCM (r x)) -> Ctx g 
          -> Pre.Body d t -> TCM (Tele r g d, UnkTm (d + g))
checkBody f g (bs Pre.:|- t) = do
  (g', bs') <- checkTele f g bs
  t'        <- check g' t
  pure (bs', t')

checkBodyOfSort :: (forall x. Ctx x -> t -> TCM (r x)) -> Ctx g -> SParSort q
                -> Pre.Body d t -> TCM (Tele r g d, Tm q (d + g))
checkBodyOfSort f g q b = do
  (bs', Ex t') <- checkBody f g b
  (bs',) <$> coeSort q t'

checkNoAnnBodyOfSort :: Ctx g -> SParSort q -> Pre.Body d () 
                     -> TCM (Tm q (d + g))
checkNoAnnBodyOfSort g q b = snd <$> checkBodyOfSort (\_ _ -> passI) g q b

buildLams :: Tele (Compose Maybe (Tm U)) g a -> Tm q (a + g) -> UnkTm g
buildLams Nil            t' = Ex t'
buildLams (as :+ Comp a) t' = buildLams as (Lam a (Inc t'))

buildPis :: Tele (Tm U) g a -> Tm U (a + g) -> Tm U g
buildPis Nil       b' = b'
buildPis (as :+ a) b' = buildPis as (Pi a (Inc b'))

check :: Ctx g -> Pre.Tm -> TCM (UnkTm g)
check g (Pre.Var i)
  | Just i' <- lookup i g = pure $ Ex $ Var $ i'
  | Nothing <- lookup i g = throw $ "Variable " <> quotes i <> " not in scope!"
check g (Pre.App t u) = do
  t'    <- checkOfSort g SPi t
  Ex u' <- check g u
  pure $ Ex $ App t' u'
check g (Pre.Lam t) = do
  (as', Ex t') 
    <- checkBody (\g' -> fmap Comp . traverse (checkOfSort g' SU)) g t
  pure $ buildLams as' t'
check g (Pre.Pi b) = do
  (as', b') <- checkBodyOfSort (\g' -> checkOfSort g' SU) g SU b
  pure $ Ex $ buildPis as' b'
check g (Pre.If m t u v) = do
  m'    <- checkNoAnnBodyOfSort g SU m
  t'    <- checkOfSort g SB t
  Ex u' <- check g u
  Ex v' <- check g v
  pure $ Ex $ If (Inc m') t' u' v'
check g (Pre.SmrtIf m t u v) = do
  m'    <- traverse (checkOfSort g SU) m
  t'    <- checkOfSort g SB t
  Ex u' <- check g u
  Ex v' <- check g v
  pure $ Ex $ SmrtIf m' t' u' v'
check g (Pre.Expl m p) = do
  m' <- traverse (checkOfSort g SU) m
  p' <- checkOfSort g SBot p
  pure $ Ex $ Expl m' p'
check g (Pre.Transp m p t) = do
  m'    <- checkNoAnnBodyOfSort g SU m
  p'    <- checkOfSort g SId p
  Ex t' <- check g t
  pure $ Ex $ Transp (Inc m') p' t'
check _ Pre.TT    = pure $ Ex TT
check _ Pre.FF    = pure $ Ex FF
check _ Pre.U     = pure $ Ex U
check _ Pre.B     = pure $ Ex B
check _ Pre.Bot   = pure $ Ex Bot
check _ Pre.Absrd = pure $ Ex $ Absrd
check g (Pre.Id a x y) = do
  a'    <- checkOfSort g SU a
  Ex x' <- check g x
  Ex y' <- check g y
  pure $ Ex $ Id a' x' y'
check g (Pre.Rfl x) = do
  x' <- traverse (check g) x
  -- TODO: Can we use a fancy combinator here?
  case x' of
    Nothing       -> pure $ Ex $ Rfl Nothing
    Just (Ex x'') -> pure $ Ex $ Rfl (Just x'')
