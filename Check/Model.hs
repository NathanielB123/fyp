{-# LANGUAGE TypeData #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-missing-pattern-synonym-signatures #-}

module Check.Model where

import Check.Utils
import Data.Kind (Constraint, Type)

type instance Ap SSort i = SSort i

instance Sing SSort (Par q) where
  fill = SPar

instance Sing SSort Neu where
  fill = SNeu

type instance Ap (<=) '(q, r) = q <= r

instance forall (q :: ParSort). Sing (<=) '(Neu, q) where
  fill = FromNeu

instance Sing (<=) '(Par q, q) where
  fill = FromPar

type instance Ap ElimSort '(d, q, r, s) = ElimSort d q r s

-- We could get rid of the explicit type annotations here if we made the kind
-- of the 2nd arg to 'Sing' depend on the first
-- The problem is that I don't think it is possible to make this dependency
-- work for open type families
instance forall (q :: ParSort) (r :: Sort)
              . (r ~ Neu) => Sing ElimSort '(Sem, q, r, Neu) where
  fill = Spn

instance forall (q :: ParSort) (r :: Sort) (s :: ParSort)
              . r ~ Neu => Sing ElimSort '(Sem, q, r, Par s) where
  fill = Stk

instance forall (q :: ParSort) (r :: Sort) (s :: ParSort)
              . r ~ Par q => Sing ElimSort '(Syn, q, r, (Par s)) 
              where
  fill = Rdx

-- I would like to make these 'recover' methods part of a typeclass also,
-- but it seems tricky to generalise over variadic number of arguments without
-- definitional eta
recoverSort :: SSort q -> Dict (Sing SSort q)
recoverSort SPar = Ev
recoverSort SNeu = Ev

type ElimSortExtra :: Dom -> ParSort -> Sort -> Constraint
type family ElimSortExtra d q r where
  ElimSortExtra Syn q r = (Par q ~ r)
  ElimSortExtra Sem q r = ()

recoverElim :: ElimSort d q r s 
            -> Dict (Sing ElimSort '(d, q, r, s), ElimSortExtra d q r)
recoverElim Rdx = Ev
recoverElim Spn = Ev
recoverElim Stk = Ev

-- Note we don't include evidence of the 'ParSort'. 
-- It turns out this is unnecessary (and actually unrecoverable from 
-- e.g. 'Stk' and 'Rdx')
data SSort q where
  SNeu :: SSort Neu
  SPar :: SSort (Par q)

data SParSort q where
  SB     :: SParSort B
  SU     :: SParSort U
  SPi    :: SParSort Pi
  SId    :: SParSort Id
  SBot   :: SParSort Bot
  SAbsrd :: SParSort Absrd

instance Show (SParSort q) where
  show SB     = "𝔹"
  show SU     = "Type"
  show SPi    = "Π" 
  show SBot   = "𝟘"
  show SId    = "="
  show SAbsrd = "Absurd"

type Var = Fin
pattern VZ = FZ
pattern VS i = FS i
{-# COMPLETE VZ, VS #-}

type data ParSort = B | U | Pi | Id | Bot | V | Absrd

-- 'Neu'tral or 'Par'tisan
type data Sort = Neu | Par ParSort

-- Spine, Stuck, or Redex
-- Terms in the semantic domain should not contain redexes
-- Terms in general should not contain "obviously" ill-typed redexes
data ElimSort d q r s where
  Spn :: ElimSort Sem q Neu     Neu
  Stk :: ElimSort Sem q Neu     (Par s)
  Rdx :: ElimSort Syn q (Par q) (Par r)

-- 'Dom'ain: 'Syn'tax (terms) or 'Sem'antics (values)
type data Dom = Syn | Sem

type family VSort d where
  VSort Sem = Neu
  VSort Syn = Par V

type EqMap g = [(Ne g, UnkVal g)]

-- TODO: For e.g. the motive of the "J" rule, we need to be able to bind 
-- multiple variables at once. Having 'Body' take an arity seems like
-- the most natural way to achieve this IMO.
data Body d q g where
  Inc :: {uninc :: Model Syn (Par q) (S g)} -> Body Syn q g
  Clo :: {
    unclo :: forall g' r. Sing SNat g' => Thin g' g -> EqMap g' 
          -> Model Sem (Par r) g' -> Model Sem (Par q) g'
  } -> Body Sem q g

type Motive :: Dom -> Maybe Nat -> Nat -> Type
type family Motive d a g where
  Motive d Nothing      g = ()
  Motive d (Just Z)     g = Maybe (Model d (Par U) g)
  Motive d (Just (S Z)) g = Body d U g
  -- TODO: Support arities > 1

type Spine :: Dom -> Maybe Nat -> ParSort -> Sort -> Nat -> Type
data Spine d a q r g where
  VarS    :: Var g -> Spine d Nothing V (VSort d) g
  AppS    :: Model d pi g -> Model d (Par q) g -> Spine d Nothing Pi pi g
  IfS     :: Model d b g -> Model d (Par q) g -> Model d (Par r) g 
          -> Spine d (Just (S Z)) B b g
  SmrtIfS :: Model d b g -> Model d (Par q) g -> Model d (Par r) g 
          -> Spine d (Just Z) B b g
  TranspS :: Model d id g -> Model d (Par q) g 
          -> Spine d (Just (S Z)) Id id g 
  ExplS   :: Model d bot g -> Spine d (Just Z) Bot bot g

type Model :: Dom -> Sort -> Nat -> Type
data Model d q g where
  Lam   :: Maybe (Model d (Par U) g) -> Body d q g -> Model d (Par Pi) g
  U     :: Model d (Par U) g
  B     :: Model d (Par U) g
  Bot   :: Model d (Par U) g
  Pi    :: Model d (Par U) g -> Body d U g -> Model d (Par U) g
  El    :: ElimSort d q r s -> Motive d a g -> Spine d a q r g -> Model d s g
  TT    :: Model d (Par B) g
  FF    :: Model d (Par B) g
  Id    :: Model d (Par U) g -> Model d (Par q) g -> Model d (Par r) g 
        -> Model d (Par U) g
  Rfl   :: Maybe (Model d (Par q) g) -> Model d (Par Id) g
  -- Absurds make no sense in scrutinee positions so giving them a unique sort
  -- seems reasonable.
  -- Of course, this prevents us from trying to enforce equality of sorts
  -- in places where terms of def equal types are expected (e.g. the branches
  -- of an 'If', but I think this is more trouble than it's worth anyway)
  Absrd :: Model q (Par Absrd) g

type Tm  q = Model Syn (Par q)
type Ty    = Tm U
type Ne    = Model Sem Neu
type Val q = Model Sem (Par q)
type VBody = Body Sem
type VTy   = Val U

data (<=) q r where
  FromNeu :: Neu   <= q
  FromPar :: Par q <= q

deriving instance Show (SSort q)

deriving instance Show (ElimSort d q r s)
instance Show (Body Syn q g) where
  show (Inc t) = show t

instance Show (Model Syn q g) where
  show (Lam _ t)        = "λ " <> show t
  show (Pi a b)         = "Π " <> parens (show a) <> " " <> parens (show b)
  show U                = "Type"
  show B                = "𝔹"
  show Bot              = "𝟘"
  show (App t u)        = parens (show t) <> " " <> parens (show u)
  show (If _ t u v)     = "if " <> parens (show t) <> " then " 
                       <> parens (show u) <> " else " 
                       <> parens (show v) <> ")"
  show (SmrtIf _ t u v) = "sif " <> parens (show t) <> " then " 
                       <> parens (show u) <> " else " 
                       <> parens (show v) <> ")"
  show (Transp _ p t)   = "transp " <> parens (show p) <> " " <> parens (show t)
  show (Expl _ p)       = "! " <> parens (show p)
  show (Var i)          = "`" <> show i
  show TT               = "TT"
  show FF               = "FF"
  show (Id _ x y)       = parens (show x) <> " = " <> parens (show y)
  show (Rfl _)          = "Rfl"
  show Absrd            = "!"

recoverSub :: q <= r -> Dict (Sing (<=) '(q, r))
recoverSub FromNeu = Ev
recoverSub FromPar = Ev

elimSortSub :: ElimSort d q r s -> r <= q
elimSortSub Rdx = FromPar
elimSortSub Spn = FromNeu
elimSortSub Stk = FromNeu

subSort :: q <= r -> SSort q
subSort FromNeu = SNeu
subSort FromPar = SPar

recoverAllElim :: ElimSort d q r s 
               -> Dict (Sing ElimSort '(d, q, r, s)
                       ,ElimSortExtra d q r
                       ,Sing (<=) '(r, q)
                       ,Sing SSort r)
recoverAllElim el@(elimSortSub -> sub) 
  | Ev <- recoverElim el 
  , Ev <- recoverSub sub
  , Ev <- recoverSort (subSort sub)
  = Ev

pattern RecSort :: () => Sing SSort q => SSort q
pattern RecSort <- (recoverSort -> Ev)
  where RecSort = fill

pattern RecElim :: () 
                => (Sing ElimSort '(d, q, r, s), ElimSortExtra d q r
                   ,Sing (<=) '(r, q), Sing SSort r) 
                => ElimSort d q r s
pattern RecElim <- (recoverAllElim -> Ev)
  where RecElim = fill

pattern Var i <- El RecElim _ (VarS i)
  where Var i = El RecElim () (VarS i)
pattern App t u <- El RecElim _ (AppS t u)
  where App t u = El RecElim () (AppS t u)
pattern If m t u v = El RecElim m (IfS t u v)
pattern Transp m p t = El RecElim m (TranspS p t)
pattern Expl m p = El RecElim m (ExplS p)
pattern SmrtIf m t u v = El RecElim m (SmrtIfS t u v)

pattern Ne :: () => () => Ne g -> Val q g
pattern Ne t <- El Stk m (El Spn m -> t)
  where Ne (El Spn m t) = El Stk m t

pattern VarNe :: () => () => Var g -> Ne g
pattern VarNe i <- El Spn _ (VarS i)
  where VarNe i = El Spn () (VarS i)

pattern AppNe :: () => () => Ne g -> Val q g -> Ne g
pattern AppNe t u <- El Spn _ (AppS t u)
  where AppNe t u = El Spn () (AppS t u)

pattern IfNe :: () => () 
             => VBody U g -> Ne g -> Val q g -> Val r g -> Ne g
pattern IfNe m t u v = El Spn m (IfS t u v)

pattern TranspNe :: () => () => VBody U g -> Ne g -> Val q g -> Ne g
pattern TranspNe m p t = El Spn m (TranspS p t)

pattern ExplNe :: () => () => Maybe (Val U g) -> Ne g -> Ne g
pattern ExplNe m t = El Spn m (ExplS t)

pattern SmrtIfNe :: () => () 
                 => Maybe (Val U g) -> Ne g -> Val q g -> Val r g -> Ne g
pattern SmrtIfNe m t u v = El Spn m (SmrtIfS t u v)

{-# COMPLETE AppNe, IfNe, SmrtIfNe, TranspNe, ExplNe, VarNe #-}
{-# COMPLETE Lam, U, B, Bot, Pi, TT, FF, Id, Rfl, Absrd, Ne #-}
{-# COMPLETE Lam, U, B, Bot, Pi, App, If, SmrtIf, Var, 
             TT, FF, Id, Rfl, Transp, Expl, Absrd #-}

data Unk d g = forall q. Ex {proj :: Model d (Par q) g}
type UnkTm  = Unk Syn
type UnkVal = Unk Sem

runUnk :: (forall q. Model d (Par q) g -> r) -> Unk d g -> r
runUnk f (Ex t) = f t

instance PshThin (Unk d) where
  thin s (Ex t) = Ex $ thin s t

instance PshThin (Body d q) where
  thin s (Inc t) = Inc $ thin (Keep s) t
  thin s (Clo t) = Clo $ t . comTh s

instance PshThin (Model d q) where
  thin _ U                = U
  thin _ B                = B
  thin _ Bot              = Bot
  thin s (Pi a b)         = Pi     (thin s a)  (thin s b)
  thin s (Id a x y)       = Id     (thin s a)  (thin s x) (thin s y)
  thin s (Lam a t)        = Lam    (fThin s a) (thin s t)
  thin s (App t u)        = App    (thin s t)  (thin s u)
  thin s (If m t u v)     = If     (thin s m)  (thin s t) (thin s u) (thin s v)
  thin s (SmrtIf m t u v) = SmrtIf (fThin s m) (thin s t) (thin s u) (thin s v)
  thin s (Transp m p t)   = Transp (thin s m)  (thin s p) (thin s t)
  thin s (Expl m p)       = Expl   (fThin s m) (thin s p)
  thin s (Var i)          = Var    (thin s i)
  thin _ TT               = TT
  thin _ FF               = FF
  thin s (Rfl t)          = Rfl    (fThin s t)
  thin _ Absrd            = Absrd

instance Sing SNat g => Show (Val q g) where
  show = show . reify

instance Sing SNat g => Show (Ne g) where 
  show = show . Ne

instance Sing SNat g => Show (UnkVal g) where
  show (Ex t) = show t

-- TODO: Switch from 'conv' to '=='
instance Sing SNat g => Eq (Ne g) where
  t == u = convNe t u

instance Sing SNat g => Eq (UnkVal g) where
  Ex t == Ex u = conv t u

instance Sing SNat g => Eq (Val q g) where
  t == u = Ex t == Ex u

type ConvJud = Bool 
data UnifJud = DefUnify | Unknown | DefAntiUnify

unifies :: ConvJud -> UnifJud
unifies True  = DefUnify
unifies False = Unknown

convertible :: UnifJud -> ConvJud
convertible DefUnify     = True
convertible Unknown      = False
convertible DefAntiUnify = False

-- Combine unification judgements (i.e. for definitionally injective forms)
(|~|) :: UnifJud -> UnifJud -> UnifJud
DefUnify     |~| DefUnify     = DefUnify
DefAntiUnify |~| _            = DefAntiUnify
_            |~| DefAntiUnify = DefAntiUnify
_            |~| _            = Unknown

-- Bodies never anti-unify because their argument type might be empty
-- (and e.g. we want to stay consistent with univalence) 
-- 
-- We *could* add a concept of definitionally non-empty types, but that seems
-- a bit overkill...
convBody :: Sing SNat g => Body Sem q g -> Body Sem r g -> ConvJud
convBody (Clo t) (Clo u)
  = conv (t wkTh [] (Var VZ)) (u wkTh [] (Var VZ))

-- Precondition: Types of values are def equal
unify :: Sing SNat g => Val q g -> Val r g -> UnifJud
unify TT  TT  = DefUnify
unify FF  FF  = DefUnify
unify TT  FF  = DefAntiUnify
unify FF  TT  = DefAntiUnify
-- We don't build-in injectivity/no-confusion for types to try and stay 
-- compatible with univalence.
unify U   U   = DefUnify
unify B   B   = DefUnify
unify Bot Bot = DefUnify
unify (Lam _ t1) (Lam _ t2) = unifies $ convBody t1 t2
unify (Pi a1 b1) (Pi a2 b2) = unifies $ conv a1 a2 && convBody b1 b2
unify (Id _ x1 y1) (Id _ x2 y2) = unifies $ conv x1 x2 && conv y1 y2
-- 'rfl's with def equal types must be def equal themselves
unify (Rfl _) (Rfl _) = DefUnify
unify (Ne t1) (Ne t2) = unifies $ convNe t1 t2
unify Absrd   Absrd   = DefUnify
-- This is a fun edge case. When we compare neutral LHSs in our rewrite map
-- to a normalised term, the normalised term my contain 'Absrd' in places
-- where that rewrite LHS does not (because the rewrite LHS has not been
-- normalised w.r.t. itself).
-- I think just unifying 'Absrd' with everything should be fine (we
-- know we are in a definitionally inconsistent context) 
unify Absrd   _       = DefUnify
unify _       Absrd   = DefUnify

-- unify Absrd   u       = __IMPOSSIBLE__ 
--   $ "Tried to unify 'Absrd' with " <> show u
-- unify t       Absrd   = __IMPOSSIBLE__ 
--   $ "Tried to unify 'Absrd' with " <> show t

unify _       _       = Unknown

-- Neutrals are either definitionally equal or unknown
convNe :: Sing SNat g => Ne g -> Ne g -> ConvJud
convNe (AppNe t1 u1) (AppNe t2 u2) = convNe t1 t2 && conv u1 u2
convNe (IfNe _ t1 u1 v1) (IfNe _ t2 u2 v2) 
  = convNe t1 t2 && conv u1 u2 && conv v1 v2
convNe (SmrtIfNe _ t1 u1 v1) (SmrtIfNe _ t2 u2 v2)
  = convNe t1 t2 && conv u1 u2 && conv v1 v2
convNe (TranspNe _ p1 t1) (TranspNe _ p2 t2) = convNe p1 p2 && conv t1 t2
convNe (ExplNe _ p1) (ExplNe _ p2) = convNe p1 p2
convNe (VarNe i1) (VarNe i2) = i1 == i2
convNe _ _ = False

conv :: Sing SNat g => Val q g -> Val r g -> ConvJud
conv t u = convertible $ unify t u

reifyBody :: Sing SNat g => Body Sem q g -> Body Syn q g
reifyBody (Clo t) = Inc $ reify (t wkTh [] (Var VZ))

reifyNe :: Sing SNat g => Ne g -> Model Syn (Par q) g
reifyNe (VarNe i)    = Var i
reifyNe (IfNe m t u v) 
  = If (reifyBody m) (reifyNe t) (reify u) (reify v)
reifyNe (SmrtIfNe m t u v)
  = SmrtIf (reify <$> m) (reifyNe t) (reify u) (reify v)
reifyNe (AppNe t u)  = App (reifyNe t) (reify u)
reifyNe (TranspNe m p t)  = Transp (reifyBody m) (reifyNe p) (reify t)
reifyNe (ExplNe m p) = Expl (reify <$> m) (reifyNe p)

reify :: Sing SNat g => Val q g -> Model Syn (Par q) g
reify (Ne t)     = reifyNe t
reify (Lam a t)  = Lam (reify <$> a) (reifyBody t)
reify (Pi a b)   = Pi (reify a) (reifyBody b)
reify (Id a x y) = Id (reify a) (reify x) (reify y)
reify (Rfl x)    = Rfl (reify <$> x)
reify TT         = TT
reify FF         = FF
reify U          = U
reify B          = B
reify Bot        = Bot
reify Absrd      = Absrd
