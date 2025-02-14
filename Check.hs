{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS -Wall #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}


{-# HLINT ignore "Use newtype instead of data" #-}


import Prelude hiding (lookup, not)
import Control.Monad (guard)
import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)
import Data.Data ((:~:)(..))

-- Open type families are cringe, but tons of similar typeclasses are also
-- cringe
type Ap :: f -> a -> Type
type family Ap f a = r | r -> f a

data Dict c = c => Ev

class Sing s i where
  fill :: Ap s i

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

-- Morally:
-- Sing ElimSort d q r s = case s of
--   Neu -> do
--     .Neu -> Spn
--   (Par s) -> case d of
--     Syn -> case r of
--       Neu      -> Stk
--       (Par .q) -> Rdx
--     Sem -> case r of
--       .Neu -> Stk
--             

-- We could get rid of the explicit type annotations here if we made the kind
-- of the 2nd arg to 'Sing' depend on the first
-- The problem is that I don't think it is possible to make this dependency
-- work for open type families
instance forall (d :: Dom) (q :: ParSort) (r :: Sort)
              . r ~ Neu => Sing ElimSort '(d, q, r, Neu) where
  fill = Spn

instance forall (q :: ParSort) (r :: Sort) (s :: ParSort)
              . r ~ Neu => Sing ElimSort '(Sem, q, r, Par s) where
  fill = Stk

instance forall (q :: ParSort) (s :: ParSort)
              . Sing ElimSort '(Syn, q, Neu, Par s) where
  fill = Stk

instance forall (q :: ParSort) (r :: ParSort) (s :: ParSort)
              . r ~ q => Sing ElimSort '(Syn, q, (Par r), (Par s)) 
              where
  fill = Rdx

-- I would like to make these 'recover' methods part of a typeclass also,
-- but it seems tricky to generalise over variadic number of arguments without
-- definitional eta
recoverSort :: SSort q -> Dict (Sing SSort q)
recoverSort SPar = Ev
recoverSort SNeu = Ev

recoverElim :: ElimSort d q r s -> Dict (Sing ElimSort '(d, q, r, s))
recoverElim Rdx = Ev
recoverElim Spn = Ev
-- This is very safe trust me bro
recoverElim @d Stk 
  | Refl <- unsafeCoerce @(d :~: d) @(d :~: Syn) Refl
  = Ev

fill2 :: (Sing f i, Sing g j) => (Ap f i, Ap g j)
fill2 = (fill, fill)

fill3 :: (Sing f i, Sing g j, Sing h k) => (Ap f i, Ap g j, Ap h k)
fill3 = (fill, fill, fill)

-- I don't like punning
type Pair a b = (a, b)
type List a   = [a]

type data Nat = S Nat | Z

type family n + m where
  Z   + m = m
  S n + m = S (n + m)

data SNat n where
  SS :: SNat n -> SNat (S n)
  SZ :: SNat Z

-- 'Bot'tom
type Bot = True ~ False

data Var n where
  VZ :: Var (S n)
  VS :: Var n -> Var (S n)
deriving instance Eq (Var n)

type data ParSort = B | U | Pi | Id

-- 'Neu'tral or 'Par'tisan
type data Sort = Neu | Par ParSort

-- Note we don't include evidence of the 'ParSort'. 
-- It turns out this is unnecessary (and actually unrecoverable from 
-- e.g. 'Stk' and 'Rdx')
data SSort q where
  SNeu :: SSort Neu
  SPar :: SSort (Par q)

-- Spine, Stuck, or Redex
-- Terms in the semantic domain should not contain redexes
data ElimSort d q r s where
  Spn :: ElimSort d   q Neu     Neu
  Stk :: ElimSort d   q Neu     (Par s)
  Rdx :: ElimSort Syn q (Par q) (Par r)


data (<=) q r where
  FromNeu :: Neu   <= q
  FromPar :: Par q <= q

-- 'Dom'ain: 'Syn'tax or 'Sem'antics
type data Dom = Syn | Sem

data Body d q g where
  Bo :: {unbo :: Model Syn (Par q) (S g)} -> Body Syn q g
  Yo :: {
    unyo :: forall g' r. OPE g' g -> Model Sem (Par r) g' 
          -> Model Sem (Par q) g'
  } -> Body Sem q g

deriving instance Show (SSort q)
deriving instance Show (Var g)
deriving instance Show (ElimSort d q r s)
deriving instance Show (Body Syn q g)
deriving instance Show (Model Syn q g)

data Model d q g where
  Lam   :: Model d (Par U) g -> Body d q g -> Model d (Par Pi) g
  U     :: Model d (Par U) g
  B     :: Model d (Par U) g
  Pi    :: Model d (Par U) g -> Body d U g -> Model d (Par U) g
  AppEl :: ElimSort d Pi pi r 
        -> Model d pi g -> Model d (Par q) g -> Model d r g
  IfEl  :: ElimSort d B b s
        -> Body d U g -> Model d b g -> Model d (Par q) g -> Model d (Par r) g 
        -> Model d s g
  JEl   :: ElimSort d Id id r
        -> Body d U g -> Model d id g -> Model d (Par q) g 
        -> Model d r g 
  Var   :: Var g -> Model d q g
  TT    :: Model d (Par B) g
  FF    :: Model d (Par B) g
  Id    :: Model d (Par U) g -> Model d (Par q) g -> Model d (Par r) g 
        -> Model d (Par U) g
  Rfl   :: Model d (Par q) g -> Model d (Par Id) g

type Tm    = Model Syn
type Ty    = Tm (Par U)
type Ne  q = Model Sem Neu
type Val q = Model Sem (Par q)
type VTy   = Val U

recoverSub :: q <= r -> Dict (Sing (<=) '(q, r))
recoverSub FromNeu = Ev
recoverSub FromPar = Ev

elimSortSub :: ElimSort d q r s -> r <= q
elimSortSub Rdx = FromPar
elimSortSub Spn = FromNeu
elimSortSub Stk = FromNeu

recoverAllElim :: ElimSort d q r s 
               -> Dict ( Sing ElimSort '(d, q, r, s)
                       , Sing (<=) '(r, q)
                       , Sing SSort r)
recoverAllElim el@(elimSortSub -> sub) 
  | Ev <- recoverElim el 
  , Ev <- recoverSub sub
  , Ev <- recoverSort (subSort sub)
  = Ev

pattern RecSort <- (recoverSort -> Ev)
  where RecSort = fill

pattern RecElim <- (recoverAllElim -> Ev)
  where RecElim = fill

pattern App t u = AppEl RecElim t u

pattern If m t u v = IfEl RecElim m t u v

pattern J m p t = JEl RecElim m p t

{-# COMPLETE Lam, U, B, Pi, App, If, Var, TT, FF, Id, Rfl, J #-}

data OPE d g where
  Eps  :: OPE Z Z
  Keep :: OPE d g -> OPE (S d) (S g)
  Drop :: OPE d g -> OPE (S d) g

idOPE :: SNat g -> OPE g g
idOPE SZ = Eps
idOPE (SS n) = Keep (idOPE n)

wkOPE :: SNat g -> OPE (S g) g
wkOPE n = Drop (idOPE n)

comOPE :: OPE d g -> OPE x d -> OPE x g
comOPE Eps       s2        = s2
comOPE (Keep s1) (Keep s2) = Keep (comOPE s1 s2)
comOPE (Drop s1) (Keep s2) = Drop (comOPE s1 s2)
comOPE s1        (Drop s2) = Drop (comOPE s1 s2)

data Env d g where
  Emp  :: Env d Z
  (:<) :: Env d g -> Val q d -> Env d (S g)

envLen :: Env d g -> SNat g
envLen Emp      = SZ
envLen (r :< _) = SS (envLen r)

data Ctx g where
  Nil  :: Ctx Z
  (:.) :: Ctx g -> VTy g -> Ctx (S g)

ctxLen :: Ctx g -> SNat g
ctxLen Nil      = SZ
ctxLen (g :. _) = SS (ctxLen g)

renBody :: OPE g2 g1 -> Body d q g1 -> Body d q g2
renBody s (Bo t) = Bo $ ren (Keep s) t
renBody s (Yo t) = Yo $ t . comOPE s

ren :: OPE g2 g1 -> Model d q g1 -> Model d q g2
ren _ U            = U
ren _ B            = B
ren s (Pi a b)     = Pi  (ren s a) (renBody s b)
ren s (Id a x y)   = Id (ren s a) (ren s x) (ren s y)
ren s (Lam a t)    = Lam (ren s a) (renBody s t)
ren s (App t u)    = App (ren s t) (ren s u)
ren s (If m t u v) = If (renBody s m) (ren s t) (ren s u) (ren s v)
-- Technically I think the type is inferrable from the motive, but that seems
-- kinda crazy to rely on
ren s (J m p t)    = J (renBody s m) (ren s p) (ren s t)
ren s (Var i)      = Var (renVar s i)
ren _ TT           = TT
ren _ FF           = FF
ren s (Rfl t)      = Rfl (ren s t)

renVar :: OPE d g -> Var g -> Var d
renVar (Keep _) VZ     = VZ
renVar (Drop s) i      = VS (renVar s i)
renVar (Keep s) (VS i) = VS (renVar s i)
renVar Eps i = case i of

renEnv :: OPE x d -> Env d g -> Env x g
renEnv _ Emp = Emp
renEnv s (r :< t) = renEnv s r :< ren s t

data UnkVal g = forall q. Ex {proj :: Model Sem (Par q) g}

type family PresVal q g = r | r -> q g where
  PresVal (Par q) g = Val q g
  PresVal Neu     g = UnkVal g

recoverElimSort :: ElimSort d q r s -> SSort s
recoverElimSort Spn = SNeu
recoverElimSort Stk = SPar
recoverElimSort Rdx = SPar

presTM :: SSort q -> UnkVal g -> PresVal q g
presTM SPar (Ex t) = coeTM t
presTM SNeu t      = t

presElim :: q <= r -> PresVal q g -> Val r g
presElim FromNeu (Ex t) = coeTM t
presElim FromPar t      = t

-- Trust me bro
coeTM :: Model d q1 g -> Model d q2 g
coeTM = unsafeCoerce

lookup :: Env d g -> Var g -> UnkVal d
lookup (_ :< t) VZ     = Ex t
lookup (r :< _) (VS i) = lookup r i
lookup Emp      i      = case i of

lookupTy :: Ctx g -> Var g -> VTy g
lookupTy (g :. a) VZ     = ren (wkOPE (ctxLen g)) a
lookupTy (g :. _) (VS i) = ren (wkOPE (ctxLen g)) (lookupTy g i)
lookupTy Nil i = case i of

appVal :: SNat g -> Val Pi g -> Val q g -> UnkVal g
appVal g (Lam _ (Yo t))         u = Ex $ t (idOPE g) u
appVal _ (AppEl Stk t1 t2)      u = Ex $ App (App t1 t2) u
appVal _ (IfEl Stk t1 t2 t3 t4) u = Ex $ App (If t1 t2 t3 t4) u
appVal _ (JEl Stk t1 t2 t3)     u = Ex $ App (J t1 t2 t3) u
appVal _ (Var i)                u = Ex $ App (Var i) u

ifVal :: Body Sem U g -> Val B g -> Val q g -> Val r g -> UnkVal g
ifVal _ TT                     u _ = Ex $ u
ifVal _ FF                     _ v = Ex $ v
ifVal m (AppEl Stk t1 t2)      u v = Ex $ If m (App t1 t2) u v
ifVal m (IfEl Stk t1 t2 t3 t4) u v = Ex $ If m (If t1 t2 t3 t4) u v
ifVal m (JEl Stk t1 t2 t3)     u v = Ex $ If m (J t1 t2 t3) u v
ifVal m (Var i)                u v = Ex $ If m (Var i) u v

jVal :: Body Sem U g -> Val Id g -> Val q g -> UnkVal g
jVal _ (Rfl _)                u = Ex $ u
jVal m (AppEl Stk t1 t2)      u = Ex $ J m (App t1 t2) u
jVal m (IfEl Stk t1 t2 t3 t4) u = Ex $ J m (If t1 t2 t3 t4) u
jVal m (JEl Stk t1 t2 t3)     u = Ex $ J m (J t1 t2 t3) u
jVal m (Var i)                u = Ex $ J m (Var i) u

wkStar :: SNat g -> SNat d -> OPE (g + d) g
wkStar SZ     SZ     = Eps
wkStar SZ     (SS d) = Drop (wkStar SZ d)
wkStar (SS g) d      = Keep (wkStar g d)

starWk :: SNat g -> SNat d -> OPE (d + g) g
starWk g SZ     = idOPE g
starWk g (SS d) = Drop (starWk g d)

toEnv :: OPE d g -> Env d g
toEnv s = renEnv s (idEnv (opeDom s))

parCom :: Env d g -> OPE d t -> Env d (g + t)
parCom Emp      s      = toEnv s
parCom (r :< t) s = parCom r s :< t

opeRng :: OPE d g -> SNat d
opeRng Eps      = SZ
opeRng (Drop s) = SS (opeRng s)
opeRng (Keep s) = SS (opeRng s)

opeDom :: OPE d g -> SNat g
opeDom Eps      = SZ
opeDom (Drop s) = opeDom s
opeDom (Keep s) = SS (opeDom s)

idEnv :: SNat g -> Env g g
idEnv SZ     = Emp
idEnv (SS n) = renEnv (wkOPE n) (idEnv n) :< Var VZ

subSort :: q <= r -> SSort q
subSort FromNeu = SNeu
subSort FromPar = SPar

evalPres :: (Sing (<=) '(q, r), Sing SSort q) 
         => SNat g2 -> Env g2 g1 -> Model d q g1 -> Val r g2
evalPres g r t = presElim fill (eval g r t)

evalBody :: Env g2 g1 -> Body d q g1 -> Body Sem q g2
evalBody r (Bo t) 
  = Yo \s u -> eval (opeRng s) (renEnv s r :< u) t
evalBody r (Yo t) 
  = Yo \s u -> 
  let g' = opeRng s 
   in eval g' (parCom (renEnv s r) (idOPE g')) 
              (t (wkStar d g') (ren (starWk g' d) u))
  where d = envLen r

eval :: Sing SSort q => SNat g2 -> Env g2 g1 -> Model d q g1 -> PresVal q g2
eval _ e (Var i) 
  = presTM fill $ lookup e i
eval g e (App t u)
  = presTM fill $ appVal g t' u'
  where t' = evalPres g e t
        u' = eval g e u
eval g e (If m t u v)
  = presTM fill $ ifVal m' t' u' v'
  where m' = evalBody e m
        t' = evalPres g e t
        u' = eval g e u
        v' = eval g e v
eval _ _ TT = TT
eval _ _ FF = FF
eval _ _ U  = U
eval _ _ B  = B
eval g e (Lam a t)
  = Lam a' (evalBody e t)
  where a' = eval g e a
eval g e (Pi a b)
  = Pi a' (evalBody e b)
  where a' = eval g e a
eval g e (Id a x y)
  = Id a' x' y'
  where a' = eval g e a
        x' = eval g e x
        y' = eval g e y
eval g e (Rfl x)
  = Rfl x'
  where x' = eval g e x
eval g e (J m p t)
  = presTM fill $ jVal m' p' t'
  where m' = evalBody e m
        p' = evalPres g e p
        t' = eval g e t

convBody :: SNat g -> Body Sem q g -> Body Sem r g -> Maybe ()
convBody g (Yo t) (Yo u) 
  = conv (SS g) (t (wkOPE g) (Var VZ)) (u (wkOPE g) (Var VZ))

conv :: SNat g -> Model Sem q g -> Model Sem r g -> Maybe ()
conv _ TT TT = pure ()
conv _ FF FF = pure ()
conv _ U  U  = pure ()
conv _ B  B  = pure ()
conv g (App t1 u1) (App t2 u2) = do
  conv g t1 t2
  conv g u1 u2
conv g (Lam a1 t1) (Lam a2 t2) = do
  conv g a1 a2
  convBody g t1 t2
conv g (Pi a1 b1) (Pi a2 b2) = do
  conv g a1 a2
  convBody g b1 b2
conv _ (Var i1) (Var i2) = guard $ i1 == i2
conv g (If m1 t1 u1 v1) (If m2 t2 u2 v2) = do
  convBody g m1 m2
  conv g t1 t2
  conv g u1 u2
  conv g v1 v2
conv _ _ _ = mempty

close :: VTy g -> Val q (S g) -> Body Sem q g
close _ t = Yo \s u -> eval (opeRng s) (toEnv s :< u) t

inferBody :: Ctx g -> Env g g -> VTy g -> Body Syn q g -> Maybe (VTy (S g))
inferBody g r a (Bo t) = infer (g :. a) (renEnv wk r :< Var VZ) t
  where wk = wkOPE (ctxLen g)

-- TODO: Use 'check' here instead of manual matching and 'conv' calls
infer :: Ctx g -> Env g g -> Tm q g -> Maybe (VTy g)
infer g r (Lam a t) = do
  U <- infer g r a
  let a' = eval l r a
  b <- inferBody g r a' t
  pure (Pi a' (close a' b))
  where l = ctxLen g
infer g r (Pi a b) = do
  U <- infer g r a
  let a' = eval l r a
  U <- inferBody g r a' b
  pure U
  where l = ctxLen g
infer g r (App t u) = do
  Pi a1 (Yo b1) <- infer g r t
  a2 <- infer g r u
  conv l a1 a2
  -- Perhaps 'infer' should return the 'eval'uated term...
  let u' = eval l r u
  pure (b1 (idOPE l) u')
  where l = ctxLen g
infer g r (If m t u v) = do
  B <- infer g r t
  a1 <- infer g r u
  a2 <- infer g r v
  U <- inferBody g r B m
  Yo m' <- pure $ evalBody r m
  let a1' = m' (idOPE l) TT
  let a2' = m' (idOPE l) FF
  conv l a1 a1'
  conv l a2 a2'
  let t' = evalPres @_ @B l r t
  pure $ m' (idOPE l) t'
  where l = ctxLen g
infer g r (Rfl x) = do
  a' <- infer g r x
  let x' = eval l r x
  pure (Id a' x' x')
  where l = ctxLen g
infer g r (Id a x y) = do
  U <- infer g r a
  let a1' = eval l r a
  a2' <- infer g r x
  conv l a1' a2'
  a3' <- infer g r y
  conv l a1' a3'
  pure U
  where l = ctxLen g
infer g r (J m p t) = do
  Id a x y <- infer g r p
  U <- inferBody g r a m
  mx1' <- infer g r t
  -- Todo can/should we eval in context extended with 'x' directly?
  Yo m' <- pure $ evalBody r m
  let mx2' = m' (idOPE l) (eval l r x)
  conv l mx1' mx2'
  pure $ m' (idOPE l) (eval l r y)
  where l = ctxLen g
infer g _ (Var i)   = pure $ lookupTy g i
infer _ _ TT        = pure B
infer _ _ FF        = pure B
infer _ _ B         = pure U
infer _ _ U         = pure U

check :: Ctx g -> Env g g -> Tm q g -> Ty g -> Maybe ()
check g r t a = do
  a' <- infer g r t
  conv l (eval l r a) a'
  where l = ctxLen g

reifyBody :: SNat g -> Body Sem q g -> Body Syn q g
reifyBody g (Yo t) = Bo (reify (SS g) (t (wkOPE g) (Var VZ)))

reify :: SNat g -> Model Sem q g -> Model Syn q g
reify _ (Var i)         = Var i
reify g (IfEl Stk m t u v) 
  = If (reifyBody g m) (reify g t) (reify g u) (reify g v)
reify g (IfEl Spn m t u v) 
  = If (reifyBody g m) (reify g t) (reify g u) (reify g v)
reify g (AppEl Stk t u) = App (reify g t) (reify g u)
reify g (AppEl Spn t u) = App (reify g t) (reify g u)
reify g (JEl Stk m p t) = J (reifyBody g m) (reify g p) (reify g t)
reify g (JEl Spn m p t) = J (reifyBody g m) (reify g p) (reify g t)   
reify g (Lam a t)       = Lam (reify g a) (reifyBody g t)
reify g (Pi a b)        = Pi (reify g a) (reifyBody g b)
reify g (Id a x y)      = Id (reify g a) (reify g x) (reify g y)
reify g (Rfl x)         = Rfl (reify g x)
reify _ TT              = TT
reify _ FF              = FF
reify _ U               = U
reify _ B               = B

var :: Var g -> Model d Neu g
var = Var @_ @_ @Neu

example :: Tm (Par Pi) Z
example = Lam B (Bo (Var VZ))

not :: Model Syn (Par Pi) g
not = Lam B (Bo (If (Bo B) (var VZ) FF TT))

proof :: Model Syn (Par Pi) g
proof = Lam B (Bo (If (Bo (Id B (Var VZ) (App not (App not (Var VZ))))) 
              (var VZ) (Rfl TT) (Rfl FF)))
