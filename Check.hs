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

type instance Ap SNat n = SNat n

instance Sing SNat Z where
  fill = SZ

instance Sing SNat n => Sing SNat (S n) where
  fill = SS fill

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
-- fill @ElimSort @'(d, q, r, s) = case s of
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

data Var n where
  VZ :: Var (S n)
  VS :: Var n -> Var (S n)
deriving instance Eq (Var n)

type data ParSort = B | U | Pi | Id | Bot

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
    unyo :: forall g' r. Sing SNat g' => OPE g' g -> Model Sem (Par r) g' 
          -> Model Sem (Par q) g'
  } -> Body Sem q g

deriving instance Show (SSort q)

varToInt :: Var g -> Int
varToInt VZ     = 0
varToInt (VS i) = varToInt i + 1

instance Show (Var g) where
  show i = show $ varToInt i

deriving instance Show (ElimSort d q r s)
instance Show (Body Syn q g) where
  show (Bo t) = show t

parens :: String -> String
parens s = "(" <> s <> ")"

instance Show (Model Syn q g) where
  show (Lam _ t)    = "λ " <> show t
  show (Pi a b)     = "Π " <> parens (show a) <> " " <> parens (show b)
  show U            = "Type"
  show B            = "𝔹"
  show Bot          = "𝟘"
  show (App t u)    = parens (show t) <> " " <> parens (show u)
  show (If _ t u v) = "if " <> parens (show t) <> " then " 
                   <> parens (show u) <> " else " 
                   <> parens (show v) <> ")"
  show (J _ p t)    = "transp " <> parens (show p) <> " " <> parens (show t)
  show (Expl _ p)   = "! " <> parens (show p)
  show (Var i)      = "`" <> show i
  show TT           = "True"
  show FF           = "False"
  show (Id _ x y)   = parens (show x) <> " = " <> parens (show y)
  show (Rfl _)      = "Refl"

data Spine d q r g where
  AppSp  :: Model d pi g -> Model d (Par q) g -> Spine d Pi pi g
  IfSp   :: Body d U g -> Model d b g -> Model d (Par q) g -> Model d (Par r) g 
         -> Spine d B b g
  JSp    :: Body d U g -> Model d id g -> Model d (Par q) g 
         -> Spine d Id id g 
  ExplSp :: Model d (Par U) g -> Model d bot g -> Spine d Bot bot g

data Model d q g where
  Lam :: Model d (Par U) g -> Body d q g -> Model d (Par Pi) g
  U   :: Model d (Par U) g
  B   :: Model d (Par U) g
  Bot :: Model d (Par U) g
  Pi  :: Model d (Par U) g -> Body d U g -> Model d (Par U) g
  El  :: ElimSort d q r s -> Spine d q r g -> Model d s g
  -- Variables really should go in 'Spine'...
  Var :: Var g -> Model d q g
  TT  :: Model d (Par B) g
  FF  :: Model d (Par B) g
  Id  :: Model d (Par U) g -> Model d (Par q) g -> Model d (Par r) g 
      -> Model d (Par U) g
  Rfl :: Model d (Par q) g -> Model d (Par Id) g

type Tm    = Model Syn
type Ty    = Tm (Par U)
type Ne    = Model Sem Neu
type Val q = Model Sem (Par q)
type VBody = Body Sem
type VTy   = Val U

recoverNat :: SNat n -> Dict (Sing SNat n)
recoverNat SZ     = Ev
recoverNat (SS n)
  | Ev <- recoverNat n
  = Ev

addNat :: SNat n -> SNat m -> SNat (n + m)
addNat SZ     m = m
addNat (SS n) m = SS $ addNat n m

recoverSub :: q <= r -> Dict (Sing (<=) '(q, r))
recoverSub FromNeu = Ev
recoverSub FromPar = Ev

elimSortSub :: ElimSort d q r s -> r <= q
elimSortSub Rdx = FromPar
elimSortSub Spn = FromNeu
elimSortSub Stk = FromNeu

recoverAllElim :: ElimSort d q r s 
               -> Dict (Sing ElimSort '(d, q, r, s)
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
                => (Sing ElimSort '(d, q, r, s), Sing (<=) '(r, q)
                   ,Sing SSort r) 
                => ElimSort d q r s
pattern RecElim <- (recoverAllElim -> Ev)
  where RecElim = fill

pattern App t u = El RecElim (AppSp t u)

pattern If m t u v = El RecElim (IfSp m t u v)

pattern J m p t = El RecElim (JSp m p t)

pattern Expl m p = El RecElim (ExplSp m p)

pattern Ne :: () => () => Ne g -> Val q g
pattern Ne t <- El Stk (El Spn -> t)
  where Ne (El Spn t) = El Stk t
        Ne (Var i)    = Var i

pattern AppNe :: () => () => Ne g -> Val q g -> Ne g
pattern AppNe t u = El Spn (AppSp t u)

pattern IfNe :: () => () => VBody U g -> Ne g -> Val q g -> Val r g -> Ne g
pattern IfNe m t u v = El Spn (IfSp m t u v)

pattern JNe :: () => () => VBody U g -> Ne g -> Val q g -> Ne g
pattern JNe m p t = El Spn (JSp m p t)

pattern ExplNe :: () => () => Val U g -> Ne g -> Ne g
pattern ExplNe m t = El Spn (ExplSp m t)

{-# COMPLETE AppNe, IfNe, JNe, ExplNe, Var #-}
{-# COMPLETE Lam, U, B, Bot, Pi, Var, TT, FF, Id, Rfl, Ne #-}
{-# COMPLETE Lam, U, B, Bot, Pi, App, If, Var, TT, FF, Id, Rfl, J, Expl #-}

data OPE d g where
  Eps  :: OPE Z Z
  Keep :: OPE d g -> OPE (S d) (S g)
  Drop :: OPE d g -> OPE (S d) g

idOPE :: SNat g -> OPE g g
idOPE SZ     = Eps
idOPE (SS n) = Keep (idOPE n)

wkOPE :: Sing SNat g => OPE (S g) g
wkOPE = Drop (idOPE fill)

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

renBody :: OPE g2 g1 -> Body d q g1 -> Body d q g2
renBody s (Bo t) = Bo $ ren (Keep s) t
renBody s (Yo t) = Yo $ t . comOPE s

ren :: OPE g2 g1 -> Model d q g1 -> Model d q g2
ren _ U            = U
ren _ B            = B
ren _ Bot          = Bot
ren s (Pi a b)     = Pi  (ren s a) (renBody s b)
ren s (Id a x y)   = Id (ren s a) (ren s x) (ren s y)
ren s (Lam a t)    = Lam (ren s a) (renBody s t)
ren s (App t u)    = App (ren s t) (ren s u)
ren s (If m t u v) = If (renBody s m) (ren s t) (ren s u) (ren s v)
-- Technically I think the type is inferrable from the motive, but that seems
-- kinda crazy to rely on
ren s (J m p t)    = J (renBody s m) (ren s p) (ren s t)
ren s (Expl m p)   = Expl (ren s m) (ren s p)
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

lookupTy :: Sing SNat g => Ctx g -> Var g -> VTy g
lookupTy @g (_ :. a) VZ     
  | SS n <- fill @SNat @g 
  , Ev   <- recoverNat n
  = ren wkOPE a
lookupTy @g (g :. _) (VS i) 
  | SS n <- fill @SNat @g 
  , Ev   <- recoverNat n
  = ren wkOPE (lookupTy g i)
lookupTy Nil i = case i of

appVal :: Sing SNat g => Val Pi g -> Val q g -> UnkVal g
appVal (Lam _ (Yo t)) u = Ex $ t (idOPE fill) u
appVal (El Stk t)     u = Ex $ App (El Spn t) u
appVal (Var i)        u = Ex $ App (Var i) u

ifVal :: Body Sem U g -> Val B g -> Val q g -> Val r g -> UnkVal g
ifVal _ TT         u _ = Ex $ u
ifVal _ FF         _ v = Ex $ v
ifVal m (El Stk t) u v = Ex $ If m (El Spn t) u v
ifVal m (Var i)    u v = Ex $ If m (Var i) u v

jVal :: Body Sem U g -> Val Id g -> Val q g -> UnkVal g
jVal _ (Rfl _)    u = Ex $ u
jVal m (El Stk t) u = Ex $ J m (El Spn t) u
jVal m (Var i)    u = Ex $ J m (Var i) u

explVal :: Val U g -> Val Bot g -> UnkVal g
explVal m (El Stk t) = Ex $ Expl m (El Spn t)
explVal m (Var i)    = Ex $ Expl m (Var i)

wkStar :: SNat g -> SNat d -> OPE (g + d) g
wkStar SZ     SZ     = Eps
wkStar SZ     (SS d) = Drop (wkStar SZ d)
wkStar (SS g) d      = Keep (wkStar g d)

starWk :: SNat g -> SNat d -> OPE (d + g) g
starWk g SZ     = idOPE g
starWk g (SS d) = Drop (starWk g d)

toEnv :: Sing SNat g => OPE d g -> Env d g
toEnv s = renEnv s (idEnv fill)

parCom :: Sing SNat t => Env d g -> OPE d t -> Env d (g + t)
parCom Emp      s = toEnv s
parCom (r :< t) s = parCom r s :< t

idEnv :: SNat g -> Env g g
idEnv SZ     = Emp
idEnv (SS n) 
  | Ev <- recoverNat n 
  = renEnv wkOPE (idEnv n) :< Var VZ

subSort :: q <= r -> SSort q
subSort FromNeu = SNeu
subSort FromPar = SPar

evalPres :: (Sing (<=) '(q, r), Sing SSort q, Sing SNat g2) 
         => Env g2 g1 -> Model d q g1 -> Val r g2
evalPres r t = presElim fill (eval r t)

evalBody :: Sing SNat g2 => Env g2 g1 -> Body d q g1 -> Body Sem q g2
evalBody r (Bo t) 
  = Yo \s u -> eval (renEnv s r :< u) t
evalBody r (Yo t) 
  = Yo \ @g' s u -> case recoverNat (addNat @_ @g' (envLen r) fill) of 
              Ev -> eval (parCom (renEnv s r) (idOPE fill)) 
                         (t (wkStar @_ @g' d fill) (ren (starWk @g' fill d) u))
  where d = envLen r

eval :: (Sing SNat g2, Sing SSort q) 
     => Env g2 g1 -> Model d q g1 -> PresVal q g2
eval r (Var i) 
  = presTM fill $ lookup r i
eval r (App t u)
  = presTM fill $ appVal t' u'
  where t' = evalPres r t
        u' = eval r u
eval r (If m t u v)
  = presTM fill $ ifVal m' t' u' v'
  where m' = evalBody r m
        t' = evalPres r t
        u' = eval r u
        v' = eval r v
eval _ TT = TT
eval _ FF = FF
eval _ U  = U
eval _ B  = B
eval _ Bot = Bot
eval r (Lam a t)
  = Lam a' (evalBody r t)
  where a' = eval r a
eval r (Pi a b)
  = Pi a' (evalBody r b)
  where a' = eval r a
eval r (Id a x y)
  = Id a' x' y'
  where a' = eval r a
        x' = eval r x
        y' = eval r y
eval r (Rfl x)
  = Rfl x'
  where x' = eval r x
eval r (J m p t)
  = presTM fill $ jVal m' p' t'
  where m' = evalBody r m
        p' = evalPres r p
        t' = eval r t
eval r (Expl m p)
  = presTM fill $ explVal m' p'
  where m' = eval r m
        p' = evalPres r p

type Error = String

throw :: Error -> TCM a
throw = Failure

orThrow :: Bool -> Error -> TCM ()
orThrow True  _ = pure ()
orThrow False e = throw e

-- Temporary hack
instance MonadFail TCM where
  fail s = throw s

convBody :: Sing SNat g => Body Sem q g -> Body Sem r g -> TCM ()
convBody (Yo t) (Yo u) 
  = conv (t wkOPE (Var VZ)) (u wkOPE (Var VZ))

convNe :: Sing SNat g => Ne g -> Ne g -> TCM ()
convNe (AppNe t1 u1) (AppNe t2 u2) = do
  convNe t1 t2
  conv u1 u2
convNe (IfNe m1 t1 u1 v1) (IfNe m2 t2 u2 v2) = do
  convBody m1 m2
  convNe t1 t2
  conv u1 u2
  conv v1 v2
convNe (JNe m1 p1 t1) (JNe m2 p2 t2) = do
  convBody m1 m2
  convNe p1 p2
  conv t1 t2
convNe (ExplNe m1 p1) (ExplNe m2 p2) = do
  conv m1 m2
  convNe p1 p2
convNe (Var i1) (Var i2)
  | i1 == i2 = pure ()
convNe _ _ = pure ()

conv :: Sing SNat g => Val q g -> Val r g -> TCM ()
conv TT  TT  = pure ()
conv FF  FF  = pure ()
conv U   U   = pure ()
conv B   B   = pure ()
conv Bot Bot = pure ()
conv (Lam a1 t1) (Lam a2 t2) = do
  conv a1 a2
  convBody t1 t2
conv (Pi a1 b1) (Pi a2 b2) = do
  conv a1 a2
  convBody b1 b2
conv (Var i1) (Var i2)
  | i1 == i2 = pure ()
conv (Id a1 x1 y1) (Id a2 x2 y2) = do
  conv a1 a2
  conv x1 x2
  conv y1 y2
conv (Rfl x1) (Rfl x2) = do
  conv x1 x2
conv t u = throw 
  $ "Failed to match " <> show (reify t) ++ " with " 
                       <> show (reify u) <> "."

close :: Sing SNat g => VTy g -> Val q (S g) -> Body Sem q g
close _ t = Yo \s u -> eval (toEnv s :< u) t

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

inferBody :: Sing SNat g => Ctx g -> Env g g -> VTy g -> Body Syn q g 
          -> TCM (VTy (S g))
inferBody g r a (Bo t) = infer (g :. a) (renEnv wkOPE r :< Var VZ) t

-- TODO: Use 'check' here instead of manual matching and 'conv' calls
infer :: Sing SNat g => Ctx g -> Env g g -> Tm q g -> TCM (VTy g)
infer g r (Lam a t) = do
  check g r a U
  let a' = eval r a
  b <- inferBody g r a' t
  pure (Pi a' (close a' b))
infer g r (Pi a b) = do
  check g r a U
  let a' = eval r a
  checkBody g r a' b U
  pure U
infer g r (App t u) = do
  Pi a1 (Yo b1) <- infer g r t
  a2 <- infer g r u
  conv a1 a2
  -- Perhaps 'infer' should return the 'eval'uated term...
  let u' = eval r u
  pure (b1 (idOPE fill) u')
infer g r (If m t u v) = do
  check g r t B
  a1 <- infer g r u
  a2 <- infer g r v
  checkBody g r B m U
  Yo m' <- pure $ evalBody r m
  let a1' = m' (idOPE fill) TT
  let a2' = m' (idOPE fill) FF
  conv a1 a1'
  conv a2 a2'
  let t' = evalPres @_ @B r t
  pure $ m' (idOPE fill) t'
infer g r (Rfl x) = do
  a' <- infer g r x
  let x' = eval r x
  pure (Id a' x' x')
infer g r (Id a x y) = do
  U <- infer g r a
  let a1' = eval r a
  a2' <- infer g r x
  conv a1' a2'
  a3' <- infer g r y
  conv a1' a3'
  pure U
infer g r (J m p t) = do
  Id a x y <- infer g r p
  checkBody g r a m U
  mx1' <- infer g r t
  -- Todo can/should we eval in context extended with 'x' directly?
  Yo m' <- pure $ evalBody r m
  let mx2' = m' (idOPE fill) (eval r x)
  conv mx1' mx2'
  pure $ m' (idOPE fill) (eval r y)
infer g r (Expl m p) = do
  check g r p Bot
  check g r m U
  pure (eval r m)
infer g _ (Var i)   = pure $ lookupTy g i
infer _ _ TT        = pure B
infer _ _ FF        = pure B
infer _ _ B         = pure U
infer _ _ Bot       = pure U
-- Type in type!
infer _ _ U         = pure U

check :: Sing SNat g => Ctx g -> Env g g -> Tm q g -> Ty g -> TCM ()
check g r t a = do
  a' <- infer g r t
  conv (eval r a) a'

checkBody :: Sing SNat g 
          => Ctx g -> Env g g -> VTy g -> Body Syn q g -> Ty (S g) -> TCM ()
checkBody g r a t b = do
  b' <- inferBody g r a t
  conv (eval (renEnv wkOPE r :< Var VZ) b) b'

reifyBody :: Sing SNat g => Body Sem q g -> Body Syn q g
reifyBody (Yo t) = Bo (reify (t wkOPE (Var VZ)))

reifyNe :: Sing SNat g => Ne g -> Model Syn (Par q) g
reifyNe (Var i)      = Var i
reifyNe (IfNe m t u v) 
  = If (reifyBody m) (reifyNe t) (reify u) (reify v)
reifyNe (AppNe t u)  = App (reifyNe t) (reify u)
reifyNe (JNe m p t)  = J (reifyBody m) (reifyNe p) (reify t)
reifyNe (ExplNe m p) = Expl (reify m) (reifyNe p)

reify :: Sing SNat g => Val q g -> Model Syn (Par q) g
reify (Var i)    = Var i
reify (Ne t)     = reifyNe t
reify (Lam a t)  = Lam (reify a) (reifyBody t)
reify (Pi a b)   = Pi (reify a) (reifyBody b)
reify (Id a x y) = Id (reify a) (reify x) (reify y)
reify (Rfl x)    = Rfl (reify x)
reify TT         = TT
reify FF         = FF
reify U          = U
reify B          = B
reify Bot        = Bot

var :: Var g -> Model d Neu g
var = Var @_ @_ @Neu

-- \b. b
identity :: Tm (Par Pi) g
identity = Lam B (Bo (Var VZ))

-- \b. if b then False else True
not :: Model Syn (Par Pi) g
not = Lam B (Bo (If (Bo B) (var VZ) FF TT))

-- '(b : B) -> b = not (not b)'
notProofTy :: Model Syn (Par U) g
notProofTy = Pi B (Bo (Id B (Var VZ) (App not (App not (Var VZ)))))

-- '\b. if b then Refl else Refl'
notProof :: Model Syn (Par Pi) g
notProof = Lam B (Bo (If (Bo (Id B (Var VZ) (App not (App not (Var VZ))))) 
              (var VZ) (Rfl TT) (Rfl FF)))

-- '\x y p. J (z. z = x) p Refl'
symProof :: Model Syn (Par Pi) g
symProof = Lam B $ Bo $ Lam B $ Bo $ Lam (Id B (Var $ VS VZ) (Var VZ)) $ Bo 
         $ J (Bo $ Id B (Var VZ) (Var (VS $ VS $ VS VZ))) (var VZ) 
             (Rfl (Var $ VS $ VS VZ))

-- We don't have a unit type, but we can very easily construct proofs of
-- 'true = true'!
unit :: Model Syn (Par U) g
unit = Id B TT TT

-- '\b. if b then Unit else Bot' 
isTrue :: Model Syn (Par Pi) g
isTrue = Lam B $ Bo $ If (Bo U) (var VZ) unit Bot

-- '\p. J (z. isTrue z) p tt'
disj :: Model Syn (Par Pi) g
disj = Lam (Id B TT FF) $ Bo 
     $ J (Bo (App isTrue (Var VZ))) (var VZ) (Rfl TT)
