{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
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

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-missing-pattern-synonym-signatures #-}

import Prelude hiding (lookup, not)
import Prelude qualified as P
import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)
import Data.Data ((:~:)(..))
import Data.Maybe (fromMaybe, maybeToList)
import Data.Bifunctor (Bifunctor(..))

-- Open type families are cringe, but additional typeclasses are also cringe
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

-- Note we don't include evidence of the 'ParSort'. 
-- It turns out this is unnecessary (and actually unrecoverable from 
-- e.g. 'Stk' and 'Rdx')
data SSort q where
  SNeu :: SSort Neu
  SPar :: SSort (Par q)

data Var n where
  VZ :: Var (S n)
  VS :: Var n -> Var (S n)
deriving instance Eq (Var n)

type data ParSort = B | U | Pi | Id | Bot | V

-- 'Neu'tral or 'Par'tisan
type data Sort = Neu | Par ParSort

-- Spine, Stuck, or Redex
-- Terms in the semantic domain should not contain redexes
-- Terms in general should not contain "obviously" ill-typed redexes
data ElimSort d q r s where
  Spn :: ElimSort d   q Neu     Neu
  Stk :: ElimSort d   q Neu     (Par s)
  Rdx :: ElimSort Syn q (Par q) (Par r)

-- 'Dom'ain: 'Syn'tax (terms) or 'Sem'antics (values)
type data Dom = Syn | Sem

data Body d q g where
  Inc :: {uninc :: Model Syn (Par q) (S g)} -> Body Syn q g
  Clo :: {
    unclo :: forall g' r. Sing SNat g' => OPE g' g -> EqMap g' 
          -> Model Sem (Par r) g' -> Model Sem (Par q) g'
  } -> Body Sem q g

data Spine d q r g where
  AppS    :: Model d pi g -> Model d (Par q) g -> Spine d Pi pi g
  IfS     :: Body d U g -> Model d b g -> Model d (Par q) g -> Model d (Par r) g 
          -> Spine d B b g
  TranspS :: Body d U g -> Model d id g -> Model d (Par q) g 
          -> Spine d Id id g 
  ExplS   :: Model d (Par U) g -> Model d bot g -> Spine d Bot bot g
  VarS    :: Var g -> Spine d V Neu g

data Model d q g where
  Lam :: Model d (Par U) g -> Body d q g -> Model d (Par Pi) g
  U   :: Model d (Par U) g
  B   :: Model d (Par U) g
  Bot :: Model d (Par U) g
  Pi  :: Model d (Par U) g -> Body d U g -> Model d (Par U) g
  El  :: ElimSort d q r s -> Spine d q r g -> Model d s g
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

data (<=) q r where
  FromNeu :: Neu   <= q
  FromPar :: Par q <= q

deriving instance Show (SSort q)

varToInt :: Var g -> Int
varToInt VZ     = 0
varToInt (VS i) = varToInt i + 1

instance Show (Var g) where
  show i = show $ varToInt i

deriving instance Show (ElimSort d q r s)
instance Show (Body Syn q g) where
  show (Inc t) = show t

parens :: String -> String
parens s = "(" <> s <> ")"

instance Show (Model Syn q g) where
  show (Lam _ t)      = "λ " <> show t
  show (Pi a b)       = "Π " <> parens (show a) <> " " <> parens (show b)
  show U              = "Type"
  show B              = "𝔹"
  show Bot            = "𝟘"
  show (App t u)      = parens (show t) <> " " <> parens (show u)
  show (If _ t u v)   = "if " <> parens (show t) <> " then " 
                     <> parens (show u) <> " else " 
                     <> parens (show v) <> ")"
  show (Transp _ p t) = "transp " <> parens (show p) <> " " <> parens (show t)
  show (Expl _ p)     = "! " <> parens (show p)
  show (Var i)        = "`" <> show i
  show TT             = "True"
  show FF             = "False"
  show (Id _ x y)     = parens (show x) <> " = " <> parens (show y)
  show (Rfl _)        = "Refl"

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

pattern App t u = El RecElim (AppS t u)
pattern If m t u v = El RecElim (IfS m t u v)
pattern Transp m p t = El RecElim (TranspS m p t)
pattern Expl m p = El RecElim (ExplS m p)
pattern Var i = El RecElim (VarS i)

pattern Ne :: () => () => Ne g -> Val q g
pattern Ne t <- El Stk (El Spn -> t)
  where Ne (El Spn t) = El Stk t

pattern VarNe :: () => () => Var g -> Ne g
pattern VarNe i = El Spn (VarS i)

pattern AppNe :: () => () => Ne g -> Val q g -> Ne g
pattern AppNe t u = El Spn (AppS t u)

pattern IfNe :: () => () => VBody U g -> Ne g -> Val q g -> Val r g -> Ne g
pattern IfNe m t u v = El Spn (IfS m t u v)

pattern TranspNe :: () => () => VBody U g -> Ne g -> Val q g -> Ne g
pattern TranspNe m p t = El Spn (TranspS m p t)

pattern ExplNe :: () => () => Val U g -> Ne g -> Ne g
pattern ExplNe m t = El Spn (ExplS m t)

{-# COMPLETE AppNe, IfNe, TranspNe, ExplNe, VarNe #-}
{-# COMPLETE Lam, U, B, Bot, Pi, TT, FF, Id, Rfl, Ne #-}
{-# COMPLETE Lam, U, B, Bot, Pi, App, If, Var, TT, FF, Id, Rfl, Transp, Expl #-}

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
renBody s (Inc t) = Inc $ ren (Keep s) t
renBody s (Clo t) = Clo $ t . comOPE s

ren :: OPE g2 g1 -> Model d q g1 -> Model d q g2
ren _ U              = U
ren _ B              = B
ren _ Bot            = Bot
ren s (Pi a b)       = Pi  (ren s a) (renBody s b)
ren s (Id a x y)     = Id (ren s a) (ren s x) (ren s y)
ren s (Lam a t)      = Lam (ren s a) (renBody s t)
ren s (App t u)      = App (ren s t) (ren s u)
ren s (If m t u v)   = If (renBody s m) (ren s t) (ren s u) (ren s v)
ren s (Transp m p t) = Transp (renBody s m) (ren s p) (ren s t)
ren s (Expl m p)     = Expl (ren s m) (ren s p)
ren s (Var i)        = Var (renVar s i)
ren _ TT             = TT
ren _ FF             = FF
ren s (Rfl t)        = Rfl (ren s t)

renVar :: OPE d g -> Var g -> Var d
renVar (Keep _) VZ     = VZ
renVar (Drop s) i      = VS (renVar s i)
renVar (Keep s) (VS i) = VS (renVar s i)
renVar Eps i = case i of

renEnv :: OPE x d -> Env d g -> Env x g
renEnv _ Emp = Emp
renEnv s (r :< t) = renEnv s r :< ren s t

data UnkVal g = forall q. Ex {proj :: Model Sem (Par q) g}

renUnk :: OPE d g -> UnkVal g -> UnkVal d
renUnk s (Ex t) = Ex (ren s t)

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

type EqMap g = [(Ne g, UnkVal g)]

iterFix :: Eq a => (a -> a) -> a -> a
iterFix f x = let x' = f x in if x == x' then x else iterFix f x'

-- TODO: To deal with arbitrary equations (i.e. neutral RHSs), we might need to 
-- reorient
mkEq :: Val q g -> Val r g -> Maybe (Ne g, UnkVal g)
mkEq (Ne t) u = pure (t, Ex u)
mkEq _      _ = Nothing

complWrtEqs :: Sing SNat g => Env g g -> EqMap g -> EqMap g -> EqMap g
complWrtEqs _ acc []       = acc
complWrtEqs r acc ((t, Ex u) : es)
  | Ex t' <- eval r es t
  , u'    <- eval r es u
  , e'    <- mkEq t' u'
  = complWrtEqs r (acc <> maybeToList e') es

complete :: Sing SNat g => Env g g -> EqMap g -> EqMap g
complete r es = iterFix (complWrtEqs r []) es

evalEnv :: Sing SNat d => Env d g -> EqMap d -> Env g t -> Env d t
evalEnv _ _  Emp       = Emp
evalEnv r es (ts :< t) = evalEnv r es ts :< eval r es t

addEq :: Sing SNat d => Env d g -> EqMap d -> Ne d -> Val q d 
      -> (Env d g, EqMap d)
addEq r es t u = (r', es'')
  where es'  = (t, Ex u) : es
        idE  = varEnv fill
        es'' = complete idE $ (t, Ex u) : es'
        idE' = idEnv es''
        r'   = evalEnv idE' es'' r

renEqMap :: OPE d g -> EqMap g -> EqMap d
renEqMap s = map (bimap (ren s) (renUnk s))

lookupNe :: Sing SNat g => EqMap g -> Ne g -> UnkVal g
lookupNe es t = fromMaybe (Ex (Ne t)) (P.lookup t es)

appVal :: Sing SNat g => EqMap g -> Val Pi g -> Val q g -> UnkVal g
appVal es (Lam _ (Clo t)) u = Ex $ t (idOPE fill) es u
appVal es (Ne t)      u     = lookupNe es $ App t u

ifVal :: Sing SNat g2
      => Env g2 g1 -> EqMap g2 -> Body Sem U g2 -> Val B g2 
      -> Model d (Par q) g1 -> Model d (Par r) g1 
      -> UnkVal g2
ifVal r es _ TT         u _ = Ex $ eval r es u
ifVal r es _ FF         _ v = Ex $ eval r es v
ifVal r es m (Ne t) u v     = lookupNe es $ If m t u' v'
  where (rT, esT) = addEq r es t TT
        (rF, esF) = addEq r es t FF
        u'  = eval rT esT u
        v'  = eval rF esF v

jVal :: Sing SNat g 
     => EqMap g -> Body Sem U g -> Val Id g -> Val q g -> UnkVal g
jVal _ _  (Rfl _)    u = Ex $ u
jVal es m (Ne t) u = lookupNe es $ Transp m t u

explVal :: Sing SNat g => EqMap g -> Val U g -> Val Bot g -> UnkVal g
explVal es m (Ne t) = lookupNe es $ Expl m t

wkStar :: SNat g -> SNat d -> OPE (g + d) g
wkStar SZ     SZ     = Eps
wkStar SZ     (SS d) = Drop (wkStar SZ d)
wkStar (SS g) d      = Keep (wkStar g d)

starWk :: SNat g -> SNat d -> OPE (d + g) g
starWk g SZ     = idOPE g
starWk g (SS d) = Drop (starWk g d)

toEnv :: (Sing SNat g, Sing SNat d) => EqMap d -> OPE d g -> Env d g
toEnv es s = rwVars es $ renEnv s $ varEnv fill

parCom :: (Sing SNat d, Sing SNat t) => Env d g -> EqMap d -> OPE d t 
       -> Env d (g + t)
parCom Emp      es s = toEnv es s
parCom (r :< t) es s = parCom r es s :< t

varEnv :: SNat g -> Env g g
varEnv SZ     = Emp
varEnv (SS n)
  | Ev <- recoverNat n 
  = renEnv wkOPE (varEnv n) :< Var VZ

-- Invariant: The passed-in environment should only contain variables
-- I think a refactor to capture this properly would be nice...
rwVars :: Sing SNat d => EqMap d -> Env d g -> Env d g
rwVars _  Emp          = Emp
rwVars es (ts :< Ne t)
  | Ex t' <- lookupNe es t
  = rwVars es ts :< t'
rwVars _ _ = error "ICE: Something went wrong!"

idEnv :: Sing SNat g => EqMap g -> Env g g
idEnv es = rwVars es (varEnv fill)

subSort :: q <= r -> SSort q
subSort FromNeu = SNeu
subSort FromPar = SPar

evalPres :: (Sing (<=) '(q, r), Sing SSort q, Sing SNat g2) 
         => Env g2 g1 -> EqMap g2 -> Model d q g1 -> Val r g2
evalPres r es t = presElim fill (eval r es t)

evalBody :: Sing SNat g2 => Env g2 g1 -> EqMap g2 -> Body d q g1 -> Body Sem q g2
evalBody r es (Inc t) 
  = Clo \s es' u -> eval (renEnv s r :< u) (renEqMap s es <> es') t
evalBody r es (Clo t) 
  = Clo \ @g' s es' u -> case recoverNat (addNat @_ @g' (envLen r) fill) of 
    Ev -> eval (parCom (renEnv s r) (es'') (idOPE fill)) es' 
               (t wk1 (renEqMap wk2 (es'' <> es')) (ren wk2 u))
      where es'' = renEqMap s es
            wk1 = wkStar @_ @g' d fill
            wk2 = starWk @g' fill d
  where d = envLen r

eval :: (Sing SNat g2, Sing SSort q) 
     => Env g2 g1 -> EqMap g2 -> Model d q g1 -> PresVal q g2
eval r _ (Var i) 
  = presTM fill $ lookup r i
eval r es (App t u)
  =  presTM fill $ appVal es t' u'
  where t' = evalPres r es t
        u' = eval r es u
eval r es (If m t u v)
  = presTM fill $ ifVal r es m' t' u v
  where m' = evalBody r es m
        t' = evalPres r es t
eval _ _ TT  = TT
eval _ _ FF  = FF
eval _ _ U   = U
eval _ _ B   = B
eval _ _ Bot = Bot
eval r es (Lam a t)
  = Lam a' t'
  where a' = eval r es a
        t' = evalBody r es t
eval r es (Pi a b)
  = Pi a' b'
  where a' = eval r es a
        b' = evalBody r es b
eval r es (Id a x y)
  = Id a' x' y'
  where a' = eval r es a
        x' = eval r es x
        y' = eval r es y
eval r es (Rfl x)
  = Rfl x'
  where x' = eval r es x
eval r es (Transp m p t)
  = presTM fill $ jVal es m' p' t'
  where m' = evalBody r es m
        p' = evalPres r es p
        t' = eval r es t
eval r es (Expl m p)
  = presTM fill $ explVal es m' p'
  where m' = eval r es m
        p' = evalPres r es p

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
convBody (Clo t) (Clo u) 
  = conv (t wkOPE [] (Var VZ)) (u wkOPE [] (Var VZ))

-- TODO: Switch from 'conv' to '=='
instance Sing SNat g => Eq (Ne g) where
  t == u = case convNe t u of
    Success _ -> True
    Failure _ -> False

instance Sing SNat g => Eq (UnkVal g) where
  Ex t == Ex u = case conv t u of
    Success _ -> True
    Failure _ -> False

instance Sing SNat g => Eq (Val q g) where
  t == u = Ex t == Ex u

convNe :: Sing SNat g => Ne g -> Ne g -> TCM ()
convNe (AppNe t1 u1) (AppNe t2 u2) = do
  convNe t1 t2
  conv u1 u2
convNe (IfNe m1 t1 u1 v1) (IfNe m2 t2 u2 v2) = do
  convBody m1 m2
  convNe t1 t2
  conv u1 u2
  conv v1 v2
convNe (TranspNe m1 p1 t1) (TranspNe m2 p2 t2) = do
  convBody m1 m2
  convNe p1 p2
  conv t1 t2
convNe (ExplNe m1 p1) (ExplNe m2 p2) = do
  conv m1 m2
  convNe p1 p2
convNe (VarNe i1) (VarNe i2)
  | i1 == i2 = pure ()
convNe t u 
  = throw $ "Failed to match " <> show (reifyNe t) ++ " with " 
                               <> show (reifyNe u) <> "."

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
conv (Id a1 x1 y1) (Id a2 x2 y2) = do
  conv a1 a2
  conv x1 x2
  conv y1 y2
conv (Rfl x1) (Rfl x2) = do
  conv x1 x2
conv (Ne t1) (Ne t2) = convNe t1 t2
conv t u 
  = throw $ "Failed to match " <> show (reify t) ++ " with " 
                               <> show (reify u) <> "."

close :: Sing SNat g => VTy g -> Val q (S g) -> Body Sem q g
close _ t = Clo \s es u -> eval (toEnv es s :< u) es t

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

inferBody :: Sing SNat g => Ctx g -> Env g g -> EqMap g -> VTy g -> Body Syn q g 
          -> TCM (VTy (S g))
inferBody g r es a (Inc t) 
  = infer (g :. a) (renEnv wkOPE r :< Var VZ) (renEqMap wkOPE es) t

-- TODO: Use 'check' here instead of manual matching and 'conv' calls
infer :: Sing SNat g => Ctx g -> Env g g -> EqMap g -> Tm q g -> TCM (VTy g)
infer g r es (Lam a t) = do
  check g r es a U
  let a' = eval r es a
  b <- inferBody g r es a' t
  pure (Pi a' (close a' b))
infer g r es (Pi a b) = do
  check g r es a U
  let a' = eval r es a
  checkBody g r es a' b U
  pure U
infer g r es (App t u) = do
  Pi a1 (Clo b1) <- infer g r es t
  a2 <- infer g r es u
  conv a1 a2
  -- Perhaps 'infer' should return the 'eval'uated term...
  let u' = eval r es u
  pure (b1 (idOPE fill) es u')
infer g r es (If m t u v) = do
  check g r es t B
  a1 <- infer g r es u
  a2 <- infer g r es v
  checkBody g r es B m U
  Clo m' <- pure $ evalBody r es m
  let a1' = m' (idOPE fill) es TT
  let a2' = m' (idOPE fill) es FF
  conv a1 a1'
  conv a2 a2'
  let t' = evalPres @_ @B r es t
  pure $ m' (idOPE fill) es t'
infer g r es (Rfl x) = do
  a' <- infer g r es x
  let x' = eval r es x
  pure (Id a' x' x')
infer g r es (Id a x y) = do
  U <- infer g r es a
  let a1' = eval r es a
  a2' <- infer g r es x
  conv a1' a2'
  a3' <- infer g r es y
  conv a1' a3'
  pure U
infer g r es (Transp m p t) = do
  Id a x y <- infer g r es p
  checkBody g r es a m U
  mx1' <- infer g r es t
  -- Todo can/should we eval in context extended with 'x' directly?
  Clo m' <- pure $ evalBody r es m
  let mx2' = m' (idOPE fill) es x
  conv mx1' mx2'
  pure $ m' (idOPE fill) es y
infer g r es (Expl m p) = do
  check g r es p Bot
  check g r es m U
  pure (eval r es m)
infer g _ _ (Var i)   = pure $ lookupTy g i
infer _ _ _ TT        = pure B
infer _ _ _ FF        = pure B
infer _ _ _ B         = pure U
infer _ _ _ Bot       = pure U
-- Type in type!
infer _ _ _ U         = pure U

check :: Sing SNat g => Ctx g -> Env g g -> EqMap g -> Tm q g -> Ty g -> TCM ()
check g r es t a = do
  a' <- infer g r es t
  conv (eval r es a) a'

checkBody :: Sing SNat g 
          => Ctx g -> Env g g -> EqMap g -> VTy g -> Body Syn q g -> Ty (S g) 
          -> TCM ()
checkBody g r es a t b = do
  b' <- inferBody g r es a t
  conv (eval (renEnv wkOPE r :< Var VZ) (renEqMap wkOPE es) b) b'

reifyBody :: Sing SNat g => Body Sem q g -> Body Syn q g
reifyBody (Clo t) = Inc $ reify (t wkOPE [] (Var VZ))

reifyNe :: Sing SNat g => Ne g -> Model Syn (Par q) g
reifyNe (VarNe i)    = Var i
reifyNe (IfNe m t u v) 
  = If (reifyBody m) (reifyNe t) (reify u) (reify v)
reifyNe (AppNe t u)  = App (reifyNe t) (reify u)
reifyNe (TranspNe m p t)  = Transp (reifyBody m) (reifyNe p) (reify t)
reifyNe (ExplNe m p) = Expl (reify m) (reifyNe p)

reify :: Sing SNat g => Val q g -> Model Syn (Par q) g
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

instance Sing SNat g => Show (Val q g) where
  show = show . reify

instance Sing SNat g => Show (Ne g) where 
  show = show . Ne

deriving instance Sing SNat g => Show (UnkVal g)

deriving instance Sing SNat d => Show (Env d g)

var :: Var g -> Model d Neu g
var = Var

-- \b. b
identity :: Tm (Par Pi) g
identity = Lam B $ Inc $ Var VZ

-- \b. if b then False else True
not :: Model Syn (Par Pi) g
not = Lam B $ Inc $ If (Inc B) (var VZ) FF TT

-- '(b : B) -> b = not (not b)'
notProofTy :: Model Syn (Par U) g
notProofTy = Pi B $ Inc $ Id B (Var VZ) (App not (App not (Var VZ)))

-- '\b. if b then Refl else Refl'
notProof :: Model Syn (Par Pi) g
notProof = Lam B $ Inc $ If (Inc (Id B (Var VZ) (App not (App not (Var VZ))))) 
              (var VZ) (Rfl TT) (Rfl FF)

-- \(b : B) -> if b then b else b
ifId :: Model Syn (Par Pi) g
ifId = Lam B $ Inc $ If (Inc B) (var VZ) (Var VZ) (Var VZ)

-- \(f : B -> B) (b : B) -> if f b then f b else f b
ifIdF :: Model Syn (Par Pi) g
ifIdF = Lam (Pi B $ Inc B) $ Inc $ Lam B $ Inc 
      $ If (Inc B) (El Spn (AppS (var (VS VZ)) (Var VZ))) 
           (App (var (VS VZ)) (Var VZ)) (App (var (VS VZ)) (Var VZ))

-- \(b : B) -> if b then not b else b
ifNot :: Model Syn (Par Pi) g
ifNot = Lam B $ Inc $ If (Inc B) (var VZ) (App not (Var VZ)) (Var VZ)

-- '\x y p. transp (z. z = x) p Refl'
symProof :: Model Syn (Par Pi) g
symProof = Lam B $ Inc $ Lam B $ Inc $ Lam (Id B (Var $ VS VZ) (Var VZ)) $ Inc 
         $ Transp (Inc $ Id B (Var VZ) (Var (VS $ VS $ VS VZ))) (var VZ) 
             (Rfl (Var $ VS $ VS VZ))

-- We don't have a unit type, but we can very easily construct proofs of
-- 'true = true'!
unit :: Model Syn (Par U) g
unit = Id B TT TT

-- '\b. if b then Unit else Bot' 
isTrue :: Model Syn (Par Pi) g
isTrue = Lam B $ Inc $ If (Inc U) (var VZ) unit Bot

-- '\p. transp (z. isTrue z) p tt'
disj :: Model Syn (Par Pi) g
disj = Lam (Id B TT FF) $ Inc 
     $ Transp (Inc (App isTrue (Var VZ))) (var VZ) (Rfl TT)
