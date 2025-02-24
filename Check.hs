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
{-# LANGUAGE MultiWayIf #-}

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE LambdaCase #-}

import Prelude hiding (lookup, not)
import Prelude qualified as P
import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)
import Data.Data ((:~:)(..))
import Data.Maybe (fromMaybe, maybeToList)
import Data.Bifunctor (Bifunctor(..))

-- Thinn type families are cringe, but additional typeclasses are also cringe
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
-- work for Thinn type families
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

type data ParSort = B | U | Pi | Id | Bot | V | Absrd

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
    unclo :: forall g' r. Sing SNat g' => Thin g' g -> EqMap g' 
          -> Model Sem (Par r) g' -> Model Sem (Par q) g'
  } -> Body Sem q g

data Spine d q r g where
  AppS    :: Model d pi g -> Model d (Par q) g -> Spine d Pi pi g
  IfS     :: Body d U g -> Model d b g -> Model d (Par q) g -> Model d (Par r) g 
          -> Spine d B b g
  SmrtIfS :: Model d (Par U) g -> Model d b g 
          -> Model d (Par q) g -> Model d (Par r) g 
          -> Spine d B b g
  TranspS :: Body d U g -> Model d id g -> Model d (Par q) g 
          -> Spine d Id id g 
  ExplS   :: Model d (Par U) g -> Model d bot g -> Spine d Bot bot g
  VarS    :: Var g -> Spine d V Neu g

data Model d q g where
  Lam   :: Model d (Par U) g -> Body d q g -> Model d (Par Pi) g
  U     :: Model d (Par U) g
  B     :: Model d (Par U) g
  Bot   :: Model d (Par U) g
  Pi    :: Model d (Par U) g -> Body d U g -> Model d (Par U) g
  El    :: ElimSort d q r s -> Spine d q r g -> Model d s g
  TT    :: Model d (Par B) g
  FF    :: Model d (Par B) g
  Id    :: Model d (Par U) g -> Model d (Par q) g -> Model d (Par r) g 
        -> Model d (Par U) g
  Rfl   :: Model d (Par q) g -> Model d (Par Id) g
  -- Absurds make no sense in scrutinee positions so giving them a unique sort
  -- seems reasonable.
  -- Of course, this prevents us from trying to enforce equality of sorts
  -- in places where terms of def equal types are expected (e.g. the branches
  -- of an 'If', but I think this is more trouble than it's worth anyway)
  Absrd :: Model Syn (Par Absrd) g

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

quotes :: String -> String
quotes s = "'" <> s <> "'"

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
  show TT               = "True"
  show FF               = "False"
  show (Id _ x y)       = parens (show x) <> " = " <> parens (show y)
  show (Rfl _)          = "Refl"
  show Absrd            = "!"

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
pattern SmrtIf m t u v = El RecElim (SmrtIfS m t u v)
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

pattern SmrtIfNe :: () => () => Val U g -> Ne g -> Val q g -> Val r g -> Ne g
pattern SmrtIfNe m t u v = El Spn (SmrtIfS m t u v)

{-# COMPLETE AppNe, IfNe, SmrtIfNe, TranspNe, ExplNe, VarNe #-}
{-# COMPLETE Lam, U, B, Bot, Pi, TT, FF, Id, Rfl, Absrd, Ne #-}
{-# COMPLETE Lam, U, B, Bot, Pi, App, If, SmrtIf, Var, 
             TT, FF, Id, Rfl, Transp, Expl, Absrd #-}

data Thin d g where
  Eps  :: Thin Z Z
  Keep :: Thin d g -> Thin (S d) (S g)
  Drop :: Thin d g -> Thin (S d) g

idTh :: SNat g -> Thin g g
idTh SZ     = Eps
idTh (SS n) = Keep (idTh n)

wkTh :: Sing SNat g => Thin (S g) g
wkTh = Drop (idTh fill)

comTh :: Thin d g -> Thin x d -> Thin x g
comTh Eps       s2        = s2
comTh (Keep s1) (Keep s2) = Keep (comTh s1 s2)
comTh (Drop s1) (Keep s2) = Drop (comTh s1 s2)
comTh s1        (Drop s2) = Drop (comTh s1 s2)

-- I would prefer to flip the indices/parameters here, but I also really want 
-- 'Vec' to be 'Functor'
data Vec g a where
  Emp  :: Vec Z a
  (:<) :: Vec g a -> a -> Vec (S g) a

deriving instance Eq a => Eq (Vec g a)

instance Functor (Vec g) where
  fmap _ Emp       = Emp
  fmap f (xs :< x) = fmap f xs :< f x

type Vals d g = Vec g (UnkVal d)
type Vars d g = Vec g (Var d)

vLen :: Vec g a -> SNat g
vLen Emp      = SZ
vLen (r :< _) = SS (vLen r)

data Tele c g where 
  Nil  :: Tele c Z
  (:.) :: Tele c g -> c g -> Tele c (S g)

type Ctx = Tele VTy

type Env d g = (Vals d g, EqMap d)

vals :: Env d g -> Vals d g
vals = fst

eqs :: Env d g -> EqMap d
eqs  = snd

incEnv :: Sing SNat d => Env d g -> Env (S d) (S g)
incEnv r = extEnv (Var VZ) (thinEnv wkTh r)

extEnv :: Val q d -> Env d g -> Env d (S g)
extEnv u (vs, es) = (vs :< Ex u, es)

-- Presheaves on the category of thinnings
class PshThin f where
  thin :: Thin d g -> f g -> f d

instance PshThin (Body d q) where
  thin s (Inc t) = Inc $ thin (Keep s) t
  thin s (Clo t) = Clo $ t . comTh s

instance PshThin (Model d q) where
  thin _ U                = U
  thin _ B                = B
  thin _ Bot              = Bot
  thin s (Pi a b)         = Pi     (thin s a) (thin s b)
  thin s (Id a x y)       = Id     (thin s a) (thin s x) (thin s y)
  thin s (Lam a t)        = Lam    (thin s a) (thin s t)
  thin s (App t u)        = App    (thin s t) (thin s u)
  thin s (If m t u v)     = If     (thin s m) (thin s t) (thin s u) (thin s v)
  thin s (SmrtIf m t u v) = SmrtIf (thin s m) (thin s t) (thin s u) (thin s v)
  thin s (Transp m p t)   = Transp (thin s m) (thin s p) (thin s t)
  thin s (Expl m p)       = Expl   (thin s m) (thin s p)
  thin s (Var i)          = Var    (thin s i)
  thin _ TT               = TT
  thin _ FF               = FF
  thin s (Rfl t)          = Rfl    (thin s t)
  thin _ Absrd            = Absrd

instance PshThin Var where
  thin (Keep _) VZ     = VZ
  thin (Drop s) i      = VS (thin s i)
  thin (Keep s) (VS i) = VS (thin s i)
  thin Eps      i      = case i of

fThin :: (Functor f, PshThin c) => Thin d g -> f (c g) -> f (c d)
fThin = fmap . thin

thinEnv :: Thin x d -> Env d g -> Env x g
thinEnv s (vs, es) = (fThin s vs, thinEqMap s es)

data UnkVal g = forall q. Ex {proj :: Model Sem (Par q) g}

instance PshThin UnkVal where
  thin s (Ex t) = Ex $ thin s t

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

vLookup :: Var g -> Vec g a -> a
vLookup VZ     (_ :< t) = t
vLookup (VS i) (r :< _) = vLookup i r

tLookup :: (Sing SNat g, PshThin c) => Var g -> Tele c g -> c g
tLookup @g VZ (_ :. a)
  | SS n <- fill @SNat @g
  , Ev   <- recoverNat n
  = thin wkTh a
tLookup @g (VS i) (g :. _) 
  | SS n <- fill @SNat @g 
  , Ev   <- recoverNat n
  = thin wkTh (tLookup i g)

envLookup :: Var g -> Env d g -> UnkVal d
envLookup i = vLookup i . vals

envLen :: Env d g -> SNat g
envLen = vLen . vals

type EqMap g = [(Ne g, UnkVal g)]

iterFix :: Eq a => (a -> a) -> a -> a
iterFix f x = let x' = f x in if x == x' then x else iterFix f x'

iterMaybeFix :: Eq a => (a -> Maybe a) -> a -> Maybe a
iterMaybeFix f x = do 
  x' <- f x
  if x == x' then pure x else iterMaybeFix f x'

data Rw g = forall q. VarEq (Var g) (Val q g)
          | forall q. NeEq  (Ne g)  (Val q g)
          | ReflEq
          | ImpEq
          | BadEq

-- TODO: To deal with arbitrary equations (i.e. neutral RHSs), we might need to 
-- reorient
mkEq :: Sing SNat g => Val q g -> Val r g -> Rw g
mkEq t u = if
  | DefUnify     <- tu -> ReflEq
  | DefAntiUnify <- tu -> ImpEq
  | Unknown      <- tu -> if
    -- TODO: Check for loopy rewrites
    | Ne (Var i) <- t  -> VarEq i u
    | Ne t'      <- t  -> NeEq t' u
    | otherwise        -> BadEq
  where tu = unify t u

vReplace :: Var g -> a -> Vec g a -> Vec g a
vReplace VZ     y (xs :< _) = xs :< y
vReplace (VS i) y (xs :< x) = vReplace i y xs :< x 

addRw :: Sing SNat g => Rw g -> Env g g -> Maybe (Env g g)
addRw (NeEq t u)  (vs, es) = pure (vs, (t, Ex u) : es)
-- Instead of tracking an identity environment and lazily replacing variables,
-- we could immediately substitute the variable for the term everywhere in all 
-- equations.
--
-- I think this might be worth trying, but I suspect it will rely on some
-- painful lemmas/unsafe coercions
addRw (VarEq i u) (vs, es) = pure (vReplace i (Ex u) vs, es)
addRw ReflEq      r        = pure r
addRw ImpEq       _        = Nothing
-- TODO: Eventually we will introduce syntax capable of creating bad equations,
-- at which point this really should be a reported type error instead of an ICE.
addRw BadEq       _        = error "Bad equation encountered!"

complWrtEqs :: Sing SNat g 
            => Maybe (Env g g) -> Vals g g -> EqMap g -> Maybe (Env g g)
complWrtEqs acc _ []               = acc
complWrtEqs acc r ((t, Ex u) : es)
  | Ex t' <- eval (r, es) t
  , u'    <- eval (r, es) u
  , eq    <- mkEq t' u' = do
    acc' <- addRw eq <$> acc
    complWrtEqs acc' r es  

runUnk :: (forall q. Val q g -> r) -> UnkVal g -> r
runUnk f (Ex t) = f t

complStep :: Sing SNat g => (Vals g g, EqMap g) 
          -> Maybe (Vec g (UnkVal g), EqMap g)
complStep (vs, es) = do
  (vs', es') <- complWrtEqs (pure (vs, [])) vs es
  -- If we applied substitutions eagerly, we wouldn't have to keep re-evaluating
  -- the values like this...
  pure (runUnk (Ex . eval (vs', es')) <$> vs', es')

complete :: Sing SNat g => Env g g -> Maybe (Env g g)
complete r = iterMaybeFix (\(vs, es) -> complWrtEqs (pure (vs, [])) vs es) r

-- evalEnv :: Sing SNat d => Env d g -> EqMap d -> Env g t -> Env d t
-- evalEnv _ _  Emp       = Emp
-- evalEnv r es (ts :< t) = evalEnv r es ts :< eval r es t

evalVals :: Sing SNat t => Env t d -> Vals d g -> Vals t g
evalVals r (ts :< Ex t) = evalVals r ts :< Ex (eval r t)
evalVals _ Emp          = Emp

addEq :: Sing SNat d => Env d g -> Ne d -> Val q d 
      -> Maybe (Env d g)
addEq (vs, es) t u = do
  r' <- complete (idVals, (t, Ex u) : es)
  pure (evalVals r' vs, eqs r')

thinEqMap :: Thin d g -> EqMap g -> EqMap d
thinEqMap s = map (bimap (thin s) (thin s))

lookupNe :: Sing SNat g => EqMap g -> Ne g -> UnkVal g
lookupNe es t = fromMaybe (Ex (Ne t)) (P.lookup t es)

appVal :: Sing SNat g => EqMap g -> Val Pi g -> Val q g -> UnkVal g
appVal es (Lam _ (Clo t)) u = Ex $ t (idTh fill) es u
appVal es (Ne t)          u = lookupNe es $ App t u

ifVal :: Sing SNat g2
      => Env g2 g1 -> Body Sem U g2 -> Val B g2 
      -> Model d (Par q) g1 -> Model d (Par r) g1 
      -> UnkVal g2
ifVal r _ TT         u _ = Ex $ eval r u
ifVal r _ FF         _ v = Ex $ eval r v
ifVal r m (Ne t) u v
  | (Just rT, Just rF) <- (addEq r t TT, addEq r t FF)
  , u'                 <- eval rT u
  , v'                 <- eval rF v 
  = lookupNe (eqs r) $ If m t u' v'
  | otherwise = error "Something went wrong!"

-- "Smart if" evaluates identically to "if"
-- We should probably try to remove duplication here by folding into the same
-- constructor...
smrtIfVal :: Sing SNat g2
          => Env g2 g1 -> Val U g2 -> Val B g2 
          -> Model d (Par q) g1 -> Model d (Par r) g1 
          -> UnkVal g2
smrtIfVal r _ TT         u _ = Ex $ eval r u
smrtIfVal r _ FF         _ v = Ex $ eval r v
smrtIfVal r m (Ne t) u v
  | Just rT <- addEq r t TT
  , Just rF <- addEq r t FF
  , u'      <- eval rT u
  , v'      <- eval rF v 
  = lookupNe (eqs r) $ SmrtIf m t u' v'
  | otherwise = error "Something went wrong!"

jVal :: Sing SNat g 
     => EqMap g -> Body Sem U g -> Val Id g -> Val q g -> UnkVal g
jVal _ _  (Rfl _)    u = Ex $ u
jVal es m (Ne t) u = lookupNe es $ Transp m t u

explVal :: Sing SNat g => EqMap g -> Val U g -> Val Bot g -> UnkVal g
explVal es m (Ne t) = lookupNe es $ Expl m t

wkStar :: SNat g -> SNat d -> Thin (g + d) g
wkStar SZ     SZ     = Eps
wkStar SZ     (SS d) = Drop (wkStar SZ d)
wkStar (SS g) d      = Keep (wkStar g d)

starWk :: SNat g -> SNat d -> Thin (d + g) g
starWk g SZ     = idTh g
starWk g (SS d) = Drop (starWk g d)

toEnv :: (Sing SNat g, Sing SNat d) => Thin d g -> Env d g
toEnv s = thinEnv s idEnv

parCom :: (Sing SNat d, Sing SNat t) => Vals d g -> Thin d t 
       -> Vals d (g + t)
parCom Emp      s = fThin s idVals
parCom (r :< t) s = parCom r s :< t

vars :: SNat g -> Vars g g
vars SZ     = Emp
vars (SS n) | Ev <- recoverNat n
            = fThin wkTh (vars n) :< VZ

idVals :: Sing SNat g => Vals g g
idVals = Ex . Var <$> vars fill

idEnv :: Sing SNat g => Env g g
idEnv = (idVals, [])

subSort :: q <= r -> SSort q
subSort FromNeu = SNeu
subSort FromPar = SPar

evalPres :: (Sing (<=) '(q, r), Sing SSort q, Sing SNat g2) 
         => Env g2 g1 -> Model d q g1 -> Val r g2
evalPres r t = presElim fill (eval r t)

evalBody :: Sing SNat g2 => Vals g2 g1 -> Body d q g1 -> Body Sem q g2
evalBody r (Inc t) 
  = Clo \s es u -> eval (fThin s r :< Ex u, es) t
evalBody r (Clo t) 
  = Clo \ @g' s es u -> 
    if |  Ev  <- recoverNat (addNat @_ @g' d fill) 
       ,  wk1 <- wkStar @_ @g' d fill
       ,  wk2 <- starWk @g' fill d
       -> eval (parCom (fThin s r) (idTh fill), es) 
               (t wk1 (thinEqMap wk2 es) (thin wk2 u))
  where d = vLen r

eval :: (Sing SNat g2, Sing SSort q) 
     => Env g2 g1 -> Model d q g1 -> PresVal q g2
eval r (Var i)   = presTM fill $ envLookup i r
eval r (App t u) = presTM fill $ appVal (eqs r) t' u'
  where t' = evalPres r t
        u' = eval r u
eval r (If m t u v) = presTM fill $ ifVal r m' t' u v
  where m' = evalBody (vals r) m
        t' = evalPres r t
eval r (SmrtIf m t u v)
  = presTM fill $ smrtIfVal r m' t' u v
  where m' = eval r m
        t' = evalPres r t
eval _ TT  = TT
eval _ FF  = FF
eval _ U   = U
eval _ B   = B
eval _ Bot = Bot
eval r (Lam a t) = Lam a' t'
  where a' = eval r a
        t' = evalBody (vals r) t
eval r (Pi a b) = Pi a' b'
  where a' = eval r a
        b' = evalBody (vals r) b
eval r (Id a x y) = Id a' x' y'
  where a' = eval r a
        x' = eval r x
        y' = eval r y
eval r (Rfl x) = Rfl x'
  where x' = eval r x
eval r (Transp m p t) = presTM fill $ jVal (eqs r) m' p' t'
  where m' = evalBody (vals r) m
        p' = evalPres r p
        t' = eval r t
eval r (Expl m p) = presTM fill $ explVal (eqs r) m' p'
  where m' = eval r m
        p' = evalPres r p
eval _ Absrd = error "Something has gone wrong!"

type Error = String

throw :: Error -> TCM a
throw = Failure

orThrow :: Bool -> Error -> TCM ()
orThrow True  _ = pure ()
orThrow False e = throw e

-- Temporary hack
instance MonadFail TCM where
  fail s = throw s

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

-- unify :: Val -> Val -> UnifyRes
-- defEq :: Val -> Val -> Bool

-- data DefRes = DefEq | DefNotEq | Unknown

-- Combine unification judgements
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

-- convBody :: Sing SNat g => Body Sem q g -> Body Sem r g -> TCM ()
-- convBody (Clo t) (Clo u) 
--   = conv (t wkTh [] (Var VZ)) (u wkTh [] (Var VZ))


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
unify _ _ = Unknown

-- Neutrals are either definitionally equal or unknown
convNe :: Sing SNat g => Ne g -> Ne g -> ConvJud
convNe (AppNe t1 u1) (AppNe t2 u2) = convNe t1 t2 && conv u1 u2
convNe (IfNe _ t1 u1 v1) (IfNe _ t2 u2 v2) 
  = convNe t1 t2 && conv u1 u2 && conv v1 v2
convNe (TranspNe _ p1 t1) (TranspNe _ p2 t2) = convNe p1 p2 && conv t1 t2
convNe (ExplNe _ p1) (ExplNe _ p2) = convNe p1 p2
convNe (VarNe i1) (VarNe i2) = i1 == i2
convNe _ _ = False

conv :: Sing SNat g => Val q g -> Val r g -> ConvJud
conv t u = convertible $ unify t u

guardThrow :: Bool -> Error -> TCM ()
guardThrow True  _ = pure ()
guardThrow False e = throw e

notConvErr :: (Show a, Show b) => a -> b -> Error
notConvErr t u = quotes (show t) <> " and " <> quotes (show u)
              <> " are not covertible."

chkConvBody :: Sing SNat g => Body Sem q g -> Body Sem r g -> TCM ()
chkConvBody t u 
  = guardThrow (convBody t u) $ notConvErr (reifyBody t) (reifyBody u)

chkConvNe :: Sing SNat g => Ne g -> Ne g -> TCM ()
chkConvNe t u = guardThrow (convNe t u) $ notConvErr (reifyNe t) (reifyNe u)

chkConv :: Sing SNat g => Val q g -> Val r g -> TCM ()
chkConv t u = guardThrow (conv t u) $ notConvErr (reify t) (reify u)

close :: Sing SNat g => Val q (S g) -> Body Sem q g
close t = Clo \s es u -> eval (fThin s idVals :< Ex u, es) t

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
inferBody g r a (Inc t) 
  = infer (g :. a) (incEnv r) t

-- TODO: Use 'check' here instead of manual matching and 'conv' calls
infer :: Sing SNat g => Ctx g -> Env g g -> Tm q g -> TCM (VTy g)
infer g r (Lam a t) = do
  check g r a U
  let a' = eval r a
  b' <- close <$> inferBody g r a' t
  pure (Pi a' b')
infer g r (Pi a b) = do
  check g r a U
  let a' = eval r a
  checkBody g r a' b U
  pure U
infer g r (App t u) = do
  Pi a1 (Clo b1) <- infer g r t
  a2 <- infer g r u
  chkConv a1 a2
  -- Perhaps 'infer' should return the 'eval'uated term...
  let u' = eval r u
  pure (b1 (idTh fill) (eqs r) u')
infer g r (If m t u v) = do
  check g r t B
  a1 <- infer g r u
  a2 <- infer g r v
  checkBody g r B m U
  Clo m' <- pure $ evalBody (vals r) m
  let a1' = m' (idTh fill) (eqs r) TT
  let a2' = m' (idTh fill) (eqs r) FF
  chkConv a1 a1'
  chkConv a2 a2'
  let t' = evalPres @_ @B r t
  pure $ m' (idTh fill) (eqs r) t'
infer g r (SmrtIf m t u v) = do
  -- TODO:
  -- I think we need to split into cases depending on whether 't' evaluates to a
  -- neutral

  -- check g r es t B
  -- t' <- eval g r t
  -- a1 <- infer g r es u
  -- let mT = uncurry eval (addEq r es _ _) m 

  -- a2 <- infer g r es v
  --
  throw "Smart if not implemented yet!"
infer g r (Rfl x) = do
  a' <- infer g r x
  let x' = eval r x
  pure (Id a' x' x')
infer g r (Id a x y) = do
  U <- infer g r a
  let a1' = eval r a
  a2' <- infer g r x
  chkConv a1' a2'
  a3' <- infer g r y
  chkConv a1' a3'
  pure U
infer g r (Transp m p t) = do
  Id a x y <- infer g r p
  checkBody g r a m U
  mx1' <- infer g r t
  -- Todo can/should we eval in context extended with 'x' directly?
  Clo m' <- pure $ evalBody (vals r) m
  let mx2' = m' (idTh fill) (eqs r) x
  chkConv mx1' mx2'
  pure $ m' (idTh fill) (eqs r) y
infer g r (Expl m p) = do
  check g r p Bot
  check g r m U
  pure (eval r m)
infer g _ (Var i)   = pure $ tLookup i g
infer _ _ TT        = pure B
infer _ _ FF        = pure B
infer _ _ B         = pure U
infer _ _ Bot       = pure U
-- Type in type!
infer _ _ U         = pure U
infer _ _ Absrd     = throw "Absurd encountered in non-absurd context!"

check :: Sing SNat g => Ctx g -> Env g g -> Tm q g -> Ty g -> TCM ()
check g r t a = do
  a' <- infer g r t
  chkConv (eval r a) a'

checkBody :: Sing SNat g 
          => Ctx g -> Env g g -> VTy g -> Body Syn q g -> Ty (S g) -> TCM ()
checkBody g r a t b = do
  b' <- inferBody g r a t
  chkConv (eval (incEnv r) b) b'

reifyBody :: Sing SNat g => Body Sem q g -> Body Syn q g
reifyBody (Clo t) = Inc $ reify (t wkTh [] (Var VZ))

reifyNe :: Sing SNat g => Ne g -> Model Syn (Par q) g
reifyNe (VarNe i)    = Var i
reifyNe (IfNe m t u v) 
  = If (reifyBody m) (reifyNe t) (reify u) (reify v)
reifyNe (SmrtIfNe m t u v)
  = SmrtIf (reify m) (reifyNe t) (reify u) (reify v)
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
deriving instance Show a => Show (Vec g a)

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
