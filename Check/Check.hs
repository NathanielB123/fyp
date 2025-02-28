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
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS -Wall #-}
{-# OPTIONS -Wpartial-fields #-}
{-# OPTIONS -Wno-unrecognised-pragmas #-}
{-# OPTIONS -Wno-missing-pattern-synonym-signatures #-}

module Check.Check where

import Prelude hiding (lookup, not)
import Prelude qualified as P
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (fromMaybe)
import Data.Bifunctor (Bifunctor(..))

import Check.Utils
import Check.Model
import Check.Common

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

thinEnv :: Thin x d -> Env d g -> Env x g
thinEnv s (vs, es) = (fThin s vs, thinEqMap s es)

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
complWrtEqs Nothing         _ []               = Nothing
complWrtEqs (Just (vs, es)) _ []               = Just (vs, reverse es)
complWrtEqs acc             r ((t, Ex u) : es)
  | Ex t' <- eval (r, es) t
  , u'    <- eval (r, es) u
  , eq    <- mkEq t' u' = do
    acc' <- addRw eq <$> acc
    complWrtEqs acc' r es  

complStep :: Sing SNat g => (Vals g g, EqMap g) 
          -> Maybe (Vec g (UnkVal g), EqMap g)
complStep (vs, es) = do
  (vs', es') <- complWrtEqs (pure (vs, [])) vs es
  -- If we applied substitutions eagerly, we wouldn't have to keep re-evaluating
  -- the values like this...
  pure (runUnk (Ex . eval (vs', es')) <$> vs', es')

complete :: Sing SNat g => Env g g -> Maybe (Env g g)
complete r = iterMaybeFix complStep r

-- evalEnv :: Sing SNat d => Env d g -> EqMap d -> Env g t -> Env d t
-- evalEnv _ _  Emp       = Emp
-- evalEnv r es (ts :< t) = evalEnv r es ts :< eval r es t

evalVals :: Sing SNat t => Env t d -> Vals d g -> Vals t g
evalVals r (ts :< Ex t) = evalVals r ts :< Ex (eval r t)
evalVals _ Emp          = Emp

addEq :: Sing SNat d => Env d g -> Val q d -> Val r d 
      -> Maybe (Env d g)
addEq (vs, es) t u = do
  r' <- addRw (mkEq t u) (idVals, es)
  r''  <- complete r'
  pure (evalVals r'' vs, eqs r'')

thinEqMap :: Thin d g -> EqMap g -> EqMap d
thinEqMap s = map (bimap (thin s) (thin s))

lookupNe :: Sing SNat g => EqMap g -> Ne g -> UnkVal g
lookupNe es t = fromMaybe (Ex (Ne t)) (P.lookup t es)

appVal :: Sing SNat g => EqMap g -> Val Pi g -> Val q g -> UnkVal g
appVal es (Lam _ (Clo t)) u = Ex $ t (idTh fill) es u
appVal es (Ne t)          u = lookupNe es $ App t u

-- TODO: It's actually unsafe to give standard if these enhanced evaluation
-- rules. Consider 'if True then u else v', which typechecks for standard if
-- even when 'v' is not '!'
ifVal :: Sing SNat g
      => EqMap g -> Body Sem U g -> Val B g -> Val q g -> Val r g 
      -> UnkVal g
ifVal _  _ TT     u _ = Ex u
ifVal _  _ FF     _ v = Ex v
ifVal es m (Ne t) u v = lookupNe es $ If m t u v

-- "Smart if" evaluates identically to "if"
-- We should probably try to remove duplication here by folding into the same
-- constructor...
smrtIfVal :: Sing SNat g2
          => Env g2 g1 -> Maybe (Val U g2) -> Val B g2 
          -> Model d (Par q) g1 -> Model d (Par r) g1 
          -> UnkVal g2
smrtIfVal r _ TT         u _ = Ex $ eval r u
smrtIfVal r _ FF         _ v = Ex $ eval r v
smrtIfVal r m (Ne t) u v
  | Just rT <- addEq r (Ne t) TT
  , Just rF <- addEq r (Ne t) FF
  , u'      <- eval rT u
  , v'      <- eval rF v 
  = lookupNe (eqs r) $ SmrtIf m t u' v'
  | otherwise = __IMPOSSIBLE__

jVal :: Sing SNat g 
     => EqMap g -> Body Sem U g -> Val Id g -> Val q g -> UnkVal g
jVal _ _  (Rfl _)    u = Ex u
jVal es m (Ne t) u = lookupNe es $ Transp m t u

explVal :: Sing SNat g => EqMap g -> Maybe (Val U g) -> Val Bot g -> UnkVal g
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
eval r (If m t u v) = presTM fill $ ifVal (eqs r) m' t' u' v'
  where m' = evalBody (vals r) m
        t' = evalPres r t
        u' = eval r u
        v' = eval r v
eval r (SmrtIf m t u v)
  = presTM fill $ smrtIfVal r m' t' u v
  where m' = eval r <$> m
        t' = evalPres r t
eval _ TT  = TT
eval _ FF  = FF
eval _ U   = U
eval _ B   = B
eval _ Bot = Bot
eval r (Lam a t) = Lam a' t'
  where a' = eval r <$> a
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
  where m' = eval r <$> m
        p' = evalPres r p
eval _ Absrd = __IMPOSSIBLE__

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

cannotInferErr :: (Show a) => a -> Error
cannotInferErr x 
  = "Cannot infer type of un-annotated " <> quotes (show x) <> "!"

inferBody :: Sing SNat g => Ctx g -> Env g g -> VTy g -> Body Syn q g 
          -> TCM (VTy (S g))
inferBody g r a (Inc t) 
  = infer (g :. a) (incEnv r) t

infer :: Sing SNat g => Ctx g -> Env g g -> Tm q g -> TCM (VTy g)
infer g r (Lam (Just a) t) = do
  check g r U a
  let a' = eval r a
  b' <- close <$> inferBody g r a' t
  pure (Pi a' b')
infer g r (Pi a b) = do
  check g r U a
  let a' = eval r a
  checkBody g r a' U b
  pure U
infer g r (App t u) = do
  Pi a1 (Clo b1) <- infer g r t
  a2 <- infer g r u
  chkConv a1 a2
  -- Perhaps 'infer' should return the 'eval'uated term...
  let u' = eval r u
  pure (b1 (idTh fill) (eqs r) u')
infer _ _ (SmrtIf Nothing _ _ _) = throw $ cannotInferErr "smart if"
infer _ _ (Expl Nothing _)       = throw $ cannotInferErr "explode"
infer _ _ (Lam Nothing _)        = throw $ cannotInferErr "lambda"
infer g r (If m t u v) = do
  check g r B t
  a1 <- infer g r u
  a2 <- infer g r v
  checkBody g r B U m
  Clo m' <- pure $ evalBody (vals r) m
  let a1' = m' (idTh fill) (eqs r) TT
  let a2' = m' (idTh fill) (eqs r) FF
  chkConv a1 a1'
  chkConv a2 a2'
  let t' = evalPres @_ @B r t
  pure $ m' (idTh fill) (eqs r) t'
infer g r (SmrtIf (Just m) t u v) = do
  check g r U m
  check g r B t
  let t' = evalPres @_ @B r t
  let rT = addEq r t' TT
  let rF = addEq r t' FF
  -- TODO: We end up re-evaluating 'm' three times here. We probably should
  -- avoid this...
  checkMaybeAbsurd g rT m u
  checkMaybeAbsurd g rF m v
  let m' = eval r m 
  pure m'
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
  checkBody g r a U m
  mx1' <- infer g r t
  -- Todo can/should we eval in context extended with 'x' directly?
  Clo m' <- pure $ evalBody (vals r) m
  let mx2' = m' (idTh fill) (eqs r) x
  chkConv mx1' mx2'
  pure $ m' (idTh fill) (eqs r) y
infer g r (Expl (Just m) p) = do
  check g r Bot p
  check g r U m
  pure (eval r m)
infer g _ (Var i)   = pure $ tLookup i g
infer _ _ TT        = pure B
infer _ _ FF        = pure B
infer _ _ B         = pure U
infer _ _ Bot       = pure U
-- Type in type!
infer _ _ U         = pure U
infer _ _ Absrd     = throw "Absurd encountered in non-inconsistent context!"

checkMaybeAbsurd :: Sing SNat g 
                 => Ctx g -> Maybe (Env g g) -> Ty g -> Tm q g -> TCM ()
checkMaybeAbsurd g (Just r) a t    = check g r a t
checkMaybeAbsurd _ Nothing _ Absrd = pure ()
checkMaybeAbsurd _ Nothing _ t     = throw 
  $  "Body in inconsistent contexts must be absurd, but was instead " 
  <> show t

checkErr :: (Show a, Show b) => a -> b -> Error
checkErr t a 
  = "Checking " <> quotes (show t) <> " has type " <> quotes (show a)

checkLamErr :: Show a => a -> Error
checkLamErr a = quotes (show a) <> " is convertible to a pi-type."

-- TODO: Refactor 'infer'/'check' to do proper bidir 
-- (i.e. don't redundantly check 'a' is of type 'U' - I think the neater
-- approach here would be for 'infer' to remove annotations, rather
-- than 'check' adding them...)
check :: Sing SNat g => Ctx g -> Env g g -> Ty g -> Tm q g -> TCM ()
check @_ @q g r a t = appendError (checkErr t a) $ case t of
  SmrtIf Nothing t' u' v' 
    -> discard $ infer @_ @q g r (SmrtIf (Just a) t' u' v')
  Expl Nothing p       
    -> discard $ infer @_ @q g r (Expl (Just a) p)
  Lam Nothing t' -> case a of
    Pi a' b' -> check g r (Pi a' b') (Lam (Just a') t')
    _        -> throw $ checkLamErr a
  _ -> do
    a' <- infer g r t
    chkConv (eval r a) a'

checkBody :: Sing SNat g 
          => Ctx g -> Env g g -> VTy g -> Ty (S g) -> Body Syn q g -> TCM ()
checkBody g r a b (Inc t) = check (g :. a) (incEnv r) b t

-- Examples:

-- '\b. b'
identity :: Tm Pi g
identity = Lam (Just B) $ Inc $ Var VZ

-- '\b. if b then False else True'
not :: Model Syn (Par Pi) g
not = Lam (Just B) $ Inc $ If (Inc B) (Var VZ) FF TT

-- '\(b : B) -> b = not (not b)'
notProofTy :: Model Syn (Par U) g
notProofTy = Pi B $ Inc $ Id B (Var VZ) (App not (App not (Var VZ)))

-- '\b. if b then Refl else Refl'
notProof :: Model Syn (Par Pi) g
notProof = Lam (Just B) $ Inc 
         $ If (Inc (Id B (Var VZ) (App not (App not (Var VZ))))) 
              (Var VZ) (Rfl TT) (Rfl FF)

-- \(b : B) -> if b then b else b
ifId :: Model Syn (Par Pi) g
ifId = Lam (Just B) $ Inc $ If (Inc B) (Var VZ) (Var VZ) (Var VZ)

-- '\(f : B -> B) (b : B) -> if f b then f b else f b'
ifIdF :: Model Syn (Par Pi) g
ifIdF = Lam (Just $ Pi B $ Inc B) $ Inc $ Lam (Just B) $ Inc 
      $ If (Inc B) (App (Var (VS VZ)) (Var VZ)) 
           (App (Var (VS VZ)) (Var VZ)) (App (Var (VS VZ)) (Var VZ))

-- \(b : B) -> if b then not b else b
ifNot :: Model Syn (Par Pi) g
ifNot = Lam (Just B) $ Inc $ If (Inc B) (Var VZ) (App not (Var VZ)) (Var VZ)

-- '\x y p. transp (z. z = x) p Refl'
symProof :: Model Syn (Par Pi) g
symProof = Lam (Just B) $ Inc $ Lam (Just B) $ Inc 
         $ Lam (Just $ Id B (Var $ VS VZ) (Var VZ)) $ Inc 
         $ Transp (Inc $ Id B (Var VZ) (Var (VS $ VS $ VS VZ))) (Var VZ) 
             (Rfl (Var $ VS $ VS VZ))

-- We don't have a unit type, but we can very easily construct proofs of
-- 'true = true'!
unit :: Model Syn (Par U) g
unit = Id B TT TT

-- '\b. if b then Unit else Bot' 
isTrue :: Model Syn (Par Pi) g
isTrue = Lam (Just B) $ Inc $ If (Inc U) (Var VZ) unit Bot

-- '\p. transp (z. isTrue z) p tt'
disj :: Model Syn (Par Pi) g
disj = Lam (Just $ Id B TT FF) $ Inc 
     $ Transp (Inc $ App isTrue (Var VZ)) (Var VZ) (Rfl TT)

-- '\f b. if b 
--    then (if f True then refl else (if f False then refl else refl)) 
--    else (if f False then (if f True then refl else refl) else refl)'
threeNotProof :: Model Syn (Par Pi) g
threeNotProof 
  = Lam (Just $ Pi B $ Inc B) $ Inc $ Lam (Just B) $ Inc 
  $ SmrtIf 
    (Just $ Id B (App (Var (VS VZ)) (Var VZ)) 
      (App (Var (VS VZ)) (App (Var (VS VZ)) 
      (App (Var (VS VZ)) (Var VZ))))) 
    (Var VZ) 
    (SmrtIf Nothing (App (Var (VS VZ)) TT) 
      (Rfl TT) 
      (SmrtIf Nothing (App (Var (VS VZ)) FF) (Rfl FF) (Rfl FF))) 
    (SmrtIf Nothing (App (Var (VS VZ)) FF) 
      (SmrtIf Nothing (App (Var (VS VZ)) TT) (Rfl TT) (Rfl TT)) 
      (Rfl FF))
