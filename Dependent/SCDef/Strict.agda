{-# OPTIONS --prop --show-irrelevant --rewriting --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

module Dependent.SCDef.Strict where

infixr 4 _∙~_

data Sig : Set
data Ctx  : Sig → Set

variable 
  Ψ Φ Ξ Ψ₁ Ψ₂ Ψ₃ Φ₁ Φ₂ Φ₃ : Sig

data Ty     : Ctx Ξ → Set
data DefVar : ∀ Ξ (Γ : Ctx Ξ) → Ty Γ → Set
data Var    : ∀ (Γ : Ctx Ξ) → Ty Γ → Set
data Tm     : ∀ (Γ : Ctx Ξ) → Ty Γ → Set
data Wk     : Sig → Sig → Set
data Tms    : Ctx Ξ → Ctx Ξ → Set

variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx Ξ
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  i j k i₁ i₂ i₃ : Var Γ A
  f g h : DefVar Ξ Γ A
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  φ ψ ξ ξ₁ ξ₂ : Wk Φ Ψ
  b b₁ b₂ : Bool

𝔹′ : Ty Γ
data EqVar  : ∀ (Γ : Ctx Ψ) → Tm Γ 𝔹′ → Bool → Set

data Ctx~  : Ctx Ψ → Ctx Ψ → Prop
data Ty~   : Ctx~ {Ψ = Ψ} Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂ → Prop
data Var~  : ∀ Γ~ → Ty~ {Ψ = Ψ} Γ~ A₁ A₂ → Var Γ₁ A₁ → Var Γ₂ A₂ → Prop
data Tm~   : ∀ Γ~ → Ty~ {Ψ = Ψ} Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Prop
data Tms~  : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂ → Prop

variable
  Γ~ Δ~ Θ~ Γ₁₂~ Γ₂₃~ Δ₁₂~ Δ₂₃~ Γ₁~ Γ₂~ Γ₃~ Γ₄~ : Ctx~ Γ₁ Γ₂
  A~ B~ A₁₂~ A₂₃~ A₁~ A₂~ A₃~ A₄~ : Ty~ _ A₁ A₂
  t~ t₁~ t₂~ : Tm~ _ _ t₁ t₂

data Ctx where
  •       : Ctx Ψ
  _▷_     : ∀ (Γ : Ctx Ψ) → Ty Γ → Ctx Ψ
  _▷_>eq_ : ∀ (Γ : Ctx Ψ) → Tm Γ 𝔹′ → Bool → Ctx Ψ

_[_]Ctx : Ctx Ψ → Wk Φ Ψ → Ctx Φ

data Ty where
  coe~ : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂

  𝔹 : Ty Γ   
  Π : ∀ A → Ty (Γ ▷ A) → Ty Γ

  IF   : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ

𝔹′ = 𝔹

_[_]Ty⁺ : Ty Γ → ∀ (ξ : Wk Φ Ψ) → Ty (Γ [ ξ ]Ctx)
_[_]Ty  : Ty Γ → Tms Δ Γ → Ty Δ
_[_] : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty)
_[_]⁺   : Tm Γ A → ∀ (ξ : Wk Φ Ψ) → Tm (Γ [ ξ ]Ctx) (A [ ξ ]Ty⁺)

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A)

{-# NON_COVERING #-}
{-# TERMINATING #-}
𝔹        [ δ ]Ty = 𝔹
Π A B    [ δ ]Ty = Π (A [ δ ]Ty) (B [ δ ^ A ]Ty)
IF t A B [ δ ]Ty = IF (t [ δ ]) (A [ δ ]Ty) (B [ δ ]Ty)

𝔹~′ : Ty~ Γ~ 𝔹′ 𝔹′
⌜_⌝𝔹 : Bool → Tm Γ 𝔹
rflCtx′ : Ctx~ Γ Γ
rflTy′  : Ty~ rflCtx′ A A

wkeq : Tms (Γ ▷ t >eq b) Γ

data Sig where
  •                  : Sig
  _▷_⇒_if_then_else_ : ∀ Ψ (Γ : Ctx Ψ) A → (t : Tm Γ 𝔹′) 
                     → Tm (Γ ▷ t >eq true) (A [ wkeq ]Ty) 
                     → Tm (Γ ▷ t >eq false) (A [ wkeq ]Ty)
                     → Sig

data Wk where
  id𝒮   : Wk Ψ Ψ
  _⨾𝒮_  : Wk Φ Ψ → Wk Ξ Φ → Wk Ξ Ψ
  wk𝒮   : Wk (Ψ ▷ Γ ⇒ A if t then u else v) Ψ
-- ε                  : Wk • •
-- _⁺_⇒_if_then_else_ : Wk Φ Ψ → ∀ Γ A t u v 
--                     → Wk (Φ ▷ Γ ⇒ A if t then u else v) Ψ

data Tms where
  coe~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂

  ε     : Tms Δ •
  _,_   : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty) → Tms Δ (Γ ▷ A) 
  -- We do some Fording here to enforce that |t [ δ ]| is considered a 
  -- structural subterm.
  ,eqℱ : ∀ (δ : Tms Δ Γ) {u} → t [ δ ] ≡ u
         → Tm~ rflCtx′ rflTy′ (t [ δ ]) ⌜ b ⌝𝔹
         → Tms Δ (Γ ▷ t >eq b)

pattern _,eq_ δ t~ = ,eqℱ δ refl t~

_[_]Tms : Tms Δ Γ → ∀ (ξ : Wk Φ Ψ) → Tms (Δ [ ξ ]Ctx) (Γ [ ξ ]Ctx)

id   : Tms Γ Γ
_⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ

wk   : Tms (Γ ▷ A) Γ

data DefVar where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → DefVar Ψ Γ₁ A₁ → DefVar Ψ Γ₂ A₂

  fz : DefVar (Ψ ▷ Γ ⇒ A if t then u else v) (Γ [ wk𝒮 ]Ctx) (A [ wk𝒮 ]Ty⁺)
  fs : DefVar Ψ Γ A 
     → DefVar (Ψ ▷ Δ ⇒ B if t then u else v) (Γ [ wk𝒮 ]Ctx) (A [ wk𝒮 ]Ty⁺)

data Var where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Var Γ₁ A₁ → Var Γ₂ A₂

  vz    : Var (Γ ▷ A) (A [ wk ]Ty)
  vs    : Var Γ B → Var (Γ ▷ A) (B [ wk ]Ty)
  vseq  : Var Γ B → Var (Γ ▷ t >eq b) (B [ wkeq ]Ty)

data EqVar where
  ez    : EqVar (Γ ▷ t >eq b) (t [ wkeq ]) b
  es    : EqVar Γ t b → EqVar (Γ ▷ A) (t [ wk ]) b
  eseq  : EqVar Γ t b₁ → EqVar (Γ ▷ u >eq b₂) (t [ wkeq ]) b₁

<_> : Tm Γ A → Tms Γ (Γ ▷ A)

record Def Ψ (Γ : Ctx Ψ) (A : Ty Γ) : Set where
  constructor if
  pattern
  field
    scrut : Tm Γ 𝔹
    lhs   : Tm (Γ ▷ scrut >eq true)  (A [ wkeq ]Ty)
    rhs   : Tm (Γ ▷ scrut >eq false) (A [ wkeq ]Ty) 
open Def public

lookup𝒮 : ∀ Ψ {Γ A} → DefVar Ψ Γ A → Def Ψ Γ A

data Tm where  
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂

  `_   : Var Γ A → Tm Γ A
  ƛ_   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  _·_  : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ < u > ]Ty)

  TT : Tm Γ 𝔹
  FF : Tm Γ 𝔹

  callℱ : ∀ (f : DefVar Ψ Γ A) {t u v} (δ : Tms Δ Γ)
        → lookup𝒮 _ f .scrut ≡ t 
        → lookup𝒮 _ f .lhs   ≡ u
        → lookup𝒮 _ f .rhs   ≡ v
        → Tm Δ (A [ δ ]Ty)

pattern call {A = A} f δ = callℱ {A = A} f δ refl refl refl

⌜ true  ⌝𝔹 = TT
⌜ false ⌝𝔹 = FF

lookup  : Var Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty)
_[_]Var : Var Γ A → ∀ (ξ : Wk Φ Ψ) → Var (Γ [ ξ ]Ctx) (A [ ξ ]Ty⁺)

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  _▷_    : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ ▷ A₁) (Γ₂ ▷ A₂)
  _▷_>eq : ∀ Γ~ → Tm~ Γ~ 𝔹~′ t₁ t₂ → Ctx~ (Γ₁ ▷ t₁ >eq b) (Γ₂ ▷ t₂ >eq b)

rflCtx′ = rfl~

data Ty~ where
  -- Equivalence
  rfl~ : Ty~ rfl~ A A
  sym~ : Ty~ Γ~ A₁ A₂ → Ty~ (sym~ Γ~) A₂ A₁
  _∙~_ : Ty~ Γ₁₂~ A₁ A₂ → Ty~ Γ₂₃~ A₂ A₃ → Ty~ (Γ₁₂~ ∙~ Γ₂₃~) A₁ A₃

  -- Coherence
  coh : Ty~ Γ~ A (coe~ Γ~ A)

  -- Congruence
  𝔹    : Ty~ Γ~ 𝔹 𝔹
  Π    : ∀ A~ → Ty~ (Γ~ ▷ A~) B₁ B₂ → Ty~ Γ~ (Π A₁ B₁) (Π A₂ B₂)
  IF   : Tm~ Γ~ 𝔹 t₁ t₂ → Ty~ Γ~ A₁ A₂ → Ty~ Γ~ B₁ B₂ 
       → Ty~ Γ~ (IF t₁ A₁ B₁) (IF t₂ A₂ B₂)

  -- Computation
  IF-TT : Ty~ rfl~ (IF TT A B) A
  IF-FF : Ty~ rfl~ (IF FF A B) B

𝔹~′    = 𝔹
rflTy′ = rfl~

-- Additional congruences
postulate
  _[_]Ty~ : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
         → Ty~ Δ~ (A₁ [ δ₁ ]Ty) (A₂ [ δ₂ ]Ty)

postulate [id]Ty : A [ id ]Ty ≡ A
{-# REWRITE [id]Ty #-}

postulate [][]Ty : A [ δ ]Ty [ σ ]Ty ≡ A [ δ ⨾ σ ]Ty
{-# REWRITE [][]Ty #-}

< t > = id , t
-- Strictified computation
postulate id⨾ : id ⨾ δ ≡ δ
{-# REWRITE id⨾ #-}

postulate ⨾id : δ ⨾ id ≡ δ 
{-# REWRITE ⨾id #-}

postulate
  _[_]~ : Tm~ Γ~ A~ t₁ t₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
        → Tm~ Δ~ (A~ [ δ~ ]Ty~) (t₁ [ δ₁ ]) (t₂ [ δ₂ ]) 


postulate ⨾⨾ : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
{-# REWRITE ⨾⨾ #-}

postulate [id] : t [ id ] ≡ t 
{-# REWRITE [id] #-}
postulate [][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
{-# REWRITE [][] #-}

[][]𝔹 : ∀ {t : Tm Γ 𝔹} → t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
[][]𝔹 {δ = δ} {t = t} = [][] {t = t} {δ = δ}
{-# REWRITE [][]𝔹 #-}

postulate ⌜⌝𝔹[] : ⌜ b ⌝𝔹 [ δ ] ≡ ⌜ b ⌝𝔹
{-# REWRITE ⌜⌝𝔹[] #-}

rflTms′ : Tms~ rfl~ rfl~ δ δ

ε            ⨾ σ = ε
(δ , t)      ⨾ σ = (δ ⨾ σ) , (t [ σ ])
(δ ,eq t~)   ⨾ σ = (δ ⨾ σ) ,eq (t~ [ rflTms′ ]~)

postulate wk⨾ : wk ⨾ (δ , t) ≡ δ
{-# REWRITE wk⨾ #-}

postulate wkeq⨾ : wkeq ⨾ (δ ,eq t~) ≡ δ
{-# REWRITE wkeq⨾ #-}

-- We make η-contraction a rewrite
postulate ,η : ∀ {δ : Tms Δ (Γ ▷ A)} → ((wk ⨾ δ) , lookup vz δ) ≡ δ 
{-# REWRITE ,η #-}

wk   {Γ = •} = ε
wkeq {Γ = •} = ε
id   {Γ = •} = ε

data Tms~ where
  -- Equivalence
  rfl~ : Tms~ rfl~ rfl~ δ δ
  sym~ : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ (sym~ Δ~) (sym~ Γ~) δ₂ δ₁
  _∙~_ : Tms~ Δ₁₂~ Γ₁₂~ δ₁ δ₂ → Tms~ Δ₂₃~ Γ₂₃~ δ₂ δ₃
       → Tms~ (Δ₁₂~ ∙~ Δ₂₃~) (Γ₁₂~ ∙~ Γ₂₃~) δ₁ δ₃

  -- Coherence
  coh  : Tms~ Δ~ Γ~ δ (coe~ Δ~ Γ~ δ)

  -- Congruence
  ε     : Tms~ Δ~ rfl~ ε ε
  _,_   : ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Tm~ Δ~ (A~ [ δ~ ]Ty~) t₁ t₂
        → Tms~ Δ~ (Γ~ ▷ A~) (δ₁ , t₁) (δ₂ , t₂)
  ,eq~  : ∀ {Δ~ : Ctx~ {Ψ = Ψ} Δ₁ Δ₂} (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
            {t₁~ : Tm~ rfl~ _ _ ⌜ b ⌝𝔹}            
        → Tms~ Δ~ (Γ~ ▷ t~ >eq) (δ₁ ,eq t₁~) (δ₂ ,eq t₂~) 

  εη : Tms~ Δ~ Γ~ δ ε

-- Additional congruences
postulate 
  id~   : Tms~ Γ~ Γ~ id id
  _⨾~_  : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ Θ~ Δ~ σ₁ σ₂ → Tms~ Θ~ Γ~ (δ₁ ⨾ σ₁) (δ₂ ⨾ σ₂)
  wk~   : ∀ (A~ : Ty~ Γ~ A₁ A₂) → Tms~ (Γ~ ▷ A~) Γ~ wk wk
  wkeq~ : Tms~ (Γ~ ▷ t~ >eq) Γ~ (wkeq {b = b}) wkeq

rflTms′ = rfl~

δ ^ A = (δ ⨾ wk) , (` vz)

data Var~ where
  -- Equivalence
  rfl~ : Var~ rfl~ rfl~ i i
  sym~ : Var~ Γ~ A~ i₁ i₂ → Var~ (sym~ Γ~) (sym~ A~) i₂ i₁
  _∙~_ : Var~ Γ₁₂~ A₁₂~ i₁ i₂ → Var~ Γ₂₃~ A₂₃~ i₂ i₃ 
       → Var~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) i₁ i₃

  -- Coherence
  coh  : Var~ Γ~ A~ i (coe~ Γ~ A~ i)

  -- Congruence
  vz : Var~ (Γ~ ▷ A~) (A~ [ wk~ A~ ]Ty~) vz vz
  vs : Var~ Γ~ B~ i₁ i₂ → Var~ (Γ~ ▷ A~) (B~ [ wk~ A~ ]Ty~) (vs i₁) (vs i₂)

-- Strict computation
lookup vz       (δ , t)        = t
lookup (vs i)   (δ , t)        = lookup i δ
lookup (vseq i) (δ ,eq t~)     = lookup i δ

postulate lookup-wk⨾ : lookup i (wk ⨾ δ) ≡ lookup (vs i) δ
{-# REWRITE lookup-wk⨾ #-}
postulate lookup-wk : lookup i (wk {A = A}) ≡ ` vs i
{-# REWRITE lookup-wk #-}
postulate lookup-id : lookup i id ≡ (` i)
{-# REWRITE lookup-id #-}
postulate lookup-⨾ : lookup i δ [ σ ] ≡ lookup i (δ ⨾ σ)
{-# REWRITE lookup-⨾ #-}

idη : wk , (` vz) ≡ id {Γ = Γ ▷ A}
idη = ,η {δ = id}
{-# REWRITE idη #-}

(` i)      [ δ ] = lookup i δ
(ƛ t)      [ δ ] = ƛ (t [ δ ^ _ ])
(t · u)    [ δ ] = (t [ δ ]) · (u [ δ ])
TT         [ δ ] = TT
FF         [ δ ] = FF
call f δ   [ σ ] = call f (δ ⨾ σ)

<_>~ : Tm~ Γ~ A~ t₁ t₂ → Tms~ Γ~ (Γ~ ▷ A~) < t₁ > < t₂ >

data Tm~ where
  -- Equivalence
  rfl~ : Tm~ rfl~ rfl~ t t
  sym~ : Tm~ Γ~ A~ t₁ t₂ → Tm~ (sym~ Γ~) (sym~ A~) t₂ t₁
  _∙~_ : Tm~ Γ₁₂~ A₁₂~ t₁ t₂ → Tm~ Γ₂₃~ A₂₃~ t₂ t₃ 
       → Tm~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) t₁ t₃

  -- Coherence
  coh  : Tm~ Γ~ A~ t (coe~ Γ~ A~ t)

  --Congruence  
  `_   : Var~ Γ~ A~ i₁ i₂ → Tm~ Γ~ A~ (` i₁) (` i₂)
  ƛ_   : Tm~ (Γ~ ▷ A~) B~ t₁ t₂ → Tm~ Γ~ (Π A~ B~) (ƛ t₁) (ƛ t₂)
  _·_  : Tm~ Γ~ (Π A~ B~) t₁ t₂ → ∀ (u~ : Tm~ Γ~ A~ u₁ u₂)
       → Tm~ Γ~ (B~ [ < u~ >~ ]Ty~) (t₁ · u₁) (t₂ · u₂) 

  TT   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 TT TT
  FF   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 FF FF

  call~ : ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Tm~ Γ~ A~ (call f δ₁) (call f δ₂) 

  -- Equational assumptions
  eq  : EqVar Γ t b → Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹

  -- Computation
  Πβ   : Tm~ rfl~ rfl~ ((ƛ t) · u) (t [ < u > ])
  Πη   : Tm~ {Ψ = Ψ} (rfl~ {Γ = Γ}) (rfl~ {A = Π A B}) 
             t (ƛ ((t [ wk ]) · (` vz)))

  call-TT : ∀ (t~ : Tm~ rfl~ rfl~ (lookup𝒮 Ψ f .scrut [ δ ]) TT)
          → Tm~ (rfl~ {Γ = Δ}) (rfl~ {A = _}) 
                (call f δ) (lookup𝒮 Ψ f .lhs [ δ ,eq t~ ])
  call-FF : ∀ (t~ : Tm~ rfl~ rfl~ (lookup𝒮 Ψ f .scrut [ δ ]) FF)
          → Tm~ (rfl~ {Γ = Δ}) (rfl~ {A = _}) 
                (call f δ) (lookup𝒮 Ψ f .rhs [ δ ,eq t~ ])

-- Additional congruences
postulate
  lookup~ : Var~ Γ~ A~ i₁ i₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
          → Tm~ Δ~ (A~ [ δ~ ]Ty~) (lookup i₁ δ₁) (lookup i₂ δ₂)

<_>~ {A~ = A~} t~ = _,_ {A~ = A~} id~ t~

π₁ : Tms Δ (Γ ▷ A) → Tms Δ Γ
π₁ δ = wk ⨾ δ

π₂ : ∀ (δ : Tms Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]Ty)
π₂ δ = lookup vz δ

π₁eq : Tms Δ (Γ ▷ t >eq b) → Tms Δ Γ
π₁eq δ = wkeq ⨾ δ

π₂eq : ∀ (δ : Tms Δ (Γ ▷ t >eq b)) → Tm~ rfl~ rfl~ (t [ π₁eq δ ]) ⌜ b ⌝𝔹
π₂eq δ = eq ez [ rfl~ {δ = δ} ]~

-- Presheaf laws for the category of thinnings

-- Additional congruences
postulate
  _[]Ctx~ : Ctx~ Γ₁ Γ₂ → Ctx~ (Γ₁ [ ξ₁ ]Ctx) (Γ₂ [ ξ₂ ]Ctx)

  _[]Ty~⁺ : Ty~ Γ~ A₁ A₂
          → Ty~ (Γ~ []Ctx~) (A₁ [ ξ₁ ]Ty⁺) (A₂ [ ξ₂ ]Ty⁺)

  _[]Tms~ : Tms~ Δ~ Γ~ δ₁ δ₂ 
          → Tms~ (Δ~ []Ctx~) (Γ~ []Ctx~) (δ₁ [ ξ₁ ]Tms) (δ₂ [ ξ₂ ]Tms)

  _[]~⁺ : Tm~ Γ~ A~ t₁ t₂ 
        → Tm~ (Γ~ []Ctx~) (A~ []Ty~⁺) (t₁ [ ξ₁ ]⁺) (t₂ [ ξ₂ ]⁺)

coeDef : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Def Ψ Γ₁ A₁ → Def Ψ Γ₂ A₂
coeDef Γ~ A~ (if t u v) 
  = if (coe~ Γ~ 𝔹 t) 
       (coe~ (Γ~ ▷ coh >eq) (A~ [ wkeq~ {t~ = coh} ]Ty~) u) 
       (coe~ (Γ~ ▷ coh >eq) (A~ [ wkeq~ {t~ = coh} ]Ty~) v) 

-- We have a fun inter-dependency between |_[_]Ctx| and |_[_]Ty⁺|
-- If we defined the syntax as one big inductive-inductive type
-- then we could properly interleave these cases (but then interleaving with
-- the recursive definitions would become trickier)
postulate 𝔹[]⁺ : 𝔹 {Γ = Γ} [ ξ ]Ty⁺ ≡ 𝔹
{-# REWRITE 𝔹[]⁺ #-}

•             [ ξ ]Ctx = •
(Γ ▷ A)       [ ξ ]Ctx = (Γ [ ξ ]Ctx) ▷ (A [ ξ ]Ty⁺)
(Γ ▷ t >eq b) [ ξ ]Ctx = (Γ [ ξ ]Ctx) ▷ (t [ ξ ]⁺) >eq b

-- TODO: I think generalising these identity weakening laws to any weakening
-- of type |Wk Ψ Ψ| should be sound
postulate [id]Ctx : Γ [ id𝒮 ]Ctx ≡ Γ
{-# REWRITE [id]Ctx #-}

postulate [][]Ctx : Γ [ φ ]Ctx [ ψ ]Ctx ≡ Γ [ φ ⨾𝒮 ψ ]Ctx
{-# REWRITE [][]Ctx #-}

𝔹        [ ξ ]Ty⁺ = 𝔹
Π A B    [ ξ ]Ty⁺ = Π (A [ ξ ]Ty⁺) (B [ ξ ]Ty⁺)
IF t A B [ ξ ]Ty⁺ = IF (t [ ξ ]⁺) (A [ ξ ]Ty⁺) (B [ ξ ]Ty⁺)

postulate [id]Ty⁺ : A [ id𝒮 ]Ty⁺ ≡ A
{-# REWRITE [id]Ty⁺ #-}

postulate [][]Ty⁺ : A [ δ ]Ty [ φ ]Ty⁺ ≡ A [ φ ]Ty⁺ [ δ [ φ ]Tms ]Ty
{-# REWRITE [][]Ty⁺ #-}

postulate [][]Ty⁺⁺ : A [ φ ]Ty⁺ [ ψ ]Ty⁺ ≡ A [ φ ⨾𝒮 ψ ]Ty⁺
{-# REWRITE [][]Ty⁺⁺ #-}

postulate ⌜⌝𝔹[]⁺ : ⌜_⌝𝔹 {Γ = Γ} b [ ξ ]⁺ ≡ ⌜ b ⌝𝔹
{-# REWRITE ⌜⌝𝔹[]⁺ #-}

postulate [id]⁺ : t [ id𝒮 ]⁺ ≡ t
{-# REWRITE [id]⁺ #-}

postulate [][]⁺ : t [ δ ] [ ξ ]⁺ ≡ t [ ξ ]⁺ [ δ [ ξ ]Tms ]
{-# REWRITE [][]⁺ #-}

postulate [][]⁺⁺ : t [ φ ]⁺ [ ψ ]⁺ ≡ t [ φ ⨾𝒮 ψ ]⁺
{-# REWRITE [][]⁺⁺ #-}

[][]𝔹⁺ : ∀ {t : Tm Γ 𝔹} → t [ δ ] [ ξ ]⁺ ≡ t [ ξ ]⁺ [ δ [ ξ ]Tms ]
[][]𝔹⁺  {δ = δ} {t = t} = [][]⁺ {t = t} {δ = δ}
{-# REWRITE [][]𝔹⁺ #-}

ε          [ ξ ]Tms = ε
(δ , t)    [ ξ ]Tms = (δ [ ξ ]Tms) , (t [ ξ ]⁺)
(δ ,eq t~) [ ξ ]Tms = (δ [ ξ ]Tms) ,eq (t~ []~⁺)

postulate id[]Tms : id {Γ = Γ} [ ξ ]Tms ≡ id
{-# REWRITE id[]Tms #-}

postulate [id]Tms : δ [ id𝒮 ]Tms ≡ δ
{-# REWRITE [id]Tms #-}

postulate wk[]   : wk {A = A} [ ξ ]Tms ≡ wk
{-# REWRITE wk[] #-}

postulate 
  wkeq[] : wkeq {t = t} {b = b} [ ξ ]Tms ≡ wkeq
{-# REWRITE wkeq[] #-}

_[_]DefVar : DefVar Ψ Γ A → ∀ (ξ : Wk Φ Ψ) 
           → DefVar Φ (Γ [ ξ ]Ctx) (A [ ξ ]Ty⁺)
f [ id𝒮    ]DefVar = f
f [ φ ⨾𝒮 ψ ]DefVar = f [ φ ]DefVar [ ψ ]DefVar 
f [ wk𝒮    ]DefVar = fs f

vz     [ ξ ]Var = vz
vs   i [ ξ ]Var = vs (i [ ξ ]Var)
vseq i [ ξ ]Var = vseq (i [ ξ ]Var)

(` i)    [ ξ ]⁺ = ` (i [ ξ ]Var) 
(ƛ t)    [ ξ ]⁺ = ƛ (t [ ξ ]⁺)
(t · u)  [ ξ ]⁺ = (t [ ξ ]⁺) · (u [ ξ ]⁺)
TT       [ ξ ]⁺ = TT
FF       [ ξ ]⁺ = FF
call f δ [ ξ ]⁺ = call (f [ ξ ]DefVar) (δ [ ξ ]Tms)

_[_]Def : Def Ψ Γ A → ∀ (φ : Wk Φ Ψ) → Def Φ (Γ [ φ ]Ctx) (A [ φ ]Ty⁺)
if t u v [ φ ]Def = if (t [ φ ]⁺) (u [ φ ]⁺) (v [ φ ]⁺)

lookup𝒮 Ψ (coe~ Γ~ A~ f) = coeDef Γ~ A~ (lookup𝒮 Ψ f)
lookup𝒮 (Ψ ▷ Γ ⇒ A if t then u else v) fz 
  = if (t [ wk𝒮 ]⁺) (u [ wk𝒮 ]⁺) (v [ wk𝒮 ]⁺)
lookup𝒮 (Ψ ▷ Γ ⇒ A if _ then _ else _) (fs f) 
  = lookup𝒮 Ψ f [ wk𝒮 ]Def
