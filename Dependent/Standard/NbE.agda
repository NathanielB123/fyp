{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils

open import Dependent.Standard.Strict

module Dependent.Standard.NbE where 

-- Bonus rewrites courtesy of #7602
postulate 
  rw₁ : lookup (vz {A = A [ δ ]T}) ((γ ⁺ (A [ δ ⨾ γ ]T)) , (` vz)) ≡ ` vz
-- rw₁ {A = A} {δ = δ} {γ = γ} 
--   = lookup-vz {δ = (γ ⁺ (A [ δ ⨾ γ ]T))} {t = ` vz}
{-# REWRITE rw₁ #-}

postulate 
  rw₂ : ∀ {t : Tm Θ (A [ δ ⨾ γ ]T)} → lookup vz (id , t) ≡ t
{-# REWRITE rw₂ #-}


data Ne : ∀ Γ A → Tm Γ A → Set
data Nf : ∀ Γ A → Tm Γ A → Set where
  TT : Nf Γ 𝔹 TT
  FF : Nf Γ 𝔹 FF
  ne : Ne Γ A t → Nf Γ A t

-- We technically could use renamings rather than thinnings, but for SCDef
-- we definitely need thinnings, so might as well practice!
data Thin : ∀ Δ Γ → Tms Δ Γ → Set

idᵀʰ : Thin Γ Γ id
wkᵀʰ : Thin (Γ , A) Γ wk

data Env : ∀ Δ Γ → Tms Δ Γ → Set
Val      : ∀ Γ (A : Ty Γ) Δ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]T) → Env Δ Γ δ → Set
eval     : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ (t [ δ ]) ρ
eval*    : ∀ δ (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)

variable
  ρ ρ₁ ρ₂ : Env Δ Γ δ

data Env where
  coe~ : ∀ Δ~ Γ~ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Env Δ₁ Γ₁ δ₁ → Env Δ₂ Γ₂ δ₂

  ε   : Env Δ ε ε
  _,_ : ∀ (ρ : Env Δ Γ δ) → Val Γ A Δ δ t ρ → Env Δ (Γ , A) (δ , t)

idℰ : Env Γ Γ id

_[_]ℰ : Env Δ Γ δ → Thin Θ Δ σ → Env Θ Γ (δ ⨾ σ)
_[_]𝒱 : Val Γ A Δ δ t ρ → ∀ (σᵀʰ : Thin Θ Δ σ) 
      → Val Γ A Θ (δ ⨾ σ) (t [ σ ]) (ρ [ σᵀʰ ]ℰ)

-- TODO: Prove these lemmas and stop using the mutual hack
postulate [id]ℰ : ρ [ idᵀʰ ]ℰ ≡ ρ
{-# REWRITE [id]ℰ #-}

if-Val : ∀ Γ (A B : Ty Γ) Δ (δ : Tms Δ Γ) {u[]} 
       → Tm Δ (if u[] (A [ δ ]T) (B [ δ ]T)) 
       → ∀ (ρ : Env Δ Γ δ) → Val Γ 𝔹 Δ δ u[] ρ → Set

Val Γ (coe~ Γ~ A) Δ δ t ρ 
  = Val _ A Δ (coe~ rfl~ (sym~ Γ~) δ) 
              (coe~ rfl~ (sym~ {Γ~ = Γ~} coh [ coh ]T~) t) 
              (coe~ rfl~ (sym~ Γ~) coh ρ)
Val Γ 𝔹           Δ δ t ρ = Nf Δ 𝔹 t
Val Γ (Π A B)     Δ δ t ρ 
  = ∀ {Θ γ} (γᵀʰ : Thin Θ Δ γ) {u}
      (uⱽ : Val Γ A Θ (δ ⨾ γ) u (ρ [ γᵀʰ ]ℰ))
  → Val (Γ , A) B Θ ((δ ⨾ γ) , u) ((t [ γ ]) · u) ((ρ [ γᵀʰ ]ℰ) , uⱽ)
Val Γ (if b A B)  Δ δ t ρ = if-Val Γ A B Δ δ t ρ (eval b ρ)

-- coe𝒱 : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
--      → Tm~ Δ~ (A~ [ δ~ ]T~) t₁ t₂
--      → Val Γ₁ A₁ Δ₁ δ₁ t₁ ρ₁ → Val Γ₂ A₂ Δ₂ δ₂ t₂ ρ₂

-- This is a pretty restrictive |coe| that doesn't account for changing
-- the substitution/weakening. We will probably need to generalise
coe𝒱 : ∀ (A~ : Ty~ rfl~ A₁ A₂) 
     → Tm~ rfl~ (A~ [ rfl~ ]T~) t₁ t₂
     → Val Γ A₁ Δ δ t₁ ρ → Val Γ A₂ Δ δ t₂ ρ

if-Val Γ A B Δ δ {u[]} t ρ TT     = Val Γ A Δ δ (coe~ rfl~ ifTT t) ρ
if-Val Γ A B Δ δ {u[]} t ρ FF     = Val Γ B Δ δ (coe~ rfl~ ifFF t) ρ
if-Val Γ A B Δ δ {u[]} t ρ (ne _) = Ne Δ (if u[] (A [ δ ]T) (B [ δ ]T)) t

lookupℰ : ∀ (i : Var Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ (lookup i δ) ρ
lookupℰ (coe~ Γ~ x i) ρ                 = {!   !}
lookupℰ vz            (ρ , uⱽ) = {! uⱽ [ wkᵀʰ ]𝒱   !}
lookupℰ (vs i)        (ρ , uⱽ) = {!   !}
lookupℰ i             (coe~ Δ~ Γ~ δ~ ρ) = {!   !}

eval (coe~ Γ~ A~ t) ρ = {!!}
eval (` i)          ρ = lookupℰ i ρ
eval {A = Π A B} {δ = δ} (ƛ t) ρ γᵀʰ uⱽ
  = coe𝒱 (rfl~ {A = B}) (sym~ β)
         (eval t ((ρ [ γᵀʰ ]ℰ) , uⱽ)) 
eval (t · u)        ρ = {!eval t ρ idᵀʰ (eval u ρ)   !}
eval TT             ρ = TT
eval FF             ρ = FF
eval (if t u v)     ρ = {!   !}
