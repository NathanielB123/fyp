{-# OPTIONS --rewriting --prop --show-irrelevant #-}

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

-- rw₁ : ∀ {δ : Tms Δ Γ} {γ : Tms Θ Δ} {A : Ty Γ} {u : Tm Θ (A [ δ ⨾ γ ]T)}
--   → lookup (vz {A = A [ δ ]T}) ((γ ⁺ (A [ δ ⨾ γ ]T)) , (` vz)) [ id , u ] ≡ u
-- rw₁ {δ = δ} {γ = γ} {u = u} = lookup-vz {δ = (γ ⁺ (A [ δ ⨾ γ ]T))}

data Ne : ∀ Γ A → Tm Γ A → Set
data Nf : ∀ Γ A → Tm Γ A → Set where
  TT : Nf Γ 𝔹 TT
  FF : Nf Γ 𝔹 FF
  ne : Ne Γ A t → Nf Γ A t

-- We technically could use renamings rather than thinnings, but for SCDef
-- we definitely need thinnings, so might as well practice!
data Thin : ∀ Δ Γ → Tms Δ Γ → Set

data Env : ∀ Δ Γ → Tms Δ Γ → Set
Val      : ∀ Γ (A : Ty Γ) Δ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]T) → Env Δ Γ δ → Set
eval     : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ (t [ δ ]) ρ
eval*    : ∀ δ (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)

data Env where
  coe~ : ∀ Δ~ Γ~ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Env Δ₁ Γ₁ δ₁ → Env Δ₂ Γ₂ δ₂

  ε   : Env Δ ε ε
  _,_ : ∀ (ρ : Env Δ Γ δ) → Val Γ A Δ δ t ρ → Env Δ (Γ , A) (δ , t)

idℰ : Env Γ Γ id

_[_]ℰ : Env Δ Γ δ → Thin Θ Δ σ → Env Θ Γ (δ ⨾ σ)

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

if-Val Γ A B Δ δ {u[]} t ρ TT     = Val Γ A Δ δ (coe~ rfl~ ifTT t) ρ
if-Val Γ A B Δ δ {u[]} t ρ FF     = Val Γ B Δ δ (coe~ rfl~ ifFF t) ρ
if-Val Γ A B Δ δ {u[]} t ρ (ne _) = Ne Δ (if u[] (A [ δ ]T) (B [ δ ]T)) t
