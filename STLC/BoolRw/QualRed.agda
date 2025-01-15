{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Utils

open import STLC.BoolRw.Syntax
open import STLC.BoolRw.BoolFlip
open import STLC.BoolRw.Reduction

module STLC.BoolRw.QualRed where

record Rw (Γ : Ctx) : Set where
  field
    lhs : Tm Γ 𝔹'
    rhs : Tm Γ 𝔹'
    l¬b : ¬IsBool lhs
    rb  : IsBool rhs
open Rw public

record Rws (Γ : Ctx) : Set where
  constructor mk
  field
    {len} : ℕ
    rws : Fin len → Rw Γ
open Rws public

uhh : ∀ {n} → Fin n → Fin (pred n) → Fin n
uhh zero    y       = suc y
uhh (suc x) zero    = zero
uhh (suc x) (suc y) = suc (uhh x y)

_-_ : (Ξ : Rws Γ) → Fin (Ξ .len) → Rws Γ
Ξ - n = mk λ m → Ξ .rws (uhh n m)

variable
  Ξ : Rws Γ

_[_]rws : Rws Γ → Vars Δ Γ → Rws Δ

_↦_∈_ : Tm Γ 𝔹' → Tm Γ 𝔹' → Rws Γ → Set

data _⊢_→s_ (Ξ : Rws Γ) : Tm Γ A → Tm Γ A → Set where
  β         : ∀ {ƛt t[u]} → ƛt ≡ ƛ t → t[u] ≡ t [ < u > ] → Ξ ⊢ (ƛt · u) →s t[u]
  rw        : t ↦ u ∈ Ξ → Ξ ⊢ t →s u
  rec-true  : Ξ ⊢ 𝔹-rec true u v →s u
  rec-false : Ξ ⊢ 𝔹-rec false u v →s v

  l·     : Ξ ⊢ t₁ →s t₂ → Ξ ⊢ (t₁ · u) →s (t₂ · u) 
  ·r     : Ξ ⊢ u₁ →s u₂ → Ξ ⊢ (t · u₁) →s (t · u₂)
  ƛ_     : (Ξ [ id ⁺ _ ]rws) ⊢ t₁ →s t₂ → Ξ ⊢ (ƛ t₁) →s (ƛ t₂)
  𝔹-rec₁ : Ξ ⊢ t₁ →s t₂ → Ξ ⊢ 𝔹-rec t₁ u v →s 𝔹-rec t₂ u v
  𝔹-rec₂ : Ξ ⊢ u₁ →s u₂ → Ξ ⊢ 𝔹-rec t u₁ v →s 𝔹-rec t u₂ v
  𝔹-rec₃ : Ξ ⊢ v₁ →s v₂ → Ξ ⊢ 𝔹-rec t u v₁ →s 𝔹-rec t u v₂

s[]→ : Ξ ⊢ t →s u → ∃ λ q→ → t [ q→ ]→ u
s[]→ (β p q)   = β Σ, β p q
s[]→ (rw p)    = rw Σ, rw {! !} {! !}
s[]→ rec-true  = β Σ, {! !}
s[]→ rec-false = β Σ, {! !}
s[]→ (l· p) = {!   !}
s[]→ (·r p) = {!   !}
s[]→ (ƛ p) = {!   !}
s[]→ (𝔹-rec₁ p) = {!   !}
s[]→ (𝔹-rec₂ p) = {!   !}
s[]→ (𝔹-rec₃ p) = {!   !}

data _⊢SN_ (Ξ : Rws Γ) (t : Tm Γ A) : Set where
  acc : (∀ {u} → Ξ ⊢ t →s u → Ξ ⊢SN u) → Ξ ⊢SN t

⊢sn-helper : SN Γ A t → Ξ ⊢SN t 
⊢sn-helper (acc a) = acc λ p → {!p  !}

_⊢sn_ : ∀ Ξ (t : Tm Γ A) → Ξ ⊢SN t
Ξ ⊢sn t = {!  !}

_⊢nf_ : ∀ Ξ (t : Tm Γ A) → Set
Ξ ⊢nf t = ∀ {u} → ¬ Ξ ⊢ t →s u

⊢Rws : Rws Γ → Set
⊢Rws Ξ = ∀ {n} → (Ξ - n) ⊢nf (Ξ .rws) n .lhs

conf : Ξ ⊢ t →s u₁ → Ξ ⊢ t →s u₂  
     → ∃ λ v → Ξ ⊢ u₁ →s v × Ξ ⊢ u₂ →s v 