{-# OPTIONS --prop --show-irrelevant #-}

open import Utils
open import STLC.Syntax
-- open import STLC.SubstEq
open import STLC.BoolRw.BoolFlip

module STLC.BoolRw.Reduction where

data Sort→ : Set where
  β rw : Sort→ 

variable
  q→ r→ s→ : Sort→

-- This relation is an over-approximation of the reduction rules we actually
-- plan on using. E.g. it allows '𝔹-rec true t u v' to reduce to 'v' as well as
-- 'u', and it allows rewriting arbitrary boolean terms to 'true' or 'false'
-- with no restrictions.
--
-- The idea is that accessibility w.r.t. this over-approximation implies
-- accessibility w.r.t. the "true" reduction relation, but the well-foundedness
-- proofs are easier.
data _[_]→_ : Tm Γ A → Sort→ → Tm Γ A → Set where
  -- We do a little Fording
  β        : ∀ {ƛt t[u]} → ƛt ≡ ƛ t → t[u] ≡ t [ < u > ] → (ƛt · u) [ β ]→ t[u]
  𝔹-rec-β₁ : IsBool t → 𝔹-rec t u v [ β ]→ u
  𝔹-rec-β₂ : IsBool t → 𝔹-rec t u v [ β ]→ v
  rw       : ¬IsBool {A = 𝔹'} t → IsBool {A = 𝔹'} u → t [ rw ]→ u

  l·     : t₁ [ q→ ]→ t₂ → (t₁ · u) [ q→ ]→ (t₂ · u) 
  ·r     : u₁ [ q→ ]→ u₂ → (t · u₁) [ q→ ]→ (t · u₂)
  ƛ_     : t₁ [ q→ ]→ t₂ → (ƛ t₁)   [ q→ ]→ (ƛ t₂)
  𝔹-rec₁ : t₁ [ q→ ]→ t₂ → 𝔹-rec t₁ u v [ q→ ]→ 𝔹-rec t₂ u v
  𝔹-rec₂ : u₁ [ q→ ]→ u₂ → 𝔹-rec t u₁ v [ q→ ]→ 𝔹-rec t u₂ v
  𝔹-rec₃ : v₁ [ q→ ]→ v₂ → 𝔹-rec t u v₁ [ q→ ]→ 𝔹-rec t u v₂

_→β_ : Tm Γ A → Tm Γ A → Set
_→β_ = _[ β ]→_

_→rw_ : Tm Γ A → Tm Γ A → Set
_→rw_ = _[ rw ]→_

data SN Γ A : Tm Γ A → Set where
  acc : (∀ {q→ u} → t [ q→ ]→ u → SN Γ A u) → SN Γ A t

sn : SN Γ A t → t [ q→ ]→ u → SN Γ A u
sn (acc a) p = a p

SN-l· : SN Γ B (t · u) → SN Γ (A ⇒ B) t
SN-l· (acc f) = acc (λ p → SN-l· (f (l· p)))

SN-·r : SN Γ B (t · u) → SN Γ A u
SN-·r (acc f) = acc (λ p → SN-·r (f (·r p)))

SN-𝔹-rec₁ : SN Γ A (𝔹-rec t u v) → SN Γ 𝔹' t
SN-𝔹-rec₁ (acc f) = acc (λ p → SN-𝔹-rec₁ (f (𝔹-rec₁ p)))

SN-𝔹-rec₂ : SN Γ A (𝔹-rec t u v) → SN Γ A u
SN-𝔹-rec₂ (acc f) = acc (λ p → SN-𝔹-rec₂ (f (𝔹-rec₂ p)))

SN-𝔹-rec₃ : SN Γ A (𝔹-rec t u v) → SN Γ A v
SN-𝔹-rec₃ (acc f) = acc (λ p → SN-𝔹-rec₃ (f (𝔹-rec₃ p)))
