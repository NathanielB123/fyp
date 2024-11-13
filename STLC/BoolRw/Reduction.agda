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

data _[_]→_ : Tm Γ A → Sort→ → Tm Γ A → Set where
  β         : ((ƛ t) · u)   [ β ]→ (t [ < u > ])
  rec-true  : 𝔹-rec true  t u [ β ]→ t
  rec-false : 𝔹-rec false t u [ β ]→ u
  rw        : ¬IsBool {A = 𝔹'} t → IsBool {A = 𝔹'} u → t [ rw ]→ u

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

-- Structural ordering on terms
data _<_ : Tm Γ A → Tm Δ B → Set where
  l· : t < (t · u)
  ·r : u < (t · u)

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

-- Structural ordering augmented with reduction
data Struc : ∀ Γ A → Tm Γ A → Set where
  acc : (∀ {q→ u}  → t [ q→ ]→ u → Struc Γ A u)
      → (∀ {Δ B u} → u < t       → Struc Δ B u)
      → Struc Γ A t

struc< : Struc Γ A t → u < t → Struc Δ B u
struc< (acc a b) = b

struc-l· : Struc Γ B (t · u) → Struc Γ (A ⇒ B) t
struc-l· (acc a b) = acc (λ p → struc-l· (a (l· p))) (λ p → struc< (b l·) p)

-- Hmm
-- sn-struc : SN Γ A t → Struc Γ A t

-- This isn't really what I want to prove, but it does seem easier...
-- sn-struc-acc : SN Γ A t → t [ q→ ]→ u₁ → v < u₂ → u₁ ≡ u₂ → Struc Δ B v

-- sn-struc (acc a) = acc (λ p → {!!}) (λ q → sn-struc-acc (acc a) {!!} q refl)

-- -- sn-struc-l· : SN Γ B (t · u) → Struc Γ (A ⇒ B) t
-- -- sn-struc-l· (acc a) = acc (λ p → sn-struc-l· (a (l· p))) (λ p → {!!})

-- -- {-# TERMINATING #-} 

-- sn-struc-acc {t = t₁@(` _) · t₂} (acc a) (·r p) l· refl = {!   !}
-- sn-struc-acc {t = t₁@(_ · _) · t₂} (acc a) (l· p) l· refl = {!   !}
-- sn-struc-acc {t = t₁@(_ · _) · t₂} (acc a) (·r p) l· refl = {!   !}
-- sn-struc-acc {t = t₁@(𝔹-rec _ _ _) · t₂} (acc a) (l· p) l· refl = {!   !}
-- sn-struc-acc {t = t₁@(𝔹-rec _ _ _) · t₂} (acc a) (·r p) l· refl = {!   !}
-- sn-struc-acc {t = (ƛ t₁) · t₂} (acc a) β l· eq 
--   = struc-l· (subst (Struc _ _) eq (sn-struc (a β)))
-- sn-struc-acc {t = (ƛ t₁) · t₂} (acc a) (rw x x₁) l· eq = {!   !}
-- sn-struc-acc {t = (ƛ t₁) · t₂} (acc a) (l· p) l· eq = {!   !}
-- sn-struc-acc {t = (ƛ t₁) · t₂} (acc a) (·r p) l· eq = {!   !}
-- sn-struc-acc {t = 𝔹-rec t₁ t₂ t₃} (acc a) rec-true  l· refl = {!   !}
-- sn-struc-acc {t = 𝔹-rec t₁ t₂ t₃} (acc a) rec-false l· refl = {!   !}
-- sn-struc-acc (acc a) (rw ¬b b) l· refl = {!   !}
-- sn-struc-acc {t = t} (acc a) p ·r eq = {!   !}

-- sn-struc-acc (acc a) q = acc (λ p → sn-struc {!!}) 
--   λ where l· → struc-l· (sn-struc (a (l· {!!})))
--           ·r → {!!}
 
  