{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Utils
-- open import STLC.BoolRw.Syntax
-- open import STLC.SubstEq
open import STLC.Syntax2
open import STLC.SubstEq2
open import STLC.BoolRw.Views

module STLC.BoolRw.SpontRed where

data Sort→ : Set where
  β rw : Sort→ 

variable
  q→ r→ s→ : Sort→

-- This relation is an over-approximation of the reduction rules we actually
-- plan on using. E.g. it allows rewriting arbitrary boolean terms 
-- "spontaneously" to 'true' or 'false' with no restrictions.
--
-- The idea is that accessibility w.r.t. this over-approximation implies
-- accessibility w.r.t. the "true" reduction relation.
data _[_]→_ : Tm Γ A → Sort→ → Tm Γ A → Set where
  -- We do a little Fording
  β         : ∀ {ƛt t[u]} → ƛt ≡ ƛ t → t[u] ≡ t [ < u > ] → (ƛt · u) [ β ]→ t[u]
  rec-true  : 𝔹-rec true u v [ β ]→ u
  rec-false : 𝔹-rec false u v [ β ]→ v
  rw        : ¬ t/f {A = 𝔹'} t → t/f {A = 𝔹'} u → t [ rw ]→ u

  l·     : t₁ [ q→ ]→ t₂ → (t₁ · u) [ q→ ]→ (t₂ · u) 
  ·r     : u₁ [ q→ ]→ u₂ → (t · u₁) [ q→ ]→ (t · u₂)
  ƛ_     : t₁ [ q→ ]→ t₂ → (ƛ t₁)   [ q→ ]→ (ƛ t₂)
  𝔹-rec₁ : t₁ [ q→ ]→ t₂ → 𝔹-rec t₁ u v [ q→ ]→ 𝔹-rec t₂ u v
  𝔹-rec₂ : u₁ [ q→ ]→ u₂ → 𝔹-rec t u₁ v [ q→ ]→ 𝔹-rec t u₂ v
  𝔹-rec₃ : v₁ [ q→ ]→ v₂ → 𝔹-rec t u v₁ [ q→ ]→ 𝔹-rec t u v₂
  +-rec₁ : t₁ [ q→ ]→ t₂ → +-rec t₁ u v [ q→ ]→ +-rec t₂ u v
  +-rec₂ : u₁ [ q→ ]→ u₂ → +-rec t u₁ v [ q→ ]→ +-rec t u₂ v
  +-rec₃ : v₁ [ q→ ]→ v₂ → +-rec t u v₁ [ q→ ]→ +-rec t u v₂

  -- TODO: Add beta laws for coproducts
  inl    : t₁ [ q→ ]→ t₂ → inl {B = B} t₁ [ q→ ]→ inl t₂
  inr    : t₁ [ q→ ]→ t₂ → inr {A = A} t₁ [ q→ ]→ inr t₂

_→β_ : Tm Γ A → Tm Γ A → Set
_→β_ = _[ β ]→_

_→rw_ : Tm Γ A → Tm Γ A → Set
_→rw_ = _[ rw ]→_

_[_]→ : t [ q→ ]→ u → (δ : Vars Δ Γ) 
      → (t [ δ ]) [ q→ ]→ (u [ δ ])
β refl refl [ δ ]→ = β refl refl
rec-true    [ δ ]→ = rec-true
rec-false   [ δ ]→ = rec-false
rw ¬b b     [ δ ]→ = rw (¬b [ δ ]¬b) (b [ δ ]b) 
l· p        [ δ ]→ = l· (p [ δ ]→)
·r p        [ δ ]→ = ·r (p [ δ ]→)
𝔹-rec₁ p    [ δ ]→ = 𝔹-rec₁ (p [ δ ]→)
𝔹-rec₂ p    [ δ ]→ = 𝔹-rec₂ (p [ δ ]→)
𝔹-rec₃ p    [ δ ]→ = 𝔹-rec₃ (p [ δ ]→)
+-rec₁ p    [ δ ]→ = +-rec₁ (p [ δ ]→)
+-rec₂ p    [ δ ]→ = +-rec₂ (p [ δ ^ _ ]→)
+-rec₃ p    [ δ ]→ = +-rec₃ (p [ δ ^ _ ]→)
inl p       [ δ ]→ = inl (p [ δ ]→)
inr p       [ δ ]→ = inr (p [ δ ]→)
(ƛ p)       [ δ ]→ = ƛ (p [ δ ^ _ ]→)

ƛ[_]⁻¹_ : (δ : Vars Δ Γ) → t [ δ ] ≡ ƛ u → ∃ λ u⁻¹ → t ≡ ƛ u⁻¹
ƛ[_]⁻¹_ {t = ƛ t} δ refl = _ Σ, refl 

[_]→⁻¹_ : ∀ (δ : Vars Δ Γ) → (t [ δ ]) [ q→ ]→ u
        → ∃ λ u⁻¹ → (t [ q→ ]→ u⁻¹) × (u⁻¹ [ δ ] ≡ u)
[_]→⁻¹_ {t = t · u} δ (β p q) with t′ Σ, refl ← ƛ[_]⁻¹_ {t = t} δ p
                               with refl       ← p
                               with refl       ← q
  = _ Σ, β refl refl Σ, refl
[_]→⁻¹_ {t = 𝔹-rec true u v}  δ rec-true  = u Σ, rec-true  Σ, refl
[_]→⁻¹_ {t = 𝔹-rec false u v} δ rec-false = v Σ, rec-false Σ, refl

[_]→⁻¹_ {t = ƛ t} δ (ƛ p) 
  = let u⁻¹   Σ, p⁻¹   Σ, q = [_]→⁻¹_ {t = t} (δ ^ _) p 
     in ƛ u⁻¹ Σ, ƛ p⁻¹ Σ, cong ƛ_ q

[_]→⁻¹_ {t = t · u} δ (l· p)
  = let t⁻¹     Σ, p′    Σ, q = [_]→⁻¹_ {t = t} δ p
     in t⁻¹ · u Σ, l· p′ Σ, cong (_· (u [ δ ])) q
[_]→⁻¹_ {t = t · u} δ (·r p)
  = let u⁻¹     Σ, p′    Σ, q = [_]→⁻¹_ {t = u} δ p
     in t · u⁻¹ Σ, ·r p′ Σ, cong (t [ δ ] ·_) q

[_]→⁻¹_ {t = 𝔹-rec t u v} δ (𝔹-rec₁ p) 
  = let t⁻¹           Σ, p′        Σ, q = [_]→⁻¹_ {t = t} δ p
     in 𝔹-rec t⁻¹ u v Σ, 𝔹-rec₁ p′ Σ, cong (λ □ → 𝔹-rec □ (u [ δ ]) (v [ δ ])) q
[_]→⁻¹_ {t = 𝔹-rec t u v} δ (𝔹-rec₂ p) 
  = let u⁻¹           Σ, p′        Σ, q = [_]→⁻¹_ {t = u} δ p
     in 𝔹-rec t u⁻¹ v Σ, 𝔹-rec₂ p′ Σ, cong (λ □ → 𝔹-rec (t [ δ ]) □ (v [ δ ])) q
[_]→⁻¹_ {t = 𝔹-rec t u v} δ (𝔹-rec₃ p) 
  = let v⁻¹           Σ, p′        Σ, q = [_]→⁻¹_ {t = v} δ p
     in 𝔹-rec t u v⁻¹ Σ, 𝔹-rec₃ p′ Σ, cong (λ □ → 𝔹-rec (t [ δ ]) (u [ δ ]) □) q

[_]→⁻¹_ {t = +-rec t u v} δ (+-rec₁ p) 
  = let t⁻¹           Σ, p′        Σ, q = [_]→⁻¹_ {t = t} δ p
     in +-rec t⁻¹ u v Σ, +-rec₁ p′ 
     Σ, cong (λ □ → +-rec □ (u [ δ ^ _ ]) (v [ δ ^ _ ])) q
[_]→⁻¹_ {t = +-rec t u v} δ (+-rec₂ p) 
  = let u⁻¹           Σ, p′        Σ, q = [_]→⁻¹_ {t = u} (δ ^ _) p
     in +-rec t u⁻¹ v Σ, +-rec₂ p′ 
     Σ, cong (λ □ → +-rec (t [ δ ]) □ (v [ δ ^ _ ])) q
[_]→⁻¹_ {t = +-rec t u v} δ (+-rec₃ p) 
  = let v⁻¹           Σ, p′        Σ, q = [_]→⁻¹_ {t = v} (δ ^ _) p
     in +-rec t u v⁻¹ Σ, +-rec₃ p′ 
     Σ, cong (λ □ → +-rec (t [ δ ]) (u [ δ ^ _ ]) □) q


[_]→⁻¹_ {t = inl t} δ (inl p)
  = let t⁻¹     Σ, p′     Σ, q = [_]→⁻¹_ {t = t} δ p
     in inl t⁻¹ Σ, inl p′ Σ, cong inl q
[_]→⁻¹_ {t = inr t} δ (inr p)
  = let t⁻¹     Σ, p′     Σ, q = [_]→⁻¹_ {t = t} δ p
     in inr t⁻¹ Σ, inr p′ Σ, cong inr q

[_]→⁻¹_ {u = true}  δ (rw ¬b _) = true  Σ, rw ([ δ ]¬b⁻¹ ¬b) true  Σ, refl
[_]→⁻¹_ {u = false} δ (rw ¬b _) = false Σ, rw ([ δ ]¬b⁻¹ ¬b) false Σ, refl

record SN→ Γ A (t : Tm Γ A) : Set where
  constructor acc
  inductive
  pattern
  field
    step : t [ q→ ]→ u → SN→ Γ A u 
open SN→ public

SN→l· : SN→ Γ B (t · u) → SN→ Γ (A ⇒ B) t
SN→l· (acc f) = acc (λ p → SN→l· (f (l· p)))

SN→·r : SN→ Γ B (t · u) → SN→ Γ A u
SN→·r (acc f) = acc (λ p → SN→·r (f (·r p)))

SN→𝔹-rec₁ : SN→ Γ A (𝔹-rec t u v) → SN→ Γ 𝔹' t
SN→𝔹-rec₁ (acc f) = acc (λ p → SN→𝔹-rec₁ (f (𝔹-rec₁ p)))

SN→𝔹-rec₂ : SN→ Γ A (𝔹-rec t u v) → SN→ Γ A u
SN→𝔹-rec₂ (acc f) = acc (λ p → SN→𝔹-rec₂ (f (𝔹-rec₂ p)))

SN→𝔹-rec₃ : SN→ Γ A (𝔹-rec t u v) → SN→ Γ A v
SN→𝔹-rec₃ (acc f) = acc (λ p → SN→𝔹-rec₃ (f (𝔹-rec₃ p)))

true-sn : SN→ Γ 𝔹' true
true-sn = acc (λ where (rw ¬b _) → ⊥-elim (¬b true))

false-sn : SN→ Γ 𝔹' false
false-sn = acc (λ where (rw ¬b _) → ⊥-elim (¬b false))

_[_]sn : SN→ Γ A t → ∀ (δ : Vars Δ Γ) → SN→ Δ A (t [ δ ])
acc a [ δ ]sn = acc (λ p → let u⁻¹ Σ, q Σ, r = [ δ ]→⁻¹ p 
                            in subst (SN→ _ _) r (a q [ δ ]sn))

[_]sn⁻¹_ : (δ : Vars Δ Γ) → SN→ Δ A (t [ δ ]) → SN→ Γ A t
[ δ ]sn⁻¹ acc a = acc (λ p → [ δ ]sn⁻¹ a (p [ δ ]→))
  