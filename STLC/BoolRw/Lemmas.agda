{-# OPTIONS --rewriting --prop --show-irrelevant --no-require-unique-meta-solutions #-}

open import Utils
open import Common.Sort

-- open import STLC.BoolRw.Syntax
-- open import STLC.SubstEq
open import STLC.Syntax2
open import STLC.SubstEq2

open import STLC.BoolRw.BoolFlip
open import STLC.BoolRw.Reduction

module STLC.BoolRw.Lemmas where

rw* : ¬IsBool {A = A} t → IsBool {A = A} u → t [ rw ]→ u
rw* {u = true}  = rw
rw* {u = false} = rw

data _→*_ : Tm Γ A → Tm Γ A → Set where
  rfl : t →* t
  _∷_ : t [ q→ ]→ u → u →* v → t →* v

_++_ : t →* u → u →* v → t →* v
rfl     ++ r = r
(p ∷ q) ++ r = p ∷ (q ++ r)

fold-→* : (f : Tm Γ A → Tm Δ B) 
        → (∀ {q→} {t u : Tm Γ A} → t [ q→ ]→ u → f t →* f u)
        → t →* u → f t →* f u
fold-→* f g rfl     = rfl
fold-→* f g (p ∷ q) = g p ++ fold-→* f g q

fold-→ : (f : Tm Γ A → Tm Δ B) 
        → (∀ {q→} {t u : Tm Γ A} → t [ q→ ]→ u → f t [ q→ ]→ f u)
        → t →* u → f t →* f u
fold-→ f g p = fold-→* f (λ q → g q ∷ rfl) p

l·* : t →* u → (t · v) →* (u · v)
l·* = fold-→ _ l·

·r* : t →* u → (v · t) →* (v · u)
·r* = fold-→ _ ·r

ƛ* : t →* u → (ƛ t) →* (ƛ u)
ƛ* = fold-→ _ ƛ_

inl* : t →* u → inl {B = B} t →* inl u
inl* = fold-→ _ inl

inr* : t →* u → inr {A = A} t →* inr u
inr* = fold-→ _ inr

𝔹-rec*₁ : t₁ →* t₂ → 𝔹-rec t₁ u v →* 𝔹-rec t₂ u v
𝔹-rec*₁ = fold-→ _ 𝔹-rec₁

𝔹-rec*₂ : u₁ →* u₂ → 𝔹-rec t u₁ v →* 𝔹-rec t u₂ v
𝔹-rec*₂ = fold-→ _ 𝔹-rec₂

𝔹-rec*₃ : v₁ →* v₂ → 𝔹-rec t u v₁ →* 𝔹-rec t u v₂
𝔹-rec*₃ = fold-→ _ 𝔹-rec₃

+-rec*₁ : t₁ →* t₂ → +-rec t₁ u v →* +-rec t₂ u v
+-rec*₁ = fold-→ _ +-rec₁

+-rec*₂ : u₁ →* u₂ → +-rec t u₁ v →* +-rec t u₂ v
+-rec*₂ = fold-→ _ +-rec₂

+-rec*₃ : v₁ →* v₂ → +-rec t u v₁ →* +-rec t u v₂
+-rec*₃ = fold-→ _ +-rec₃

rfl≡ : t ≡ u → t →* u
rfl≡ refl = rfl

data Sub- : ∀ Δ Γ → Tms[ T ] Δ Γ → Tms[ V ] Γ Δ → Set where
  <_>- : IsBool t → Sub- Γ (Γ , A) < t > wk
  _^-_ : Sub- Δ Γ δ σ → ∀ A → Sub- (Δ , A) (Γ , A) (δ ^ A) (σ ^ A)

boolsub : ∀ (i : Var Γ A) → Sub- Δ Γ δ σ 
        → IsBool (i [ δ ]) ⊎ ((` i) ≡ i [ δ ] [ σ ])
boolsub vz     < b >-    = inl b
boolsub vz     (δσ ^- A) = inr refl
boolsub (vs i) < b >-    = inr refl
boolsub (vs i) (δσ ^- A) with boolsub i δσ 
... | inl b  = inl (b [ wk ]b)
... | inr eq = inr (cong _[ wk ] eq)

boolsub→ : ∀ (t : Tm Γ A) → Sub- Δ Γ δ σ → t →* (t [ δ ] [ σ ])
boolsub→ {σ = σ} (` i) δσ with boolsub i δσ
... | inl b  = rw* tt (b [ σ ]b) ∷ rfl
... | inr eq = rfl≡ eq
boolsub→ (t · u)       δσ = l·* (boolsub→ t δσ) ++ ·r* (boolsub→ u δσ)
boolsub→ (ƛ t)         δσ = ƛ* (boolsub→ t (δσ ^- _))
boolsub→ true          δσ = rfl
boolsub→ false         δσ = rfl
boolsub→ (𝔹-rec t u v) δσ 
  = 𝔹-rec*₁ (boolsub→ t δσ) ++ (𝔹-rec*₂ (boolsub→ u δσ) 
                            ++  𝔹-rec*₃ (boolsub→ v δσ))
boolsub→ (inl t)       δσ = inl* (boolsub→ t δσ)
boolsub→ (inr t)       δσ = inr* (boolsub→ t δσ)
boolsub→ (+-rec t u v) δσ 
  = +-rec*₁ (boolsub→ t δσ) ++ (+-rec*₂ (boolsub→ u (δσ ^- _)) 
                            ++  +-rec*₃ (boolsub→ v (δσ ^- _)))

-- Todo: Generalise to parallel substitutions (we don't actually need to, but
-- I think it would be neater)
data Sub+ : ∀ Δ Γ → Tms[ T ] Δ Γ → Set where
  <_>+ : ¬IsBool t → Sub+ Γ (Γ , A) < t >
  _^+_ : Sub+ Δ Γ δ → ∀ A → Sub+ (Δ , A) (Γ , A) (δ ^ A)

[_]b+⁻¹_ : Sub+ Δ Γ δ → IsBool (t [ δ ]) → IsBool t
[_]b+⁻¹_ {t = true}    δ+       tt = tt
[_]b+⁻¹_ {t = false}   δ+       tt = tt
[_]b+⁻¹_ {t = ` vz}    < ¬b >+  b  = ¬bool← ¬b b
[_]b+⁻¹_ {t = ` vs i} (δ+ ^+ _) b  = [_]b+⁻¹_ {t = (` i)} δ+ ([ wk ]b⁻¹ b)

_[_]¬b+ : ¬IsBool t → Sub+ Δ Γ δ → ¬IsBool (t [ δ ])
¬b [ δ+ ]¬b+ = ¬bool→ λ b → ¬bool← ¬b ([ δ+ ]b+⁻¹ b)

_[_]→+ : t [ q→ ]→ u → Sub+ Δ Γ δ → (t [ δ ]) [ q→ ]→ (u [ δ ])
_[_]→+ {δ = δ} (rw ¬b b) δ+ = rw (¬b [ δ+ ]¬b+) (b [ δ ]b)
β refl refl [ δ+ ]→+ = β refl refl
rec-true    [ δ+ ]→+ = rec-true
rec-false   [ δ+ ]→+ = rec-false
(l· p)      [ δ+ ]→+ = l· (p [ δ+ ]→+)
(·r p)      [ δ+ ]→+ = ·r (p [ δ+ ]→+)
(ƛ p)       [ δ+ ]→+ = ƛ (p [ δ+ ^+ _ ]→+)
(𝔹-rec₁ p)  [ δ+ ]→+ = 𝔹-rec₁ (p [ δ+ ]→+)
(𝔹-rec₂ p)  [ δ+ ]→+ = 𝔹-rec₂ (p [ δ+ ]→+)
(𝔹-rec₃ p)  [ δ+ ]→+ = 𝔹-rec₃ (p [ δ+ ]→+)
(+-rec₁ p)  [ δ+ ]→+ = +-rec₁ (p [ δ+ ]→+)
(+-rec₂ p)  [ δ+ ]→+ = +-rec₂ (p [ δ+ ^+ _ ]→+)
(+-rec₃ p)  [ δ+ ]→+ = +-rec₃ (p [ δ+ ^+ _ ]→+)
(inl p)     [ δ+ ]→+ = inl (p [ δ+ ]→+)
(inr p)     [ δ+ ]→+ = inr (p [ δ+ ]→+)
