{-# OPTIONS --prop #-}

open import Utils
open import STLC.Syntax

-- Example of trying to augment reduction with structural orderings
-- The real use-case is in 'BoolRw.Reduction', but there are quite a few extra
-- details
module STLC.ReductionExample where

-- Heterogeneous because this gives a bit of extra flexibility later, but this
-- shouldn't be necessary
data _→β_ : Tm Γ A → Tm Δ B → Set where
  β  : ((ƛ t) · u) →β (t [ < u > ])
  l· : t₁ →β t₂ → (t₁ · u) →β (t₂ · u) 
  ·r : u₁ →β u₂ → (t · u₁) →β (t · u₂)
  ƛ_ : t₁ →β t₂ → (ƛ t₁)   →β (ƛ t₂)

data SN Γ A : Tm Γ A → Set where
  acc : (∀ {u} → t →β u → SN Γ A u) → SN Γ A t

-- Structural ordering on terms
data _<_ : Tm Γ A → Tm Δ B → Set where
  l· : t < (t · u)
  ·r : u < (t · u)
  ƛ_ : t < (ƛ t)

-- Strong normalisability augmented with structural ordering
data Struc : ∀ Γ A → Tm Γ A → Set where
  acc : (∀ {u}     → t →β u → Struc Γ A u)
      → (∀ {Δ B u} → u < t  → Struc Δ B u)
      → Struc Γ A t

SN-l· : SN Γ B (t · u) → SN Γ (A ⇒ B) t
SN-l· (acc a) = acc λ p → SN-l· (a (l· p))

SN-·r : SN Γ B (t · u) → SN Γ A u
SN-·r (acc a) = acc λ p → SN-·r (a (·r p))

SN-ƛ : SN Γ (A ⇒ B) (ƛ t) → SN (Γ , A) B t
SN-ƛ (acc a) = acc λ p → SN-ƛ (a (ƛ p))

struc< : Struc Γ A t → u < t  → Struc Δ B u
struc< (acc a b) = b

struc-l· : Struc Γ B (t · u) → Struc Γ (A ⇒ B) t
struc-l· (acc a b) = acc (λ p → struc-l· (a (l· p))) (struc< (b l·))

-- Oh dear...
sn-struc : SN Γ A t → Struc Γ A t
sn-struc (acc a) = acc (λ p → sn-struc (a p)) 
                 λ where l· → sn-struc (SN-l· (acc a))
                         ·r → sn-struc (SN-·r (acc a))
                         ƛ_ → sn-struc (SN-ƛ (acc a))
