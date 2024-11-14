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

-- Stack of constructors, held inside out.
-- the type of unroll should clarify the role of the indices
data Stk Γ C : ∀ Δ B → Set where
  []     :                                    Stk Γ C Γ C
  ·[_]∷_ : Tm Δ A       → Stk Γ C Δ B       → Stk Γ C Δ (A ⇒ B)
  [_]·∷_ : Tm Δ (A ⇒ B) → Stk Γ C Δ B       → Stk Γ C Δ A
  ƛ∷_    :                Stk Γ C Δ (A ⇒ B) → Stk Γ C (Δ , A) B

unroll : (c : Stk Γ C Δ B) (t : Tm Δ B) → Tm Γ C
unroll [] t = t
unroll (·[ x ]∷ c) t = unroll c (t · x)
unroll ([ f ]·∷ c) t = unroll c (f · t)
unroll (ƛ∷ c) t = unroll c (ƛ t)

unroll-→β : (c : Stk Γ C Δ B) {t u : Tm Δ B} →
            t →β u →
            unroll c t →β unroll c u
unroll-→β [] r = r
unroll-→β (·[ x ]∷ c) r = unroll-→β c (l· r)
unroll-→β ([ x ]·∷ c) r = unroll-→β c (·r r)
unroll-→β (ƛ∷ c) r = unroll-→β c (ƛ r)

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

sn-struc-general :
  (c : Stk Γ C Δ B) {t : Tm Δ B} →
  SN Γ C (unroll c t) →
  Struc Δ B t
sn-struc-subterm :
  (c : Stk Γ C Δ B) {t : Tm Δ B} →
  SN Γ C (unroll c t) →
  ∀ {u} → u < t → Struc Θ A u

sn-struc-general c (acc f)
  = acc (λ r → sn-struc-general c (f (unroll-→β c r)))
        (sn-struc-subterm c (acc f))

sn-struc-subterm c sn l· = sn-struc-general (·[ _ ]∷ c) sn
sn-struc-subterm c sn ·r = sn-struc-general ([ _ ]·∷ c) sn
sn-struc-subterm c sn ƛ_ = sn-struc-general (ƛ∷ c) sn

sn-struc : SN Γ A t → Struc Γ A t
sn-struc = sn-struc-general []


{-
-- Oh dear...
sn-struc : SN Γ A t → Struc Γ A t
sn-struc (acc a) = acc (λ p → sn-struc (a p))
                 λ where l· → sn-struc (SN-l· (acc a))
                         ·r → sn-struc (SN-·r (acc a))
                         ƛ_ → sn-struc (SN-ƛ (acc a))
-}
{-
/home/nathaniel/agda/fyp/STLC/ReductionExample.agda:50,1-54,54
Termination checking failed for the following functions:
  sn-struc
Problematic calls:
  sn-struc (a p)
    (at /home/nathaniel/agda/fyp/STLC/ReductionExample.agda:51,31-39)
  λ { l· → sn-struc (SN-l· (acc a))
    ; ·r → sn-struc (SN-·r (acc a))
    ; ƛ_ → sn-struc (SN-ƛ (acc a))
    }
    (at /home/nathaniel/agda/fyp/STLC/ReductionExample.agda:52,18-54,54)
  sn-struc (SN-l· (acc a))
    (at /home/nathaniel/agda/fyp/STLC/ReductionExample.agda:52,31-39)
  sn-struc (SN-ƛ (acc a))
    (at /home/nathaniel/agda/fyp/STLC/ReductionExample.agda:54,31-39)
-}
