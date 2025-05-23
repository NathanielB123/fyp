{-# OPTIONS --prop #-}

open import Utils

-- A boolean algebra where 'true' ('T') is structurally larger than 'false' 
-- ('V')
module Common.Sort where

data Sort : Set where
  V   : Sort
  T>V : ∀ v → v ≡ V → Sort

pattern T = T>V V refl

_⊔_ : Sort → Sort → Sort
T ⊔ q = T
V ⊔ q = q

variable
  q r s : Sort 

data _⊑_ : Sort → Sort → Prop where
  V⊑T : V ⊑ T
  rfl : q ⊑ q

variable
  q⊑r : q ⊑ r

⊑T : q ⊑ T
⊑T {q = V} = V⊑T
⊑T {q = T} = rfl

V⊑ : V ⊑ q
V⊑ {q = V} = rfl
V⊑ {q = T} = V⊑T

⊑⊔₁ : q ⊑ (q ⊔ r)
⊑⊔₁ {q = V} = V⊑
⊑⊔₁ {q = T} = rfl

⊑⊔₂ : q ⊑ (r ⊔ q)
⊑⊔₂ {r = V} = rfl
⊑⊔₂ {r = T} = ⊑T

⊑⊔s : q ⊑ r → (q ⊔ s) ⊑ (r ⊔ s)
⊑⊔s V⊑T = ⊑T
⊑⊔s rfl = rfl

s⊔⊑ : q ⊑ r → (s ⊔ q) ⊑ (s ⊔ r)
s⊔⊑ {s = V} q⊑r = q⊑r
s⊔⊑ {s = T} _   = rfl
