{-# OPTIONS --prop --rewriting #-}

import Agda.Builtin.Equality.Rewrite
open import Utils

-- Some slightly suspect bonus utilities for manipulating identity types
module Utils.IdExtras where

infix 4 _≡[_]≡ᴾ_
infix 4 _≡ᴾ_
infixr 4 _∙ᴾ_

private variable
  A B C : Set ℓ
  x y z : A

data _≡ᴾ_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ᴾ x

private variable
  p  q  : x ≡ y
  pᴾ qᴾ : x ≡ᴾ y

-- Subsingleton elimination for |Prop|-valued identity type
-- Sound, but implies UIP
postulate 
  ≡↑  : x ≡ᴾ y → x ≡ y
  ≡↑β : ≡↑ (refl {x = x}) ≡ refl

{-# REWRITE ≡↑β #-}

≡↓ : x ≡ y → x ≡ᴾ y
≡↓ refl = refl

-- Indexing with |Set|-valued identity here feels a little inconsistent, but
-- IMO in practice ends up more convenient (if only we could enable subsingleton
-- elimination natively in Agda)
_≡[_]≡ᴾ_ : A → A ≡ᴾ B → B → Prop _
x ≡[ p ]≡ᴾ y with refl ← ≡↑ p = x ≡ᴾ y

≡[]↑ : x ≡[ ≡↓ p ]≡ᴾ y → x ≡[ p ]≡ y
≡[]↑ {p = refl} = ≡↑

≡[]↓ : x ≡[ p ]≡ y → x ≡[ ≡↓ p ]≡ᴾ y
≡[]↓ {p = refl} = ≡↓

symᴾ : x ≡ᴾ y → y ≡ᴾ x
symᴾ refl = refl

sym[]ᴾ : x ≡[ pᴾ ]≡ᴾ y → y ≡[ symᴾ pᴾ ]≡ᴾ x
sym[]ᴾ {pᴾ = refl} = symᴾ

_∙ᴾ_ : x ≡ᴾ y → y ≡ᴾ z → x ≡ᴾ z
refl ∙ᴾ refl = refl

_∙[]ᴾ_ : x ≡[ pᴾ ]≡ᴾ y → y ≡[ qᴾ ]≡ᴾ z → x ≡[ pᴾ ∙ᴾ qᴾ ]≡ᴾ z
_∙[]ᴾ_ {pᴾ = refl} {qᴾ = refl} = _∙ᴾ_

congᴾ : ∀ (f : A → B) → x ≡ᴾ y → f x ≡ᴾ f y
congᴾ f refl = refl

coeᴾ : A ≡ᴾ B → A → B
coeᴾ p x with refl ← ≡↑ p = x

subst-coecong : ∀ {f : A → Set ℓ} {p : x ≡ y} {z : f x} 
              → subst f p z ≡ coe (cong f p) z
subst-coecong {p = refl} = refl

{-# REWRITE subst-coecong #-}

{-# REWRITE sym-cong #-}

sym-sym : ∀ {p : x ≡ y} → sym (sym p) ≡ p
sym-sym {p = refl} = refl

{-# REWRITE sym-sym #-}

{-# DISPLAY coe (cong f p) x = subst f p x #-}

coh[]ᴾ : x ≡[ pᴾ ]≡ᴾ coeᴾ pᴾ x
coh[]ᴾ {pᴾ = refl} = refl

Bool-splitᴾ : ∀ (b : Bool) → (b ≡ᴾ true → A) → (b ≡ᴾ false → A) → A
Bool-splitᴾ true  t f = t refl
Bool-splitᴾ false t f = f refl

postulate
  funextᴾ   : ∀ {B : A → Set ℓ} {f g : ∀ x → B x} → (∀ x → f x ≡ᴾ g x) → f ≡ᴾ g
  funext    : ∀ {B : A → Set ℓ} {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g
  funextImp : ∀ {B : A → Set ℓ} {f g : ∀ {x} → B x} → (∀ x → f {x} ≡ g {x}) 
            → _≡_ {A = ∀ {x} → B x} f g

record ⊤ᴾ : Prop where
  constructor tt

data ⊥ᴾ : Prop where

record Σᴾ (A : Prop ℓ₁) (B : A → Prop ℓ₂) : Prop (ℓ₁ ⊔ℓ ℓ₂) where
  constructor _Σ,_
  field
    fst : A
    snd : B fst
open Σᴾ

cong∙ : ∀ {f : A → B} → cong f (p ∙ q) ≡ (cong f p ∙ cong f q)
cong∙ {p = refl} = refl

{-# REWRITE cong∙ #-}

coe∙ : coe (p ∙ q) x ≡ coe q (coe p x) 
coe∙ {p = refl} = refl
{-# REWRITE coe∙ #-}

sym∙ : sym (p ∙ q) ≡ (sym q ∙ sym p)
sym∙ {p = refl} {q = refl} = refl
{-# REWRITE sym∙ #-}
