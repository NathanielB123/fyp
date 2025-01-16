{-# OPTIONS --prop --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Common.Sort
open import Utils

-- open import STLC.BoolRw.Syntax
open import STLC.Syntax2

-- Views on terms. Specifically to provide info about whether they start with 
-- various introduction forms.
module STLC.BoolRw.Views where

data t/f {Γ} : Tm Γ A → Set where
  true  : t/f true
  false : t/f false

t/f? : (t : Tm Γ A) → Dec (t/f t)
t/f? true          = yes true
t/f? false         = yes false
t/f? (` _)         = no λ ()
t/f? (_ · _)       = no λ ()
t/f? (ƛ _)         = no λ ()
t/f? (𝔹-rec _ _ _) = no λ ()
t/f? (inl _)       = no λ ()
t/f? (inr _)       = no λ ()
t/f? (+-rec _ _ _) = no λ ()

_[_]b : t/f t → (δ : Tms[ q ] Δ Γ) → t/f (t [ δ ])
true  [ δ ]b = true
false [ δ ]b = false

[_]b⁻¹_ : (δ : Vars Δ Γ) → t/f (t [ δ ]) → t/f t
[_]b⁻¹_ {t = true}  δ true  = true
[_]b⁻¹_ {t = false} δ false = false

_[_]¬b : ¬ t/f t → (δ : Vars Δ Γ) → ¬ t/f (t [ δ ])
(¬b [ δ ]¬b) b[] = ¬b ([ δ ]b⁻¹ b[])

[_]¬b⁻¹_ : (δ : Tms[ q ] Δ Γ) → ¬ t/f (t [ δ ]) → ¬ t/f t
([ δ ]¬b⁻¹ ¬b[]) b = ¬b[] (b [ δ ]b)

-- Placing this in 'Prop' and 'true/false' in 'Set' is inconsistent but just
-- happens to be most convenenient ('true/false t : Set' means a
-- coprododuct of it and the identity type can be taken in 'Lemmas' without
-- boxing and there is a tricky lemma in 'StrongNorm' which benefits 
-- significantly from  'inl/inr t : Prop') so I am going with it...
data inl/inr {Γ} : Tm Γ A → Prop where
  inl : inl/inr (inl {A = A} {B = B} t)
  inr : inl/inr (inr {B = B} {A = A} t)

inl/inr? : (t : Tm Γ A) → Dec∥ inl/inr t ∥
inl/inr? (inl t)       = yes inl
inl/inr? (inr t)       = yes inr
inl/inr? (` _)         = no λ ()
inl/inr? (_ · _)       = no λ ()
inl/inr? (ƛ _)         = no λ ()
inl/inr? true          = no λ ()
inl/inr? false         = no λ ()
inl/inr? (𝔹-rec _ _ _) = no λ ()
inl/inr? (+-rec _ _ _) = no λ ()

_[_]i : inl/inr t → (δ : Vars Δ Γ) → inl/inr (t [ δ ])
inl [ δ ]i = inl
inr [ δ ]i = inr

[_]i⁻¹_ : (δ : Vars Δ Γ) → inl/inr (t [ δ ]) → inl/inr t
[_]i⁻¹_ {t = inl _} δ inl = inl
[_]i⁻¹_ {t = inr _} δ inr = inr

_[_]¬i : ¬∥ inl/inr t ∥ → (δ : Vars Δ Γ) → ¬∥ inl/inr (t [ δ ]) ∥
(¬i [ δ ]¬i) i[] = ¬i ([ δ ]i⁻¹ i[])

[_]¬i⁻¹_ : (δ : Vars Δ Γ) → ¬∥ inl/inr (t [ δ ]) ∥ → ¬∥ inl/inr t ∥
([ δ ]¬i⁻¹ ¬i[]) i = ¬i[] (i [ δ ]i)

inl/inr[] : {δ : Vars Δ Γ} → inl/inr? (t [ δ ]) .does ≡ inl/inr? t .does
inl/inr[] {t = t} {δ = δ} with inl/inr? t | inl/inr? (t [ δ ])
... | yes i | yes i[] = refl
... | no ¬i | yes i[] = ∥⊥∥-elim (¬i ([ δ ]i⁻¹ i[]))
... | yes i | no ¬i[] = ∥⊥∥-elim (¬i[] (i [ δ ]i))
... | no ¬i | no ¬i[] = refl

{-# REWRITE inl/inr[] #-}
