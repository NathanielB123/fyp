{-# OPTIONS --prop --rewriting --show-irrelevant 
            --no-require-unique-meta-solutions #-}

open import Utils
open import Common.Sort

-- open import STLC.BoolRw.Syntax
-- open import STLC.SubstEq
open import STLC.Syntax2
open import STLC.SubstEq2

open import STLC.BoolRw.Views
open import STLC.BoolRw.SpontRed

-- Logical relation/reducibility candidate/computability predicate
-- Naming it 'Val' is a hold-over from NbE. I probably should change this...
module STLC.BoolRw.Pred where

𝔹Val : ∀ Γ → Tm Γ 𝔹' → Set
𝔹Val Γ t = SN Γ 𝔹' t

+ValRec : ∀ Γ A B (ValA : Tm Γ A → Set) (ValB : Tm Γ B → Set)
            (t : Tm Γ (A +' B)) → Dec∥ inl/inr t ∥ → Set
      
record +ValStkRec (Γ : Ctx) (A B : Ty) 
                  (ValA : Tm Γ A → Set) (ValB : Tm Γ B → Set)
                  (t : Tm Γ (A +' B)) : Set
                  where
  constructor acc
  inductive
  pattern
  field 
    +ValStk→  : t [ q→ ]→ u → +ValRec Γ A B ValA ValB u (inl/inr? u) 
open +ValStkRec public

+ValRec Γ A B ValA ValB t       (no _)  = +ValStkRec Γ A B ValA ValB t
+ValRec Γ A B ValA ValB (inl t) (yes _) = ValA t
+ValRec Γ A B ValA ValB (inr t) (yes _) = ValB t


Val : ∀ Γ A → Tm Γ A → Set

+ValStk : ∀ Γ A B → Tm Γ (A +' B) → Set
+ValStk Γ A B t = +ValStkRec Γ A B (Val Γ A) (Val Γ B) t

+Val∣ : ∀ Γ A B (t : Tm Γ (A +' B)) → Dec∥ inl/inr t ∥ → Set
+Val∣ Γ A B t i = +ValRec Γ A B (Val Γ A) (Val Γ B) t i

+Val : ∀ Γ A B → Tm Γ (A +' B) → Set
+Val Γ A B t = +Val∣ Γ A B t (inl/inr? t)

Val Γ 𝔹' t       = 𝔹Val Γ t
Val Γ (A +' B) t = +Val Γ A B t
-- Putting 'SN' along with 'Val' on the left of the arrow here is non-standard,
-- but seems to be necessary to ensure termination
Val Γ (A ⇒ B) t 
  = ∀ {Δ} (δ : Vars Δ Γ) {u} → Val Δ A u → SN Δ A u → Val Δ B ((t [ δ ]) · u)

{-# INJECTIVE_FOR_INFERENCE +ValRec #-}
{-# INJECTIVE_FOR_INFERENCE Val #-}

stk-val : ¬∥ inl/inr t ∥ → +ValStk Γ A B t → +Val Γ A B t
stk-val {t = ` _}         ¬i tⱽ = tⱽ
stk-val {t = _ · _}       ¬i tⱽ = tⱽ
stk-val {t = 𝔹-rec _ _ _} ¬i tⱽ = tⱽ
stk-val {t = +-rec _ _ _} ¬i tⱽ = tⱽ
stk-val {t = inl _}       ¬i tⱽ = ∥⊥∥-elim (¬i inl)
stk-val {t = inr _}       ¬i tⱽ = ∥⊥∥-elim (¬i inr)

data Env (Δ : Ctx) : ∀ Γ → Tms[ T ] Δ Γ → Set where
  ε   : Env Δ ε ε
  _,_ : Env Δ Γ δ → Val Δ A t → Env Δ (Γ , A) (δ , t)

Val→ : t [ q→ ]→ u → Val Γ A t → Val Γ A u
+Val→ : (i : Dec∥ inl/inr t ∥) → t [ q→ ]→ u → +Val∣ Γ A B t i → +Val Γ A B u

+Val→ (yes _) (inl p) tⱽ       = Val→ p tⱽ
+Val→ (yes _) (inr p) tⱽ       = Val→ p tⱽ
+Val→ (no _)  p       (acc tⱽ) = tⱽ p

Val→ {A = 𝔹'}     p (acc a)          = a p
Val→ {A = A +' B} p tⱽ               = +Val→ (inl/inr? _) p tⱽ
Val→ {A = A ⇒ B}  p tⱽ      δ uⱽ uˢⁿ = Val→ (l· (p [ δ ]→)) (tⱽ δ uⱽ uˢⁿ)

_∋_[_]V : ∀ A {t} → Val Γ A t → ∀ (δ : Vars Δ Γ) → Val Δ A (t [ δ ])
_∣_[_]+V : ∀ (i : Dec∥ inl/inr t ∥) → +Val∣ Γ A B t i 
         → (δ : Vars Δ Γ) → +Val Δ A B (t [ δ ])

no ¬i ∣ acc tⱽ [ δ ]+V
  = stk-val (¬i [ δ ]¬i) (acc λ p → case [_]→⁻¹_ δ p of 
                              λ where (t′ Σ, p′ Σ, refl) → _ ∣ tⱽ p′ [ δ ]+V)
_∣_[_]+V {t = inl _} (yes _) tⱽ δ = _ ∋ tⱽ [ δ ]V
_∣_[_]+V {t = inr _} (yes _) tⱽ δ = _ ∋ tⱽ [ δ ]V

𝔹'       ∋ tⱽ [ δ ]V       = tⱽ [ δ ]sn
(A +' B) ∋ tⱽ [ δ ]V       = _ ∣ tⱽ [ δ ]+V
((A ⇒ B) ∋ tⱽ [ δ ]V) σ uⱽ = tⱽ (δ ⨾ σ) uⱽ

_[_]E : Env Δ Γ δ → ∀ (σ : Vars Θ Δ) → Env Θ Γ (δ ⨾ σ)
ε        [ σ ]E = ε
(ρ , tⱽ) [ σ ]E = (ρ [ σ ]E) , (_ ∋ tⱽ [ σ ]V)
