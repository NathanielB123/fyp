{-# OPTIONS --prop #-}

module Utils where

open import Level using (Level) renaming (_⊔_ to _⊔ℓ_; zero to 0ℓ; suc to suℓ) 
  public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product using (Σ; ∃; _×_; proj₁; proj₂)
  renaming (_,_ to _Σ,_) public
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; erefl; cong; cong₂; dcong₂; subst; sym)
  renaming (trans to infixr 4 _∙_)
  public
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; refl) 
  public
open import Data.Bool using (Bool; true; false) public
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr) public
open import Data.Nat using (ℕ) 
  renaming (zero to ze; suc to su; _⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _*_ to _×ℕ_) 
  public
open import Data.Fin using (Fin; zero; suc; _↑ʳ_) public
open import Relation.Nullary.Negation using (¬_) public
open import Induction.WellFounded using (WellFounded; Acc; acc; WfRec) public
open import Relation.Binary.Construct.Closure.Transitive 
  using (TransClosure; _∷_; wellFounded) 
  renaming ([_] to ⟪_⟫)
  public
open import Data.Maybe using (Maybe; just; nothing) public
open import Function using (_∘_; case_of_) public

-- TODO: Figure out how we want to expose 'Dec'idability of proof-relevant
-- stuff
-- open import Relation.Nullary.Reflects using (Reflects; ofʸ; ofⁿ) public
-- open import Relation.Nullary.Decidable 
--   using (Dec; _because_; does) public

variable
  ℓ : Level
  ℓ₁ ℓ₂ ℓ₃ : Level

data ∥⊥∥ : Prop where

∥⊥∥-elim : ∀ {A : Set ℓ} → ∥⊥∥ → A
∥⊥∥-elim ()

∥¬∥_ : Prop ℓ → Prop ℓ
∥¬∥ p = p → ∥⊥∥

reflects : Prop ℓ → Bool → Prop ℓ
reflects p true  = p
reflects p false = ∥¬∥ p

map-reflects : ∀ {P : Prop ℓ₁} {Q : Prop ℓ₂} {b : Bool} 
             → (P → Q) → (Q → P) → reflects P b → reflects Q b
map-reflects {b = true}  pq qp p    = pq p
map-reflects {b = false} pq qp ¬p q = ¬p (qp q)

record DecProp (A : Prop ℓ) : Set ℓ where
  constructor _because_
  field
    does  : Bool
    proof : reflects A does

open DecProp public

pattern yes a = true  because a
pattern no  a = false because a

map-Dec : ∀ {P : Prop ℓ₁} {Q : Prop ℓ₂} 
        → (P → Q) → (Q → P) → DecProp P → DecProp Q
map-Dec pq qp (b because p) = b because map-reflects pq qp p

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B 
        → Set ℓ
x ≡[ refl ]≡ y = x ≡ y

infix 4 _≡[_]≡_

coe : ∀ {A B : Set ℓ} → A ≡ B → A → B
coe refl x = x

pred : ℕ → ℕ
pred ze     = ze
pred (su n) = n

data _+_+_ (A : Set ℓ₁) (B : Set ℓ₂) (C : Set ℓ₃) : Set (ℓ₁ ⊔ℓ ℓ₂ ⊔ℓ ℓ₃) where
  inl : A → A + B + C
  inm : B → A + B + C
  inr : C → A + B + C
 