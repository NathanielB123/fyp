module Utils where

open import Level using (Level) public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product using (Σ; ∃; _×_; proj₁; proj₂)
  renaming (_,_ to _Σ,_) public
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; dcong₂; subst; sym)
  renaming (trans to infixr 4 _∙_)
  public
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; refl) 
  public
open import Data.Bool using (Bool; true; false) public
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr) public
open import Data.Nat using (ℕ) renaming (zero to ze; suc to su) public
open import Data.Fin using (Fin; zero; suc; _↑ʳ_) public
open import Relation.Nullary.Negation using (¬_) public
open import Induction.WellFounded using (WellFounded; Acc; acc; WfRec) public
open import Relation.Binary.Construct.Closure.Transitive 
  using (TransClosure; _∷_; wellFounded) 
  renaming ([_] to ⟪_⟫)
  public
open import Function using (case_of_) public

variable
  ℓ : Level

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B 
        → Set ℓ
x ≡[ refl ]≡ y = x ≡ y

infix 4 _≡[_]≡_

coe : ∀ {A B : Set ℓ} → A ≡ B → A → B
coe refl x = x
