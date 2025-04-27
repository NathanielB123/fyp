{-# OPTIONS --prop #-}

module Utils where

open import Level using (Level) renaming (_⊔_ to _⊔ℓ_; zero to 0ℓ; suc to suℓ) 
  public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product using (Σ; ∃; _×_; proj₁; proj₂; ∃-syntax)
  renaming (_,_ to _Σ,_) public
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; erefl; cong; cong₂; dcong₂; subst; sym)
  renaming (trans to infixr 4 _∙_)
  public
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; refl)
  renaming (cong to hcong; cong₂ to hcong₂) 
  public
open import Data.Bool 
  using (Bool; true; false) 
  renaming (not to !_; if_then_else_ to select) 
  public
open import Data.Sum 
  using (_⊎_) 
  renaming (inj₁ to inl; inj₂ to inr; map to map⊎; map₁ to mapl; map₂ to mapr) 
  public
open import Data.Nat using (ℕ) 
  renaming (zero to ze; suc to su; _⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _*_ to _×ℕ_) 
  public
open import Data.Fin using (Fin; _↑ʳ_) public
  renaming (zero to fz; suc to fs)
open import Relation.Nullary.Negation using (¬_) public
open import Induction.WellFounded 
  using (WellFounded; acc; WfRec; Acc) 
  public
open Induction.WellFounded.Subrelation public
open import Relation.Binary.Construct.Closure.Transitive 
  using (_∷_; TransClosure) 
  renaming ([_] to ⟪_⟫; wellFounded to wellFounded+)
  public
open import Relation.Binary.Construct.Closure.Reflexive
  using (refl; ReflClosure)
  renaming ([_] to ⟪_⟫; map to map?)
  public
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (ε; Star)
  renaming (_◅_ to _∷_; _◅◅_ to _∘*_; gmap to map*)
  public
open import Relation.Binary.Construct.Union
  using (_∪_)
  public
open import Data.Maybe using (Maybe; just; nothing) public
  renaming (map to map-maybe)
open import Function 
  using (_∘_; case_of_; flip) 
  public
open import Data.Vec 
  using (Vec; _∷_; []; _[_]≔_; lookup; updateAt; removeAt) 
  renaming (map to vmap)
  public

variable
  ℓ : Level
  ℓ₁ ℓ₂ ℓ₃ : Level

private variable
  A B   : Set ℓ
  P Q   : Prop ℓ
  n m   : ℕ
  x y z : A
  xs ys zs : Vec A n
  i j k : Fin n
  r r₁ r₂ r₃ r₄ : A → A → Set ℓ

SN : (A → A → Set ℓ) → A → Set _
SN r = Acc (flip r)

pattern _<∶_ x y = y ∷ x
pattern _∶>_ x y = x ∷ y

_[_]+_ : A → (A → A → Set ℓ) → A → Set _
x [ r ]+ y = TransClosure r x y

_[_]*_ : A → (A → A → Set ℓ) → A → Set _
x [ r ]* y = Star r x y

_[_]?_ : A → (A → A → Set ℓ) → A → Set _
x [ r ]? y = ReflClosure r x y

_[_∣_]_ : A → (A → A → Set ℓ₁) → (A → A → Set ℓ₂) → A → Set _
x [ r₁ ∣ r₂ ] y = (r₁ ∪ r₂) x y 

pattern ⟪_⟫* p = p ∷ ε

?to* : x [ r ]? y → x [ r ]* y
?to* ⟪ p ⟫ = p ∷ ε
?to* refl  = ε

flip* : x [ r ]* y → y [ flip r ]* x
flip* ε       = ε
flip* (p ∷ q) = flip* q ∘* (p ∷ ε)

⟦_⟧𝔹 : Bool → Set
⟦ true  ⟧𝔹 = ⊤
⟦ false ⟧𝔹 = ⊥

is : (A → Bool) → A → Set
is p x = ⟦ p x ⟧𝔹

¬is : (A → Bool) → A → Set
¬is p x = ⟦ ! p x ⟧𝔹

record Box (P : Prop ℓ) : Set ℓ where
  constructor box
  field
    unbox : P
open Box public

data ∥⊥∥ : Prop where

∥⊥∥-elim : ∥⊥∥ → A
∥⊥∥-elim ()

∥⊥-elim_∥ : ∥⊥∥ → P
∥⊥-elim_∥ ()

¬∥_∥ : Prop ℓ → Prop ℓ
¬∥ p ∥ = p → ∥⊥∥

-- I prefer this reducing definition of 'reflects' to the Agda Standard Library
-- indexed definition
reflects : Set ℓ → Bool → Set ℓ
reflects p true  = p
reflects p false = ¬ p

reflects-⟦_⟧𝔹 : ∀ (b : Bool) → reflects ⟦ b ⟧𝔹 b
reflects-⟦_⟧𝔹 true  = tt
reflects-⟦_⟧𝔹 false = λ ()

-- Agda could really do with sort-polymorphism...
∥reflects∥ : Prop ℓ → Bool → Prop ℓ
∥reflects∥ p true  = p
∥reflects∥ p false = ¬∥ p ∥

map-∥reflects∥ : ∀ {b} → (P → Q) → (Q → P) → ∥reflects∥ P b → ∥reflects∥ Q b
map-∥reflects∥ {b = true}  pq qp p    = pq p
map-∥reflects∥ {b = false} pq qp ¬p q = ¬p (qp q)

map-reflects : ∀ {b} → (A → B) → (B → A) → reflects A b → reflects B b
map-reflects {b = true}  f g x    = f x
map-reflects {b = false} f g ¬x y = ¬x (g y)

record Dec∥_∥ (A : Prop ℓ) : Set ℓ where
  constructor _because_
  field
    does  : Bool
    proof : ∥reflects∥ A does

open Dec∥_∥ public

record Dec (A : Set ℓ) : Set ℓ where
  constructor _because_
  field
    does  : Bool
    proof : reflects A does
open Dec public

decide : (p : A → Bool) (x : A) → Dec (is p x)
decide p x .does  = p x
decide p x .proof = reflects-⟦ p x ⟧𝔹

pattern yes a = true  because a
pattern no  a = false because a

map-Dec∥∥ : (P → Q) → (Q → P) → Dec∥ P ∥ → Dec∥ Q ∥
map-Dec∥∥ pq qp (b because p) = b because map-∥reflects∥ pq qp p

map-Dec : (A → B) → (B → A) → Dec A → Dec B
map-Dec pq qp (b because p) = b because map-reflects pq qp p

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B 
        → Set ℓ
x ≡[ refl ]≡ y = x ≡ y

infix 4 _≡[_]≡_

-- A variation on heterogeneous equality which isn't as much of a pain to use
-- without type-constructor injectivity
data HEq (f : A → Set) {x} (fx : f x) : ∀ {y} → f y → Set where
  refl : HEq f fx fx

coe : ∀ {A B : Set ℓ} → A ≡ B → A → B
coe refl x = x

pred : ℕ → ℕ
pred ze     = ze
pred (su n) = n

data _+_+_ (A : Set ℓ₁) (B : Set ℓ₂) (C : Set ℓ₃) : Set (ℓ₁ ⊔ℓ ℓ₂ ⊔ℓ ℓ₃) where
  inl : A → A + B + C
  inm : B → A + B + C
  inr : C → A + B + C
