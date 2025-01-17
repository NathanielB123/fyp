{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Utils

-- open import STLC.BoolRw.Syntax
open import STLC.Syntax2
open import STLC.BoolRw.Views
open import STLC.BoolRw.SpontRed
open import STLC.BoolRw.Lemmas
open import STLC.BoolRw.StrongNorm

-- Conditional Reduction: The actual reduction relation we want to use!

-- Note we seemingly need to define a new term syntax to express how new
-- equations get introduced via e.g. the '𝔹-rec' construct
module STLC.BoolRw.CondRed where

data Eqs : Ctx → Set
data _⊢_~_ (Ξ : Eqs Γ) : Tm Γ A → Tm Γ A → Set

variable
  Ξ : Eqs Γ


data Eqs where
  ε    : Eqs Γ
  _,_↝_ : Eqs Γ → Tm Γ A → t/f u → Eqs Γ

variable
  tᵇ uᵇ vᵇ : t/f t
  tᵇ₁ tᵇ₂ uᵇ₁ uᵇ₂ vᵇ₁ vᵇ₂ : t/f t

infix 4 _↝_∈_
infix 4 _⊢_~_
infix 4 _⊢_>>_


data _↝_∈_ : Tm Γ A → Tm Γ A → Eqs Γ → Set where
  here  : {uᵇ : t/f u} → t ↝ u ∈ (Ξ , t ↝ uᵇ)
  there : t₁ ↝ t₂ ∈ Ξ → t₁ ↝ t₂ ∈ (Ξ , u ↝ vᵇ)

-- Congruence closure of _~_∈_
data _⊢_~_ Ξ where
  ∈~   : t ↝ u ∈ Ξ → Ξ ⊢ t ~ u
  _⁻¹  : Ξ ⊢ t ~ u → Ξ ⊢ u ~ t
  rfl  : Ξ ⊢ t ~ t
  ∙~   : Ξ ⊢ t ~ t → Ξ ⊢ t ~ t → Ξ ⊢ t ~ t
  _·_  : Ξ ⊢ t₁ ~ u₁ → Ξ ⊢ t₂ ~ u₂ → Ξ ⊢ t₁ · t₂ ~ u₁ · u₂
  -- etc...

-- TODO: I think our condition will have to admit weakening to go under
-- binders. I'll worry about this later.

-- Parameterising 'TmRel' by some renaming is probably neatest
TmRel : Ctx → Set₁
TmRel Γ = ∀ {Δ A} → Vars Δ Γ → Tm Δ A → Tm Δ A → Set

_[_]R : TmRel Γ → Vars Δ Γ → TmRel Δ
(𝒞 [ δ ]R) σ = 𝒞 (δ ⨾ σ) 

-- Conditional small-step reduction
data _⊢_>>_ (𝒞 : TmRel Γ) : Tm Γ A → Tm Γ A → Set where
  β         : ∀ {ƛt t[u]} → ƛt ≡ ƛ t → t[u] ≡ t [ < u > ] → 𝒞 ⊢ (ƛt · u) >> t[u]
  rec-true  : 𝒞 ⊢ 𝔹-rec true  u v >> u
  rec-false : 𝒞 ⊢ 𝔹-rec false u v >> v
  rw        : 𝒞 id t u → ¬ t/f t → t/f u → 𝒞 ⊢ t >> u

  l·        : 𝒞 ⊢ t₁ >> t₂ → 𝒞 ⊢ (t₁ · u) >> (t₂ · u) 
  ·r        : 𝒞 ⊢ u₁ >> u₂ → 𝒞 ⊢ (t · u₁) >> (t · u₂)
  ƛ_        : 𝒞 [ wk ]R ⊢ t₁ >> t₂ → 𝒞 ⊢ (ƛ t₁)   >> (ƛ t₂)
  -- Additional congruence closure rules
  -- 𝔹-rec₁ : Ξ ⊢ t₁ >> t₂ → Ξ ⊢ 𝔹-rec t₁ u v >> 𝔹-rec t₂ u v
  -- 𝔹-rec₂ : Ξ ⊢ u₁ >> u₂ → Ξ ⊢ 𝔹-rec t u₁ v >> 𝔹-rec t u₂ v
  -- 𝔹-rec₃ : Ξ ⊢ v₁ >> v₂ → Ξ ⊢ 𝔹-rec t u v₁ >> 𝔹-rec t u v₂
  -- +-rec₁ : Ξ ⊢ t₁ >> t₂ → Ξ ⊢ +-rec t₁ u v >> +-rec t₂ u v
  -- +-rec₂ : Ξ ⊢ u₁ >> u₂ → Ξ ⊢ +-rec t u₁ v >> +-rec t u₂ v
  -- +-rec₃ : Ξ ⊢ v₁ >> v₂ → Ξ ⊢ +-rec t u v₁ >> +-rec t u v₂

-- I think this maybe should just be called "stk"
record _⊢nf_ (𝒞 : TmRel Γ) (t : Tm Γ A) : Set where
  constructor nf
  field
    ¬step : ¬ 𝒞 ⊢ t >> u
open _⊢nf_ public

variable
  𝒞 : TmRel Γ
  tⁿᶠ uⁿᶠ vⁿᶠ : 𝒞 ⊢nf t
  tⁿᶠ₁ tⁿᶠ₂ uⁿᶠ₁ uⁿᶠ₂ vⁿᶠ₁ vⁿᶠ₂ : 𝒞 ⊢nf t

record _⊢SN_ (𝒞 : TmRel Γ) (t : Tm Γ A) : Set where
  constructor acc
  inductive
  pattern
  field
    sn>> : 𝒞 ⊢ t >> u → 𝒞 ⊢SN u
open _⊢SN_ public

included : 𝒞 ⊢ t >> u → ∃ λ q→ → t [ q→ ]→ u 
included (β p q)     = _ Σ, β p q
included rec-true    = _ Σ, rec-true
included rec-false   = _ Σ, rec-false
included (rw _ ¬b b) = _ Σ, rw* ¬b b
included (l· p)      with included p
... | _ Σ, p′ = _ Σ, l· p′
included (·r p)      with included p
... | _ Σ, p′ = _ Σ, ·r p′
included (ƛ p)       with included p
... | _ Σ, p′ = _ Σ, ƛ p′

sn-⊢sn : SN Γ A t → 𝒞 ⊢SN t
sn-⊢sn (acc p) = acc λ q → sn-⊢sn (p (included q .proj₂))

⊢sn : 𝒞 ⊢SN t
⊢sn = sn-⊢sn (strong-norm _)

_-_ : (Ξ : Eqs Γ) → t ↝ u ∈ Ξ → Eqs Γ
(Ξ , t ↝ uᵇ) - here    = Ξ
(Ξ , t ↝ uᵇ) - there p = (Ξ - p) , t ↝ uᵇ

_[_]~ : Eqs Γ → Vars Δ Γ → Eqs Δ

record Rws Γ (Ξ : Eqs Γ) : Set where
  field
    reduced : ∀ (p : t ↝ u ∈ Ξ) → (λ δ → (Ξ [ δ ]~) ⊢_~_) ⊢nf t
open Rws public

-- record Rw Γ (Ξ : Eqs Γ) (A : Ty) (t : Tm Γ A) (u : Tm Γ A) : Set where
--   constructor _↝ᵣ_
--   field
--     rw-nf : {!!} ⊢nf t
--     rhsᵇ  : t/f u

-- I think it would be neater to change this to a single case
-- Instead of zero or one reductions, we could support 'n' reductions but
-- require the output is fully reduced
-- To do this properly, we would take advantage of how 'true'/'false' are
-- immediately stuck
data Reduced Γ (𝒞 : TmRel Γ) A (t : Tm Γ A) : Set where
  red : 𝒞 ⊢ t >> u → Reduced Γ 𝒞 A t
  stk : 𝒞 ⊢nf t → Reduced Γ 𝒞 A t

-- record Reduced Γ (Ξ : Eqs Γ) A (t : Tm Γ A) : Set where
--   constructor _,_
--   field
--     red  : Tm Γ A
--     step : (Ξ ⊢_~_) ⊢ t >> red

_≡[]≡t?_ : ∀ (t : Tm Γ A) (u : Tm Γ B) → Dec (∃ λ p → t ≡[ cong (Tm _) p ]≡ u)

-- Our rewriting algorithm is extremely naive. We look through each rewrite
-- in turn, attempting to apply it everywhere in the target term.

-- rw-desc : ∀ t (u : Tm Γ B) (¬uᵇ : ¬ t/f u) (vᵇ : t/f v) 
--         → (¬ ∃ λ p → t ≡[ cong (Tm _) p ]≡ u)
--         → Reduced Γ (λ u′ v′ → ∃ λ p → u′ ≡[ cong (Tm _) p ]≡ u 
--                                      × v′ ≡[ cong (Tm _) p ]≡ v) 
--                   A t
-- rw-desc (` i) u ¬uᵇ vᵇ p = stk (nf λ where (rw (q₁ Σ, q₂ Σ, _) ¬b b) → p (q₁ Σ, q₂))
-- rw-desc (t₁ · t₂) u ¬uᵇ vᵇ p = {!   !}
-- rw-desc (ƛ t) u ¬uᵇ vᵇ p = {!   !}
-- rw-desc true u ¬uᵇ vᵇ p = {!   !}
-- rw-desc false u ¬uᵇ vᵇ p = {!   !}
-- rw-desc (𝔹-rec t₁ t₂ t₃) u ¬uᵇ vᵇ p = {!   !}
-- rw-desc (inl t) u ¬uᵇ vᵇ p = {!   !}
-- rw-desc (inr t) u ¬uᵇ vᵇ p = {!   !}
-- rw-desc (+-rec t₁ t₂ t₃) u ¬uᵇ vᵇ p = {!   !}

-- try-rw : ∀ t (tⁿᶠ : (λ _ _ → ⊥) ⊢nf t) (u : Tm Γ B) (¬uᵇ : ¬ t/f u) (vᵇ : t/f v) 
--        → Reduced Γ (λ u′ v′ → ∃ λ p → u′ ≡[ cong (Tm _) p ]≡ u 
--                                     × v′ ≡[ cong (Tm _) p ]≡ v) 
--                  A t
-- try-rw t tⁿᶠ u ¬uᵇ vᵇ with t ≡[]≡t? u
-- ... | yes (refl Σ, refl) = red (rw (refl Σ, refl Σ, refl) ¬uᵇ vᵇ) 
-- ... | no ¬p              = stk (nf λ p → ¬step tⁿᶠ {!  !})
-- wait, this is wrong!!

conv : Dec (Ξ ⊢ t ~ u)






consistent : Eqs Γ → Set
consistent Ξ = Ξ ⊢ true ~ false

-- In an inconsistent context, we reduce to '⊥'
data Tm? Γ (Ξ : Eqs Γ) (A : Ty) : Set where
  _⊢_ : consistent Ξ → Tm Γ A → Tm? Γ Ξ A
  _⊢⊥ : ¬ consistent Ξ → Tm? Γ Ξ A

-- record Rw (Γ : Ctx) : Set where
--   field
--     lhs : Tm Γ 𝔹'
--     rhs : Tm Γ 𝔹'
--     l¬b : ¬IsBool lhs
--     rb  : IsBool rhs
-- open Rw public

-- record Rws (Γ : Ctx) : Set where
--   constructor mk
--   field
--     {len} : ℕ
--     rws : Fin len → Rw Γ
-- open Rws public

-- uhh : ∀ {n} → Fin n → Fin (pred n) → Fin n
-- uhh zero    y       = suc y
-- uhh (suc x) zero    = zero
-- uhh (suc x) (suc y) = suc (uhh x y)

-- _-_ : (Ξ : Rws Γ) → Fin (Ξ .len) → Rws Γ
-- Ξ - n = mk λ m → Ξ .rws (uhh n m)

-- variable
--   Ξ : Rws Γ

-- _[_]rws : Rws Γ → Vars Δ Γ → Rws Δ

-- _↦_∈_ : Tm Γ 𝔹' → Tm Γ 𝔹' → Rws Γ → Set

-- data _⊢_→s_ (Ξ : Rws Γ) : Tm Γ A → Tm Γ A → Set where
--   β         : ∀ {ƛt t[u]} → ƛt ≡ ƛ t → t[u] ≡ t [ < u > ] → Ξ ⊢ (ƛt · u) →s t[u]
--   rw        : t ↦ u ∈ Ξ → Ξ ⊢ t →s u
--   rec-true  : Ξ ⊢ 𝔹-rec true u v →s u
--   rec-false : Ξ ⊢ 𝔹-rec false u v →s v

--   l·     : Ξ ⊢ t₁ →s t₂ → Ξ ⊢ (t₁ · u) →s (t₂ · u) 
--   ·r     : Ξ ⊢ u₁ →s u₂ → Ξ ⊢ (t · u₁) →s (t · u₂)
--   ƛ_     : (Ξ [ id ⁺ _ ]rws) ⊢ t₁ →s t₂ → Ξ ⊢ (ƛ t₁) →s (ƛ t₂)
--   𝔹-rec₁ : Ξ ⊢ t₁ →s t₂ → Ξ ⊢ 𝔹-rec t₁ u v →s 𝔹-rec t₂ u v
--   𝔹-rec₂ : Ξ ⊢ u₁ →s u₂ → Ξ ⊢ 𝔹-rec t u₁ v →s 𝔹-rec t u₂ v
--   𝔹-rec₃ : Ξ ⊢ v₁ →s v₂ → Ξ ⊢ 𝔹-rec t u v₁ →s 𝔹-rec t u v₂

-- s[]→ : Ξ ⊢ t →s u → ∃ λ q→ → t [ q→ ]→ u
-- s[]→ (β p q)   = β Σ, β p q
-- s[]→ (rw p)    = rw Σ, rw {! !} {! !}
-- s[]→ rec-true  = β Σ, {! !}
-- s[]→ rec-false = β Σ, {! !}
-- s[]→ (l· p) = {!   !}
-- s[]→ (·r p) = {!   !}
-- s[]→ (ƛ p) = {!   !}
-- s[]→ (𝔹-rec₁ p) = {!   !}
-- s[]→ (𝔹-rec₂ p) = {!   !}
-- s[]→ (𝔹-rec₃ p) = {!   !}

-- data _⊢SN_ (Ξ : Rws Γ) (t : Tm Γ A) : Set where
--   acc : (∀ {u} → Ξ ⊢ t →s u → Ξ ⊢SN u) → Ξ ⊢SN t

-- ⊢sn-helper : SN Γ A t → Ξ ⊢SN t 
-- ⊢sn-helper (acc a) = acc λ p → {!p  !}

-- _⊢sn_ : ∀ Ξ (t : Tm Γ A) → Ξ ⊢SN t
-- Ξ ⊢sn t = {!   !}
 
-- _⊢nf_ : ∀ Ξ (t : Tm Γ A) → Set
-- Ξ ⊢nf t = ∀ {u} → ¬ Ξ ⊢ t →s u
 
-- ⊢Rws : Rws Γ → Set
-- ⊢Rws Ξ = ∀ {n} → (Ξ - n) ⊢nf (Ξ .rws) n .lhs
 
-- conf : Ξ ⊢ t →s u₁ → Ξ ⊢ t →s u₂  
--      → ∃ λ v → Ξ ⊢ u₁ →s v × Ξ ⊢ u₂ →s v  