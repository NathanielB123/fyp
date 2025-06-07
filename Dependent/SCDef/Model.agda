{-# OPTIONS --prop --rewriting --show-irrelevant 
            --no-require-unique-meta-solutions #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Syntax

-- Like "ModelOld.agda" but without asserting termination.
--
-- To achieve this, we use some trickery with foeqard references, with-clauses 
-- and specialising helpers, which makes unfortunately the definitions a bit 
-- clunkier in places.
module Dependent.SCDef.Model where

⟦Sig⟧ : Set₁
⟦Sig⟧ = Set


⟦Ctx⟧ : ⟦Sig⟧ → Set₁
⟦Ctx⟧ ⟦Ψ⟧ = ⟦Ψ⟧ → Set

variable
  ⟦Ψ⟧ ⟦Φ⟧ ⟦Ξ⟧ : ⟦Sig⟧ 

⟦Ty⟧ : ⟦Ctx⟧ ⟦Ψ⟧ → Set₁
⟦Ty⟧ ⟦Γ⟧ = ∀ χ → ⟦Γ⟧ χ → Set

⟦Tm⟧ : ∀ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) → ⟦Ty⟧ ⟦Γ⟧ → Set
⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ = ∀ χ ρ → ⟦A⟧ χ ρ

⟦Wk⟧ : ⟦Sig⟧ → ⟦Sig⟧ → Set
⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ = ⟦Φ⟧ → ⟦Ψ⟧

⟦[]C⟧ : ⟦Ctx⟧ ⟦Ψ⟧ → ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ → ⟦Ctx⟧ ⟦Φ⟧
⟦[]C⟧ ⟦Γ⟧ ⟦δ⟧ = λ χ → ⟦Γ⟧ (⟦δ⟧ χ)

⟦Tms⟧ : ⟦Ctx⟧ ⟦Φ⟧ → ⟦Ctx⟧ ⟦Ψ⟧ → Set
⟦Tms⟧ {⟦Φ⟧ = ⟦Φ⟧} {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Δ⟧ ⟦Γ⟧ 
  = Σ (⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧) λ ⟦δ⟧ → ∀ {χ} → ⟦Δ⟧ χ → ⟦[]C⟧ ⟦Γ⟧ ⟦δ⟧ χ

variable
  ⟦Ψ₁⟧ ⟦Ψ₂⟧ ⟦Φ₁⟧ ⟦Φ₂⟧ : ⟦Sig⟧
  ⟦Γ⟧ ⟦Δ⟧ ⟦Θ⟧ ⟦Γ₁⟧ ⟦Γ₂⟧ ⟦Δ₁⟧ ⟦Δ₂⟧ ⟦Θ₁⟧ ⟦Θ₂⟧       : ⟦Ctx⟧ ⟦Ψ⟧
  ⟦A⟧ ⟦B⟧ ⟦A₁⟧ ⟦A₂⟧ ⟦B₁⟧ ⟦B₂⟧       : ⟦Ty⟧  ⟦Γ⟧ 
  ⟦t⟧ ⟦u⟧ ⟦v⟧ ⟦t₁⟧ ⟦t₂⟧ ⟦u₁⟧ ⟦u₂⟧ ⟦v₁⟧ ⟦v₂⟧ : ⟦Tm⟧  ⟦Γ⟧ ⟦A⟧
  ⟦δ⟧ ⟦δ₁⟧ ⟦δ₂⟧ ⟦σ₁⟧ ⟦σ₂⟧                     : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧
  ⟦γ⟧ ⟦γ₁⟧ ⟦γ₂⟧                 : ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧

Ctx≡ : ⟦Ψ₁⟧ ≡ᴾ ⟦Ψ₂⟧ → ⟦Ctx⟧ ⟦Ψ₁⟧ ≡ᴾ ⟦Ctx⟧ ⟦Ψ₂⟧
Ctx≡ refl = refl

Ty≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧ → ⟦Ty⟧ {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Γ₁⟧ ≡ᴾ ⟦Ty⟧ ⟦Γ₂⟧
Ty≡ refl = refl

Tm≡ : ∀ Γ≡ → ∀ (A≡ : ⟦A₁⟧ ≡[ Ty≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ ]≡ᴾ ⟦A₂⟧) 
    → ⟦Tm⟧ ⟦Γ₁⟧ ⟦A₁⟧ ≡ᴾ ⟦Tm⟧ ⟦Γ₂⟧ ⟦A₂⟧
Tm≡ refl refl = refl

Wk≡ : ⟦Φ₁⟧ ≡ᴾ ⟦Φ₂⟧ → ⟦Ψ₁⟧ ≡ᴾ ⟦Ψ₂⟧ → ⟦Wk⟧ ⟦Φ₁⟧ ⟦Ψ₁⟧ ≡ᴾ ⟦Wk⟧ ⟦Φ₂⟧ ⟦Ψ₂⟧
Wk≡ refl refl = refl

Tms≡ : ⟦Δ₁⟧ ≡ᴾ ⟦Δ₂⟧ → ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧ → ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧ ≡ᴾ ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧
Tms≡ refl refl = refl

Tms≡′ : ∀ (Φ≡ : ⟦Φ₁⟧ ≡ᴾ ⟦Φ₂⟧) (Ψ≡ : ⟦Ψ₁⟧ ≡ᴾ ⟦Ψ₂⟧) 
          (Δ≡ : ⟦Δ₁⟧ ≡[ Ctx≡ Φ≡ ]≡ᴾ ⟦Δ₂⟧) 
          (Γ≡ : ⟦Γ₁⟧ ≡[ Ctx≡ Ψ≡ ]≡ᴾ ⟦Γ₂⟧)
      → ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧ ≡ᴾ ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧ 
Tms≡′ refl refl refl refl = refl

⟦𝔹⟧ : ⟦Ty⟧ ⟦Γ⟧
⟦𝔹⟧ = λ χ ρ → Bool

⟦▷>eq⟧ : ∀ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) → ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧ → Bool → ⟦Ctx⟧ ⟦Ψ⟧
⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ b = λ χ → Σ (⟦Γ⟧ χ) (λ ρ → Box (⟦t⟧ χ ρ ≡ᴾ b))

⟦id𝒮⟧ : ⟦Wk⟧ ⟦Ψ⟧ ⟦Ψ⟧
⟦id𝒮⟧ = λ χ → χ

⟦id⟧ : ⟦Tms⟧ ⟦Γ⟧ ⟦Γ⟧
⟦id⟧ = ⟦id𝒮⟧ Σ, λ ρ → ρ

⟦wkeq⟧ : ⟦Tms⟧ (⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ b) ⟦Γ⟧
⟦wkeq⟧ = ⟦id𝒮⟧ Σ, fst

⟦π₁eq⟧ : ⟦Tms⟧ ⟦Δ⟧ (⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ b) → ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧
⟦π₁eq⟧ ⟦δ⟧ = ⟦δ⟧ .fst Σ, λ ρ → ⟦δ⟧ .snd ρ .fst


⟦[]T⟧ : ⟦Ty⟧ ⟦Γ⟧ → ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧ → ⟦Ty⟧ ⟦Δ⟧
⟦[]T⟧ ⟦A⟧ ⟦δ⟧ χ ρ = ⟦A⟧ (⟦δ⟧ .fst χ) (⟦δ⟧ .snd ρ)

⟦▷𝒮⟧ : ∀ ⟦Ψ⟧ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) ⟦A⟧ ⟦t⟧
     → ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ true)   (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧) 
     → ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ false)  (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧) 
     → ⟦Sig⟧
⟦▷𝒮⟧ ⟦Ψ⟧ ⟦Γ⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ 
  = Σ ⟦Ψ⟧ λ χ → 
    Σ (∀ ρ → ⟦A⟧ χ ρ) λ f → 
      (∀ ρ (t~ : ⟦t⟧ χ ρ ≡ᴾ true) 
    → Box (f ρ ≡ᴾ ⟦u⟧ χ (ρ Σ, box t~)))
    × (∀ ρ (t~ : ⟦t⟧ χ ρ ≡ᴾ false)
    → Box (f ρ ≡ᴾ ⟦v⟧ χ (ρ Σ, box t~)))

⟦⨾𝒮⟧ : ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ → ⟦Wk⟧ ⟦Ξ⟧ ⟦Φ⟧ → ⟦Wk⟧ ⟦Ξ⟧ ⟦Ψ⟧
⟦⨾𝒮⟧ ⟦δ⟧ ⟦σ⟧ = λ χ → ⟦δ⟧ (⟦σ⟧ χ)

⟦⌜⌝𝒮⟧ : ∀ (⟦δ⟧ : ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧) → ⟦Tms⟧ (⟦[]C⟧ ⟦Γ⟧ ⟦δ⟧) ⟦Γ⟧
⟦⌜⌝𝒮⟧ ⟦δ⟧ = ⟦δ⟧ Σ, λ ρ → ρ

⟦⨾⟧ : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧ → ⟦Tms⟧ ⟦Θ⟧ ⟦Δ⟧ → ⟦Tms⟧ ⟦Θ⟧ ⟦Γ⟧
⟦⨾⟧ (⟦δ⟧ Σ, ⟦δ⟧′) (⟦σ⟧ Σ, ⟦σ⟧′) = ⟦⨾𝒮⟧ ⟦δ⟧ ⟦σ⟧ Σ, λ ρ → ⟦δ⟧′ (⟦σ⟧′ ρ)

⟦ε⟧ : ⟦Ctx⟧ ⟦Ψ⟧
⟦ε⟧ = λ _ → ⊤

⟦wk𝒮⟧ : ⟦▷𝒮⟧ ⟦Ψ⟧ ⟦Γ⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ → ⟦Ψ⟧
⟦wk𝒮⟧ (χ Σ, f) = χ

⟦call⟧ : ⟦Tm⟧ {⟦Ψ⟧ = ⟦▷𝒮⟧ ⟦Ψ⟧ ⟦Γ⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧} 
              (⟦[]C⟧ ⟦Γ⟧ ⟦wk𝒮⟧) (⟦[]T⟧ ⟦A⟧ (⟦⌜⌝𝒮⟧ ⟦wk𝒮⟧))
⟦call⟧ (χ Σ, f) ρ = f .fst ρ

variable
  Φ≡ Ψ≡ : ⟦Ψ₁⟧ ≡ᴾ ⟦Ψ₂⟧
  Γ≡ Δ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧
  A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧

⟦▷⟧ : ∀ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) → ⟦Ty⟧ ⟦Γ⟧ → ⟦Ctx⟧ ⟦Ψ⟧
⟦▷⟧ ⟦Γ⟧ ⟦A⟧ = λ χ → Σ (⟦Γ⟧ χ) (λ ρ → ⟦A⟧ χ ρ) 

▷≡ : ∀ Γ≡ → ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧ → ⟦▷⟧ ⟦Γ₁⟧ ⟦A₁⟧ ≡ᴾ ⟦▷⟧ ⟦Γ₂⟧ ⟦A₂⟧ 
▷≡ refl refl = refl

⟦Π⟧ : ∀ ⟦A⟧ → ⟦Ty⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) → ⟦Ty⟧ ⟦Γ⟧
⟦Π⟧ ⟦A⟧ ⟦B⟧ = λ χ ρ → ∀ uⱽ → ⟦B⟧ χ (ρ Σ, uⱽ)

𝔹≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦𝔹⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦𝔹⟧
𝔹≡ refl = refl

▷>eq≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧ 
      → ⟦▷>eq⟧ ⟦Γ₁⟧ ⟦t₁⟧ b ≡ᴾ ⟦▷>eq⟧ ⟦Γ₂⟧ ⟦t₂⟧ b
▷>eq≡ refl refl = refl

⨾≡ : ∀ {⟦δ₁⟧ : ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧} {⟦δ₂⟧ : ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧} 
       {⟦σ₁⟧ : ⟦Tms⟧ ⟦Θ₁⟧ ⟦Δ₁⟧} {⟦σ₂⟧ : ⟦Tms⟧ ⟦Θ₂⟧ ⟦Δ₂⟧}
       (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (Δ≡ : ⟦Δ₁⟧ ≡ᴾ ⟦Δ₂⟧) (Θ≡ : ⟦Θ₁⟧ ≡ᴾ ⟦Θ₂⟧)
   → ⟦δ₁⟧ ≡[ Tms≡ Δ≡ Γ≡ ]≡ᴾ ⟦δ₂⟧ 
   → ⟦σ₁⟧ ≡[ Tms≡ Θ≡ Δ≡ ]≡ᴾ ⟦σ₂⟧
   → ⟦⨾⟧ {⟦Γ⟧ = ⟦Γ₁⟧} ⟦δ₁⟧ ⟦σ₁⟧ ≡[ Tms≡ Θ≡ Γ≡ ]≡ᴾ ⟦⨾⟧ {⟦Γ⟧ = ⟦Γ₂⟧} ⟦δ₂⟧ ⟦σ₂⟧
⨾≡ refl refl refl δ≡ σ≡ = {!!}

Π≡ : ∀ Γ≡ A≡ → ⟦B₁⟧ ≡[ Ty≡ (▷≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧
     → ⟦Π⟧ ⟦A₁⟧ ⟦B₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦Π⟧ ⟦A₂⟧ ⟦B₂⟧
Π≡ refl refl refl = refl

⟦TT⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧
⟦TT⟧ _ _ = true

TT≡ : (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦TT⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦TT⟧ 
TT≡ refl = refl

⟦FF⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧
⟦FF⟧ _ _ = false

FF≡ : (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦FF⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦FF⟧ 
FF≡ refl = refl

⟦ƛ⟧ : ⟦Tm⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧ → ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧)
⟦ƛ⟧ ⟦t⟧ χ ρ uⱽ = ⟦t⟧ χ (ρ Σ, uⱽ)

ƛ≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) 
       (A≡ : ⟦A₁⟧ ≡[ Ty≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ ]≡ᴾ ⟦A₂⟧)
       (B≡ : ⟦B₁⟧ ≡[ Ty≡ (▷≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧)
   → ⟦t₁⟧ ≡[ Tm≡ (▷≡ Γ≡ A≡) B≡ ]≡ᴾ ⟦t₂⟧
   → ⟦ƛ⟧ ⟦t₁⟧ ≡[ Tm≡ Γ≡ (Π≡ Γ≡ A≡ B≡) ]≡ᴾ ⟦ƛ⟧ ⟦t₂⟧
ƛ≡ refl refl refl refl = refl

⟦ƛ⁻¹⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧) → ⟦Tm⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧
⟦ƛ⁻¹⟧ ⟦t⟧ χ (ρ Σ, uⱽ) = ⟦t⟧ χ ρ uⱽ

ƛ⁻¹≡ : ∀ {⟦B₂⟧ ⟦t₂⟧} (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) 
         (A≡ : ⟦A₁⟧ ≡[ Ty≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ ]≡ᴾ ⟦A₂⟧)
         (B≡ : ⟦B₁⟧ ≡[ Ty≡ (▷≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧)
   → ⟦t₁⟧ ≡[ Tm≡ Γ≡ (Π≡ Γ≡ A≡ B≡) ]≡ᴾ ⟦t₂⟧
   → ⟦ƛ⁻¹⟧ ⟦t₁⟧ ≡[ Tm≡ (▷≡ Γ≡ A≡) B≡ ]≡ᴾ ⟦ƛ⁻¹⟧ ⟦t₂⟧
ƛ⁻¹≡ refl refl refl refl = refl

[]T≡ : ∀ {⟦A₁⟧ : ⟦Ty⟧ ⟦Γ₁⟧} {⟦A₂⟧ : ⟦Ty⟧ ⟦Γ₂⟧}
         {⟦δ₁⟧ : ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧} {⟦δ₂⟧ : ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧}
         Γ≡ Δ≡ → ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧ → ⟦δ₁⟧ ≡[ Tms≡ Δ≡ Γ≡ ]≡ᴾ ⟦δ₂⟧
     → ⟦[]T⟧ ⟦A₁⟧ ⟦δ₁⟧ ≡[ Ty≡ Δ≡ ]≡ᴾ ⟦[]T⟧ ⟦A₂⟧ ⟦δ₂⟧
[]T≡ refl refl refl δ≡ = {!!}

wkeq≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (t≡ : ⟦t₁⟧ ≡[ Tm≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧) 
      → ⟦wkeq⟧ ≡[ Tms≡  (▷>eq≡ {b = b} Γ≡ t≡) Γ≡ ]≡ᴾ ⟦wkeq⟧
wkeq≡ refl refl = refl

⟦if⟧ : ∀ ⟦t⟧ 
     → ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ true)  (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧)
     → ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ false) (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧)
     → ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧
⟦if⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ 
  = λ χ ρ → Bool-splitᴾ (⟦t⟧ χ ρ) 
                        (λ t~ → ⟦u⟧ χ (ρ Σ, box t~)) 
                        (λ t~ → ⟦v⟧ χ (ρ Σ, box t~)) 

if≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (A≡ : ⟦A₁⟧ ≡[ Ty≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ ]≡ᴾ ⟦A₂⟧) 
        (t≡ : ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧)
    → ⟦u₁⟧ ≡[ Tm≡ (▷>eq≡ Γ≡ t≡) ([]T≡ Γ≡ (▷>eq≡ Γ≡ t≡) A≡ (wkeq≡ Γ≡ t≡)) 
           ]≡ᴾ ⟦u₂⟧
    → ⟦v₁⟧ ≡[ Tm≡ (▷>eq≡ Γ≡ t≡) ([]T≡ Γ≡ (▷>eq≡ Γ≡ t≡) A≡ (wkeq≡ Γ≡ t≡)) 
           ]≡ᴾ ⟦v₂⟧
    → ⟦if⟧ ⟦t₁⟧ ⟦u₁⟧ ⟦v₁⟧ ≡[ Tm≡ Γ≡ A≡ ]≡ᴾ ⟦if⟧ ⟦t₂⟧ ⟦u₂⟧ ⟦v₂⟧
if≡ refl refl refl refl refl = refl

⟦[]t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ → ∀ (⟦δ⟧ : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧) → ⟦Tm⟧ ⟦Δ⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧)
⟦[]t⟧ ⟦t⟧ (⟦δ⟧ Σ, ⟦δ⟧′) = λ χ ρ → ⟦t⟧ (⟦δ⟧ χ) (⟦δ⟧′ ρ)

-- TODO: Generalise further?
[]C≡ : ∀ (Φ≡ : ⟦Φ₁⟧ ≡ᴾ ⟦Φ₂⟧)
     → ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧ → ⟦γ₁⟧ ≡[ Wk≡ Φ≡ refl ]≡ᴾ ⟦γ₂⟧
     → ⟦[]C⟧ ⟦Γ₁⟧ ⟦γ₁⟧ ≡[ Ctx≡ Φ≡ ]≡ᴾ ⟦[]C⟧ ⟦Γ₂⟧ ⟦γ₂⟧
[]C≡ refl refl refl = refl

⌜⌝𝒮≡ : ∀ {⟦γ₁⟧ : ⟦Wk⟧ ⟦Φ₁⟧ ⟦Ψ₁⟧} 
         (Φ≡ : ⟦Φ₁⟧ ≡ᴾ ⟦Φ₂⟧) (Ψ : ⟦Ψ₁⟧ ≡ᴾ ⟦Ψ₂⟧) 
         (γ≡ : ⟦γ₁⟧ ≡[ Wk≡ Φ≡ Ψ≡ ]≡ᴾ ⟦γ₂⟧) 
     → ⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦γ₁⟧ 
     ≡[ Tms≡′ {⟦Γ₁⟧ = ⟦Γ⟧} Φ≡ Ψ≡ ([]C≡ {⟦Γ₁⟧ = ⟦Γ⟧} Φ≡ refl γ≡) refl 
     ]≡ᴾ ⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦γ₂⟧
⌜⌝𝒮≡  refl refl refl = refl

Ty≡-inst : ∀ {χ : ⟦Ψ⟧} {ρ : ⟦Γ⟧ χ} → ⟦A₁⟧ ≡ᴾ ⟦A₂⟧ → ⟦A₁⟧ χ ρ ≡ᴾ ⟦A₂⟧ χ ρ
Ty≡-inst refl = refl

Tm≡-inst : ∀ {χ : ⟦Ψ⟧} {ρ : ⟦Γ⟧ χ} → ⟦t₁⟧ ≡ᴾ ⟦t₂⟧ → ⟦t₁⟧ χ ρ ≡ᴾ ⟦t₂⟧ χ ρ
Tm≡-inst refl = refl

Tm[]≡-inst : ∀ {χ : ⟦Ψ⟧} {ρ : ⟦Γ⟧ χ} (A≡ : ⟦A₁⟧ ≡ᴾ ⟦A₂⟧) 
           → ⟦t₁⟧ ≡[ Tm≡ refl A≡ ]≡ᴾ ⟦t₂⟧ 
           → ⟦t₁⟧ χ ρ ≡[ Ty≡-inst A≡ ]≡ᴾ ⟦t₂⟧ χ ρ
Tm[]≡-inst refl refl = refl

⟦,eq⟧ : ∀ (⟦δ⟧ : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧) → ⟦[]t⟧ ⟦t⟧ ⟦δ⟧ ≡ᴾ (λ χ ρ → b)
      → ⟦Tms⟧ ⟦Δ⟧ (⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ b)
⟦,eq⟧ (⟦δ⟧ Σ, ⟦δ⟧′) t≡ = ⟦δ⟧ Σ, λ ρ → ⟦δ⟧′ ρ Σ, box (Tm≡-inst t≡)

⟦_⟧Sig : Sig → ⟦Sig⟧
⟦_⟧Ctx : Ctx Ψ → ⟦Ctx⟧ ⟦ Ψ ⟧Sig
⟦_⟧Ty  : Ty Γ → ⟦Ty⟧ ⟦ Γ ⟧Ctx
⟦_⟧Tm  : Tm Γ A → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
⟦_⟧Wk  : Wk Φ Ψ → ⟦Wk⟧ ⟦ Φ ⟧Sig ⟦ Ψ ⟧Sig 
⟦_⟧Tms : Tms Δ Γ → ⟦Tms⟧ ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx

variable
  χ χ₁ χ₂ : ⟦Ψ⟧
  ρ ρ₁ ρ₂ : ⟦Γ⟧ χ

⟦_⟧Ctx~ : Ctx~ Γ₁ Γ₂ → ⟦ Γ₁ ⟧Ctx ≡ᴾ ⟦ Γ₂ ⟧Ctx
⟦_⟧Ty~  : Ty~ Γ~ A₁ A₂ → ⟦ A₁ ⟧Ty ≡[ congᴾ ⟦Ty⟧ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ A₂ ⟧Ty
⟦_⟧Tm~  : Tm~ Γ~ A~ t₁ t₂ 
        → ⟦ t₁ ⟧Tm ≡[ Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ]≡ᴾ ⟦ t₂ ⟧Tm
⟦⟧Wk~   : ⟦ ξ₁ ⟧Wk ≡ᴾ ⟦ ξ₂ ⟧Wk
⟦_⟧Tms~ : Tms~ Δ~ Γ~ δ₁ δ₂ 
        → ⟦ δ₁ ⟧Tms ≡[ Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ δ₂ ⟧Tms

⟦𝔹⟧′ : ⟦ 𝔹 {Γ = Γ} ⟧Ty ≡ᴾ λ χ ρ → Bool 

⟦▷>eq⟧′ : ∀ (Γ : Ctx Ψ) → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ 𝔹 ⟧Ty → Bool → ⟦Ctx⟧ ⟦ Ψ ⟧Sig

⟦ •           ⟧Ctx = λ χ → ⊤
⟦ Γ ▷ A       ⟧Ctx = λ χ → Σ (⟦ Γ ⟧Ctx χ) (λ ρ → ⟦ A ⟧Ty χ ρ)
⟦ Γ ▷ t >eq b ⟧Ctx = ⟦▷>eq⟧′ Γ ⟦ t ⟧Tm b
⟦ Γ [ δ ]     ⟧Ctx = λ χ → ⟦ Γ ⟧Ctx (⟦ δ ⟧Wk χ)


⟦ coe~ Γ~ A ⟧Ty = coeᴾ (Ty≡ ⟦ Γ~ ⟧Ctx~) ⟦ A ⟧Ty
⟦ 𝔹         ⟧Ty = ⟦𝔹⟧
⟦ Π A B     ⟧Ty = λ χ ρ → ∀ tⱽ → ⟦ B ⟧Ty χ (ρ Σ, tⱽ)
⟦ A [ δ ]   ⟧Ty = ⟦[]T⟧ ⟦ A ⟧Ty ⟦ δ ⟧Tms
⟦ if t A B  ⟧Ty = λ χ ρ → Bool-rec (⟦ t ⟧Tm χ ρ) (⟦ A ⟧Ty χ ρ) (⟦ B ⟧Ty χ ρ)

⟦▷>eq⟧′ Γ ⟦t⟧ b = ⟦▷>eq⟧ ⟦ Γ ⟧Ctx ⟦t⟧ b


⟦TT⟧′ : ⟦ TT {Γ = Γ} ⟧Tm ≡ᴾ λ χ ρ → true
⟦FF⟧′ : ⟦ FF {Γ = Γ} ⟧Tm ≡ᴾ λ χ ρ → false
⟦[]⟧′ : ∀ {t : Tm Γ A} {δ : Tms {Φ = Φ} {Ψ = Ψ} Δ Γ} 
      → ⟦ t [ δ ] ⟧Tm 
      ≡ᴾ λ χ ρ → ⟦ t ⟧Tm (⟦ δ ⟧Tms .fst χ) (⟦ δ ⟧Tms .snd ρ)

⟦wk𝒮⟧′ : ⟦ Ψ ▷ Γ ⇒ A if t then u else v ⟧Sig → ⟦ Ψ ⟧Sig

⟦ id    ⟧Wk = ⟦id𝒮⟧
⟦ δ ⨾ σ ⟧Wk = λ χ → ⟦ δ ⟧Wk (⟦ σ ⟧Wk χ)
⟦ wk𝒮   ⟧Wk = ⟦wk𝒮⟧′

⟦,eq⟧′ : ∀ (δ : Tms {Φ = Φ} {Ψ = Ψ} Δ Γ) {t : Tm Γ 𝔹} 
           χ (ρ : ⟦ Δ ⟧Ctx χ) 
       → ⟦[]t⟧ ⟦ t ⟧Tm ⟦ δ ⟧Tms χ ρ ≡ᴾ b
       → ⟦[]C⟧ (⟦▷>eq⟧ ⟦ Γ ⟧Ctx ⟦ t ⟧Tm b) (⟦ δ ⟧Tms .fst) χ

⟦ coe~ Δ~ Γ~ δ ⟧Tms = coeᴾ (Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~) ⟦ δ ⟧Tms
⟦ π₁ δ         ⟧Tms = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦ δ ⟧Tms .snd ρ .fst
⟦ id           ⟧Tms = ⟦id⟧
⟦ π₁eq {t = t} δ ⟧Tms = ⟦π₁eq⟧ {⟦t⟧ = ⟦ t ⟧Tm} ⟦ δ ⟧Tms            
⟦ ε            ⟧Tms = ⟦id𝒮⟧ Σ, λ ρ → tt
⟦ δ , t ⟧Tms        = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦ δ ⟧Tms .snd ρ Σ, ⟦ t ⟧Tm _ ρ
⟦ ,eqℱ {b = true} δ {u = u} refl t~ ⟧Tms 
  with symᴾ (⟦[]⟧′ {δ = δ}) ∙ᴾ ⟦ t~ ⟧Tm~ ∙ᴾ ⟦TT⟧′
... | t≡ = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦,eq⟧′ δ _ ρ (Tm≡-inst t≡)
⟦ ,eqℱ {b = false} δ {u = u} refl t~ ⟧Tms 
  with symᴾ (⟦[]⟧′ {δ = δ}) ∙ᴾ ⟦ t~ ⟧Tm~ ∙ᴾ ⟦FF⟧′
... | t≡ = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦,eq⟧′ δ _ ρ (Tm≡-inst t≡)
⟦ δ ⨾ σ ⟧Tms = _ Σ, λ ρ → ⟦ δ ⟧Tms .snd (⟦ σ ⟧Tms .snd ρ)
⟦ wk𝒮 ⟧Tms = ⟦wk𝒮⟧′ Σ, λ ρ → ρ

⟦ •                               ⟧Sig = ⊤
⟦ Ψ ▷  Γ ⇒ A if t then u else v   ⟧Sig
  = ⟦▷𝒮⟧ ⟦ Ψ ⟧Sig ⟦ Γ ⟧Ctx ⟦ A ⟧Ty ⟦ t ⟧Tm ⟦ u ⟧Tm ⟦ v ⟧Tm

⟦wk𝒮⟧′ (χ Σ, f) = χ

⟦ coe~ Γ~ A~ t ⟧Tm = coeᴾ (Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~) ⟦ t ⟧Tm

⟦ ƛ t     ⟧Tm = λ χ ρ uⱽ → ⟦ t ⟧Tm χ (ρ Σ, uⱽ)
⟦ ƛ⁻¹ t   ⟧Tm = λ χ (ρ Σ, uⱽ)   → ⟦ t ⟧Tm χ ρ uⱽ
⟦ TT      ⟧Tm = λ χ ρ          → true
⟦ FF      ⟧Tm = λ χ ρ          → false
⟦ t [ δ ] ⟧Tm = ⟦[]t⟧ ⟦ t ⟧Tm ⟦ δ ⟧Tms
⟦ π₂ δ  ⟧Tm = λ χ ρ → ⟦ δ ⟧Tms .snd ρ .snd
⟦ call {A = A} ⟧Tm (χ Σ, f) ρ 
  = f .fst ρ

⟦,eq⟧′ {b = b} δ χ ρ t≡ = ⟦ δ ⟧Tms .snd ρ Σ, box t≡

⟦TT⟧′ = refl
⟦FF⟧′ = refl
⟦[]⟧′ = refl

⟦𝔹⟧′ = refl

⟦⌜⌝𝒮⟧≡ : ∀ {⌜ξ⌝} → ⌜ξ⌝ ≡ᴾ ⌜_⌝𝒮 {Γ = Γ} ξ
       → ⟦ ⌜ξ⌝ ⟧Tms ≡ᴾ ⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦ Γ ⟧Ctx} ⟦ ξ ⟧Wk
⟦⌜⌝𝒮⟧≡ {ξ = id} refl = refl
⟦⌜⌝𝒮⟧≡ {Γ = Γ} {ξ = φ ⨾ ψ} refl
  = ⨾≡ (refl {x = ⟦ Γ ⟧Ctx}) refl refl 
       (⟦⌜⌝𝒮⟧≡ {ξ = φ} refl) (⟦⌜⌝𝒮⟧≡ {ξ = ψ} refl)
⟦⌜⌝𝒮⟧≡ {ξ = wk𝒮} refl = refl

-- I'm not immediately sure how to prove this, but it is obviously true
-- Perhaps this would be easier if we enforced that |Wk| in the model was
-- unique (rather than an arbitrary function between signatures, we could use a
-- first-order representation) but I think losing functor laws would be 
-- kinda miserable
wk-uniq : ∀ {ξ₁ ξ₂ : Wk χ Ψ} → ⟦ ξ₁ ⟧Wk ≡ᴾ ⟦ ξ₂ ⟧Wk
wk-uniq = {!!}
 
⟦ rfl~         ⟧Ctx~ = refl
⟦ sym~ Γ~      ⟧Ctx~ = symᴾ ⟦ Γ~ ⟧Ctx~
⟦ Γ₁₂~ ∙~ Γ₂₃~ ⟧Ctx~ = ⟦ Γ₁₂~ ⟧Ctx~ ∙ᴾ ⟦ Γ₂₃~ ⟧Ctx~
⟦ Γ~ ▷ A~      ⟧Ctx~ = ▷≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~
⟦ Γ~ ▷ t~ >eq  ⟧Ctx~ = ▷>eq≡ ⟦ Γ~ ⟧Ctx~ ⟦ t~ ⟧Tm~
⟦ _[] {ξ₁ = ξ₁} {ξ₂ = ξ₂} Γ~ ⟧Ctx~ 
  = []C≡ refl ⟦ Γ~ ⟧Ctx~ (wk-uniq {ξ₁ = ξ₁} {ξ₂ = ξ₂})
⟦ •[] ⟧Ctx~ = refl
⟦ ▷[]ℱ {ξ = ξ} {A = A} refl ⟧Ctx~ 
  = ▷≡ refl ([]T≡ refl refl (refl {x = ⟦ A ⟧Ty}) (symᴾ (⟦⌜⌝𝒮⟧≡ {ξ = ξ} refl)))
⟦ ▷>eq[] ⟧Ctx~ = {!  !}
⟦ [id] ⟧Ctx~ = refl
⟦ [][] ⟧Ctx~ = refl

⟦ rfl~              ⟧Ty~ = refl
⟦ sym~ A~           ⟧Ty~ = sym[]ᴾ ⟦ A~ ⟧Ty~
⟦ A₁₂~ ∙~ A₂₃~      ⟧Ty~ = ⟦ A₁₂~ ⟧Ty~ ∙[]ᴾ ⟦ A₂₃~ ⟧Ty~
⟦ coh               ⟧Ty~ = coh[]ᴾ
⟦ 𝔹 {Γ~ = Γ~}       ⟧Ty~ = 𝔹≡ ⟦ Γ~ ⟧Ctx~
⟦ Π {Γ~ = Γ~} A~ B~ ⟧Ty~ = Π≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ B~ ⟧Ty~
⟦ _[_] {Γ~ = Γ~} {Δ~ = Δ~} A~ δ~ ⟧Ty~ 
  = []T≡ ⟦ Γ~ ⟧Ctx~ ⟦ Δ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ δ~ ⟧Tms~
⟦ if t~ A~ B~ ⟧Ty~ = {!   !}

⟦ ifTT              ⟧Ty~ = refl
⟦ ifFF              ⟧Ty~ = refl
⟦ Π[]               ⟧Ty~ = refl
⟦ if[]              ⟧Ty~ = refl
⟦ 𝔹[]               ⟧Ty~ = refl
⟦ [][]              ⟧Ty~ = refl
⟦ [id]              ⟧Ty~ = refl

-- Specialisation of |coh[]ᴾ| to assist with termination
cohTm : ∀ {⟦t⟧ : ⟦Tm⟧ {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Γ₁⟧ ⟦A₁⟧} {Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧} 
          {A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧} 
      → ⟦t⟧ ≡[ Tm≡ Γ≡ A≡ ]≡ᴾ coeᴾ (Tm≡ Γ≡ A≡) ⟦t⟧
cohTm {Γ≡ = refl} {A≡ = refl} = refl

call-TT≡ : ∀ {⟦t⟧ : ⟦Tm⟧ {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Γ⟧ ⟦𝔹⟧}  {⟦A⟧}
             {⟦u⟧ : ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧)} 
             {⟦v⟧ : ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧)} 
             {⟦δ⟧ : ⟦Tms⟧ {⟦Φ⟧ = ⟦Φ⟧} ⟦Δ⟧ 
                          (⟦[]C⟧ ⟦Γ⟧ (⟦wk𝒮⟧ {⟦A⟧ = ⟦A⟧} {⟦t⟧ = ⟦t⟧}))} 
             (t≡ : ⟦[]t⟧ ⟦t⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦Γ⟧} (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦wk𝒮⟧) ⟦δ⟧) 
                 ≡ᴾ ⟦TT⟧)
             → ⟦[]t⟧ (⟦call⟧ {⟦u⟧ = ⟦u⟧} {⟦v⟧ = ⟦v⟧}) ⟦δ⟧  
             ≡ᴾ ⟦[]t⟧ ⟦u⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ _}
                      (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ _} (⟦wk𝒮⟧ )) 
                      (⟦,eq⟧ {⟦Γ⟧ = ⟦[]C⟧ ⟦Γ⟧ ⟦wk𝒮⟧} 
                             {⟦t⟧ = ⟦[]t⟧ ⟦t⟧ (⟦⌜⌝𝒮⟧ ⟦wk𝒮⟧)} ⟦δ⟧ t≡))
call-TT≡ {⟦δ⟧ = ⟦δ⟧} t≡ 
  = funextᴾ λ χ → funextᴾ λ ρ → 
      let (φ′ Σ, (f Σ, fTT Σ, fFF)) = ⟦δ⟧ .fst χ
          ρ′ = ⟦δ⟧ .snd ρ
      in unbox (fTT ρ′ (Tm≡-inst t≡))

call-FF≡ : ∀ {⟦t⟧ : ⟦Tm⟧ {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Γ⟧ ⟦𝔹⟧}  {⟦A⟧}
             {⟦u⟧ : ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧)} 
             {⟦v⟧ : ⟦Tm⟧ (⟦▷>eq⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkeq⟧)} 
             {⟦δ⟧ : ⟦Tms⟧ {⟦Φ⟧ = ⟦Φ⟧} ⟦Δ⟧ 
                          (⟦[]C⟧ ⟦Γ⟧ (⟦wk𝒮⟧ {⟦A⟧ = ⟦A⟧} {⟦t⟧ = ⟦t⟧}))} 
             (t≡ : ⟦[]t⟧ ⟦t⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦Γ⟧} (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦wk𝒮⟧) ⟦δ⟧) 
                 ≡ᴾ ⟦FF⟧)
             → ⟦[]t⟧ (⟦call⟧ {⟦u⟧ = ⟦u⟧} {⟦v⟧ = ⟦v⟧}) ⟦δ⟧  
             ≡ᴾ ⟦[]t⟧ ⟦v⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ _}
                      (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦▷>eq⟧ ⟦Γ⟧ ⟦t⟧ _} (⟦wk𝒮⟧ )) 
                      (⟦,eq⟧ {⟦Γ⟧ = ⟦[]C⟧ ⟦Γ⟧ ⟦wk𝒮⟧} 
                             {⟦t⟧ = ⟦[]t⟧ ⟦t⟧ (⟦⌜⌝𝒮⟧ ⟦wk𝒮⟧)} ⟦δ⟧ t≡))
call-FF≡ {⟦δ⟧ = ⟦δ⟧} t≡ 
  = funextᴾ λ χ → funextᴾ λ ρ → 
      let (φ′ Σ, (f Σ, fTT Σ, fFF)) = ⟦δ⟧ .fst χ
          ρ′ = ⟦δ⟧ .snd ρ
      in unbox (fFF ρ′ (Tm≡-inst t≡))

⟦ rfl~         ⟧Tm~ = refl
⟦ sym~ t~      ⟧Tm~ = sym[]ᴾ ⟦ t~ ⟧Tm~
⟦ t₁₂~ ∙~ t₂₃~ ⟧Tm~ = ⟦ t₁₂~ ⟧Tm~ ∙[]ᴾ ⟦ t₂₃~ ⟧Tm~

⟦ coh {Γ~ = Γ~} {A~ = A~} ⟧Tm~ = cohTm {Γ≡ = ⟦ Γ~ ⟧Ctx~} {A≡ = ⟦ A~ ⟧Ty~}

⟦ ƛ_ {Γ~ = Γ~} {A~ = A~} {B~ = B~} t~   ⟧Tm~ 
  = ƛ≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ B~ ⟧Ty~ ⟦ t~ ⟧Tm~
⟦ ƛ⁻¹_ {Γ~ = Γ~} {A~ = A~} {B~ = B~} t~ ⟧Tm~ 
  = ƛ⁻¹≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ B~ ⟧Ty~ ⟦ t~ ⟧Tm~
⟦ π₂ δ~        ⟧Tm~ = {!   !}
⟦ TT Γ~        ⟧Tm~ = TT≡ ⟦ Γ~ ⟧Ctx~
⟦ FF Γ~        ⟧Tm~ = FF≡ ⟦ Γ~ ⟧Ctx~
⟦ t~ [ δ~ ]    ⟧Tm~ = {!   !}
⟦ π₂eq {b = true}  δ ⟧Tm~ with ⟦ δ ⟧Tms
... | ⟦δ⟧ = funextᴾ λ χ → funextᴾ λ ρ → ⟦δ⟧ .snd ρ .snd .unbox
⟦ π₂eq {b = false}  δ ⟧Tm~ with ⟦ δ ⟧Tms
... | ⟦δ⟧ = funextᴾ λ χ → funextᴾ λ ρ → ⟦δ⟧ .snd ρ .snd .unbox
⟦ TT[]               ⟧Tm~ = refl
⟦ FF[]               ⟧Tm~ = refl
⟦ ƛ[]                ⟧Tm~ = refl
⟦ [id]               ⟧Tm~ = refl
⟦ [][]               ⟧Tm~ = refl
⟦ β                  ⟧Tm~ = refl
⟦ η                  ⟧Tm~ = refl
⟦ π₂,                ⟧Tm~ = refl
⟦ π₂⨾                ⟧Tm~ = refl
⟦ callTT {δ = δ} t~  ⟧Tm~ = call-TT≡ {⟦δ⟧ = ⟦ δ ⟧Tms} ⟦ t~ ⟧Tm~
⟦ callFF {δ = δ} t~  ⟧Tm~ = call-FF≡ {⟦δ⟧ = ⟦ δ ⟧Tms} ⟦ t~ ⟧Tm~

⟦ rfl~              ⟧Tms~ = refl
⟦ sym~ δ~           ⟧Tms~ = sym[]ᴾ ⟦ δ~ ⟧Tms~
⟦ δ₁₂~ ∙~ δ₂₃~      ⟧Tms~ = ⟦ δ₁₂~ ⟧Tms~ ∙[]ᴾ ⟦ δ₂₃~ ⟧Tms~
⟦ coh               ⟧Tms~ = coh[]ᴾ
⟦ ε                 ⟧Tms~ = {!   !}
⟦ δ~ , t~           ⟧Tms~ = {!   !}
⟦ ,eq~ δ~           ⟧Tms~ = {!   !}
⟦ id                ⟧Tms~ = {!   !}
⟦ δ~ ⨾ σ~           ⟧Tms~ = {!   !}
⟦ π₁ A~ δ~          ⟧Tms~ = {!   !}
⟦ π₁eq t~ δ~        ⟧Tms~ = {!   !}
⟦ εη                ⟧Tms~ = {!!}
⟦ ,η                ⟧Tms~ = refl
⟦ ,eqη {b = true}   ⟧Tms~ = refl
⟦ ,eqη {b = false}  ⟧Tms~ = refl
⟦ π₁,               ⟧Tms~ = refl
⟦ π₁eq, {b = false} ⟧Tms~ = refl
⟦ π₁eq, {b = true}  ⟧Tms~ = refl
⟦ π₁⨾               ⟧Tms~ = refl
⟦ π₁eq⨾             ⟧Tms~ = refl
⟦ id⨾               ⟧Tms~ = refl
⟦ ⨾id               ⟧Tms~ = refl
⟦ ⨾⨾                ⟧Tms~ = refl
⟦ ,⨾                ⟧Tms~ = refl
⟦ ,eq⨾ {b = true}   ⟧Tms~ = refl
⟦ ,eq⨾ {b = false}  ⟧Tms~ = refl
⟦ wk𝒮               ⟧Tms~ = {!!}
⟦ wk⨾π₁             ⟧Tms~ = {!!}
⟦ wk⨾π₁eq           ⟧Tms~ = {!!}
