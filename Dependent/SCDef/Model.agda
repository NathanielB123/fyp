{-# OPTIONS --prop --rewriting --show-irrelevant 
            --no-require-unique-meta-solutions #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Syntax

-- Like "ModelOld.agda" but without asserting termination.
--
-- To achieve this, we use some trickery with forward references, with-clauses 
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
⟦Ty⟧ ⟦Γ⟧ = ∀ φ → ⟦Γ⟧ φ → Set

⟦Tm⟧ : ∀ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) → ⟦Ty⟧ ⟦Γ⟧ → Set
⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ = ∀ φ ρ → ⟦A⟧ φ ρ

⟦Wk⟧ : ⟦Sig⟧ → ⟦Sig⟧ → Set
⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ = ⟦Φ⟧ → ⟦Ψ⟧

⟦[]C⟧ : ⟦Ctx⟧ ⟦Ψ⟧ → ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ → ⟦Ctx⟧ ⟦Φ⟧
⟦[]C⟧ ⟦Γ⟧ ⟦δ⟧ = λ φ → ⟦Γ⟧ (⟦δ⟧ φ)

⟦Tms⟧ : ⟦Ctx⟧ ⟦Φ⟧ → ⟦Ctx⟧ ⟦Ψ⟧ → Set
⟦Tms⟧ {⟦Φ⟧ = ⟦Φ⟧} {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Δ⟧ ⟦Γ⟧ 
  = Σ (⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧) λ ⟦δ⟧ → ∀ {φ} → ⟦Δ⟧ φ → ⟦[]C⟧ ⟦Γ⟧ ⟦δ⟧ φ

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
⟦𝔹⟧ = λ φ ρ → Bool

⟦,>rw⟧ : ∀ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) → ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧ → Bool → ⟦Ctx⟧ ⟦Ψ⟧
⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ b = λ φ → Σ (⟦Γ⟧ φ) (λ ρ → Box (⟦t⟧ φ ρ ≡ᴾ b))

⟦id𝒮⟧ : ⟦Wk⟧ ⟦Ψ⟧ ⟦Ψ⟧
⟦id𝒮⟧ = λ φ → φ

⟦id⟧ : ⟦Tms⟧ ⟦Γ⟧ ⟦Γ⟧
⟦id⟧ = ⟦id𝒮⟧ Σ, λ ρ → ρ

⟦wkrw⟧ : ⟦Tms⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ b) ⟦Γ⟧
⟦wkrw⟧ = ⟦id𝒮⟧ Σ, fst

⟦π₁rw⟧ : ⟦Tms⟧ ⟦Δ⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ b) → ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧
⟦π₁rw⟧ ⟦δ⟧ = ⟦δ⟧ .fst Σ, λ ρ → ⟦δ⟧ .snd ρ .fst


⟦[]T⟧ : ⟦Ty⟧ ⟦Γ⟧ → ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧ → ⟦Ty⟧ ⟦Δ⟧
⟦[]T⟧ ⟦A⟧ ⟦δ⟧ φ ρ = ⟦A⟧ (⟦δ⟧ .fst φ) (⟦δ⟧ .snd ρ)

⟦,def⟧ : ∀ ⟦Ψ⟧ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) ⟦A⟧ ⟦t⟧
       → ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ true)   (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧) 
       → ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ false)  (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧) 
       → ⟦Sig⟧
⟦,def⟧ ⟦Ψ⟧ ⟦Γ⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ 
  = Σ ⟦Ψ⟧ λ φ → 
    Σ (∀ ρ → ⟦A⟧ φ ρ) λ f → 
      (∀ ρ (t~ : ⟦t⟧ φ ρ ≡ᴾ true) 
    → Box (f ρ ≡ᴾ ⟦u⟧ φ (ρ Σ, box t~)))
    × (∀ ρ (t~ : ⟦t⟧ φ ρ ≡ᴾ false)
    → Box (f ρ ≡ᴾ ⟦v⟧ φ (ρ Σ, box t~)))

⟦⨾𝒮⟧ : ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ → ⟦Wk⟧ ⟦Ξ⟧ ⟦Φ⟧ → ⟦Wk⟧ ⟦Ξ⟧ ⟦Ψ⟧
⟦⨾𝒮⟧ ⟦δ⟧ ⟦σ⟧ = λ φ → ⟦δ⟧ (⟦σ⟧ φ)

⟦⌜⌝𝒮⟧ : ∀ (⟦δ⟧ : ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧) → ⟦Tms⟧ (⟦[]C⟧ ⟦Γ⟧ ⟦δ⟧) ⟦Γ⟧
⟦⌜⌝𝒮⟧ ⟦δ⟧ = ⟦δ⟧ Σ, λ ρ → ρ

⟦⨾⟧ : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧ → ⟦Tms⟧ ⟦Θ⟧ ⟦Δ⟧ → ⟦Tms⟧ ⟦Θ⟧ ⟦Γ⟧
⟦⨾⟧ (⟦δ⟧ Σ, ⟦δ⟧′) (⟦σ⟧ Σ, ⟦σ⟧′) = ⟦⨾𝒮⟧ ⟦δ⟧ ⟦σ⟧ Σ, λ ρ → ⟦δ⟧′ (⟦σ⟧′ ρ)

⟦ε⟧ : ⟦Ctx⟧ ⟦Ψ⟧
⟦ε⟧ = λ _ → ⊤

⟦wk𝒮⟧ : ⟦,def⟧ ⟦Ψ⟧ ⟦Γ⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ → ⟦Ψ⟧
⟦wk𝒮⟧ (φ Σ, f) = φ

⟦call⟧ : ⟦Tm⟧ {⟦Ψ⟧ = ⟦,def⟧ ⟦Ψ⟧ ⟦Γ⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧} 
              (⟦[]C⟧ ⟦Γ⟧ ⟦wk𝒮⟧) (⟦[]T⟧ ⟦A⟧ (⟦⌜⌝𝒮⟧ ⟦wk𝒮⟧))
⟦call⟧ (φ Σ, f) ρ = f .fst ρ

variable
  Φ≡ Ψ≡ : ⟦Ψ₁⟧ ≡ᴾ ⟦Ψ₂⟧
  Γ≡ Δ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧
  A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧

⟦,⟧ : ∀ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) → ⟦Ty⟧ ⟦Γ⟧ → ⟦Ctx⟧ ⟦Ψ⟧
⟦,⟧ ⟦Γ⟧ ⟦A⟧ = λ φ → Σ (⟦Γ⟧ φ) (λ ρ → ⟦A⟧ φ ρ) 

,≡ : ∀ Γ≡ → ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧ → ⟦,⟧ ⟦Γ₁⟧ ⟦A₁⟧ ≡ᴾ ⟦,⟧ ⟦Γ₂⟧ ⟦A₂⟧ 
,≡ refl refl = refl

⟦Π⟧ : ∀ ⟦A⟧ → ⟦Ty⟧ (⟦,⟧ ⟦Γ⟧ ⟦A⟧) → ⟦Ty⟧ ⟦Γ⟧
⟦Π⟧ ⟦A⟧ ⟦B⟧ = λ φ ρ → ∀ uⱽ → ⟦B⟧ φ (ρ Σ, uⱽ)

𝔹≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦𝔹⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦𝔹⟧
𝔹≡ refl = refl

,>rw≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧ 
      → ⟦,>rw⟧ ⟦Γ₁⟧ ⟦t₁⟧ b ≡ᴾ ⟦,>rw⟧ ⟦Γ₂⟧ ⟦t₂⟧ b
,>rw≡ refl refl = refl

⨾≡ : ∀ {⟦δ₁⟧ : ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧} {⟦δ₂⟧ : ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧} 
       {⟦σ₁⟧ : ⟦Tms⟧ ⟦Θ₁⟧ ⟦Δ₁⟧} {⟦σ₂⟧ : ⟦Tms⟧ ⟦Θ₂⟧ ⟦Δ₂⟧}
       (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (Δ≡ : ⟦Δ₁⟧ ≡ᴾ ⟦Δ₂⟧) (Θ≡ : ⟦Θ₁⟧ ≡ᴾ ⟦Θ₂⟧)
   → ⟦δ₁⟧ ≡[ Tms≡ Δ≡ Γ≡ ]≡ᴾ ⟦δ₂⟧ 
   → ⟦σ₁⟧ ≡[ Tms≡ Θ≡ Δ≡ ]≡ᴾ ⟦σ₂⟧
   → ⟦⨾⟧ {⟦Γ⟧ = ⟦Γ₁⟧} ⟦δ₁⟧ ⟦σ₁⟧ ≡[ Tms≡ Θ≡ Γ≡ ]≡ᴾ ⟦⨾⟧ {⟦Γ⟧ = ⟦Γ₂⟧} ⟦δ₂⟧ ⟦σ₂⟧
⨾≡ refl refl refl δ≡ σ≡ = {!!}

Π≡ : ∀ Γ≡ A≡ → ⟦B₁⟧ ≡[ Ty≡ (,≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧
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

⟦ƛ⟧ : ⟦Tm⟧ (⟦,⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧ → ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧)
⟦ƛ⟧ ⟦t⟧ φ ρ uⱽ = ⟦t⟧ φ (ρ Σ, uⱽ)

ƛ≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) 
       (A≡ : ⟦A₁⟧ ≡[ Ty≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ ]≡ᴾ ⟦A₂⟧)
       (B≡ : ⟦B₁⟧ ≡[ Ty≡ (,≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧)
   → ⟦t₁⟧ ≡[ Tm≡ (,≡ Γ≡ A≡) B≡ ]≡ᴾ ⟦t₂⟧
   → ⟦ƛ⟧ ⟦t₁⟧ ≡[ Tm≡ Γ≡ (Π≡ Γ≡ A≡ B≡) ]≡ᴾ ⟦ƛ⟧ ⟦t₂⟧
ƛ≡ refl refl refl refl = refl

⟦ƛ⁻¹⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧) → ⟦Tm⟧ (⟦,⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧
⟦ƛ⁻¹⟧ ⟦t⟧ φ (ρ Σ, uⱽ) = ⟦t⟧ φ ρ uⱽ

ƛ⁻¹≡ : ∀ {⟦B₂⟧ ⟦t₂⟧} (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) 
         (A≡ : ⟦A₁⟧ ≡[ Ty≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ ]≡ᴾ ⟦A₂⟧)
         (B≡ : ⟦B₁⟧ ≡[ Ty≡ (,≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧)
   → ⟦t₁⟧ ≡[ Tm≡ Γ≡ (Π≡ Γ≡ A≡ B≡) ]≡ᴾ ⟦t₂⟧
   → ⟦ƛ⁻¹⟧ ⟦t₁⟧ ≡[ Tm≡ (,≡ Γ≡ A≡) B≡ ]≡ᴾ ⟦ƛ⁻¹⟧ ⟦t₂⟧
ƛ⁻¹≡ refl refl refl refl = refl

[]T≡ : ∀ {⟦A₁⟧ : ⟦Ty⟧ ⟦Γ₁⟧} {⟦A₂⟧ : ⟦Ty⟧ ⟦Γ₂⟧}
         {⟦δ₁⟧ : ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧} {⟦δ₂⟧ : ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧}
         Γ≡ Δ≡ → ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧ → ⟦δ₁⟧ ≡[ Tms≡ Δ≡ Γ≡ ]≡ᴾ ⟦δ₂⟧
     → ⟦[]T⟧ ⟦A₁⟧ ⟦δ₁⟧ ≡[ Ty≡ Δ≡ ]≡ᴾ ⟦[]T⟧ ⟦A₂⟧ ⟦δ₂⟧
[]T≡ refl refl refl δ≡ = {!!}

wkrw≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (t≡ : ⟦t₁⟧ ≡[ Tm≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧) 
      → ⟦wkrw⟧ ≡[ Tms≡  (,>rw≡ {b = b} Γ≡ t≡) Γ≡ ]≡ᴾ ⟦wkrw⟧
wkrw≡ refl refl = refl

⟦if⟧ : ∀ ⟦t⟧ 
     → ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ true)  (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧)
     → ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ false) (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧)
     → ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧
⟦if⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ 
  = λ φ ρ → Bool-splitᴾ (⟦t⟧ φ ρ) 
                        (λ t~ → ⟦u⟧ φ (ρ Σ, box t~)) 
                        (λ t~ → ⟦v⟧ φ (ρ Σ, box t~)) 

if≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (A≡ : ⟦A₁⟧ ≡[ Ty≡ {⟦Ψ⟧ = ⟦Ψ⟧} Γ≡ ]≡ᴾ ⟦A₂⟧) 
        (t≡ : ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧)
    → ⟦u₁⟧ ≡[ Tm≡ (,>rw≡ Γ≡ t≡) ([]T≡ Γ≡ (,>rw≡ Γ≡ t≡) A≡ (wkrw≡ Γ≡ t≡)) 
           ]≡ᴾ ⟦u₂⟧
    → ⟦v₁⟧ ≡[ Tm≡ (,>rw≡ Γ≡ t≡) ([]T≡ Γ≡ (,>rw≡ Γ≡ t≡) A≡ (wkrw≡ Γ≡ t≡)) 
           ]≡ᴾ ⟦v₂⟧
    → ⟦if⟧ ⟦t₁⟧ ⟦u₁⟧ ⟦v₁⟧ ≡[ Tm≡ Γ≡ A≡ ]≡ᴾ ⟦if⟧ ⟦t₂⟧ ⟦u₂⟧ ⟦v₂⟧
if≡ refl refl refl refl refl = refl

⟦[]t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ → ∀ (⟦δ⟧ : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧) → ⟦Tm⟧ ⟦Δ⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧)
⟦[]t⟧ ⟦t⟧ (⟦δ⟧ Σ, ⟦δ⟧′) = λ φ ρ → ⟦t⟧ (⟦δ⟧ φ) (⟦δ⟧′ ρ)

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

Ty≡-inst : ∀ {φ : ⟦Ψ⟧} {ρ : ⟦Γ⟧ φ} → ⟦A₁⟧ ≡ᴾ ⟦A₂⟧ → ⟦A₁⟧ φ ρ ≡ᴾ ⟦A₂⟧ φ ρ
Ty≡-inst refl = refl

Tm≡-inst : ∀ {φ : ⟦Ψ⟧} {ρ : ⟦Γ⟧ φ} → ⟦t₁⟧ ≡ᴾ ⟦t₂⟧ → ⟦t₁⟧ φ ρ ≡ᴾ ⟦t₂⟧ φ ρ
Tm≡-inst refl = refl

Tm[]≡-inst : ∀ {φ : ⟦Ψ⟧} {ρ : ⟦Γ⟧ φ} (A≡ : ⟦A₁⟧ ≡ᴾ ⟦A₂⟧) 
           → ⟦t₁⟧ ≡[ Tm≡ refl A≡ ]≡ᴾ ⟦t₂⟧ 
           → ⟦t₁⟧ φ ρ ≡[ Ty≡-inst A≡ ]≡ᴾ ⟦t₂⟧ φ ρ
Tm[]≡-inst refl refl = refl

⟦,rw⟧ : ∀ (⟦δ⟧ : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧) → ⟦[]t⟧ ⟦t⟧ ⟦δ⟧ ≡ᴾ (λ φ ρ → b)
      → ⟦Tms⟧ ⟦Δ⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ b)
⟦,rw⟧ (⟦δ⟧ Σ, ⟦δ⟧′) t≡ = ⟦δ⟧ Σ, λ ρ → ⟦δ⟧′ ρ Σ, box (Tm≡-inst t≡)

⟦_⟧Sig : Sig → ⟦Sig⟧
⟦_⟧Ctx : Ctx Ψ → ⟦Ctx⟧ ⟦ Ψ ⟧Sig
⟦_⟧Ty  : Ty Γ → ⟦Ty⟧ ⟦ Γ ⟧Ctx
⟦_⟧Tm  : Tm Γ A → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
⟦_⟧Wk  : Wk Φ Ψ → ⟦Wk⟧ ⟦ Φ ⟧Sig ⟦ Ψ ⟧Sig 
⟦_⟧Tms : Tms Δ Γ → ⟦Tms⟧ ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx

variable
  φ ψ     : ⟦Ψ⟧
  ρ ρ₁ ρ₂ : ⟦Γ⟧ φ

⟦_⟧Ctx~ : Ctx~ Γ₁ Γ₂ → ⟦ Γ₁ ⟧Ctx ≡ᴾ ⟦ Γ₂ ⟧Ctx
⟦_⟧Ty~  : Ty~ Γ~ A₁ A₂ → ⟦ A₁ ⟧Ty ≡[ congᴾ ⟦Ty⟧ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ A₂ ⟧Ty
⟦_⟧Tm~  : Tm~ Γ~ A~ t₁ t₂ 
        → ⟦ t₁ ⟧Tm ≡[ Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ]≡ᴾ ⟦ t₂ ⟧Tm
⟦⟧Wk~   : ⟦ δ₁ ⟧Wk ≡ᴾ ⟦ δ₂ ⟧Wk
⟦_⟧Tms~ : Tms~ Δ~ Γ~ δ₁ δ₂ 
        → ⟦ δ₁ ⟧Tms ≡[ Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ δ₂ ⟧Tms

⟦𝔹⟧′ : ⟦ 𝔹 {Γ = Γ} ⟧Ty ≡ᴾ λ φ ρ → Bool 

⟦,>rw⟧′ : ∀ (Γ : Ctx Ψ) → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ 𝔹 ⟧Ty → Bool → ⟦Ctx⟧ ⟦ Ψ ⟧Sig

⟦ ε           ⟧Ctx = λ φ → ⊤
⟦ Γ , A       ⟧Ctx = λ φ → Σ (⟦ Γ ⟧Ctx φ) (λ ρ → ⟦ A ⟧Ty φ ρ)
⟦ Γ , t >rw b ⟧Ctx = ⟦,>rw⟧′ Γ ⟦ t ⟧Tm b
⟦ Γ [ δ ]     ⟧Ctx = λ φ → ⟦ Γ ⟧Ctx (⟦ δ ⟧Wk φ)


⟦ coe~ Γ~ A ⟧Ty = coeᴾ (Ty≡ ⟦ Γ~ ⟧Ctx~) ⟦ A ⟧Ty
⟦ 𝔹         ⟧Ty = ⟦𝔹⟧
⟦ Π A B     ⟧Ty = λ φ ρ → ∀ tⱽ → ⟦ B ⟧Ty φ (ρ Σ, tⱽ)
⟦ A [ δ ]   ⟧Ty = ⟦[]T⟧ ⟦ A ⟧Ty ⟦ δ ⟧Tms
⟦ if t A B  ⟧Ty = λ φ ρ → Bool-rec (⟦ t ⟧Tm φ ρ) (⟦ A ⟧Ty φ ρ) (⟦ B ⟧Ty φ ρ)

⟦,>rw⟧′ Γ ⟦t⟧ b = ⟦,>rw⟧ ⟦ Γ ⟧Ctx ⟦t⟧ b


⟦TT⟧′ : ⟦ TT {Γ = Γ} ⟧Tm ≡ᴾ λ φ ρ → true
⟦FF⟧′ : ⟦ FF {Γ = Γ} ⟧Tm ≡ᴾ λ φ ρ → false
⟦[]⟧′ : ∀ {t : Tm Γ A} {δ : Tms {Φ = Φ} {Ψ = Ψ} Δ Γ} 
      → ⟦ t [ δ ] ⟧Tm 
      ≡ᴾ λ φ ρ → ⟦ t ⟧Tm (⟦ δ ⟧Tms .fst φ) (⟦ δ ⟧Tms .snd ρ)

⟦wk𝒮⟧′ : ⟦ Ψ ,def Γ ⇒ A if t then u else v ⟧Sig → ⟦ Ψ ⟧Sig

⟦ id    ⟧Wk = ⟦id𝒮⟧
⟦ δ ⨾ σ ⟧Wk = λ φ → ⟦ δ ⟧Wk (⟦ σ ⟧Wk φ)
⟦ wk𝒮   ⟧Wk = ⟦wk𝒮⟧′

⟦,rw⟧′ : ∀ (δ : Tms {Φ = Φ} {Ψ = Ψ} Δ Γ) {t : Tm Γ 𝔹} 
           φ (ρ : ⟦ Δ ⟧Ctx φ) 
       → ⟦[]t⟧ ⟦ t ⟧Tm ⟦ δ ⟧Tms φ ρ ≡ᴾ b
       → ⟦[]C⟧ (⟦,>rw⟧ ⟦ Γ ⟧Ctx ⟦ t ⟧Tm b) (⟦ δ ⟧Tms .fst) φ

⟦ coe~ Δ~ Γ~ δ ⟧Tms = coeᴾ (Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~) ⟦ δ ⟧Tms
⟦ π₁ δ         ⟧Tms = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦ δ ⟧Tms .snd ρ .fst
⟦ id           ⟧Tms = ⟦id⟧
⟦ π₁rw {t = t} δ ⟧Tms = ⟦π₁rw⟧ {⟦t⟧ = ⟦ t ⟧Tm} ⟦ δ ⟧Tms            
⟦ ε            ⟧Tms = ⟦id𝒮⟧ Σ, λ ρ → tt
⟦ δ , t ⟧Tms        = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦ δ ⟧Tms .snd ρ Σ, ⟦ t ⟧Tm _ ρ
⟦ ,rwℱ {b = true} δ {u = u} refl t~ ⟧Tms 
  with symᴾ (⟦[]⟧′ {δ = δ}) ∙ᴾ ⟦ t~ ⟧Tm~ ∙ᴾ ⟦TT⟧′
... | t≡ = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦,rw⟧′ δ _ ρ (Tm≡-inst t≡)
⟦ ,rwℱ {b = false} δ {u = u} refl t~ ⟧Tms 
  with symᴾ (⟦[]⟧′ {δ = δ}) ∙ᴾ ⟦ t~ ⟧Tm~ ∙ᴾ ⟦FF⟧′
... | t≡ = ⟦ δ ⟧Tms .fst Σ, λ ρ → ⟦,rw⟧′ δ _ ρ (Tm≡-inst t≡)
⟦ δ ⨾ σ ⟧Tms = _ Σ, λ ρ → ⟦ δ ⟧Tms .snd (⟦ σ ⟧Tms .snd ρ)
⟦ wk𝒮 ⟧Tms = ⟦wk𝒮⟧′ Σ, λ ρ → ρ

⟦ ε                               ⟧Sig = ⊤
⟦ Ψ ,def Γ ⇒ A if t then u else v ⟧Sig
  = ⟦,def⟧ ⟦ Ψ ⟧Sig ⟦ Γ ⟧Ctx ⟦ A ⟧Ty ⟦ t ⟧Tm ⟦ u ⟧Tm ⟦ v ⟧Tm

⟦wk𝒮⟧′ (φ Σ, f) = φ

⟦ coe~ Γ~ A~ t ⟧Tm = coeᴾ (Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~) ⟦ t ⟧Tm

⟦ ƛ t     ⟧Tm = λ φ ρ uⱽ → ⟦ t ⟧Tm φ (ρ Σ, uⱽ)
⟦ ƛ⁻¹ t   ⟧Tm = λ φ (ρ Σ, uⱽ)   → ⟦ t ⟧Tm φ ρ uⱽ
⟦ TT      ⟧Tm = λ φ ρ          → true
⟦ FF      ⟧Tm = λ φ ρ          → false
⟦ t [ δ ] ⟧Tm = ⟦[]t⟧ ⟦ t ⟧Tm ⟦ δ ⟧Tms
⟦ π₂ δ  ⟧Tm = λ φ ρ → ⟦ δ ⟧Tms .snd ρ .snd
⟦ call {A = A} ⟧Tm (φ Σ, f) ρ 
  = f .fst ρ

⟦,rw⟧′ {b = b} δ φ ρ t≡ = ⟦ δ ⟧Tms .snd ρ Σ, box t≡

⟦TT⟧′ = refl
⟦FF⟧′ = refl
⟦[]⟧′ = refl

⟦𝔹⟧′ = refl

⟦⌜⌝𝒮⟧≡ : ∀ {⌜δ⌝} → ⌜δ⌝ ≡ᴾ ⌜_⌝𝒮 {Γ = Γ} δ
       → ⟦ ⌜δ⌝ ⟧Tms ≡ᴾ ⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦ Γ ⟧Ctx} ⟦ δ ⟧Wk
⟦⌜⌝𝒮⟧≡ {δ = id} refl = refl
⟦⌜⌝𝒮⟧≡ {Γ = Γ} {δ = δ ⨾ σ} refl
  = ⨾≡ (refl {x = ⟦ Γ ⟧Ctx}) refl refl (⟦⌜⌝𝒮⟧≡ {δ = δ} refl) (⟦⌜⌝𝒮⟧≡ {δ = σ} refl)
⟦⌜⌝𝒮⟧≡ {δ = wk𝒮} refl = refl

-- I'm not immediately sure how to prove this, but it is obviously true
-- Perhaps this would be easier if we enforced that |Wk| in the model was
-- unique (rather than an arbitrary function between signatures, we could use a
-- first-order representation) but I think losing functor laws would be 
-- kinda miserable
wk-uniq : ∀ {δ₁ δ₂ : Wk Φ Ψ} → ⟦ δ₁ ⟧Wk ≡ᴾ ⟦ δ₂ ⟧Wk
wk-uniq = {!!}
 
⟦ rfl~         ⟧Ctx~ = refl
⟦ sym~ Γ~      ⟧Ctx~ = symᴾ ⟦ Γ~ ⟧Ctx~
⟦ Γ₁₂~ ∙~ Γ₂₃~ ⟧Ctx~ = ⟦ Γ₁₂~ ⟧Ctx~ ∙ᴾ ⟦ Γ₂₃~ ⟧Ctx~
⟦ Γ~ , A~      ⟧Ctx~ = ,≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~
⟦ Γ~ , t~ >rw  ⟧Ctx~ = ,>rw≡ ⟦ Γ~ ⟧Ctx~ ⟦ t~ ⟧Tm~
⟦ _[] {δ₁ = δ₁} {δ₂ = δ₂} Γ~ ⟧Ctx~ 
  = []C≡ refl ⟦ Γ~ ⟧Ctx~ (wk-uniq {δ₁ = δ₁} {δ₂ = δ₂})
⟦ ε[] ⟧Ctx~ = refl
⟦ ,[]ℱ {δ = δ} {A = A} refl ⟧Ctx~ 
  = ,≡ refl ([]T≡ refl refl (refl {x = ⟦ A ⟧Ty}) (symᴾ (⟦⌜⌝𝒮⟧≡ {δ = δ} refl)))
⟦ ,>rw[] ⟧Ctx~ = {!  !}
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
             {⟦u⟧ : ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧)} 
             {⟦v⟧ : ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧)} 
             {⟦δ⟧ : ⟦Tms⟧ {⟦Φ⟧ = ⟦Φ⟧} ⟦Δ⟧ 
                          (⟦[]C⟧ ⟦Γ⟧ (⟦wk𝒮⟧ {⟦A⟧ = ⟦A⟧} {⟦t⟧ = ⟦t⟧}))} 
             (t≡ : ⟦[]t⟧ ⟦t⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦Γ⟧} (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦wk𝒮⟧) ⟦δ⟧) 
                 ≡ᴾ ⟦TT⟧)
             → ⟦[]t⟧ (⟦call⟧ {⟦u⟧ = ⟦u⟧} {⟦v⟧ = ⟦v⟧}) ⟦δ⟧  
             ≡ᴾ ⟦[]t⟧ ⟦u⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ _}
                      (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ _} (⟦wk𝒮⟧ )) 
                      (⟦,rw⟧ {⟦Γ⟧ = ⟦[]C⟧ ⟦Γ⟧ ⟦wk𝒮⟧} 
                             {⟦t⟧ = ⟦[]t⟧ ⟦t⟧ (⟦⌜⌝𝒮⟧ ⟦wk𝒮⟧)} ⟦δ⟧ t≡))
call-TT≡ {⟦δ⟧ = ⟦δ⟧} t≡ 
  = funextᴾ λ φ → funextᴾ λ ρ → 
      let (φ′ Σ, (f Σ, fTT Σ, fFF)) = ⟦δ⟧ .fst φ
          ρ′ = ⟦δ⟧ .snd ρ
      in unbox (fTT ρ′ (Tm≡-inst t≡))

call-FF≡ : ∀ {⟦t⟧ : ⟦Tm⟧ {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Γ⟧ ⟦𝔹⟧}  {⟦A⟧}
             {⟦u⟧ : ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧)} 
             {⟦v⟧ : ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ _ _) (⟦[]T⟧ ⟦A⟧ ⟦wkrw⟧)} 
             {⟦δ⟧ : ⟦Tms⟧ {⟦Φ⟧ = ⟦Φ⟧} ⟦Δ⟧ 
                          (⟦[]C⟧ ⟦Γ⟧ (⟦wk𝒮⟧ {⟦A⟧ = ⟦A⟧} {⟦t⟧ = ⟦t⟧}))} 
             (t≡ : ⟦[]t⟧ ⟦t⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦Γ⟧} (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦wk𝒮⟧) ⟦δ⟧) 
                 ≡ᴾ ⟦FF⟧)
             → ⟦[]t⟧ (⟦call⟧ {⟦u⟧ = ⟦u⟧} {⟦v⟧ = ⟦v⟧}) ⟦δ⟧  
             ≡ᴾ ⟦[]t⟧ ⟦v⟧ (⟦⨾⟧ {⟦Γ⟧ = ⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ _}
                      (⟦⌜⌝𝒮⟧ {⟦Γ⟧ = ⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ _} (⟦wk𝒮⟧ )) 
                      (⟦,rw⟧ {⟦Γ⟧ = ⟦[]C⟧ ⟦Γ⟧ ⟦wk𝒮⟧} 
                             {⟦t⟧ = ⟦[]t⟧ ⟦t⟧ (⟦⌜⌝𝒮⟧ ⟦wk𝒮⟧)} ⟦δ⟧ t≡))
call-FF≡ {⟦δ⟧ = ⟦δ⟧} t≡ 
  = funextᴾ λ φ → funextᴾ λ ρ → 
      let (φ′ Σ, (f Σ, fTT Σ, fFF)) = ⟦δ⟧ .fst φ
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
⟦ π₂rw {b = true}  δ ⟧Tm~ with ⟦ δ ⟧Tms
... | ⟦δ⟧ = funextᴾ λ φ → funextᴾ λ ρ → ⟦δ⟧ .snd ρ .snd .unbox
⟦ π₂rw {b = false}  δ ⟧Tm~ with ⟦ δ ⟧Tms
... | ⟦δ⟧ = funextᴾ λ φ → funextᴾ λ ρ → ⟦δ⟧ .snd ρ .snd .unbox
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
⟦ ,rw~ δ~           ⟧Tms~ = {!   !}
⟦ id                ⟧Tms~ = {!   !}
⟦ δ~ ⨾ σ~           ⟧Tms~ = {!   !}
⟦ π₁ A~ δ~          ⟧Tms~ = {!   !}
⟦ π₁rw t~ δ~        ⟧Tms~ = {!   !}
⟦ εη                ⟧Tms~ = {!!}
⟦ ,η                ⟧Tms~ = refl
⟦ ,rwη {b = true}   ⟧Tms~ = refl
⟦ ,rwη {b = false}  ⟧Tms~ = refl
⟦ π₁,               ⟧Tms~ = refl
⟦ π₁rw, {b = false} ⟧Tms~ = refl
⟦ π₁rw, {b = true}  ⟧Tms~ = refl
⟦ π₁⨾               ⟧Tms~ = refl
⟦ π₁rw⨾             ⟧Tms~ = refl
⟦ id⨾               ⟧Tms~ = refl
⟦ ⨾id               ⟧Tms~ = refl
⟦ ⨾⨾                ⟧Tms~ = refl
⟦ ,⨾                ⟧Tms~ = refl
⟦ ,rw⨾ {b = true}   ⟧Tms~ = refl
⟦ ,rw⨾ {b = false}  ⟧Tms~ = refl
⟦ wk𝒮               ⟧Tms~ = {!!}
⟦ wk⨾π₁             ⟧Tms~ = {!!}
⟦ wk⨾π₁rw           ⟧Tms~ = {!!}
