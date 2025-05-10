{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCBool.Syntax

-- Like "ModelOld.agda" but without asserting termination.
--
-- To achieve this, we use some trickery with forward references, with-clauses 
-- and specialising helpers, which makes unfortunately the definitions a bit 
-- clunkier in places.
module Dependent.SCBool.Model where

⟦Ctx⟧ : Set₁
⟦Ctx⟧ = Set

⟦Ty⟧ : ⟦Ctx⟧ → Set₁
⟦Ty⟧ Γ = Γ → Set

⟦Tm⟧ : ∀ Γ → ⟦Ty⟧ Γ → Set
⟦Tm⟧ Γ A = ∀ ρ → A ρ

⟦Tms⟧ : ⟦Ctx⟧ → ⟦Ctx⟧ → Set
⟦Tms⟧ Δ Γ = Δ → Γ

variable
  ⟦Γ⟧ ⟦Δ⟧ ⟦Γ₁⟧ ⟦Γ₂⟧ ⟦Δ₁⟧ ⟦Δ₂⟧   : ⟦Ctx⟧
  ⟦A⟧ ⟦B⟧ ⟦A₁⟧ ⟦A₂⟧ ⟦B₁⟧ ⟦B₂⟧   : ⟦Ty⟧ ⟦Γ⟧ 
  ⟦t⟧ ⟦t₁⟧ ⟦t₂⟧ ⟦u₁⟧ ⟦u₂⟧ ⟦v₁⟧ ⟦v₂⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧
  ⟦δ₁⟧ ⟦δ₂⟧                     : ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧

Ty≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧ → ⟦Ty⟧ ⟦Γ₁⟧ ≡ᴾ ⟦Ty⟧ ⟦Γ₂⟧
Ty≡ refl = refl

Tm≡ : ∀ Γ≡ → ∀ (A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧) 
    → ⟦Tm⟧ ⟦Γ₁⟧ ⟦A₁⟧ ≡ᴾ ⟦Tm⟧ ⟦Γ₂⟧ ⟦A₂⟧
Tm≡ refl refl = refl

Tms≡ : ⟦Δ₁⟧ ≡ᴾ ⟦Δ₂⟧ → ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧ → ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧ ≡ᴾ ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧
Tms≡ refl refl = refl

variable
  Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧
  A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧


⟦,⟧ = Σ

,≡ : ∀ Γ≡ → ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧ → ⟦,⟧ ⟦Γ₁⟧ ⟦A₁⟧ ≡ᴾ ⟦,⟧ ⟦Γ₂⟧ ⟦A₂⟧ 
,≡ refl refl = refl

⟦Π⟧ : ∀ ⟦A⟧ → ⟦Ty⟧ (⟦,⟧ ⟦Γ⟧ ⟦A⟧) → ⟦Ty⟧ ⟦Γ⟧
⟦Π⟧ ⟦A⟧ ⟦B⟧ = λ ρ → ∀ x → ⟦B⟧ (ρ Σ, x)

⟦𝔹⟧ : ⟦Ty⟧ ⟦Γ⟧
⟦𝔹⟧ = λ _ → Bool

⟦,>rw⟧ : ∀ ⟦Γ⟧ → ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧ → Bool → ⟦Ctx⟧
⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ b = Σ ⟦Γ⟧ (λ ρ → Box (⟦t⟧ ρ ≡ᴾ b))

𝔹≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦𝔹⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦𝔹⟧
𝔹≡ refl = refl

,>rw≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧ 
      → ⟦,>rw⟧ ⟦Γ₁⟧ ⟦t₁⟧ b ≡ᴾ ⟦,>rw⟧ ⟦Γ₂⟧ ⟦t₂⟧ b
,>rw≡ refl refl = refl

Π≡ : ∀ Γ≡ A≡ → ⟦B₁⟧ ≡[ Ty≡ (,≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧
     → ⟦Π⟧ ⟦A₁⟧ ⟦B₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦Π⟧ ⟦A₂⟧ ⟦B₂⟧
Π≡ refl refl refl = refl

⟦TT⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧
⟦TT⟧ _ = true

TT≡ : (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦TT⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦TT⟧ 
TT≡ refl = refl

⟦FF⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧
⟦FF⟧ _ = false

FF≡ : (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦FF⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦FF⟧ 
FF≡ refl = refl

⟦ƛ⟧ : ⟦Tm⟧ (⟦,⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧ → ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧)
⟦ƛ⟧ ⟦t⟧ ρ ⟦u⟧ = ⟦t⟧ (ρ Σ, ⟦u⟧)

-- TODO: Agda ICEs with "IMPOSSIBLE" here if we remove explicit quantification 
-- over |{⟦B₂⟧ ⟦t₂⟧}|!
ƛ≡ : ∀ {⟦B₂⟧ ⟦t₂⟧} (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧)
     (B≡ : ⟦B₁⟧ ≡[ Ty≡ (,≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧)
   → ⟦t₁⟧ ≡[ Tm≡ (,≡ Γ≡ A≡) B≡ ]≡ᴾ ⟦t₂⟧
   → ⟦ƛ⟧ ⟦t₁⟧ ≡[ Tm≡ Γ≡ (Π≡ Γ≡ A≡ B≡) ]≡ᴾ ⟦ƛ⟧ ⟦t₂⟧
ƛ≡ refl refl refl refl = refl

⟦ƛ⁻¹⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧) → ⟦Tm⟧ (⟦,⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧
⟦ƛ⁻¹⟧ ⟦t⟧ (ρ Σ, ⟦u⟧) = ⟦t⟧ ρ ⟦u⟧

ƛ⁻¹≡ : ∀ {⟦B₂⟧ ⟦t₂⟧} (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧)
     (B≡ : ⟦B₁⟧ ≡[ Ty≡ (,≡ Γ≡ A≡) ]≡ᴾ ⟦B₂⟧)
   → ⟦t₁⟧ ≡[ Tm≡ Γ≡ (Π≡ Γ≡ A≡ B≡) ]≡ᴾ ⟦t₂⟧
   → ⟦ƛ⁻¹⟧ ⟦t₁⟧ ≡[ Tm≡ (,≡ Γ≡ A≡) B≡ ]≡ᴾ ⟦ƛ⁻¹⟧ ⟦t₂⟧
ƛ⁻¹≡ refl refl refl refl = refl

⟦[]T⟧ : ⟦Ty⟧ ⟦Γ⟧ → ⟦Tms⟧ ⟦Δ⟧ ⟦Γ⟧ → ⟦Ty⟧ ⟦Δ⟧
⟦[]T⟧ ⟦A⟧ ⟦δ⟧ ρ = ⟦A⟧ (⟦δ⟧ ρ)

[]T≡ : ∀ Γ≡ Δ≡ → ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧ → ⟦δ₁⟧ ≡[ Tms≡ Δ≡ Γ≡ ]≡ᴾ ⟦δ₂⟧
     → ⟦[]T⟧ ⟦A₁⟧ ⟦δ₁⟧ ≡[ Ty≡ Δ≡ ]≡ᴾ ⟦[]T⟧ ⟦A₂⟧ ⟦δ₂⟧
[]T≡ refl refl refl refl = refl

⟦π₁rw⟧ : ⟦Tms⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ b) ⟦Γ⟧
⟦π₁rw⟧ = fst

π₁rw≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (t≡ : ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧) 
      → ⟦π₁rw⟧ ≡[ Tms≡ (,>rw≡ {b = b} Γ≡ t≡) Γ≡ ]≡ᴾ ⟦π₁rw⟧
π₁rw≡ refl refl = refl

⟦if⟧ : ∀ ⟦t⟧ 
     → ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ true)  (⟦[]T⟧ ⟦A⟧ ⟦π₁rw⟧)
     → ⟦Tm⟧ (⟦,>rw⟧ ⟦Γ⟧ ⟦t⟧ false) (⟦[]T⟧ ⟦A⟧ ⟦π₁rw⟧)
     → ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧
⟦if⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ = λ ρ → Bool-splitᴾ (⟦t⟧ ρ) (λ t~ → ⟦u⟧ (ρ Σ, box t~)) 
                                             (λ t~ → ⟦v⟧ (ρ Σ, box t~))

if≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧) 
        (t≡ : ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧)
    → ⟦u₁⟧ ≡[ Tm≡ (,>rw≡ Γ≡ t≡) ([]T≡ Γ≡ (,>rw≡ Γ≡ t≡) A≡ (π₁rw≡ Γ≡ t≡)) 
           ]≡ᴾ ⟦u₂⟧
    → ⟦v₁⟧ ≡[ Tm≡ (,>rw≡ Γ≡ t≡) ([]T≡ Γ≡ (,>rw≡ Γ≡ t≡) A≡ (π₁rw≡ Γ≡ t≡)) 
           ]≡ᴾ ⟦v₂⟧
    → ⟦if⟧ ⟦t₁⟧ ⟦u₁⟧ ⟦v₁⟧ ≡[ Tm≡ Γ≡ A≡ ]≡ᴾ ⟦if⟧ ⟦t₂⟧ ⟦u₂⟧ ⟦v₂⟧
if≡ refl refl refl refl refl = refl

⟦_⟧Ctx : Ctx → ⟦Ctx⟧
⟦_⟧Ty  : Ty Γ → ⟦Ty⟧ ⟦ Γ ⟧Ctx
⟦_⟧Tm  : Tm Γ A → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
⟦_⟧Tms : Tms Δ Γ → ⟦Tms⟧ ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx

variable
  ρ ρ₁ ρ₂ : ⟦Γ⟧

⟦_⟧Ctx~ : Ctx~ Γ₁ Γ₂ → ⟦ Γ₁ ⟧Ctx ≡ᴾ ⟦ Γ₂ ⟧Ctx
⟦_⟧Ty~  : Ty~ Γ~ A₁ A₂ → ⟦ A₁ ⟧Ty ≡[ congᴾ ⟦Ty⟧ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ A₂ ⟧Ty
⟦_⟧Tm~ : Tm~ Γ~ A~ t₁ t₂ 
        → ⟦ t₁ ⟧Tm ≡[ Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ]≡ᴾ ⟦ t₂ ⟧Tm
⟦_⟧Tms~ : Tms~ Δ~ Γ~ δ₁ δ₂ 
         → ⟦ δ₁ ⟧Tms ≡[ Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ δ₂ ⟧Tms

⟦𝔹⟧′ : ⟦ 𝔹 {Γ = Γ} ⟧Ty ≡ᴾ λ ρ → Bool 
⌜⌝𝔹≡ : ⟦ ⌜ b ⌝𝔹 ⟧Tm ≡[ Tm≡ (refl {x = ⟦ Γ ⟧Ctx}) ⟦𝔹⟧′ ]≡ᴾ λ ρ → b


Ty≡-inst : ⟦A₁⟧ ≡ᴾ ⟦A₂⟧ → ⟦A₁⟧ ρ ≡ᴾ ⟦A₂⟧ ρ
Ty≡-inst refl = refl

Tm≡-inst : ⟦t₁⟧ ≡ᴾ ⟦t₂⟧ → ⟦t₁⟧ ρ ≡ᴾ ⟦t₂⟧ ρ
Tm≡-inst refl = refl

Tm[]≡-inst : ∀ {ρ : ⟦ Γ ⟧Ctx} (A≡ : ⟦A₁⟧ ≡ᴾ ⟦A₂⟧) → ⟦t₁⟧ ≡[ Tm≡ refl A≡ ]≡ᴾ ⟦t₂⟧ 
           → ⟦t₁⟧ ρ ≡[ Ty≡-inst A≡ ]≡ᴾ ⟦t₂⟧ ρ
Tm[]≡-inst refl refl = refl


⟦ ε     ⟧Ctx = ⊤
⟦ Γ , A ⟧Ctx = Σ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty

⟦ Γ , t >rw b ⟧Ctx = Σ ⟦ Γ ⟧Ctx (λ ρ → Box (⟦ t ⟧Tm ρ ≡[ Ty≡-inst ⟦𝔹⟧′ ]≡ᴾ b))

⟦ 𝔹 ⟧Ty = λ ρ → Bool
⟦ coe~ Γ~ A ⟧Ty = coeᴾ (Ty≡ ⟦ Γ~ ⟧Ctx~) ⟦ A ⟧Ty
⟦ Π A B     ⟧Ty = λ ρ → ∀ x → ⟦ B ⟧Ty (ρ Σ, x)
⟦ A [ δ ]   ⟧Ty = λ ρ → ⟦ A ⟧Ty (⟦ δ ⟧Tms ρ)
⟦ if t A B  ⟧Ty = λ ρ → Bool-rec (⟦ t ⟧Tm ρ) (⟦ A ⟧Ty ρ) (⟦ B ⟧Ty ρ)


⟦TT⟧′ : ⟦ TT {Γ = Γ} ⟧Tm ≡ᴾ λ ρ → true
⟦FF⟧′ : ⟦ FF {Γ = Γ} ⟧Tm ≡ᴾ λ ρ → false
⟦[]⟧′ : ⟦ t [ δ ] ⟧Tm ≡ᴾ λ ρ → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ)

⟦ π₁ δ  ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ .fst


⟦ id     ⟧Tms = λ ρ → ρ
⟦ π₁rw δ ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ .fst                             
⟦ coe~ Δ~ Γ~ δ ⟧Tms = coeᴾ (Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~) ⟦ δ ⟧Tms
⟦ ε            ⟧Tms = λ ρ → tt
⟦ δ , t        ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ

⟦ ,rwℱ {b = true} δ refl t~ ⟧Tms 
  with symᴾ (⟦[]⟧′ {δ = δ}) ∙ᴾ ⟦ t~ ⟧Tm~ ∙ᴾ ⟦TT⟧′
... | eq = λ ρ → ⟦ δ ⟧Tms ρ Σ, box (Tm≡-inst eq)
⟦ ,rwℱ {b = false} δ refl t~ ⟧Tms 
  with symᴾ (⟦[]⟧′ {δ = δ}) ∙ᴾ ⟦ t~ ⟧Tm~ ∙ᴾ ⟦FF⟧′
... | eq = λ ρ → ⟦ δ ⟧Tms ρ Σ,  box (Tm≡-inst eq)

⟦ δ ⨾ σ ⟧Tms = λ ρ → ⟦ δ ⟧Tms (⟦ σ ⟧Tms ρ)

⟦ coe~ Γ~ A~ t ⟧Tm = coeᴾ (Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~) ⟦ t ⟧Tm

⟦ ƛ t     ⟧Tm = λ ρ        x → ⟦ t ⟧Tm (ρ Σ, x)
⟦ ƛ⁻¹ t   ⟧Tm = λ (ρ Σ, x)   → ⟦ t ⟧Tm ρ x
⟦ TT      ⟧Tm = λ ρ          → true
⟦ FF      ⟧Tm = λ ρ          → false
⟦ t [ δ ] ⟧Tm = λ ρ          → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ)
⟦ π₂ δ  ⟧Tm = λ ρ → ⟦ δ ⟧Tms ρ .snd
⟦ if t u v ⟧Tm = λ ρ → Bool-splitᴾ (⟦ t ⟧Tm ρ) (λ t~ → ⟦ u ⟧Tm (ρ Σ, box t~)) 
                                               (λ t~ → ⟦ v ⟧Tm (ρ Σ, box t~))
⟦TT⟧′ = refl
⟦FF⟧′ = refl
⟦[]⟧′ = refl

⟦𝔹⟧′ = refl

⌜⌝𝔹≡ {b = false} = refl
⌜⌝𝔹≡ {b = true}  = refl

⟦ rfl~         ⟧Ctx~ = refl
⟦ sym~ Γ~      ⟧Ctx~ = symᴾ ⟦ Γ~ ⟧Ctx~
⟦ Γ₁₂~ ∙~ Γ₂₃~ ⟧Ctx~ = ⟦ Γ₁₂~ ⟧Ctx~ ∙ᴾ ⟦ Γ₂₃~ ⟧Ctx~
⟦ Γ~ , A~      ⟧Ctx~ = ,≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~
⟦ Γ~ , t~ >rw  ⟧Ctx~ = ,>rw≡ ⟦ Γ~ ⟧Ctx~ ⟦ t~ ⟧Tm~

⟦ rfl~              ⟧Ty~ = refl
⟦ sym~ A~           ⟧Ty~ = sym[]ᴾ ⟦ A~ ⟧Ty~
⟦ A₁₂~ ∙~ A₂₃~      ⟧Ty~ = ⟦ A₁₂~ ⟧Ty~ ∙[]ᴾ ⟦ A₂₃~ ⟧Ty~
⟦ coh               ⟧Ty~ = coh[]ᴾ
⟦ 𝔹 {Γ~ = Γ~}       ⟧Ty~ = 𝔹≡ ⟦ Γ~ ⟧Ctx~
⟦ Π {Γ~ = Γ~} A~ B~ ⟧Ty~ = Π≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ B~ ⟧Ty~
⟦ _[_] {Γ~ = Γ~} {Δ~ = Δ~} A~ δ~ ⟧Ty~ 
  = []T≡ ⟦ Γ~ ⟧Ctx~ ⟦ Δ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ (⟦ δ~ ⟧Tms~)
⟦ if t~ A~ B~ ⟧Ty~ = {!   !}

⟦ ifTT              ⟧Ty~ = refl
⟦ ifFF              ⟧Ty~ = refl
⟦ Π[]               ⟧Ty~ = refl
⟦ if[]              ⟧Ty~ = refl
⟦ 𝔹[]               ⟧Ty~ = refl
⟦ [][]              ⟧Ty~ = refl
⟦ [id]              ⟧Ty~ = refl

-- Specialisation of |coh[]ᴾ| to assist with termination
cohTm : ∀ {⟦t⟧ : ⟦Tm⟧ ⟦Γ₁⟧ ⟦A₁⟧} {Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧} 
          {A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧} 
      → ⟦t⟧ ≡[ Tm≡ Γ≡ A≡ ]≡ᴾ coeᴾ (Tm≡ Γ≡ A≡) ⟦t⟧

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
⟦ if {Γ~ = Γ~} {A~ = A~} t~ u~ v~  ⟧Tm~ 
  = if≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ t~ ⟧Tm~ ⟦ u~ ⟧Tm~ ⟦ v~ ⟧Tm~
⟦ t~ [ δ~ ]    ⟧Tm~ = {!   !}
⟦ π₂rw {b = true}  δ ⟧Tm~ with ⟦ δ ⟧Tms
... | ⟦δ⟧ = funextᴾ (λ ρ → ⟦δ⟧ ρ .snd .unbox)
⟦ π₂rw {b = false} δ ⟧Tm~ with ⟦ δ ⟧Tms
... | ⟦δ⟧ = funextᴾ (λ ρ → ⟦δ⟧ ρ .snd .unbox)
⟦ TT[]               ⟧Tm~ = refl
⟦ FF[]               ⟧Tm~ = refl
⟦ ƛ[]                ⟧Tm~ = refl
⟦ if[]               ⟧Tm~ = refl
⟦ [id]               ⟧Tm~ = refl
⟦ [][]               ⟧Tm~ = refl
⟦ ifTT               ⟧Tm~ = refl
⟦ ifFF               ⟧Tm~ = refl
⟦ β                  ⟧Tm~ = refl
⟦ η                  ⟧Tm~ = refl
⟦ π₂,                ⟧Tm~ = refl
⟦ π₂⨾                ⟧Tm~ = refl

cohTm {Γ≡ = refl} {A≡ = refl} = refl

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
⟦ εη                ⟧Tms~ = refl
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
 