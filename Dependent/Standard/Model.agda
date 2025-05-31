{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Utils
open import Utils.IdExtras

open import Dependent.Standard.Syntax

module Dependent.Standard.Model where

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

𝔹≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) → ⟦𝔹⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦𝔹⟧
𝔹≡ refl = refl

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

⟦<>⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ → ⟦Tms⟧ ⟦Γ⟧ (⟦,⟧ ⟦Γ⟧ ⟦A⟧)
⟦<>⟧ ⟦t⟧ = λ ρ → ρ Σ, ⟦t⟧ ρ

⟦if⟧ : ∀ (⟦A⟧ : ⟦Ty⟧ (⟦,⟧ ⟦Γ⟧ ⟦𝔹⟧)) (⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦𝔹⟧) 
     → ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦A⟧ (⟦<>⟧ ⟦TT⟧))
     → ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦A⟧ (⟦<>⟧ ⟦FF⟧))
     → ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦A⟧ (⟦<>⟧ ⟦t⟧))
⟦if⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧ ⟦v⟧ 
  = λ ρ → Bool-elim (λ b → ⟦A⟧ (ρ Σ, b)) (⟦t⟧ ρ) (⟦u⟧ ρ) (⟦v⟧ ρ)

-- if≡ : ∀ (Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧) (A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧) 
--         (t≡ : ⟦t₁⟧ ≡[ Tm≡ Γ≡ (𝔹≡ Γ≡) ]≡ᴾ ⟦t₂⟧)
--     → ⟦u₁⟧ ≡[ Tm≡ (,>rw≡ Γ≡ t≡) ([]T≡ Γ≡ (,>rw≡ Γ≡ t≡) A≡ (wkrw≡ Γ≡ t≡)) 
--            ]≡ᴾ ⟦u₂⟧
--     → ⟦v₁⟧ ≡[ Tm≡ (,>rw≡ Γ≡ t≡) ([]T≡ Γ≡ (,>rw≡ Γ≡ t≡) A≡ (wkrw≡ Γ≡ t≡)) 
--            ]≡ᴾ ⟦v₂⟧
--     → ⟦if⟧ ⟦t₁⟧ ⟦u₁⟧ ⟦v₁⟧ ≡[ Tm≡ Γ≡ A≡ ]≡ᴾ ⟦if⟧ ⟦t₂⟧ ⟦u₂⟧ ⟦v₂⟧
-- if≡ refl refl refl refl refl = refl

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

⟦ ε     ⟧Ctx = ⊤
⟦ Γ , A ⟧Ctx = Σ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty

⟦ coe~ Γ~ A ⟧Ty = coeᴾ (Ty≡ ⟦ Γ~ ⟧Ctx~) ⟦ A ⟧Ty
⟦ 𝔹         ⟧Ty = λ ρ → Bool
⟦ Π A B     ⟧Ty = λ ρ → ∀ uⱽ → ⟦ B ⟧Ty (ρ Σ, uⱽ)
⟦ A [ δ ]   ⟧Ty = λ ρ → ⟦ A ⟧Ty (⟦ δ ⟧Tms ρ)
⟦ if t A B  ⟧Ty = λ ρ → Bool-rec (⟦ t ⟧Tm ρ) (⟦ A ⟧Ty ρ) (⟦ B ⟧Ty ρ)

⟦ coe~ Δ~ Γ~ δ ⟧Tms = coeᴾ (Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~) ⟦ δ ⟧Tms

⟦ π₁ δ  ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ .fst
⟦ id    ⟧Tms = λ ρ → ρ                            
⟦ ε     ⟧Tms = λ ρ → tt
⟦ δ , t ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ
⟦ δ ⨾ σ ⟧Tms = λ ρ → ⟦ δ ⟧Tms (⟦ σ ⟧Tms ρ)

⟦ coe~ Γ~ A~ t ⟧Tm = coeᴾ (Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~) ⟦ t ⟧Tm

⟦ ƛ t     ⟧Tm = λ ρ         uⱽ → ⟦ t ⟧Tm (ρ Σ, uⱽ)
⟦ ƛ⁻¹ t   ⟧Tm = λ (ρ Σ, uⱽ)    → ⟦ t ⟧Tm ρ uⱽ
⟦ TT      ⟧Tm = λ ρ            → true
⟦ FF      ⟧Tm = λ ρ            → false
⟦ t [ δ ] ⟧Tm = λ ρ            → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ)
⟦ π₂ δ    ⟧Tm = λ ρ → ⟦ δ ⟧Tms ρ .snd
⟦ if A t u v ⟧Tm 
  = λ ρ → Bool-elim (λ b → ⟦ A ⟧Ty (ρ Σ, b)) (⟦ t ⟧Tm ρ) (⟦ u ⟧Tm ρ) (⟦ v ⟧Tm ρ)

⟦ rfl~         ⟧Ctx~ = refl
⟦ sym~ Γ~      ⟧Ctx~ = symᴾ ⟦ Γ~ ⟧Ctx~
⟦ Γ₁₂~ ∙~ Γ₂₃~ ⟧Ctx~ = ⟦ Γ₁₂~ ⟧Ctx~ ∙ᴾ ⟦ Γ₂₃~ ⟧Ctx~
⟦ Γ~ , A~      ⟧Ctx~ = ,≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~

⟦ rfl~              ⟧Ty~ = refl
⟦ sym~ A~           ⟧Ty~ = sym[]ᴾ ⟦ A~ ⟧Ty~
⟦ A₁₂~ ∙~ A₂₃~      ⟧Ty~ = ⟦ A₁₂~ ⟧Ty~ ∙[]ᴾ ⟦ A₂₃~ ⟧Ty~
⟦ coh               ⟧Ty~ = coh[]ᴾ
⟦ 𝔹 {Γ~ = Γ~}       ⟧Ty~ = 𝔹≡ ⟦ Γ~ ⟧Ctx~
⟦ Π {Γ~ = Γ~} A~ B~ ⟧Ty~ = Π≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ B~ ⟧Ty~
⟦ _[_] {Γ~ = Γ~} {Δ~ = Δ~} A~ δ~ ⟧Ty~ 
  = []T≡ ⟦ Γ~ ⟧Ctx~ ⟦ Δ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ (⟦ δ~ ⟧Tms~)
⟦ if t~ A~ B~ ⟧Ty~ = {!   !}

⟦ ifTT ⟧Ty~ = refl
⟦ ifFF ⟧Ty~ = refl
⟦ Π[]  ⟧Ty~ = refl
⟦ if[] ⟧Ty~ = refl
⟦ 𝔹[]  ⟧Ty~ = refl
⟦ [][] ⟧Ty~ = refl
⟦ [id] ⟧Ty~ = refl

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
⟦ if {Γ~ = Γ~} A~ t~ u~ v~  ⟧Tm~ 
  = {!!}
⟦ t~ [ δ~ ]    ⟧Tm~ = {!   !}
⟦ TT[] ⟧Tm~ = refl
⟦ FF[] ⟧Tm~ = refl
⟦ ƛ[]  ⟧Tm~ = refl
⟦ if[] ⟧Tm~ = refl
⟦ [id] ⟧Tm~ = refl
⟦ [][] ⟧Tm~ = refl
⟦ ifTT ⟧Tm~ = refl
⟦ ifFF ⟧Tm~ = refl
⟦ β    ⟧Tm~ = refl
⟦ η    ⟧Tm~ = refl
⟦ π₂,  ⟧Tm~ = refl
⟦ π₂⨾  ⟧Tm~ = refl

cohTm {Γ≡ = refl} {A≡ = refl} = refl

⟦ rfl~              ⟧Tms~ = refl
⟦ sym~ δ~           ⟧Tms~ = sym[]ᴾ ⟦ δ~ ⟧Tms~
⟦ δ₁₂~ ∙~ δ₂₃~      ⟧Tms~ = ⟦ δ₁₂~ ⟧Tms~ ∙[]ᴾ ⟦ δ₂₃~ ⟧Tms~
⟦ coh               ⟧Tms~ = coh[]ᴾ
⟦ ε                 ⟧Tms~ = {!   !}
⟦ δ~ , t~           ⟧Tms~ = {!   !}
⟦ id                ⟧Tms~ = {!   !}
⟦ δ~ ⨾ σ~           ⟧Tms~ = {!   !}
⟦ π₁ A~ δ~          ⟧Tms~ = {!   !}
⟦ εη  ⟧Tms~ = refl
⟦ ,η  ⟧Tms~ = refl
⟦ π₁, ⟧Tms~ = refl
⟦ π₁⨾ ⟧Tms~ = refl
⟦ id⨾ ⟧Tms~ = refl
⟦ ⨾id ⟧Tms~ = refl
⟦ ⨾⨾  ⟧Tms~ = refl
⟦ ,⨾  ⟧Tms~ = refl
