{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCBool.Syntax
open import Dependent.SCBool.MutualInd

-- First attempt at "Model.agda". Unfortunately, Agda's termination checker is
-- not happy.
module Dependent.SCBool.ModelOld where

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

⟦_⟧Sortℓ : Sort → Level

⟦ ctx     ⟧Sortℓ = 1ℓ
⟦ ty _    ⟧Sortℓ = 1ℓ
⟦ tm _ _  ⟧Sortℓ = 0ℓ
⟦ tms _ _ ⟧Sortℓ = 0ℓ

⟦_⟧Sort : ∀ 𝒮 → Set ⟦ 𝒮 ⟧Sortℓ

{-# TERMINATING #-}
⟦_⟧_ : Syn 𝒮 → SortMarker 𝒮 → ⟦ 𝒮 ⟧Sort
⟦_⟧Ctx : Ctx → ⟦Ctx⟧
⟦_⟧Ty  : Ty Γ → ⟦Ty⟧ ⟦ Γ ⟧Ctx
⟦_⟧Tm  : Tm Γ A → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
⟦_⟧Tms : Tms Δ Γ → ⟦Tms⟧ ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx

⟦ ctx     ⟧Sort = Set
⟦ ty Γ    ⟧Sort = ⟦Ty⟧ ⟦ Γ ⟧Ctx
⟦ tm Γ A  ⟧Sort = ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
⟦ tms Δ Γ ⟧Sort = ⟦Tms⟧ ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx

⟦_⟧Ctx = ⟦_⟧ CTX
⟦_⟧Ty  = ⟦_⟧ TY
⟦_⟧Tm  = ⟦_⟧ TM
⟦_⟧Tms = ⟦_⟧ TMS

variable
  ρ ρ₁ ρ₂ : ⟦Γ⟧

⟦_⟧Ctx~ : Ctx~ Γ₁ Γ₂ → ⟦ Γ₁ ⟧Ctx ≡ᴾ ⟦ Γ₂ ⟧Ctx
⟦_⟧Ty~  : Ty~ Γ~ A₁ A₂ → ⟦ A₁ ⟧Ty ≡[ congᴾ ⟦Ty⟧ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ A₂ ⟧Ty
⟦_⟧Tm~  : Tm~ Γ~ A~ t₁ t₂ 
         → ⟦ t₁ ⟧Tm ≡[ Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ]≡ᴾ ⟦ t₂ ⟧Tm
⟦_⟧Tms~ : Tms~ Δ~ Γ~ δ₁ δ₂ 
         → ⟦ δ₁ ⟧Tms ≡[ Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~ ]≡ᴾ ⟦ δ₂ ⟧Tms

⟦𝔹⟧′ : ⟦ 𝔹 {Γ = Γ} ⟧Ty ≡ᴾ λ ρ → Bool 

Ty≡-inst : ⟦A₁⟧ ≡ᴾ ⟦A₂⟧ → ⟦A₁⟧ ρ ≡ᴾ ⟦A₂⟧ ρ
Ty≡-inst refl = refl

Tm≡-inst : ⟦t₁⟧ ≡ᴾ ⟦t₂⟧ → ⟦t₁⟧ ρ ≡ᴾ ⟦t₂⟧ ρ
Tm≡-inst refl = refl

Tm[]≡-inst : ∀ {ρ : ⟦ Γ ⟧Ctx} (A≡ : ⟦A₁⟧ ≡ᴾ ⟦A₂⟧) → ⟦t₁⟧ ≡[ Tm≡ refl A≡ ]≡ᴾ ⟦t₂⟧ 
           → ⟦t₁⟧ ρ ≡[ Ty≡-inst A≡ ]≡ᴾ ⟦t₂⟧ ρ
Tm[]≡-inst refl refl = refl

⟦ ε     ⟧ CTX = ⊤
⟦ Γ , A ⟧ CTX = Σ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty

⟦ 𝔹 ⟧ TY = λ ρ → Bool

⟦ Γ , t >rw b ⟧ CTX = Σ ⟦ Γ ⟧Ctx (λ ρ → Box (⟦ t ⟧Tm ρ ≡ᴾ b))

⟦ coe~ Γ~ A ⟧ TY = coeᴾ (Ty≡ ⟦ Γ~ ⟧Ctx~) ⟦ A ⟧Ty
⟦ Π A B     ⟧ TY = λ ρ → ∀ x → ⟦ B ⟧Ty (ρ Σ, x)
⟦ A [ δ ]   ⟧ TY = λ ρ → ⟦ A ⟧Ty (⟦ δ ⟧Tms ρ)
⟦ if t A B  ⟧ TY = λ ρ → Bool-rec (⟦ t ⟧Tm ρ) (⟦ A ⟧Ty ρ) (⟦ B ⟧Ty ρ)

⟦ coe~ Γ~ A~ t ⟧ TM = coeᴾ (Tm≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~) ⟦ t ⟧Tm

⟦ ƛ t     ⟧ TM = λ ρ        x → ⟦ t ⟧Tm (ρ Σ, x)
⟦ ƛ⁻¹ t   ⟧ TM = λ (ρ Σ, x)   → ⟦ t ⟧Tm ρ x
⟦ TT      ⟧ TM = λ ρ          → true
⟦ FF      ⟧ TM = λ ρ          → false
⟦ t [ δ ] ⟧ TM = λ ρ          → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ)

⟦ π₁ δ  ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ .fst

⟦ π₂ δ  ⟧ TM = λ ρ → ⟦ δ ⟧Tms ρ .snd

⟦ id     ⟧ TMS = λ ρ → ρ
⟦ π₁rw δ ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ .fst

⟦ if t u v ⟧ TM = λ ρ → Bool-splitᴾ (⟦ t ⟧Tm ρ) (λ t~ → ⟦ u ⟧Tm (ρ Σ, box t~)) 
                                                (λ t~ → ⟦ v ⟧Tm (ρ Σ, box t~))
                                          
⟦ coe~ Δ~ Γ~ δ ⟧ TMS = coeᴾ (Tms≡ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~) ⟦ δ ⟧Tms
⟦ ε            ⟧ TMS = λ ρ → tt
⟦ δ , t        ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ

⟦ ,rwℱ {b = true} δ refl t~ ⟧ TMS 
  = λ ρ → ⟦ δ ⟧Tms ρ Σ, box (Tm≡-inst ⟦ t~ ⟧Tm~)
⟦ ,rwℱ {b = false} δ refl t~ ⟧ TMS 
  = λ ρ → ⟦ δ ⟧Tms ρ Σ, box (Tm≡-inst ⟦ t~ ⟧Tm~)
⟦ δ ⨾ σ ⟧ TMS = λ ρ → ⟦ δ ⟧Tms (⟦ σ ⟧Tms ρ)
  
⟦𝔹⟧′ = refl

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

⟦ 𝔹[]  ⟧Ty~ = refl
⟦ [][] ⟧Ty~ = refl
⟦ [id] ⟧Ty~ = refl

⟦ rfl~               ⟧Tm~ = refl
⟦ sym~ t~            ⟧Tm~ = sym[]ᴾ ⟦ t~ ⟧Tm~
⟦ t₁₂~ ∙~ t₂₃~       ⟧Tm~ = ⟦ t₁₂~ ⟧Tm~ ∙[]ᴾ ⟦ t₂₃~ ⟧Tm~
⟦ coh                ⟧Tm~ = coh[]ᴾ
⟦ TT Γ~              ⟧Tm~ = TT≡ ⟦ Γ~ ⟧Ctx~
⟦ FF Γ~              ⟧Tm~ = FF≡ ⟦ Γ~ ⟧Ctx~

⟦ if {Γ~ = Γ~} {A~ = A~} t~ u~ v~ ⟧Tm~ 
  = if≡ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ⟦ t~ ⟧Tm~ ⟦ u~ ⟧Tm~ ⟦ v~ ⟧Tm~

⟦ t~ [ δ~ ]          ⟧Tm~ = {!   !}
⟦ π₂rw {b = true}  δ ⟧Tm~ = funextᴾ (λ ρ → ⟦ δ ⟧Tms ρ .snd .unbox)
⟦ π₂rw {b = false} δ ⟧Tm~ = funextᴾ (λ ρ → ⟦ δ ⟧Tms ρ .snd .unbox)
⟦ TT[]               ⟧Tm~ = refl
⟦ FF[]               ⟧Tm~ = refl
⟦ [id]               ⟧Tm~ = refl
⟦ [][]               ⟧Tm~ = refl
⟦ ifTT               ⟧Tm~ = refl
⟦ ifFF               ⟧Tm~ = refl
⟦ π₂⨾                ⟧Tm~ = refl

⟦ rfl~              ⟧Tms~ = refl
⟦ sym~ δ~           ⟧Tms~ = sym[]ᴾ ⟦ δ~ ⟧Tms~
⟦ δ₁₂~ ∙~ δ₂₃~      ⟧Tms~ = ⟦ δ₁₂~ ⟧Tms~ ∙[]ᴾ ⟦ δ₂₃~ ⟧Tms~
⟦ coh               ⟧Tms~ = coh[]ᴾ
⟦ δ~ , t~           ⟧Tms~ = {!   !}
⟦ ,rw~ δ~           ⟧Tms~ = {!   !}
⟦ id                ⟧Tms~ = {!   !}
⟦ δ~ ⨾ σ~           ⟧Tms~ = {!   !}
⟦ π₁rw t~ δ~        ⟧Tms~ = {!   !}
⟦ εη                ⟧Tms~ = refl
⟦ ,η                ⟧Tms~ = refl
⟦ πrwη {b = true}   ⟧Tms~ = refl
⟦ πrwη {b = false}  ⟧Tms~ = refl
⟦ π₁rw, {b = false} ⟧Tms~ = refl
⟦ π₁rw, {b = true}  ⟧Tms~ = refl
⟦ π₁⨾               ⟧Tms~ = refl
⟦ π₁rw⨾             ⟧Tms~ = refl
⟦ id⨾               ⟧Tms~ = refl
⟦ ⨾id               ⟧Tms~ = refl
⟦ ,⨾                ⟧Tms~ = refl
⟦ ,rw⨾ {b = true}   ⟧Tms~ = refl
⟦ ,rw⨾ {b = false}  ⟧Tms~ = refl
