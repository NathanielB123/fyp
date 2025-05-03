{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCBool.Syntax
open import Dependent.SCBool.MutualInd

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
  ⟦Γ⟧ ⟦Γ₁⟧ ⟦Γ₂⟧ ⟦Δ₁⟧ ⟦Δ₂⟧ : ⟦Ctx⟧
  ⟦A⟧ ⟦B⟧ ⟦A₁⟧ ⟦A₂⟧ ⟦B₁⟧ ⟦B₂⟧ : ⟦Ty⟧ ⟦Γ⟧ 
  ⟦t₁⟧ ⟦t₂⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧

  Γ≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧


Ty≡ : ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧ → ⟦Ty⟧ ⟦Γ₁⟧ ≡ᴾ ⟦Ty⟧ ⟦Γ₂⟧
Ty≡ refl = refl

Tm≡ : ∀ Γ≡ → ∀ (A≡ : ⟦A₁⟧ ≡[ Ty≡ Γ≡ ]≡ᴾ ⟦A₂⟧) 
    → ⟦Tm⟧ ⟦Γ₁⟧ ⟦A₁⟧ ≡ᴾ ⟦Tm⟧ ⟦Γ₂⟧ ⟦A₂⟧
Tm≡ refl refl = refl

Tms≡ : ⟦Δ₁⟧ ≡ᴾ ⟦Δ₂⟧ → ⟦Γ₁⟧ ≡ᴾ ⟦Γ₂⟧ → ⟦Tms⟧ ⟦Δ₁⟧ ⟦Γ₁⟧ ≡ᴾ ⟦Tms⟧ ⟦Δ₂⟧ ⟦Γ₂⟧
Tms≡ refl refl = refl

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



⟦_⟧Sortℓ : Sort → Level

⟦ ctx     ⟧Sortℓ = 1ℓ
⟦ ty _    ⟧Sortℓ = 1ℓ
⟦ tm _ _  ⟧Sortℓ = 0ℓ
⟦ tms _ _ ⟧Sortℓ = 0ℓ

⟦_⟧Sort : ∀ 𝒮 → Set ⟦ 𝒮 ⟧Sortℓ

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

-- {-# INLINE ⟦_⟧Ctx #-}
-- {-# INLINE ⟦_⟧Ty #-}
-- {-# INLINE ⟦_⟧Tm #-}
-- {-# INLINE ⟦_⟧Tms #-}

variable
  ρ ρ₁ ρ₂ : ⟦ Γ ⟧Ctx

⟦_⟧Ctx~ᴾ : Ctx~ Γ₁ Γ₂ → ⟦ Γ₁ ⟧Ctx ≡ᴾ ⟦ Γ₂ ⟧Ctx
-- ⟦_⟧Ctx~ : Ctx~ Γ₁ Γ₂ → ⟦ Γ₁ ⟧Ctx ≡ ⟦ Γ₂ ⟧Ctx
⟦_⟧Ty~ᴾ  : Ty~ Γ~ A₁ A₂ → ⟦ A₁ ⟧Ty ≡[ congᴾ ⟦Ty⟧ ⟦ Γ~ ⟧Ctx~ᴾ ]≡ᴾ ⟦ A₂ ⟧Ty
-- ⟦_⟧Ty~  : Ty~ Γ~ A₁ A₂ → ⟦ A₁ ⟧Ty ≡[ cong ⟦Ty⟧ ⟦ Γ~ ⟧Ctx~ ]≡ ⟦ A₂ ⟧Ty

-- ⟦ A~ ⟧Ty~  = ≡[]↑ {p = cong ⟦Ty⟧ ⟦ _ ⟧Ctx~ } ⟦ A~ ⟧Ty~ᴾ
-- ⟦ Γ~ ⟧Ctx~ = ≡↑   ⟦ Γ~ ⟧Ctx~ᴾ

-- {-# INLINE ⟦_⟧Ctx~ #-}
-- {-# INLINE ⟦_⟧Ty~ #-}

-- ⟦_⟧Tm~ᴾ  : Tm~ Γ~ A~ t₁ t₂ → ∀ (ρ~ : ρ₁ ≡[ ⟦ Γ~ ⟧Ctx~ᴾ ]≡ᴾ ρ₂)
--          → ⟦ t₁ ⟧Tm ρ₁ ≡[ ⟦ A~ ⟧Ty~ᴾ ρ~ ]≡ᴾ ⟦ t₂ ⟧Tm ρ₂


-- ⟦_⟧Tm~  : Tm~ Γ~ A~ t₁ t₂ 
--         → ⟦ t₁ ⟧Tm ≡[ dcong₂ ⟦Tm⟧ ⟦ Γ~ ⟧Ctx~ ⟦ A~ ⟧Ty~ ]≡ ⟦ t₂ ⟧Tm



⟦𝔹⟧′ : ⟦ 𝔹 {Γ = Γ} ⟧Ty ≡ᴾ λ ρ → Bool 
⌜⌝𝔹≡ : ⟦ ⌜ b ⌝𝔹 ⟧Tm ≡[ Tm≡ (refl {x = ⟦ Γ ⟧Ctx}) ⟦𝔹⟧′ ]≡ᴾ λ ρ → b



Ty≡-inst : ⟦A₁⟧ ≡ᴾ ⟦A₂⟧ → ⟦A₁⟧ ρ ≡ᴾ ⟦A₂⟧ ρ
Ty≡-inst refl = refl

-- ⟦_⟧Tm~ᴾ  : Tm~ Γ~ A~ t₁ t₂ 
--          → ⟦ t₁ ⟧Tm ≡[ Tm≡ ⟦ Γ~ ⟧Ctx~ᴾ ⟦ A~ ⟧Ty~ᴾ ]≡ᴾ ⟦ t₂ ⟧Tm
-- foo : Tm~ Γ~ A~ t₁ t₂ → (⟦ t₁ ⟧Tm ρ ≡[ Ty≡-inst ⟦ A~ ⟧Ty~ᴾ ]≡ᴾ ⟦ t₂ ⟧Tm ρ)

⟦_⟧Tm~ᴾ :  Tm~ Γ~ A~ t₁ t₂ → (⟦ t₁ ⟧Tm ρ ≡[ Ty≡-inst ⟦ A~ ⟧Ty~ᴾ ]≡ᴾ ⟦ t₂ ⟧Tm ρ)

Tm≡-inst : ∀ {⟦t₁⟧ : ⟦Tm⟧ ⟦ Γ ⟧Ctx (λ _ → Bool)} 
         → ⟦t₁⟧ ≡ᴾ ⟦t₂⟧ → ⟦t₁⟧ ρ ≡ᴾ ⟦t₂⟧ ρ
Tm≡-inst refl = refl

⟦ ε     ⟧ CTX = ⊤
⟦ Γ , A ⟧ CTX = Σ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty

⟦ 𝔹 ⟧ TY = λ ρ → Bool

⟦ Γ , t >rw b ⟧ CTX = Σ ⟦ Γ ⟧Ctx (λ ρ → ⟦ t ⟧Tm ρ ≡ b)

⟦ coe~ Γ~ A ⟧ TY = coeᴾ (Ty≡ ⟦ Γ~ ⟧Ctx~ᴾ) ⟦ A ⟧Ty
⟦ Π A B     ⟧ TY = λ ρ → ∀ x → ⟦ B ⟧Ty (ρ Σ, x)
⟦ A [ δ ]   ⟧ TY = λ ρ → ⟦ A ⟧Ty (⟦ δ ⟧Tms ρ)
⟦ if t A B  ⟧ TY = λ ρ → Bool-rec (⟦ t ⟧Tm ρ) (⟦ A ⟧Ty ρ) (⟦ B ⟧Ty ρ)

⟦ coe~ Γ~ A~ t ⟧ TM = coeᴾ (Tm≡ ⟦ Γ~ ⟧Ctx~ᴾ ⟦ A~ ⟧Ty~ᴾ) ⟦ t ⟧Tm

⟦ ƛ t     ⟧ TM = λ ρ        x → ⟦ t ⟧Tm (ρ Σ, x)
⟦ ƛ⁻¹ t   ⟧ TM = λ (ρ Σ, x)   → ⟦ t ⟧Tm ρ x
⟦ TT      ⟧ TM = λ ρ          → true
⟦ FF      ⟧ TM = λ ρ          → false
⟦ t [ δ ] ⟧ TM = λ ρ          → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ)

⟦ π₁ δ  ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ .fst

⟦ π₂ δ  ⟧ TM = λ ρ → ⟦ δ ⟧Tms ρ .snd

⟦ id     ⟧ TMS = λ ρ → ρ
⟦ π₁rw δ ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ .fst

⟦ if t u v ⟧ TM = λ ρ → Bool-split (⟦ t ⟧Tm ρ) (λ t~ → ⟦ u ⟧Tm (ρ Σ, t~)) 
                                               (λ t~ → ⟦ v ⟧Tm (ρ Σ, t~))
                                          
⟦ coe~ Δ~ Γ~ δ ⟧ TMS = coeᴾ (Tms≡ ⟦ Δ~ ⟧Ctx~ᴾ ⟦ Γ~ ⟧Ctx~ᴾ) ⟦ δ ⟧Tms
⟦ ε            ⟧ TMS = λ ρ → tt
⟦ δ , t        ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ
⟦ ,rwℱ {Δ = Δ} δ refl refl t~ ⟧ TMS 
  = λ ρ → ⟦ δ ⟧Tms ρ Σ, ≡↑ (⟦ t~ ⟧Tm~ᴾ ∙ᴾ Tm≡-inst {Γ = Δ} ⌜⌝𝔹≡)
  -- Tm≡-inst {Γ = Δ} (⟦ t~ ⟧Tm~ᴾ
  -- (≡↑ (Tm≡-inst {Γ = Δ} (⟦ t~ ⟧Tm~ᴾ ∙ᴾ ⌜⌝𝔹≡)))
⟦ δ ⨾ σ        ⟧ TMS = λ ρ → ⟦ δ ⟧Tms (⟦ σ ⟧Tms ρ)

⟦𝔹⟧′ = refl

⌜⌝𝔹≡ {b = false} = refl
⌜⌝𝔹≡ {b = true}  = refl

⟦ rfl~ ⟧Ctx~ᴾ         = refl
⟦ sym~ Γ~ ⟧Ctx~ᴾ      = symᴾ ⟦ Γ~ ⟧Ctx~ᴾ
⟦ Γ₁₂~ ∙~ Γ₂₃~ ⟧Ctx~ᴾ = ⟦ Γ₁₂~ ⟧Ctx~ᴾ ∙ᴾ ⟦ Γ₂₃~ ⟧Ctx~ᴾ
⟦ Γ~ , A~ ⟧Ctx~ᴾ      = ,≡ ⟦ Γ~ ⟧Ctx~ᴾ ⟦ A~ ⟧Ty~ᴾ
⟦ Γ~ , t~ >rw ⟧Ctx~ᴾ  = {!!}

⟦ rfl~              ⟧Ty~ᴾ = refl
⟦ sym~ A~           ⟧Ty~ᴾ = sym[]ᴾ ⟦ A~ ⟧Ty~ᴾ
⟦ A₁₂~ ∙~ A₂₃~      ⟧Ty~ᴾ = {!   !}
⟦ coh               ⟧Ty~ᴾ = {!!}
⟦ 𝔹 {Γ~ = Γ~}       ⟧Ty~ᴾ = 𝔹≡ ⟦ Γ~ ⟧Ctx~ᴾ
⟦ Π {Γ~ = Γ~} A~ B~ ⟧Ty~ᴾ = Π≡ ⟦ Γ~ ⟧Ctx~ᴾ ⟦ A~ ⟧Ty~ᴾ ⟦ B~ ⟧Ty~ᴾ
⟦ A~ [ δ~ ]         ⟧Ty~ᴾ = {!!}
⟦ 𝔹[]               ⟧Ty~ᴾ = refl
⟦ [][]              ⟧Ty~ᴾ = refl
⟦ [id]              ⟧Ty~ᴾ = refl


⟦ rfl~         ⟧Tm~ᴾ = refl
⟦ sym~ t~      ⟧Tm~ᴾ = {!   !}
⟦ t₁₂~ ∙~ t₂₃~ ⟧Tm~ᴾ = {!   !}
⟦ coh          ⟧Tm~ᴾ = {!   !}
⟦ rw x         ⟧Tm~ᴾ = {!   !}
⟦ TT Γ~        ⟧Tm~ᴾ = refl
⟦ FF Γ~        ⟧Tm~ᴾ = refl
⟦ if t~ u~ v~  ⟧Tm~ᴾ = {!   !}
⟦ t~ [ δ~ ]    ⟧Tm~ᴾ = {!   !}
⟦ π₂rw δ       ⟧Tm~ᴾ = {!   !}
⟦ TT[]         ⟧Tm~ᴾ = {!   !}
⟦ FF[]         ⟧Tm~ᴾ = {!   !}
⟦ [id]         ⟧Tm~ᴾ = {!   !}
⟦ [][]         ⟧Tm~ᴾ = {!   !}
⟦ ifTT         ⟧Tm~ᴾ = {!   !}
⟦ ifFF         ⟧Tm~ᴾ = {!   !}
⟦ π₂⨾          ⟧Tm~ᴾ = {!   !}

