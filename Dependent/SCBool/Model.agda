{-# OPTIONS --prop --show-irrelevant #-}

open import Utils

open import Dependent.SCBool.Syntax
open import Dependent.SCBool.MutualInd

module Dependent.SCBool.Model where

-- 𝔹-elim : (P : Bool → Set) → ∀ b → P true → P false → P b
-- 𝔹-elim P true Ptt Pff = Ptt
-- 𝔹-elim P true Ptt Pff = Pff


⟦Ctx⟧ : Set₁
⟦Ctx⟧ = Set

⟦Ty⟧ : ⟦Ctx⟧ → Set₁
⟦Ty⟧ Γ = Γ → Set

⟦Tm⟧ : ∀ Γ → ⟦Ty⟧ Γ → Set
⟦Tm⟧ Γ A = ∀ ρ → A ρ

⟦Tms⟧ : ⟦Ctx⟧ → ⟦Ctx⟧ → Set
⟦Tms⟧ Δ Γ = Δ → Γ

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

variable
  ρ ρ₁ ρ₂ : ⟦ Γ ⟧Ctx

⟦_⟧Ctx~ : Ctx~ Γ₁ Γ₂ → ⟦ Γ₁ ⟧Ctx ≡ ⟦ Γ₂ ⟧Ctx
⟦_⟧Ty~  : Ty~ Γ~ A₁ A₂ → ρ₁ ≡[ ⟦ Γ~ ⟧Ctx~ ]≡ ρ₂ → ⟦ A₁ ⟧Ty ρ₁ ≡ ⟦ A₂ ⟧Ty ρ₂
⟦_⟧Tm~  : Tm~ Γ~ A~ t₁ t₂ → ∀ (ρ~ : ρ₁ ≡[ ⟦ Γ~ ⟧Ctx~ ]≡ ρ₂)
        → ⟦ t₁ ⟧Tm ρ₁ ≡[ ⟦ A~ ⟧Ty~ ρ~ ]≡ ⟦ t₂ ⟧Tm ρ₂

⟦ ε     ⟧ CTX = ⊤
⟦ Γ , A ⟧ CTX = Σ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty

⟦ 𝔹 ⟧ TY = λ ρ → Bool

⟦ Γ , t >rw b ⟧ CTX = Σ ⟦ Γ ⟧Ctx (λ ρ → ⟦ t ⟧Tm ρ ≡ b)

⟦ coe~ Γ~ A ⟧ TY = subst ⟦Ty⟧ ⟦ Γ~ ⟧Ctx~ ⟦ A ⟧Ty
⟦ Π A B     ⟧ TY = λ ρ → ∀ x → ⟦ B ⟧Ty (ρ Σ, x)
⟦ A [ δ ]   ⟧ TY = λ ρ → ⟦ A ⟧Ty (⟦ δ ⟧Tms ρ)

-- Hmm
⟦ coe~ Γ~ A~ t ⟧ TM = coe (dcong₂ ⟦Tm⟧ ⟦ Γ~ ⟧Ctx~ {!!}) ⟦ t ⟧Tm

⟦ ƛ t     ⟧ TM = λ ρ        x → ⟦ t ⟧Tm (ρ Σ, x)
⟦ ƛ⁻¹ t   ⟧ TM = λ (ρ Σ, x)   → ⟦ t ⟧Tm ρ x
⟦ TT      ⟧ TM = λ ρ          → true
⟦ FF      ⟧ TM = λ ρ          → false
⟦ t [ δ ] ⟧ TM = λ ρ          → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ)

⟦ π₁ δ  ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ .fst

⟦ π₂ δ  ⟧ TM = λ ρ → ⟦ δ ⟧Tms ρ .snd

⟦ id     ⟧ TMS = λ ρ → ρ
⟦ π₁rw δ ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ .fst

⟦ if t u v ⟧ TM = λ ρ → 𝔹-split (⟦ t ⟧Tm ρ) (λ t~ → ⟦ u ⟧Tm (ρ Σ, t~)) 
                                            (λ t~ → ⟦ v ⟧Tm (ρ Σ, t~))
                                          
⟦ coe~ Δ~ Γ~ δ ⟧ TMS = coe (cong₂ ⟦Tms⟧ ⟦ Δ~ ⟧Ctx~ ⟦ Γ~ ⟧Ctx~) ⟦ δ ⟧Tms
⟦ ε            ⟧ TMS = λ ρ → tt
⟦ δ , t        ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ
⟦ δ ,rw t~     ⟧ TMS = λ ρ → ⟦ δ ⟧Tms ρ Σ, {!⟦ t~ ⟧Tm~ refl!}
⟦ δ ⨾ σ        ⟧ TMS = λ ρ → ⟦ δ ⟧Tms (⟦ σ ⟧Tms ρ)


-- ⟦ coe~ Δ~ Γ~ δ ⟧Tms = {!   !}
-- ⟦ ε            ⟧Tms = {!   !}
-- ⟦ δ , t        ⟧Tms ρ = ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ
-- ⟦ δ ,rw t~     ⟧Tms ρ = ⟦ δ ⟧Tms ρ Σ, {!⟦ t~ ⟧Tm~  !}
-- ⟦ id           ⟧Tms ρ = ρ
-- ⟦ δ ⨾ σ        ⟧Tms = {!   !}
-- ⟦ π₁ δ         ⟧Tms = {!   !}
-- ⟦ π₁rw δ       ⟧Tms ρ = ⟦ δ ⟧Tms ρ .fst 

-- ⟦ coe~ Γ~ A~ t ⟧Tm ρ          = {!   !}
-- ⟦ ƛ t          ⟧Tm ρ        x = ⟦ t ⟧Tm (ρ Σ, x)
-- ⟦ ƛ⁻¹ t        ⟧Tm (ρ Σ, x)   = ⟦ t ⟧Tm ρ x
-- ⟦ TT           ⟧Tm ρ          = true
-- ⟦ FF           ⟧Tm ρ          = false
-- ⟦ if t u v     ⟧Tm ρ          with ⟦ t ⟧Tm ρ in eq
-- ... | true  = ⟦ u ⟧Tm (ρ Σ, eq)
-- ... | false = ⟦ v ⟧Tm (ρ Σ, eq)
-- ⟦ π₂ δ         ⟧Tm ρ          = {!   !}
-- ⟦ t [ δ ]      ⟧Tm ρ          = {!   !}

