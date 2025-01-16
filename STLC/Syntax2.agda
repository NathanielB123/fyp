{-# OPTIONS --prop #-}

open import Utils
open import Common.Sort

-- Provides the same interfaces as 'STLC.Syntax' but not indexed by extensions
-- This makes typechecking way faster
module STLC.Syntax2 where

module Syntax where
  infixr 5 _⇒_
  infixl 4  _,_
  infix  5  ƛ_
  infixl 6  _·_
  infix  7  `_

  data Ctx   : Set
  data Ty    : Set
  data Tm[_] : Sort → Ctx → Ty → Set
  Var = Tm[ V ]
  Tm  = Tm[ T ]

  variable
    Γ Δ Θ : Ctx
    A B C : Ty
    A₁ A₂ A₃ B₁ B₂ B₃ C₁ C₂ C₃ : Ty
    i j k : Var Γ A
    t u v : Tm Γ A
    t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
    x y z : Tm[ q ] Γ A
    x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : Tm[ q ] Γ A

  data Ctx where
    ε   : Ctx
    _,_ : Ctx → Ty → Ctx

  data Ty where
    _⇒_  : Ty → Ty → Ty
    𝔹'   : Ty
    _+'_ : Ty → Ty → Ty

  data Tm[_] where
    vz    : Var (Γ , A) A
    vs    : Var Γ B → Var (Γ , A) B
    
    `_    : Var Γ A → Tm Γ A
    _·_   : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ƛ_    : Tm (Γ , A) B → Tm Γ (A ⇒ B)

    true  : Tm Γ 𝔹'
    false : Tm Γ 𝔹'
    𝔹-rec : Tm Γ 𝔹' → Tm Γ A → Tm Γ A → Tm Γ A 

    inl   : Tm Γ A → Tm Γ (A +' B)
    inr   : Tm Γ B → Tm Γ (A +' B)
    +-rec : Tm Γ (A +' B) → Tm (Γ , A) C → Tm (Γ , B) C → Tm Γ C

open Syntax public 

module Substitution where
  tm⊑ : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
  tm⊑ {q = V} {r = T} _ i = ` i
  tm⊑ {q = V} {r = V} _ i = i
  tm⊑ {q = T} {r = T} _ t = t

  -- TODO: Move 'Tms' out of the parameterised module to avoid case splitting
  -- pain (https://github.com/agda/agda/issues/3209)
  data Tms[_] (q : Sort) : Ctx → Ctx → Set where
    ε   : Tms[ q ] Δ ε
    _,_ : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ , A)

  variable
    δ σ ξ δ₁ δ₂ δ₃ σ₁ σ₂ σ₃ ξ₁ ξ₂ ξ₃ : Tms[ q ] Δ Γ

  Vars = Tms[ V ]
  Tms  = Tms[ T ]

  vz[_] : ∀ q → Tm[ q ] (Γ , A) A
  vz[ V ] = vz
  vz[ T ] = ` vz

  suc[_] : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ , A) B
  _⁺_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) Γ
  _^_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) (Γ , A)
  _[_]   : Tm[ q ] Γ A → Tms[ s ] Δ Γ → Tm[ q ⊔ s ] Δ A 
  id : Vars Γ Γ

  id′ : Sort → Vars Γ Γ

  id = id′ V
  {-# INLINE id #-} 

  id′ {Γ = ε}     _ = ε
  id′ {Γ = Γ , A} _ = id ^ A

  suc[ V ]   = vs
  suc[ T ] t = t [ id ⁺ _ ]

  ε       ⁺ A = ε
  (δ , t) ⁺ A = (δ ⁺ A) , suc[ _ ] t

  δ ^ A = (δ ⁺ A) , vz[ _ ]

  vz          [ δ , t ] = t
  vs i        [ δ , t ] = i [ δ ]
  (` i)       [ δ ]     = tm⊑ ⊑T (i [ δ ])
  (t · u)     [ δ ]     = t [ δ ] · u [ δ ]
  (ƛ t)       [ δ ]     = ƛ (t [ δ ^ _ ])
  true        [ δ ]     = true
  false       [ δ ]     = false
  𝔹-rec c t u [ δ ]     = 𝔹-rec (c [ δ ]) (t [ δ ]) (u [ δ ])
  inl t       [ δ ]     = inl (t [ δ ])
  inr t       [ δ ]     = inr (t [ δ ])
  +-rec s l r [ δ ]     = +-rec (s [ δ ]) (l [ δ ^ _ ]) (r [ δ ^ _ ])
  
  _⨾_ : Tms[ q ] Δ Γ → Tms[ r ] Θ Δ → Tms[ q ⊔ r ] Θ Γ
  ε       ⨾ σ = ε
  (δ , x) ⨾ σ = (δ ⨾ σ) , (x [ σ ])

  tms⊑ : q ⊑ r → Tms[ q ] Δ Γ → Tms[ r ] Δ Γ
  tms⊑ p ε       = ε
  tms⊑ p (δ , x) = tms⊑ p δ , tm⊑ p x

  id[_]  : ∀ q → Tms[ q ] Γ Γ
  id[ _ ] = tms⊑ V⊑ id
  
  <_> : Tm Γ A → Tms[ T ] Γ (Γ , A)
  < t > = id[ T ] , t

  ƛ⁻¹_ : Tm Γ (A ⇒ B) → Tm (Γ , A) B
  ƛ⁻¹ t = t [ id ⁺ _ ] · (` vz)

  wk : Tms[ V ] (Γ , A) Γ
  wk = id ⁺ _
  
open Substitution public
