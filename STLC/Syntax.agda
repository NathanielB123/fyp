{-# OPTIONS --rewriting --prop #-}

import Agda.Builtin.Equality.Rewrite

open import Utils

module STLC.Syntax where

module Syntax where
  infixr 5 _⇒_
  infixl  4  _,_
  infix   5  ƛ_
  infixl  6  _·_
  infix   7  `_

  data Sort : Set where
    V   : Sort
    T>V : ∀ v → v ≡ V → Sort

  pattern T = T>V V refl

  variable
    q r s : Sort

  _⊔_ : Sort → Sort → Sort
  T ⊔ q = T
  V ⊔ q = q

  data _⊑_ : Sort → Sort → Prop where
    V⊑T : V ⊑ T
    rfl : q ⊑ q

  data Ctx : Set
  data Ty  : Set
  data Tm[_] : Sort → Ctx → Ty → Set
  Var = Tm[ V ]
  Tm  = Tm[ T ]

  variable
    Γ Δ Θ : Ctx
    A B C : Ty
    i j k : Var Γ A
    t u v : Tm Γ A
    x y z : Tm[ q ] Γ A

  data Ctx where
    ε   : Ctx
    _,_ : Ctx → Ty → Ctx

  data Ty where
    𝔹'  : Ty 
    _⇒_ : Ty → Ty → Ty

  data Tm[_] where
    vz    : Var (Γ , A) A
    vs    : Var Γ B → Var (Γ , A) B
    
    `_    : Var Γ A → Tm Γ A
    _·_   : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ƛ_    : Tm (Γ , A) B → Tm Γ (A ⇒ B)
    
    true  : Tm Γ 𝔹'
    false : Tm Γ 𝔹'
    𝔹-rec : Tm Γ 𝔹' → Tm Γ A → Tm Γ A → Tm Γ A 

  tm⊑ : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
  tm⊑ {q = V} {r = T} _ i = ` i
  tm⊑ {q = V} {r = V} _ i = i
  tm⊑ {q = T} {r = T} _ t = t

  ⊑T : q ⊑ T
  ⊑T {q = V} = V⊑T
  ⊑T {q = T} = rfl

  V⊑ : V ⊑ q
  V⊑ {q = V} = rfl
  V⊑ {q = T} = V⊑T

  ⊑⊔₁ : q ⊑ (q ⊔ r)
  ⊑⊔₁ {q = V} = V⊑
  ⊑⊔₁ {q = T} = rfl

  ⊑⊔₂ : q ⊑ (r ⊔ q)
  ⊑⊔₂ {r = V} = rfl
  ⊑⊔₂ {r = T} = ⊑T

  data Ne : Ctx → Ty → Set
  data Nf : Ctx → Ty → Set

  data Ne where
    `_    : Var Γ A → Ne Γ A
    _·_   : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    
    𝔹-rec : Ne Γ 𝔹' → Nf Γ A → Nf Γ A → Ne Γ A 

  data Nf where
    ne  : Ne Γ A → Nf Γ A
    ƛ_  : Nf (Γ , A) B → Nf Γ (A ⇒ B)
    
    true  : Nf Γ 𝔹'
    false : Nf Γ 𝔹'

  ne→tm : Ne Γ A → Tm Γ A
  nf→tm : Nf Γ A → Tm Γ A

  ne→tm (` i)         = ` i
  ne→tm (t · u)       = ne→tm t · nf→tm u
  ne→tm (𝔹-rec c t u) = 𝔹-rec (ne→tm c) (nf→tm t) (nf→tm u)

  nf→tm (ne t) = ne→tm t
  nf→tm (ƛ t)  = ƛ nf→tm t
  nf→tm true   = true
  nf→tm false  = false

open Syntax public

module Subst where
  data Tms[_] (q : Sort) : Ctx → Ctx → Set where
    ε   : Tms[ q ] Δ ε
    _,_ : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ , A)

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
  
  _[_]ne : Ne Γ A → Vars Δ Γ → Ne Δ A
  _[_]nf : Nf Γ A → Vars Δ Γ → Nf Δ A

  (` i)       [ δ ]ne = ` (i [ δ ])
  (t · u)     [ δ ]ne = t [ δ ]ne · u [ δ ]nf
  𝔹-rec c t u [ δ ]ne = 𝔹-rec (c [ δ ]ne) (t [ δ ]nf) (u [ δ ]nf)

  ne t  [ δ ]nf = ne (t [ δ ]ne)
  (ƛ t) [ δ ]nf = ƛ  (t [ δ ^ _ ]nf)
  true  [ δ ]nf = true
  false [ δ ]nf = false

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
  
open Subst public

ƛ⁻¹_ : Tm Γ (A ⇒ B) → Tm (Γ , A) B
ƛ⁻¹ t = t [ id ⁺ _ ] · (` vz)
