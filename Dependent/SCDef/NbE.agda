{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Strict

module Dependent.SCDef.NbE where 

data Thin {Ξ} : ∀ Δ Γ → Tms {Ξ = Ξ} Δ Γ → Set where
  coe~  : ∀ Δ~ Γ~ → Tms~ Δ~ Γ~ δ₁ δ₂ → Thin Δ₁ Γ₁ δ₁ → Thin Δ₂ Γ₂ δ₂

  ε     : Thin • • ε
  _^ᵀʰ_ : Thin Δ Γ δ → ∀ A 
        → Thin  (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A) (δ ^ A)
  _⁺ᵀʰ_ : Thin Δ Γ δ 
        → ∀ A → Thin (Δ ▷ A) Γ (δ ⨾ wk)

Ne : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set
data PreNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set
data Nf    : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set 

variable
  tᴾᴺᵉ uᴾᴺᵉ : PreNe Γ A t
  tᴺᵉ       : Ne Γ A t
  tᴺᶠ       : Nf Γ A t

predNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Prop
predNe Γ A t = ∀ {Γ′} b Γ~ A~ → ¬∥ Tm~ {Γ₂ = Γ′} Γ~ A~ t ⌜ b ⌝𝔹 ∥

Ne Γ A t = PreNe Γ A t × Box (predNe Γ A t)

data PreNe where
  coe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → PreNe Γ₁ A₁ t₁ → PreNe Γ₂ A₂ t₂

  `_  : ∀ i → PreNe Γ A (` i)
  _·_ : Ne Γ (Π A B) t → Nf Γ A u
      → PreNe Γ (B [ < u > ]Ty) (t · u)

  call : Ne Δ 𝔹 (lookup𝒮 Ψ f .scrut [ δ ]) 
       → PreNe Δ (A [ δ ]Ty) (call {A = A} f δ)

data Nf where
  coe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂

  ne𝔹  : Ne Γ 𝔹 t → Nf Γ 𝔹 t
  neIF : Ne Γ 𝔹 u → Ne Γ (IF u A B) t → Nf Γ (IF u A B) t
  ƛ_   : Nf (Γ ▷ A) B t → Nf Γ (Π A B) (ƛ t)
  TT   : Nf Γ 𝔹 TT
  FF   : Nf Γ 𝔹 FF

coeNe : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Ne Γ₁ A₁ t₁ → Ne Γ₂ A₂ t₂
coeNe Γ~ A~ t~ (tᴺᵉ Σ, box p) 
  =  coe~ Γ~ A~ t~ tᴺᵉ 
  Σ, box λ b Γ~′ A~′ t~′ → p b (Γ~ ∙~ Γ~′) (A~ ∙~ A~′) (t~ ∙~ t~′)

⌜_⌝𝔹ᴺᶠ : ∀ b → Nf Γ 𝔹 ⌜ b ⌝𝔹
⌜ true  ⌝𝔹ᴺᶠ = TT 
⌜ false ⌝𝔹ᴺᶠ = FF 

data TRS (Γ : Ctx Ψ) : Set where
  •       : TRS Γ
  _▷_>rw_ : TRS Γ → PreNe Γ 𝔹 t → Bool → TRS Γ

variable
  Γᶜ : TRS Γ

data RwVar : TRS Γ → PreNe Γ 𝔹 t → Bool → Set where
  rz : RwVar (Γᶜ ▷ tᴾᴺᵉ >rw b) tᴾᴺᵉ b
  rs : RwVar Γᶜ tᴾᴺᵉ b₁ → RwVar (Γᶜ ▷ uᴾᴺᵉ >rw b₂) tᴾᴺᵉ b₁
  
record ValidTRS (Γ : Ctx Ψ) : Set where
  field
    trs    : TRS Γ
    sound  : RwVar {t = t} trs tᴾᴺᵉ b → Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹
    compl  : EqVar Γ t b → ∀ (tᴾᴺᵉ : PreNe Γ 𝔹 t) → RwVar trs tᴾᴺᵉ b

-- Disjoint contexts intuitively are ones where every LHS is β-neutral and
-- disjoint
-- This seems kinda miserable to mechanise in Agda
data DisjCtx : Ctx Ψ → Set where

-- Disjoint contexts can be "completed" to build TRSs by just 
-- weakening every LHS.
-- Of course, injecting the disjoint β-neutral terms into |Ne| is non-trivial,
-- and completeness is also tricky.
-- I think we might need reduction to get there
complete : DisjCtx Γ → ValidTRS Γ

data 𝔹Valᵗᶠ : ∀ (Γ : Ctx Ψ) {A} → Tm Γ A → Set where
  TT : Tm~ Γ~ A~ t TT → 𝔹Valᵗᶠ Γ t
  FF : Tm~ Γ~ B~ t FF → 𝔹Valᵗᶠ Γ t

data 𝔹Val : ∀ (Γ : Ctx Ψ) {A} → Tm Γ A → Set where
  TT : Tm~ Γ~ A~ t TT → 𝔹Val Γ t
  FF : Tm~ Γ~ B~ t FF → 𝔹Val Γ t
  ne : Ty~ Γ~ A 𝔹 → Ne Γ A t → 𝔹Val Γ t

checkrw : TRS Γ → PreNe Γ A t → Ne Γ A t × 𝔹Valᵗᶠ Γ t

SigEnv : Sig → Set
Env    : SigEnv Ξ → ∀ Δ Γ → Tms {Ξ = Ξ} Δ Γ → Set
Val    : ∀ (Ξℰ : SigEnv Ξ) Γ A Δ δ → Env Ξℰ Δ Γ δ → Tm Δ (A [ δ ]Ty) → Set
eval   : ∀ (Ξℰ : SigEnv Ξ) (t : Tm Γ A) (ρ : Env Ξℰ Δ Γ δ) 
       → Val Ξℰ Γ A Δ δ ρ (t [ δ ])
eval*  : ∀ (Ξℰ : SigEnv Ξ) δ (ρ : Env Ξℰ Θ Δ σ) → Env Ξℰ Θ Γ (δ ⨾ σ)

variable
  Ξℰ : SigEnv Ξ
  ρ : Env Ξℰ Δ Γ δ

uval : ∀ A {t} → PreNe Δ (A [ δ ]Ty) t → Val Ξℰ Γ A Δ δ ρ t

record DefVal (Ξℰ : SigEnv Ξ) (d : Def Ξ Γ A) : Set where
  constructor defⱽ
  pattern
  field
    lhsⱽ : ∀ (ρ : Env Ξℰ Δ Γ δ) (t~ : Tm~ rfl~ rfl~ (d .scrut [ δ ]) TT)
         → Val Ξℰ Γ A Δ δ ρ (d .lhs [ δ ,eq t~ ])
    rhsⱽ : ∀ (ρ : Env Ξℰ Δ Γ δ) (t~ : Tm~ rfl~ rfl~ (d .scrut [ δ ]) FF)
         → Val Ξℰ Γ A Δ δ ρ (d .rhs [ δ ,eq t~ ])

SigEnv • = ⊤
SigEnv (Ψ ▷ Γ ⇒ A if t then u else v)
  = Σ⟨ Ξℰ ∶ SigEnv Ψ ⟩× DefVal Ξℰ (if t u v)

lookup𝒮ℰ : ∀ (Ξℰ : SigEnv Ξ) (f : DefVar Ξ Γ A) → DefVal Ξℰ (lookup𝒮 Ξ f)
lookup𝒮ℰ Ξℰ (coe~ Γ~ A~ f) = {!   !}
lookup𝒮ℰ (Ξℰ Σ, defⱽ uⱽ vⱽ) fz = defⱽ {!!} {!!}
lookup𝒮ℰ (Ξℰ Σ, dⱽ) (fs f) 
  using defⱽ uⱽ vⱽ ← lookup𝒮ℰ Ξℰ f
  = defⱽ {!!} {!!} 

_[_]ℰ : Env {Ξ = Ξ} Ξℰ Δ Γ δ → Thin Θ Δ σ → Env Ξℰ Θ Γ (δ ⨾ σ)

postulate
  -- coeℰ : ∀ Δ~ Γ~ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Env Δ₁ Γ₁ δ₁ → Env Δ₂ Γ₂ δ₂

  coe𝒱 : ∀ {ρ : Env {Ξ = Ξ} Ξℰ Δ Γ δ} (A~ : Ty~ rfl~ A₁ A₂)
        → Tm~ Δ~ (A~ [ rfl~ ]Ty~) t₁ t₂
        → Val Ξℰ Γ A₁ Δ δ ρ t₁ → Val Ξℰ Γ A₂ Δ δ ρ t₂

Env Ξℰ Δ •       δ = ⊤
Env Ξℰ Δ (Γ ▷ A) δ = Σ (Env Ξℰ Δ Γ (π₁ δ))
                   λ ρ → Val Ξℰ Γ A Δ (π₁ δ) ρ (π₂ δ)
Env Ξℰ Δ (Γ ▷ t >eq b) δ 
  = {!!}

Val Ξℰ Γ (coe~ Γ~ A) Δ δ ρ t 
  = {!!}
Val Ξℰ Γ 𝔹          Δ δ ρ t = 𝔹Val Δ t
Val Ξℰ Γ (IF b A B) Δ δ ρ t = {!if-Val Γ A B Δ δ ρ t (eval b ρ)!}
Val {Ξ = Ξ} Ξℰ Γ (Π A B)    Δ δ ρ t 
  = ∀ {Θ γ} (γᵀʰ : Thin Θ Δ γ) {u}
      (uⱽ : Val Ξℰ Γ A Θ (δ ⨾ γ) (_[_]ℰ {Γ = Γ} ρ γᵀʰ) u)
  → Val Ξℰ (Γ ▷ A) B Θ ((δ ⨾ γ) , u) ((_[_]ℰ {Γ = Γ} ρ γᵀʰ) Σ, uⱽ) 
        ((t [ γ ]) · u)

eval-call : (f : DefVar Ξ Γ A) (ρ : Env Ξℰ Δ Γ δ)
            (tⱽ : Val Ξℰ Γ 𝔹 Δ δ ρ (lookup𝒮 Ξ f .scrut [ δ ])) 
          → DefVal Ξℰ (lookup𝒮 Ξ f)
          → Val Ξℰ Γ A Δ δ ρ (call f δ)
eval-call f ρ (TT {Γ~ = Γ~} t~)     (defⱽ uⱽ vⱽ) 
  = coe𝒱 rfl~ (sym~ (call-TT {f = f} (t~ ∙~ TT (sym~ Γ~)))) uⱽ′
  where uⱽ′ = uⱽ ρ (t~ ∙~ TT (sym~ Γ~))
eval-call f ρ (FF {Γ~ = Γ~} t~)     (defⱽ uⱽ vⱽ) 
  = coe𝒱 rfl~ (sym~ (call-FF {f = f} (t~ ∙~ FF (sym~ Γ~)))) vⱽ′
  where vⱽ′ = vⱽ ρ (t~ ∙~ FF (sym~ Γ~))
eval-call f ρ (ne A~ tᴺᵉ) (defⱽ uⱽ vⱽ) 
  = uval _ (call {f = f} tᴺᵉ)

eval Ξℰ (coe~ Γ~ A~ t) ρ = {!   !}
eval Ξℰ (` i)          ρ = {!   !}
eval Ξℰ (ƛ t)          ρ = {!   !}
eval Ξℰ (t · u)        ρ = {!   !}
eval Ξℰ TT             ρ = {!   !}
eval Ξℰ FF             ρ = {!   !}
eval Ξℰ (call f δ)     ρ = {!fδⱽ!}
  where δⱽ = eval* Ξℰ δ ρ
        fδⱽ = eval-call f δⱽ (eval Ξℰ (lookup𝒮 _ f .scrut) δⱽ) 
                        (lookup𝒮ℰ Ξℰ f)
