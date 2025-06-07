{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Strict

module Dependent.SCDef.NbE2 where

data Thin {Ξ} : ∀ Δ Γ → Tms {Ξ = Ξ} Δ Γ → Set where
  coe~  : ∀ Δ~ Γ~ → Tms~ Δ~ Γ~ δ₁ δ₂ → Thin Δ₁ Γ₁ δ₁ → Thin Δ₂ Γ₂ δ₂

  ε     : Thin • • ε
  _^ᵀʰ_ : Thin Δ Γ δ → ∀ A 
        → Thin  (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A) (δ ^ A)
  _⁺ᵀʰ_ : Thin Δ Γ δ 
        → ∀ A → Thin (Δ ▷ A) Γ (δ ⨾ wk)

idᵀʰ : Thin Γ Γ id
_⨾ᵀʰ_ : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)

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

  callNe : Ne Δ 𝔹 (lookup𝒮 Ψ f .scrut [ δ ]) 
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
  
-- TODO: Is this enough for confluence? I don't think so?
record ValidTRS (Γ : Ctx Ψ) : Set where
  field
    trs    : TRS Γ
    sound  : RwVar {t = t} trs tᴾᴺᵉ b → Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹
    compl  : EqVar Γ t b → ∀ (tᴾᴺᵉ : PreNe Γ 𝔹 t) → RwVar trs tᴾᴺᵉ b

def-incon : Ctx Ψ → Prop
def-incon Γ = Tm~ (rfl~ {Γ = Γ}) rfl~ TT FF

data ComplTRS (Γ : Ctx Ψ) : Set where
  compl  : ValidTRS Γ → ComplTRS Γ
  !!     : def-incon Γ → ComplTRS Γ

data 𝔹Valᵗᶠ : ∀ (Γ : Ctx Ψ) {A} → Tm Γ A → Set where
  TT : Tm~ Γ~ A~ t TT → 𝔹Valᵗᶠ Γ t
  FF : Tm~ Γ~ B~ t FF → 𝔹Valᵗᶠ Γ t

data 𝔹Val : ∀ (Γ : Ctx Ψ) {A} → Tm Γ A → Set where
  TT : Tm~ Γ~ A~ t TT → 𝔹Val Γ t
  FF : Tm~ Γ~ B~ t FF → 𝔹Val Γ t
  ne : Ty~ Γ~ A 𝔹 → Ne Γ A t → 𝔹Val Γ t

checkrw : TRS Γ → PreNe Γ A t → Ne Γ A t × 𝔹Valᵗᶠ Γ t

-- Ah I think we need to add signature-environments back, but not for
-- storing evaluated definitions. Instead, they should store TRSs!
Env    : ∀ Ξ Δ Γ → Tms {Ξ = Ξ} Δ Γ → Set
Val    : ∀ Γ A Δ δ → Env Ξ Δ Γ δ → Tm Δ (A [ δ ]Ty) → Set
eval   : ∀ (t : Tm Γ A) (ρ : Env Ξ Δ Γ δ) 
       → Val Γ A Δ δ ρ (t [ δ ])
eval*  : ∀ δ (ρ : Env Ξ Θ Δ σ) → Env Ξ Θ Γ (δ ⨾ σ)

variable
  ρ : Env Ξ Δ Γ δ

uval : ∀ A {t} → PreNe Δ (A [ δ ]Ty) t → Val Γ A Δ δ ρ t

postulate
  coe𝒱 : ∀ {ρ : Env Ξ Δ Γ δ} (A~ : Ty~ rfl~ A₁ A₂)
        → Tm~ Δ~ (A~ [ rfl~ ]Ty~) t₁ t₂
        → Val Γ A₁ Δ δ ρ t₁ → Val Γ A₂ Δ δ ρ t₂

_[_]ℰ    : Env Ξ Δ Γ δ → Thin Θ Δ σ → Env Ξ Θ Γ (δ ⨾ σ)

postulate 
  [id]ℰ  : ∀ {ρ : Env Ξ Δ Γ δ} → ρ [ idᵀʰ ]ℰ ≡ ρ
  [][]ℰ  : ∀ {ρ : Env Ξ Δ Γ δ} 
             {σᵀʰ : Thin Θ Δ σ} {γᵀʰ : Thin _ Θ γ}
         → ρ [ σᵀʰ ]ℰ [ γᵀʰ ]ℰ ≡ ρ [ σᵀʰ ⨾ᵀʰ γᵀʰ ]ℰ
{-# REWRITE [id]ℰ #-}
{-# REWRITE [][]ℰ #-}

Env Ξ Δ •       δ = ⊤
Env Ξ Δ (Γ ▷ A) δ = Σ (Env Ξ Δ Γ (π₁ δ))
                   λ ρ → Val Γ A Δ (π₁ δ) ρ (π₂ δ)
Env Ξ Δ (Γ ▷ t >eq b) δ
  = Env Ξ Δ Γ (π₁eq δ)

postulate
  id-pres-rw    : ∀ {ρ : Env Ξ Δ Γ δ} 
                → eval* {σ = δ} id ρ ≡ ρ
  wk-pres-rw    : ∀ {ρ : Env Ξ Δ (Γ ▷ A) δ} → eval* wk ρ ≡ ρ .fst

  wkeq-pres-rw  : ∀ {ρ : Env Ξ Δ (Γ ▷ t >eq b) δ} 
                → eval* (wkeq {t = t} {b = b}) ρ ≡ ρ
  []Ty-pres-rw  : ∀ {ρ : Env Ξ Θ Δ σ}
                → Val Δ (A [ δ ]Ty) Θ σ ρ t 
                ≡ Val Γ A Θ (δ ⨾ σ) (eval* δ ρ) t

{-# REWRITE id-pres-rw #-}
{-# REWRITE wk-pres-rw #-}
{-# REWRITE wkeq-pres-rw #-}
{-# REWRITE []Ty-pres-rw #-}

Val Γ (coe~ Γ~ A) Δ δ ρ t 
  = {!!}
Val Γ 𝔹          Δ δ ρ t = 𝔹Val Δ t
Val Γ (IF b A B) Δ δ ρ t = {!if-Val Γ A B Δ δ ρ t (eval b ρ)!}
Val Γ (Π A B)    Δ δ ρ t 
  = ∀ {Θ γ} (γᵀʰ : Thin Θ Δ γ) {u}
      (uⱽ : Val Γ A Θ (δ ⨾ γ) (_[_]ℰ {Γ = Γ} ρ γᵀʰ) u)
  → Val (Γ ▷ A) B Θ ((δ ⨾ γ) , u) ((_[_]ℰ {Γ = Γ} ρ γᵀʰ) Σ, uⱽ) 
        ((t [ γ ]) · u)


eval* (coe~ Δ~ Γ~ δ)  ρ = {!!}
eval* ε               ρ = tt
eval* (δ , t)         ρ = eval* δ ρ Σ, eval t ρ
eval* (δ ,eq t~)      ρ = {!!}

eval-call  : ∀  {f : DefVar Ξ Γ A} (ρ : Env Ξ Δ Γ δ)
                (tⱽ : Val Γ 𝔹 Δ δ ρ (lookup𝒮 Ξ f .scrut [ δ ])) 
           → (∀ t~ → Val Γ A Δ δ ρ (lookup𝒮 Ξ f .lhs [ δ ,eq t~ ]))
           → (∀ t~ → Val Γ A Δ δ ρ (lookup𝒮 Ξ f .rhs [ δ ,eq t~ ]))
           → Val Γ A Δ δ ρ (call f δ)
eval-call {f = f} ρ (TT {Γ~ = Γ~} t~)      uⱽ vⱽ 
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-TT {f = f} (t~ ∙~ TT (sym~ Γ~)))) uⱽ′
  where uⱽ′ = uⱽ (t~ ∙~ TT (sym~ Γ~))
eval-call {f = f} ρ (FF {Γ~ = Γ~} t~)      uⱽ vⱽ
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-FF {f = f} (t~ ∙~ FF (sym~ Γ~)))) vⱽ′
  where vⱽ′ = vⱽ (t~ ∙~ FF (sym~ Γ~))
eval-call ρ (ne A~ tᴺᵉ)  uⱽ vⱽ = {!   !}

eval (coe~ Γ~ A~ t) ρ = {!   !}
eval (` i)          ρ = {!   !}
eval (ƛ t)          ρ = {!   !}
eval (t · u)        ρ = eval t ρ idᵀʰ (eval u ρ)
eval TT             ρ = TT rfl~
eval FF             ρ = FF rfl~
eval {δ = σ} (call f δ)     ρ 
  using δⱽ ← eval* δ ρ
  with eval (lookup𝒮 _ f .scrut) δⱽ 
  | (λ t~ →  eval {δ = (δ ⨾ σ) ,eq t~} (lookup𝒮 _ f .lhs) δⱽ)
  | (λ t~ →  eval {δ = (δ ⨾ σ) ,eq t~} (lookup𝒮 _ f .rhs) δⱽ)
... | tⱽ | uⱽ | vⱽ = eval-call {f = f} δⱽ tⱽ uⱽ vⱽ

