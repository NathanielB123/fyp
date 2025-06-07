{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Strict

module Dependent.SCDef.NbE where 

[][]⁺⁺₁ : ∀ {t : Tm Γ 𝔹} → t [ φ ]⁺ [ ψ ]⁺ ≡ t [ φ ⨾𝒮 ψ ]⁺
[][]⁺⁺₁ = [][]⁺⁺
{-# REWRITE [][]⁺⁺₁ #-}
[][]⁺⁺₂ : ∀ {t : Tm (Γ ▷ u >eq b) (A [ wkeq ]Ty)}
        → t [ φ ]⁺ [ ψ ]⁺ ≡ t [ φ ⨾𝒮 ψ ]⁺
[][]⁺⁺₂ {t = t} = [][]⁺⁺ {t = t}
{-# REWRITE [][]⁺⁺₂ #-}

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

SigEnv : Sig → Set
Env    : SigEnv Ξ → ∀ Δ Γ → Tms {Ξ = Ξ} Δ Γ → Set
Val    : ∀ (Ξℰ : SigEnv Ξ) Γ A Δ δ → Env Ξℰ Δ Γ δ → Tm Δ (A [ δ ]Ty) → Set
eval   : ∀ (Ξℰ : SigEnv Ξ) (t : Tm Γ A) (ρ : Env Ξℰ Δ Γ δ) 
       → Val Ξℰ Γ A Δ δ ρ (t [ δ ])
eval*  : ∀ (Ξℰ : SigEnv Ξ) δ (ρ : Env Ξℰ Θ Δ σ) → Env Ξℰ Θ Γ (δ ⨾ σ)

variable
  Ξℰ Ψℰ : SigEnv Ξ
  ρ : Env Ξℰ Δ Γ δ

uval : ∀ A {t} → PreNe Δ (A [ δ ]Ty) t → Val Ξℰ Γ A Δ δ ρ t

-- _[_]𝒮ℰ   : SigEnv Ψ → Wk Φ Ψ → SigEnv Φ

record DefVal (Ψℰ : SigEnv Ψ) (d : Def Ψ Γ A) : Set where
  constructor defⱽ
  pattern
  field
    lhsⱽ  : ∀  (ρ : Env Ψℰ Δ Γ δ) 
               (t~ : Tm~ rfl~ rfl~ (d .scrut [ δ ]) TT)
          → Val  Ψℰ Γ A Δ δ ρ 
                 (d .lhs [ δ ,eq t~ ])
    rhsⱽ  : ∀  (ρ : Env Ψℰ Δ Γ δ) 
               (t~ : Tm~ rfl~ rfl~ (d .scrut [ δ ]) FF)
          → Val  Ψℰ Γ A Δ δ ρ 
                 (d .rhs [ δ ,eq t~ ])
    -- lhsⱽ  : ∀  (φ : Wk Φ Ψ) {δ} (ρ : Env (Ψℰ [ φ ]𝒮ℰ) Δ (Γ [ φ ]Ctx) δ) 
    --            (t~ : Tm~ rfl~ rfl~ (d .scrut [ φ ]⁺ [ δ ]) TT)
    --       → Val  (Ψℰ [ φ ]𝒮ℰ) (Γ [ φ ]Ctx) (A [ φ ]Ty⁺) Δ δ ρ 
    --              (d .lhs [ φ ]⁺ [ δ ,eq t~ ])
    -- rhsⱽ  : ∀  (φ : Wk Φ Ψ) {δ} (ρ : Env (Ψℰ [ φ ]𝒮ℰ) Δ (Γ [ φ ]Ctx) δ) 
    --            (t~ : Tm~ rfl~ rfl~ (d .scrut [ φ ]⁺ [ δ ]) FF)
    --       → Val  (Ψℰ [ φ ]𝒮ℰ) (Γ [ φ ]Ctx) (A [ φ ]Ty⁺) Δ δ ρ 
    --              (d .rhs [ φ ]⁺ [ δ ,eq t~ ])

-- _[_]Def𝒱  : ∀ {d : Def Ψ Γ A}
--           → DefVal Ψℰ d → ∀ (φ : Wk Φ Ψ) → DefVal (Ψℰ [ φ ]𝒮ℰ) (d [ φ ]Def)

-- _[_]Wkℰ  : Env Ψℰ Δ Γ δ → ∀ (φ : Wk Φ Ψ) 
--          → Env (Ψℰ [ φ ]𝒮ℰ) (Δ [ φ ]Ctx) (Γ [ φ ]Ctx) (δ [ φ ]Tms) 
_[_]ℰ    : Env {Ξ = Ξ} Ξℰ Δ Γ δ → Thin Θ Δ σ → Env Ξℰ Θ Γ (δ ⨾ σ)

postulate 
  -- [id]𝒮ℰ : Ξℰ [ id𝒮 ]𝒮ℰ ≡ Ξℰ
  [id]ℰ  : ∀ {ρ : Env Ξℰ Δ Γ δ} → ρ [ idᵀʰ ]ℰ ≡ ρ
  [][]ℰ  : ∀ {ρ : Env Ξℰ Δ Γ δ} 
             {σᵀʰ : Thin Θ Δ σ} {γᵀʰ : Thin _ Θ γ}
         → ρ [ σᵀʰ ]ℰ [ γᵀʰ ]ℰ ≡ ρ [ σᵀʰ ⨾ᵀʰ γᵀʰ ]ℰ
-- {-# REWRITE [id]𝒮ℰ #-}
{-# REWRITE [id]ℰ #-}
{-# REWRITE [][]ℰ #-}

postulate
  coe𝒱 : ∀ {ρ : Env {Ξ = Ξ} Ξℰ Δ Γ δ} (A~ : Ty~ rfl~ A₁ A₂)
        → Tm~ Δ~ (A~ [ rfl~ ]Ty~) t₁ t₂
        → Val Ξℰ Γ A₁ Δ δ ρ t₁ → Val Ξℰ Γ A₂ Δ δ ρ t₂

Env Ξℰ Δ •       δ = ⊤
Env Ξℰ Δ (Γ ▷ A) δ = Σ (Env Ξℰ Δ Γ (π₁ δ))
                   λ ρ → Val Ξℰ Γ A Δ (π₁ δ) ρ (π₂ δ)
-- I am going to leave this as a hole until I reach a point in the NbE code
-- when it is necessary. In the standard model, we interpreted convertibility
-- assumptions as propositional equalities. In this NbE algorithm, TRS is
-- already kinda dealing with the rewrites, so I'm not sure what would be
-- useful to put here (equations between values seem weird to me, but maybe
-- that is the way to go)
Env Ξℰ Δ (Γ ▷ t >eq b) δ 
  = {!!}

-- TODO: Is this the neatest approach?
-- Strengthening feels inherently a bit ugly to me...
-- One possible idea: could we parameterise over signature environments?
-- Oh lol this is literally the idea behind Env
-- So I guess we could set |SigEnv Ξ = SigEnv′ Ξ Ξ|
-- Weakening can then take us from |SigEnv′ Φ Ψ| to |SigEnv′ (Φ ▷ ...) Ψ|

[_]𝒮ℰ⁻¹ : Wk Φ Ψ → SigEnv Φ → SigEnv Ψ

[_]ℰ⁻¹_ : ∀ (φ : Wk Φ Ψ) → Env Ξℰ (Δ [ φ ]Ctx) (Γ [ φ ]Ctx) (δ [ φ ]Tms) 
        → Env ([ φ ]𝒮ℰ⁻¹ Ξℰ) Δ Γ δ

postulate
  id-pres-rw    : ∀ {Ξℰ : SigEnv Ξ} {ρ : Env Ξℰ Δ Γ δ} 
                → eval* {σ = δ} Ξℰ id ρ ≡ ρ
  wk-pres-rw    : ∀ {Ξℰ : SigEnv Ξ} {ρ : Env Ξℰ Δ (Γ ▷ A) δ} → eval* Ξℰ wk ρ ≡ ρ .fst
  []Ty-pres-rw  : ∀ {Ξℰ : SigEnv Ξ} {ρ : Env Ξℰ Θ Δ σ}
                → Val Ξℰ Δ (A [ δ ]Ty) Θ σ ρ t 
                ≡ Val Ξℰ Γ A Θ (δ ⨾ σ) (eval* Ξℰ δ ρ) t

  -- This is a terrible rewrite rule, because both the LHS and RHS have
  -- operators that will basically never occur in practice...
  -- We *could* define strengthening operators for our entire syntax, but
  -- that seems kinda miserable?
  []Ty⁺-pres-rw : ∀ {φ : Wk Ξ Ψ} 
                    {ρ : Env Ξℰ (Δ [ φ ]Ctx) (Γ [ φ ]Ctx) (δ [ φ ]Tms)}
                → Val  Ξℰ (Γ [ φ ]Ctx) (A [ φ ]Ty⁺) 
                       (Δ [ φ ]Ctx) (δ [ φ ]Tms) ρ (t [ φ ]⁺) 
                ≡ Val ([ φ ]𝒮ℰ⁻¹ Ξℰ) Γ A Δ δ ([_]ℰ⁻¹_ {δ = δ} φ ρ) t
  
{-# REWRITE id-pres-rw #-}
{-# REWRITE wk-pres-rw #-}
{-# REWRITE []Ty-pres-rw #-}
{-# REWRITE []Ty⁺-pres-rw #-}

SigEnv • = ⊤
SigEnv (Ψ ▷ Γ ⇒ A if t ≔ u ∣ v)
  = Σ⟨ Ξℰ ∶ SigEnv Ψ ⟩× DefVal Ξℰ (if t u v)

lookup𝒮ℰ : ∀ (Ξℰ : SigEnv Ξ) (f : DefVar Ξ Γ A) → DefVal Ξℰ (lookup𝒮 Ξ f)

-- _[_]𝒮ℰ {Ψ = •} tt φ = {!!}
-- _[_]𝒮ℰ {Ψ = Ψ ▷ Γ ⇒ A if t then u else v} (Ψℰ Σ, dⱽ) φ = 
--   Ψℰ [ wk𝒮 ⨾𝒮 φ ]𝒮ℰ

-- Ψℰ [ id𝒮 ]𝒮ℰ    = Ψℰ
-- Ψℰ [ φ ⨾𝒮 ψ ]𝒮ℰ = Ψℰ [ φ ]𝒮ℰ [ ψ ]𝒮ℰ
-- Ψℰ [ wk𝒮 ]𝒮ℰ    = {!   !} Σ, {!!}

-- defⱽ uⱽ vⱽ [ φ ]Def𝒱 
--   = defⱽ (λ ψ ρ t~ → uⱽ (φ ⨾𝒮 ψ) ρ t~) 
--          (λ ψ ρ t~ → vⱽ (φ ⨾𝒮 ψ) ρ t~) 


-- We need signature environments because recursively calling, e.g.
-- |eval (lookup𝒮 f .lhs) ρ| is not structurally recursive in |call|

-- Except... we can Ford right?
-- Obvious follow-up question: why are signatures even useful then?
-- I think it comes down to just congruence of equality. We make sure
-- to only evaluate the LHS or RHS after the equation holds definitionally,
-- but this means congruence definitely is not satisfied.

lookup𝒮ℰ Ξℰ (coe~ Γ~ A~ f) = {!   !}
lookup𝒮ℰ (Ξℰ Σ, defⱽ uⱽ vⱽ) fz
  -- = {!dⱽ!}
  = defⱽ (λ ρ t~ → {!uⱽ ([ wk𝒮 ]ℰ⁻¹ ρ) _!}) {!!}
lookup𝒮ℰ (Ξℰ Σ, dⱽ) (fs f) 
  using defⱽ uⱽ vⱽ ← lookup𝒮ℰ Ξℰ f
  = defⱽ {!!} {!!} 

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
  = uval _ (callNe {f = f} tᴺᵉ)

eval* Ξℰ (coe~ Δ~ Γ~ δ)  ρ = {!!}
eval* Ξℰ ε               ρ = tt
eval* Ξℰ (δ , t)         ρ = eval* Ξℰ δ ρ Σ, eval Ξℰ t ρ
eval* Ξℰ (δ ,eq t~)      ρ = {!!}

eval Ξℰ (coe~ Γ~ A~ t) ρ = {!   !}
eval Ξℰ (` i)          ρ = {!   !}
eval Ξℰ (ƛ t)          ρ = {!   !}
eval Ξℰ (t · u)        ρ = eval Ξℰ t ρ idᵀʰ (eval Ξℰ u ρ)
eval Ξℰ TT             ρ = TT rfl~
eval Ξℰ FF             ρ = FF rfl~
eval Ξℰ (call f δ)     ρ 
  using δⱽ ← eval* Ξℰ δ ρ
  with eval Ξℰ (lookup𝒮 _ f .scrut) δⱽ
... | tⱽ = eval-call f δⱽ tⱽ (lookup𝒮ℰ Ξℰ f)
