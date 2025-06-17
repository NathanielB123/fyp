{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Strict

-- Note: Currently missing a lot of cases pertaining to e.g. large elimination
-- See Dependent/Standard/Nbe.agda for more detail on how to deal with
-- these ("Smart Case" doesn't change much)
module Dependent.SCDef.NbE where

data Thin {Ξ} : ∀ Δ Γ → Tms {Ξ = Ξ} Δ Γ → Set where
  coe~  : ∀ Δ~ Γ~ → Tms~ Δ~ Γ~ δ₁ δ₂ → Thin Δ₁ Γ₁ δ₁ → Thin Δ₂ Γ₂ δ₂

  ε         : Thin • • ε
  _^ᵀʰ_     : Thin Δ Γ δ → ∀ A 
            → Thin (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A) (δ ^ A)
  _^ᵀʰ_>eq_ : Thin Δ Γ δ → ∀ t b
            → Thin (Δ ▷ t [ δ ] >eq b) (Γ ▷ t >eq b) (δ ^ t >eq b)
  _⁺ᵀʰ_     : Thin Δ Γ δ 
            → ∀ A → Thin (Δ ▷ A) Γ (δ ⨾ wk)

idᵀʰ   : Thin Γ Γ id
_⨾ᵀʰ_  : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)
wkᵀʰ   : Thin (Γ ▷ A) Γ wk

Ne : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set
data PreNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set
data Nf    : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set 

variable
  tᴾᴺᵉ uᴾᴺᵉ t₁ᴾᴺᵉ t₂ᴾᴺᵉ : PreNe Γ A t
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

data TRS (Γ : Ctx Ξ) : Set where
  •       : TRS Γ
  _▷_>rw_ : TRS Γ → PreNe Γ 𝔹 t → Bool → TRS Γ

coeTRS : Ctx~ Γ₁ Γ₂ → TRS Γ₁ → TRS Γ₂
coeTRS Γ~ •                  = •
coeTRS Γ~ (Γᵀᴿ ▷ tᴾᴺᵉ >rw b) = coeTRS Γ~ Γᵀᴿ ▷ coe~ Γ~ 𝔹 coh tᴾᴺᵉ >rw b

variable
  Γᵀᴿ Γ₁ᵀᴿ Γ₂ᵀᴿ : TRS Γ  
  t₃ᴾᴺᵉ : PreNe Γ A t
  t₁₂~ t₂₃~ : Tm~ _ _ t₁ t₂

-- We define equivalence on pre-neutral terms as "equivalence up to coherence" 
-- I.e. syntactic equality of the underlying untyped objects. 
-- This is obviously stricter than conversion.
data PreNe~  : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂
             → PreNe Γ₁ A₁ t₁ → PreNe Γ₂ A₂ t₂ → Prop where
  rfl~ : PreNe~ rfl~ rfl~ rfl~ tᴾᴺᵉ tᴾᴺᵉ
  sym~ : PreNe~ Γ~ A~ t~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ
       → PreNe~ (sym~ Γ~) (sym~ A~) (sym~ t~) t₂ᴾᴺᵉ t₁ᴾᴺᵉ
  _∙~_ : PreNe~ Γ₁₂~ A₁₂~ t₁₂~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ 
       → PreNe~ Γ₂₃~ A₂₃~ t₂₃~ t₂ᴾᴺᵉ t₃ᴾᴺᵉ
       → PreNe~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) (t₁₂~ ∙~ t₂₃~) t₁ᴾᴺᵉ t₃ᴾᴺᵉ

  coh  : PreNe~ Γ~ A~ t~ tᴾᴺᵉ (coe~ Γ~ A~ t~ tᴾᴺᵉ)
  -- Todo: Congruence cases

data DecPreNe~ (Γ~ : Ctx~ Γ₁ Γ₂) 
               (t₁ᴾᴺᵉ : PreNe {Ξ = Ξ} Γ₁ A₁ t₁) 
               (t₂ᴾᴺᵉ : PreNe {Ξ = Ξ} Γ₂ A₂ t₂) : Set where
  conv  : PreNe~ Γ~ A~ t~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ →  DecPreNe~ Γ~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ
  ¬conv : (∀ {A~ t~} → PreNe~ Γ~ A~ t~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ → ∥⊥∥) 
        → DecPreNe~ Γ~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ

-- Syntactic equality of pre-neutral terms (equivalence up to coherence) is
-- decidable (defined mutually with deciding equality of neutral/normal forms).
-- We follow Altenkirch and Kaposi's "Normalisation by Evaluation for Type 
-- Theory in Type Theory" and synthesise the equation between the types of the 
-- neutrals.
-- Implementing the failure cases here requires proving disjointness of 
-- constructors, which is certainly possible, but a bit painful...
synCmp : ∀ Γ~ (t₁ᴾᴺᵉ : PreNe Γ₁ A₁ t₁) (t₂ᴾᴺᵉ : PreNe Γ₂ A₂ t₂)
       → DecPreNe~ Γ~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ

-- We define TRS equivalence with only the congruence cases in order to get 
-- a nicer induction principle
data TRS~  : Ctx~ Γ₁ Γ₂ → TRS Γ₁ → TRS Γ₂ → Prop where
  •      : TRS~ Γ~ • •
  _▷_>rw : TRS~ Γ~ Γ₁ᵀᴿ Γ₂ᵀᴿ → PreNe~ Γ~ 𝔹 t~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ
         → TRS~ Γ~ (Γ₁ᵀᴿ ▷ t₁ᴾᴺᵉ >rw b) (Γ₂ᵀᴿ ▷ t₂ᴾᴺᵉ >rw b)

rflTRS~ : TRS~ rfl~ Γᵀᴿ Γᵀᴿ
rflTRS~ {Γᵀᴿ = •}                = •
rflTRS~ {Γᵀᴿ = Γᵀᴿ ▷ tᴾᴺᵉ >rw b} = rflTRS~ ▷ rfl~ >rw

data RwVar : TRS {Ξ = Ξ} Γ → PreNe Γ A t → Bool → Set where
  coe~  : TRS~ Γ~ Γ₁ᵀᴿ Γ₂ᵀᴿ
        → PreNe~ Γ~ A~ t~ t₁ᴾᴺᵉ t₂ᴾᴺᵉ
        → RwVar Γ₁ᵀᴿ t₁ᴾᴺᵉ b → RwVar Γ₂ᵀᴿ t₂ᴾᴺᵉ b

  rz : RwVar (Γᵀᴿ ▷ tᴾᴺᵉ >rw b) tᴾᴺᵉ b
  rs : RwVar Γᵀᴿ tᴾᴺᵉ b₁ → RwVar (Γᵀᴿ ▷ uᴾᴺᵉ >rw b₂) tᴾᴺᵉ b₁

record ValidTRS (Γ : Ctx Ψ) : Set where
  field
    trs    : TRS Γ
    sound  : ∀ (r : RwVar {t = t} trs tᴾᴺᵉ b) 
           → Tm~ Γ~ A~ t ⌜ b ⌝𝔹
    compl  : Tm~ Γ~ A~ t ⌜ b ⌝𝔹 → ∀ (tᴾᴺᵉ : PreNe Γ A t) 
           → RwVar trs tᴾᴺᵉ b
open ValidTRS using (trs) renaming (sound to soundTR; compl to complTR)

variable
  Γᶜ Δᶜ Θᶜ : ValidTRS Γ

_[_]TRS : ValidTRS Γ → Thin Δ Γ δ → ValidTRS Δ

def-incon : Ctx Ψ → Prop
def-incon Γ = Tm~ (rfl~ {Γ = Γ}) rfl~ TT FF

data ComplTRS (Γ : Ctx Ψ) : Set where
  compl  : ValidTRS Γ → ComplTRS Γ
  !!     : def-incon Γ → ComplTRS Γ

record 𝔹Valᵗᶠ (Γ : Ctx Ξ) {A} (t : Tm Γ A) : Set where
  constructor closed
  field
    {ctx}   : Ctx Ξ
    {ctx~}  : Ctx~ Γ ctx
    {ty~}   : Ty~ ctx~ A 𝔹
    bool    : Bool
    tm~     : Tm~ ctx~ ty~ t ⌜ bool ⌝𝔹

data 𝔹Val : ∀ (Γ : Ctx Ψ) {A} → Tm Γ A → Set where
  TT : Tm~ Γ~ A~ t TT → 𝔹Val Γ t
  FF : Tm~ Γ~ A~ t FF → 𝔹Val Γ t
  ne : Ty~ Γ~ A 𝔹 → Ne Γ A t → 𝔹Val Γ t

_[_]Nf     : Nf Γ A t → Thin Δ Γ δ → Nf Δ (A [ δ ]Ty) (t [ δ ])
_[_]Ne     : Ne Γ A t → Thin Δ Γ δ → Ne Δ (A [ δ ]Ty) (t [ δ ])
_[_]PreNe  : PreNe Γ A t → Thin Δ Γ δ → PreNe Δ (A [ δ ]Ty) (t [ δ ])
_[_]𝔹Val   : 𝔹Val Γ t → Thin Δ Γ δ → 𝔹Val Δ (t [ δ ])

data 𝔹Val~ : ∀ Γ~ A~ → Tm~ {Ξ = Ξ} Γ~ A~ t₁ t₂ 
           → 𝔹Val Γ₁ {A = A₁} t₁ → 𝔹Val Γ₂ {A = A₂} t₂ 
           → Prop where
  rfl~    : ∀ {tⱽ : 𝔹Val Γ t} → 𝔹Val~ rfl~ rfl~ rfl~ tⱽ tⱽ
  -- TODO: This is very specialised to the implementation of |eval|.
  -- Like, these equations should be provable, but I am not sure they are the
  -- best choice as direct constructors
  TT-coh  : 𝔹Val~ rfl~ rfl~ (t~ ∙~ TT (sym~ Γ~)) (TT t~) (TT rfl~)
  FF-coh  : 𝔹Val~ rfl~ rfl~ (t~ ∙~ FF (sym~ Γ~)) (FF t~) (FF rfl~)

data DecRw (Γᵀᴿ : TRS Γ) (tᴾᴺᵉ : PreNe Γ A t) : Set where
  rw   : RwVar Γᵀᴿ tᴾᴺᵉ b → DecRw Γᵀᴿ tᴾᴺᵉ
  stk  : (∀ b → RwVar Γᵀᴿ tᴾᴺᵉ b → ∥⊥∥) → DecRw Γᵀᴿ tᴾᴺᵉ

checkrw  : ∀ (Γᵀᴿ : TRS Γ) (tᴾᴺᵉ : PreNe Γ A t) 
         → DecRw Γᵀᴿ tᴾᴺᵉ

rwVal : ValidTRS Γ → PreNe Γ A t → Box (predNe Γ A t) ⊎ 𝔹Valᵗᶠ Γ t

Env    : ∀ Ξ Δ Γ → ValidTRS Δ → Tms {Ξ = Ξ} Δ Γ → Set
Val    : ∀ Γ A Δ Δᶜ δ
       → Env Ξ Δ Γ Δᶜ δ → Tm Δ (A [ δ ]Ty) → Set
eval   : ∀ Δᶜ (t : Tm Γ A) (ρ : Env Ξ Δ Γ Δᶜ δ) 
       → Val Γ A Δ Δᶜ δ ρ (t [ δ ])
eval*  : ∀ Θᶜ δ (ρ : Env Ξ Θ Δ Θᶜ σ) → Env Ξ Θ Γ Θᶜ (δ ⨾ σ)

variable
  ρ : Env Ξ Δ Γ Δᶜ δ

uvalpre  : ∀ A {t} → PreNe Δ (A [ δ ]Ty) t → Val Γ A Δ Δᶜ δ ρ t
uval     : ∀ A {t} → Ne Δ (A [ δ ]Ty) t → Val Γ A Δ Δᶜ δ ρ t
qval     : ∀ A {t} → Val Γ A Δ Δᶜ δ ρ t → Nf Δ (A [ δ ]Ty) t

postulate
  coe𝒱 : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} (A~ : Ty~ rfl~ A₁ A₂)
        → Tm~ Δ~ (A~ [ rfl~ ]Ty~) t₁ t₂
       → Val Γ A₁ Δ Δᶜ δ ρ t₁ → Val Γ A₂ Δ Δᶜ δ ρ t₂

_[_]ℰ    : Env Ξ Δ Γ Δᶜ δ → ∀ (σᵀʰ : Thin Θ Δ σ) 
         → Env Ξ Θ Γ (Δᶜ [ σᵀʰ ]TRS) (δ ⨾ σ)

variable
  δᵀʰ σᵀʰ : Thin Δ Γ δ

postulate
  [id]TRS : Γᶜ [ idᵀʰ ]TRS ≡ Γᶜ
  [][]TRS : Γᶜ [ δᵀʰ ]TRS [ σᵀʰ ]TRS ≡ Γᶜ [ δᵀʰ ⨾ᵀʰ σᵀʰ ]TRS
{-# REWRITE [id]TRS [][]TRS #-}

variable
  Τ : Ctx Ξ

postulate
  [id]ℰ  : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} → ρ [ idᵀʰ ]ℰ ≡ ρ
  [][]ℰ  : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} 
             {σᵀʰ : Thin Θ Δ σ} {γᵀʰ : Thin Τ Θ γ}
         → ρ [ σᵀʰ ]ℰ [ γᵀʰ ]ℰ ≡ ρ [ σᵀʰ ⨾ᵀʰ γᵀʰ ]ℰ
{-# REWRITE [id]ℰ #-}
{-# REWRITE [][]ℰ #-}

>eqEnv  : ∀ (t : Tm Γ 𝔹) (b : Bool) δ
        → Env Ξ Δ Γ Δᶜ (π₁eq {t = t} {b = b} δ) → Prop

Env Ξ Δ •       Δᶜ δ = ⊤
Env Ξ Δ (Γ ▷ A) Δᶜ δ 
  = Σ⟨ ρ ∶ Env Ξ Δ Γ Δᶜ (π₁ δ) ⟩× Val Γ A Δ Δᶜ (π₁ δ) ρ (π₂ δ)
Env Ξ Δ (Γ ▷ t >eq b) Δᶜ δ
  = Σ⟨ ρ ∶ Env Ξ Δ Γ Δᶜ (π₁eq δ) ⟩× Box (>eqEnv t b δ ρ)

idℰ : Env Ξ Γ Γ Γᶜ id

postulate
  id-pres-rw    : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} 
                → eval* {σ = δ} Δᶜ id ρ ≡ ρ
  wk-pres-rw    : ∀ {ρ : Env Ξ Δ (Γ ▷ A) Δᶜ δ} 
                → eval* Δᶜ wk ρ ≡ ρ .fst

  wkeq-pres-rw  : ∀ {ρ : Env Ξ Δ (Γ ▷ t >eq b) Δᶜ δ} 
                → eval* {σ = δ} Δᶜ (wkeq {t = t} {b = b}) ρ ≡ ρ .fst
  []Ty-pres-rw  : ∀ {ρ : Env Ξ Θ Δ Θᶜ σ}
                → Val Δ (A [ δ ]Ty) Θ Θᶜ σ ρ t 
                ≡ Val Γ A Θ Θᶜ (δ ⨾ σ) (eval* {σ = σ} Θᶜ δ ρ) t

{-# REWRITE id-pres-rw #-}
{-# REWRITE wk-pres-rw #-}
{-# REWRITE wkeq-pres-rw #-}
{-# REWRITE []Ty-pres-rw #-}

Val Γ (coe~ Γ~ A) Δ Δᶜ δ ρ t 
  = {!!}
Val Γ 𝔹          Δ Δᶜ δ ρ t = 𝔹Val Δ t
Val Γ (IF b A B) Δ Δᶜ δ ρ t = {!if-Val Γ A B Δ δ ρ t (eval b ρ)!}
Val Γ (Π A B)    Δ Δᶜ δ ρ t 
  = ∀ {Θ γ} (γᵀʰ : Thin Θ Δ γ) {u}
      (uⱽ : Val Γ A Θ (Δᶜ [ γᵀʰ ]TRS) (δ ⨾ γ) (_[_]ℰ {Γ = Γ} ρ γᵀʰ) u)
  → Val (Γ ▷ A) B Θ (Δᶜ [ γᵀʰ ]TRS) ((δ ⨾ γ) , u) 
        ((_[_]ℰ {Γ = Γ} ρ γᵀʰ) Σ, uⱽ) ((t [ γ ]) · u)

⌜_⌝𝔹𝒱 : ∀ b → 𝔹Val Γ ⌜ b ⌝𝔹
⌜ true   ⌝𝔹𝒱 = TT rfl~
⌜ false  ⌝𝔹𝒱 = FF rfl~

>eqEnv t b δ ρ = 𝔹Val~ rfl~ rfl~ (π₂eq δ) (eval _ t ρ) ⌜ b ⌝𝔹𝒱

eval* Δᶜ (coe~ Δ~ Γ~ δ)  ρ = {!!}
eval* Δᶜ ε               ρ = tt
eval* Δᶜ (δ , t)         ρ = eval* Δᶜ δ ρ Σ, eval Δᶜ t ρ
-- Need a mutual soundness proof here!
eval* Δᶜ (δ ,eq t~)      ρ = eval* Δᶜ δ ρ Σ, box {!!}

eval-call  : ∀  {f : DefVar Ξ Γ A} (ρ : Env Ξ Δ Γ Δᶜ δ)
                (tⱽ : 𝔹Val Δ (lookup𝒮 Ξ f .scrut [ δ ])) 
           → (∀ t~ → 𝔹Val~ rfl~ rfl~ t~ tⱽ (TT rfl~) 
             → Val Γ A Δ Δᶜ δ ρ (lookup𝒮 Ξ f .lhs [ δ ,eq t~ ]))
           → (∀ t~ → 𝔹Val~ rfl~ rfl~ t~ tⱽ (FF rfl~) 
             → Val Γ A Δ Δᶜ δ ρ (lookup𝒮 Ξ f .rhs [ δ ,eq t~ ]))
           → Val Γ A Δ Δᶜ δ ρ (call f δ)
eval-call {f = f} ρ (TT {Γ~ = Γ~} t~) uⱽ vⱽ 
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-TT {f = f} (t~ ∙~ TT (sym~ Γ~)))) uⱽ′
  where uⱽ′ = uⱽ (t~ ∙~ TT (sym~ Γ~)) (TT-coh {Γ~ = Γ~})
eval-call {f = f} ρ (FF {Γ~ = Γ~} t~) uⱽ vⱽ
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-FF {f = f} (t~ ∙~ FF (sym~ Γ~)))) vⱽ′
  where vⱽ′ = vⱽ (t~ ∙~ FF (sym~ Γ~)) (FF-coh {Γ~ = Γ~})
-- Interesting: Because |call| only recurses into the definition 
-- when the equation is satisfied, we don't have any dependence on quoting
-- here.
eval-call {f = f} ρ (ne A~ tᴺᵉ) uⱽ vⱽ 
  = uvalpre _ (callNe {f = f} tᴺᵉ)

lookupℰ : ∀ (i : Var Γ A) (ρ : Env Ξ Δ Γ Δᶜ δ) → Val Γ A Δ Δᶜ δ ρ (lookup i δ)

eval Δᶜ (coe~ Γ~ A~ t) ρ = {!   !}
eval Δᶜ (` i)          ρ = lookupℰ i ρ
eval {δ = δ} Δᶜ (ƛ t) ρ {γ = γ} γᵀʰ {u = u} uⱽ 
  = coe𝒱 rfl~ (sym~ (Πβ {t = t [ (_ ⨾ _) ^ _ ]} {u = u}))
         (eval {δ = (_ ⨾ _) , u} (Δᶜ [ γᵀʰ ]TRS) t 
               ((_[_]ℰ {δ = δ} ρ γᵀʰ) Σ, uⱽ))
eval Δᶜ (t · u)        ρ = eval Δᶜ t ρ idᵀʰ (eval Δᶜ u ρ)
eval Δᶜ TT             ρ = TT rfl~
eval Δᶜ FF             ρ = FF rfl~
eval {δ = σ} Δᶜ (call f δ) ρ 
  using δⱽ ← eval* Δᶜ δ ρ
  with eval Δᶜ (lookup𝒮 _ f .scrut) δⱽ 
  | (λ t~ tⱽ~ →  eval  {δ = (δ ⨾ σ) ,eq t~} Δᶜ 
                       (lookup𝒮 _ f .lhs) (δⱽ Σ, box tⱽ~))
  | (λ t~ tⱽ~ →  eval  {δ = (δ ⨾ σ) ,eq t~} Δᶜ 
                       (lookup𝒮 _ f .rhs) (δⱽ Σ, box tⱽ~))
... | tⱽ | uⱽ | vⱽ = eval-call {f = f} δⱽ tⱽ uⱽ vⱽ


⌜⌝𝔹~ : Tm~ Γ~ 𝔹 ⌜ b ⌝𝔹 ⌜ b ⌝𝔹
⌜⌝𝔹~ {b = true}   = TT _
⌜⌝𝔹~ {b = false}  = FF _

¬rw• : RwVar • tᴾᴺᵉ b → ∥⊥∥
¬rw• (coe~ • tᴾᴺᵉ~ r) = ¬rw• r

¬rw▷ : (RwVar Γᵀᴿ tᴾᴺᵉ b₂ → ∥⊥∥) 
     → (∀ {Γ~ A~ t~} → PreNe~ Γ~ A~ t~ tᴾᴺᵉ uᴾᴺᵉ → ∥⊥∥) 
     → RwVar (Γᵀᴿ ▷ uᴾᴺᵉ >rw b₁) tᴾᴺᵉ b₂ → ∥⊥∥
¬rw▷ ¬r ¬~ (coe~ (Γᵀᴿ~ ▷ uᴾᴺᵉ~ >rw) tᴾᴺᵉ~ r) 
  = ¬rw▷ (λ r′ → ¬r (coe~ Γᵀᴿ~ tᴾᴺᵉ~ r′)) 
         (λ ~ → ¬~ ((sym~ tᴾᴺᵉ~ ∙~ ~) ∙~ uᴾᴺᵉ~))
         r
¬rw▷ ¬r ¬~ rz     = ¬~ rfl~
¬rw▷ ¬r ¬~ (rs r) = ¬r r

checkrw •                  tᴾᴺᵉ 
  = stk (λ _ r → ¬rw• r)
checkrw (Γᵀᴿ ▷ uᴾᴺᵉ >rw b) tᴾᴺᵉ with checkrw Γᵀᴿ tᴾᴺᵉ
... | rw  r  = rw (rs r)
... | stk ¬r with synCmp rfl~ tᴾᴺᵉ uᴾᴺᵉ
... | conv  tᴾᴺᵉ~  = rw (coe~ rflTRS~ (sym~ tᴾᴺᵉ~) rz)
... | ¬conv ¬~     = stk λ where _ r → ¬rw▷ (¬r _) ¬~ r

rwVar-lemma : ∀ (r : RwVar {Ξ = Ξ} {Γ = Γ} {A = A} Γᵀᴿ tᴾᴺᵉ b)
            →  Σ⟨ Γ′ ∶ Ctx Ξ ⟩× Σ⟨ Γ~ ∶ Box (Ctx~ Γ Γ′) 
               ⟩× Box (Ty~ (unbox Γ~) A 𝔹) 
rwVar-lemma (coe~ {Γ~ = Γ~} {A~ = A~} Γᵀᴿ~ tᴾᴺᵉ~ r) 
  using _ Σ, box Γ~′ Σ, box A~′ ← rwVar-lemma r
  = _ Σ, box (sym~ Γ~ ∙~ Γ~′) Σ, box (sym~ A~ ∙~ A~′)
rwVar-lemma rz     = _ Σ, box rfl~ Σ, box rfl~
rwVar-lemma (rs r) = rwVar-lemma r

rwVarTy~  : ∀ (r : RwVar {A = A} Γᵀᴿ tᴾᴺᵉ b)
          → Ty~ (rwVar-lemma r .snd .fst .unbox) A 𝔹
rwVarTy~ r = rwVar-lemma r .snd .snd .unbox

rwVal Γᶜ tᴾᴺᵉ with checkrw (Γᶜ .trs) tᴾᴺᵉ
... | rw {b = b} r 
  = inr  (closed b (Γᶜ .soundTR {A~ = rwVarTy~ r} r))
... | stk ¬r 
  = inl  (box λ b Γ~ A~ t~ → ¬r b (Γᶜ .complTR t~ tᴾᴺᵉ))

-- TODO: Justify this... somehow
postulate
  coe𝒱′ : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} (A~ : Ty~ rfl~ A₁ (A₂ [ δ ]Ty))
        → Tm~ Δ~ A~ t₁ t₂
        → Val Δ A₁ Δ Δᶜ id idℰ t₁ → Val Γ A₂ Δ Δᶜ δ ρ t₂

uvalpre {Δᶜ = Δᶜ} A tᴾᴺᵉ with rwVal Δᶜ tᴾᴺᵉ 
... | inl tᴾ          = uval A (tᴾᴺᵉ Σ, tᴾ)
... | inr (closed {ctx~ = Γ~} {ty~ = A~} b t~) 
  = coe𝒱′ (𝔹 {Γ~ = Γ~} ∙~ sym~ A~) (⌜⌝𝔹~ {Γ~ = Γ~} ∙~ sym~ t~) ⌜ b ⌝𝔹𝒱

uval (coe~ Γ~ A) tᴺᵉ = {!   !}
uval 𝔹 tᴺᵉ = ne rfl~ tᴺᵉ
uval (Π A B) {t = t}     tᴺᵉ γᵀʰ {u} uⱽ 
  = uvalpre B (_·_ {t = t [ _ ]} (tᴺᵉ  [ γᵀʰ ]Ne) (qval A uⱽ))
uval (IF t A B) tᴺᵉ = {!   !}

q𝔹Val : 𝔹Val Γ t → Nf Γ 𝔹 t
q𝔹Val (TT t~)     = coe~ _ _ (sym~ t~) TT
q𝔹Val (FF t~)     = coe~ _ _ (sym~ t~) FF
q𝔹Val (ne A~ tᴺᵉ) = coe~ _ _ rfl~ (ne𝔹 tᴺᵉ)

qval (coe~ Γ~ A)     tⱽ = {!!}
qval 𝔹               tⱽ = q𝔹Val tⱽ
qval (Π A B)         tⱽ = coe~ rfl~ rfl~ (sym~ Πη) tᴺᶠ′
  where vzⱽ = uvalpre {δ = _ ⨾ wk {A = (A [ _ ]Ty)}} A (` vz)
        tᴺᶠ′ = ƛ qval B (tⱽ wkᵀʰ vzⱽ)
qval (IF b A B)      tⱽ = {!!}


-- Obviously missing here is how to actually construct 'ValidTRS's
-- I think a nice first step here would be to prove

inv-lemma : PreNe Γ A t → Tm~ Γ~ A~ t ⌜ b ⌝𝔹 → EqVar Γ (coe~ Γ~ A~ t) b

-- This should be provable by introducing small-step reduction
-- i.e. no reductions are applicable to a |PreNe| except for rewriting,
-- so if we can map from declarative to algorithmic conversion, then we
-- can extract out the |RwVar|
-- Of course, this relies on proving confluence
