{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Strict

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
  Γᵀᴿ : TRS Γ

data RwVar : TRS Γ → PreNe Γ 𝔹 t → Bool → Set where
  rz : RwVar (Γᵀᴿ ▷ tᴾᴺᵉ >rw b) tᴾᴺᵉ b
  rs : RwVar Γᵀᴿ tᴾᴺᵉ b₁ → RwVar (Γᵀᴿ ▷ uᴾᴺᵉ >rw b₂) tᴾᴺᵉ b₁

record ValidTRS (Γ : Ctx Ψ) : Set where
  field
    trs    : TRS Γ
    sound  : RwVar {t = t} trs tᴾᴺᵉ b → Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹
    compl  : EqVar Γ t b → ∀ (tᴾᴺᵉ : PreNe Γ 𝔹 t) → RwVar trs tᴾᴺᵉ b
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
    {bool}  : Bool
    {ctx~}  : Ctx~ Γ ctx
    {ty~}   : Ty~ ctx~ A 𝔹
    tm~     : Tm~ ctx~ ty~ t ⌜ bool ⌝𝔹

data 𝔹Val : ∀ (Γ : Ctx Ψ) {A} → Tm Γ A → Set where
  TT : Tm~ Γ~ A~ t TT → 𝔹Val Γ t
  FF : Tm~ Γ~ A~ t FF → 𝔹Val Γ t
  ne : Ty~ Γ~ A 𝔹 → Ne Γ A t → 𝔹Val Γ t

_[_]Nf     : Nf Γ A t → Thin Δ Γ δ → Nf Δ (A [ δ ]Ty) (t [ δ ])
_[_]Ne     : Ne Γ A t → Thin Δ Γ δ → Ne Δ (A [ δ ]Ty) (t [ δ ])
_[_]PreNe  : PreNe Γ A t → Thin Δ Γ δ → PreNe Δ (A [ δ ]Ty) (t [ δ ])
_[_]𝔹Val   : 𝔹Val Γ t → Thin Δ Γ δ → 𝔹Val Δ (t [ δ ])

data CheckRwResult (Γᶜ : TRS Γ) (tᴾᴺᵉ : PreNe Γ A t) : Set where
  rw   : RwVar Γᶜ (coe~ rfl~ A~ coh tᴾᴺᵉ) b → CheckRwResult Γᶜ tᴾᴺᵉ
  stk  : (∀ A~ b → ¬ RwVar Γᶜ (coe~ rfl~ A~ coh tᴾᴺᵉ) b) 
       → CheckRwResult Γᶜ tᴾᴺᵉ

checkrw : ∀ (Γᶜ : TRS Γ) (tᴺᵉ : PreNe Γ A t) 
         → CheckRwResult Γᶜ tᴾᴺᵉ

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

Env Ξ Δ •       Δᶜ δ = ⊤
Env Ξ Δ (Γ ▷ A) Δᶜ δ = Σ (Env Ξ Δ Γ Δᶜ (π₁ δ))
                        λ ρ → Val Γ A Δ Δᶜ (π₁ δ) ρ (π₂ δ)
Env Ξ Δ (Γ ▷ t >eq b) Δᶜ δ
  = Env Ξ Δ Γ Δᶜ (π₁eq δ)

idℰ : Env Ξ Γ Γ Γᶜ id

postulate
  id-pres-rw    : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} 
                → eval* {σ = δ} Δᶜ id ρ ≡ ρ
  wk-pres-rw    : ∀ {ρ : Env Ξ Δ (Γ ▷ A) Δᶜ δ} 
                → eval* Δᶜ wk ρ ≡ ρ .fst

  wkeq-pres-rw  : ∀ {ρ : Env Ξ Δ (Γ ▷ t >eq b) Δᶜ δ} 
                → eval* {σ = δ} Δᶜ (wkeq {t = t} {b = b}) ρ ≡ ρ
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


eval* Δᶜ (coe~ Δ~ Γ~ δ)  ρ = {!!}
eval* Δᶜ ε               ρ = tt
eval* Δᶜ (δ , t)         ρ = eval* Δᶜ δ ρ Σ, eval Δᶜ t ρ
eval* Δᶜ (δ ,eq t~)      ρ = eval* Δᶜ δ ρ

eval-call  : ∀  {f : DefVar Ξ Γ A} (ρ : Env Ξ Δ Γ Δᶜ δ)
                (tⱽ : 𝔹Val Δ (lookup𝒮 Ξ f .scrut [ δ ])) 
           → (∀ t~ → Val Γ A Δ Δᶜ δ ρ (lookup𝒮 Ξ f .lhs [ δ ,eq t~ ]))
           → (∀ t~ → Val Γ A Δ Δᶜ δ ρ (lookup𝒮 Ξ f .rhs [ δ ,eq t~ ]))
           → Val Γ A Δ Δᶜ δ ρ (call f δ)
eval-call {f = f} ρ (TT {Γ~ = Γ~} t~)      uⱽ vⱽ 
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-TT {f = f} (t~ ∙~ TT (sym~ Γ~)))) uⱽ′
  where uⱽ′ = uⱽ (t~ ∙~ TT (sym~ Γ~))
eval-call {f = f} ρ (FF {Γ~ = Γ~} t~)      uⱽ vⱽ
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-FF {f = f} (t~ ∙~ FF (sym~ Γ~)))) vⱽ′
  where vⱽ′ = vⱽ (t~ ∙~ FF (sym~ Γ~))
-- Interesting: Because |call| only recurses into the definition 
-- when the equation is satisfied, we don't have any dependence on quoting
-- here.
eval-call {f = f} ρ (ne A~ tᴺᵉ) uⱽ vⱽ 
  = uvalpre _ (callNe {f = f} tᴺᵉ)

eval Δᶜ (coe~ Γ~ A~ t) ρ = {!   !}
eval Δᶜ (` i)          ρ = {!   !}
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
  | (λ t~ →  eval {δ = (δ ⨾ σ) ,eq t~} Δᶜ (lookup𝒮 _ f .lhs) δⱽ)
  | (λ t~ →  eval {δ = (δ ⨾ σ) ,eq t~} Δᶜ (lookup𝒮 _ f .rhs) δⱽ)
... | tⱽ | uⱽ | vⱽ = eval-call {f = f} δⱽ tⱽ uⱽ vⱽ

∥_∥⊥ : ⊥ → ∥⊥∥
∥_∥⊥ ()

-- This should be provable by introducing small-step reduction
-- i.e. no reductions are applicable to a |PreNe| except for rewriting,
-- so if we can map from declarative to algorithmic conversion, then we
-- can extract out the |RwVar|
inv-lemma : PreNe Γ A t → Tm~ Γ~ A~ t ⌜ b ⌝𝔹 → EqVar Γ (coe~ Γ~ A~ t) b

⌜⌝𝔹~ : Tm~ Γ~ 𝔹 ⌜ b ⌝𝔹 ⌜ b ⌝𝔹

rwVal Γᶜ tᴾᴺᵉ with checkrw (Γᶜ .trs) tᴾᴺᵉ
... | rw {b = b} r 
  = inr (closed (coh ∙~ Γᶜ .soundTR r))
... | stk ¬r 
  = inl  (box λ b Γ~ A~ t~ → ∥ ¬r _ _
         (Γᶜ .complTR (inv-lemma tᴾᴺᵉ (t~ ∙~ ⌜⌝𝔹~ {Γ~ = sym~ Γ~})) 
         (coe~ _ _ coh tᴾᴺᵉ)) ∥⊥)

uvalpre {Δᶜ = Δᶜ} A tᴾᴺᵉ with rwVal Δᶜ tᴾᴺᵉ 
... | inl tᴾ          = uval A (tᴾᴺᵉ Σ, tᴾ)
-- We need a |coe𝒱| that takes a context equation to make this work properly
... | inr (closed {bool = true}   t~) = {!!}
... | inr (closed {bool = false}  t~) = {!!}

uval (coe~ Γ~ A) tᴺᵉ = {!   !}
uval 𝔹 tᴺᵉ = ne rfl~ tᴺᵉ
uval (Π A B) {t = t}     tᴺᵉ γᵀʰ {u} uⱽ 
  = uvalpre B (PreNe._·_ {t = t [ _ ]} (tᴺᵉ  [ γᵀʰ ]Ne) (qval A uⱽ))
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
