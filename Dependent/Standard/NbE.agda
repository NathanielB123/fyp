{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils

open import Dependent.Standard.Strict

module Dependent.Standard.NbE where 

data Ne : ∀ Γ A → Tm Γ A → Set
data Nf : ∀ Γ A → Tm Γ A → Set

data Ne where
  coe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Ne Γ₁ A₁ t₁ → Ne Γ₂ A₂ t₂

  `_  : ∀ i → Ne Γ A (` i)
  _·_ : Ne Γ (Π A B) t → Nf Γ A u → Ne Γ (B [ < u > ]T) (t · u)
  if  : Ne Γ 𝔹 t → Nf Γ (A [ < TT > ]T) u → Nf Γ (A [ < FF > ]T) v
      → Ne Γ (A [ < t > ]T) (if t u v)

data Nf where
  coe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂

  ne : Ne Γ 𝔹 t → Nf Γ 𝔹 t
  ƛ_ : Nf (Γ , A) B t → Nf Γ (Π A B) (ƛ t)
  TT : Nf Γ 𝔹 TT
  FF : Nf Γ 𝔹 FF

data 𝔹Val : ∀ Γ {A} → Tm Γ A → Set where
  TT : Tm~ Γ~ A~ t TT → 𝔹Val Γ t
  FF : Tm~ Γ~ B~ t FF → 𝔹Val Γ t
  ne : Ty~ Γ~ A 𝔹 → Ne Γ A t → 𝔹Val Γ t

coe𝔹Val : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → 𝔹Val Γ₁ t₁ → 𝔹Val Γ₂ t₂
coe𝔹Val Γ~ A~ t~ (TT t~′)   = TT (sym~ t~ ∙~ t~′)
coe𝔹Val Γ~ A~ t~ (FF t~′)   = FF (sym~ t~ ∙~ t~′)
coe𝔹Val Γ~ A~ t~ (ne A~′ t) = ne (sym~ A~ ∙~ A~′) (coe~ Γ~ A~ t~ t)

q𝔹Val : 𝔹Val Γ t → Nf Γ 𝔹 t
q𝔹Val (TT t~)     = coe~ _ _ (sym~ t~) TT
q𝔹Val (FF t~)     = coe~ _ _ (sym~ t~) FF
q𝔹Val (ne A~ tᴺᵉ) = coe~ _ _ rfl~ (ne tᴺᵉ)

-- TODO: Prove these disjointness properties
TTFF-disj : Tm~ Γ~ A~ TT FF → ⊥
TTne-disj : Ne Γ 𝔹 TT → ⊥
FFne-disj : Ne Γ 𝔹 FF → ⊥

variable
  A~₁ A~₂ : Ty~ Γ~ A₁ A₂
  t~₁ t~₂ : Tm~ Γ~ A~ t₁ t₂
  tᴺᵉ₁ tᴺᵉ₂ : Ne Γ A t

-- We technically could use renamings rather than thinnings, but for SCDef
-- we definitely need thinnings, so might as well practice!
data Thin : ∀ Δ Γ → Tms Δ Γ → Set where
  coe~  : ∀ Δ~ Γ~ → Tms~ Δ~ Γ~ δ₁ δ₂ → Thin Δ₁ Γ₁ δ₁ → Thin Δ₂ Γ₂ δ₂

  ε     : Thin ε ε ε
  _^ᵀʰ_ : Thin Δ Γ δ → ∀ A → Thin (Δ , (A [ δ ]T)) (Γ , A) (δ ^ A)
  _⁺ᵀʰ_ : Thin Δ Γ δ → ∀ A → Thin (Δ , A) Γ (δ ⁺ A)

idᵀʰ : Thin Γ Γ id
idᵀʰ {Γ = ε}     = ε
idᵀʰ {Γ = Γ , A} = idᵀʰ ^ᵀʰ A

wkᵀʰ : Thin (Γ , A) Γ wk
wkᵀʰ = idᵀʰ ⁺ᵀʰ _

_[_]Nf : Nf Γ A t → Thin Δ Γ δ → Nf Δ (A [ δ ]T) (t [ δ ])
_[_]Ne : Ne Γ A t → Thin Δ Γ δ → Ne Δ (A [ δ ]T) (t [ δ ])

data Mut𝔹Val : 𝔹Val Γ t → 𝔹Val Γ t → Set where
  TT : Mut𝔹Val (TT t~₁) (TT t~₂)
  FF : Mut𝔹Val (FF t~₁) (FF t~₂)
  ne : Mut𝔹Val (ne A~₁ tᴺᵉ₁) (ne A~₂ tᴺᵉ₂)

mut𝔹Val : ∀ (tⱽ₁ tⱽ₂ : 𝔹Val Γ t) → Mut𝔹Val tⱽ₁ tⱽ₂
mut𝔹Val (TT t~₁)      (TT t~₂)      = TT
mut𝔹Val (FF t~₁)      (FF t~₂)      = FF
mut𝔹Val (ne A~₁ tᴺᵉ₁) (ne A~₂ tᴺᵉ₂) = ne
mut𝔹Val (TT t~₁)      (FF t~₂)      
  =  ⊥-elim (TTFF-disj (sym~ t~₁ ∙~ t~₂))
mut𝔹Val (FF t~₁)      (TT t~₂)      
  = ⊥-elim (TTFF-disj (sym~ t~₂ ∙~ t~₁))
mut𝔹Val (TT {Γ~ = Γ~₁} t~₁) (ne {Γ~ = Γ~₂} A~₂ tᴺᵉ₂) 
  = ⊥-elim (TTne-disj (coe~ _ _ (t~₁ ∙~ TT (sym~ Γ~₁ ∙~ Γ~₂)) tᴺᵉ₂))
mut𝔹Val (ne {Γ~ = Γ~₁} A~₁ tᴺᵉ₁) (TT {Γ~ = Γ~₂}  t~₂)      
  = ⊥-elim (TTne-disj (coe~ _ _ (t~₂ ∙~ TT (sym~ Γ~₂ ∙~ Γ~₁)) tᴺᵉ₁))
mut𝔹Val (FF {Γ~ = Γ~₁} t~₁) (ne {Γ~ = Γ~₂} A~₂ tᴺᵉ₂) 
  = ⊥-elim (FFne-disj (coe~ _ _ (t~₁ ∙~ FF (sym~ Γ~₁ ∙~ Γ~₂)) tᴺᵉ₂))
mut𝔹Val (ne {Γ~ = Γ~₁} A~₁ tᴺᵉ₁) (FF {Γ~ = Γ~₂} t~₂)      
  = ⊥-elim (FFne-disj (coe~ _ _ (t~₂ ∙~ FF (sym~ Γ~₂ ∙~ Γ~₁)) tᴺᵉ₁))

data Env : ∀ Δ Γ → Tms Δ Γ → Set
Val      : ∀ Γ (A : Ty Γ) Δ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]T) → Env Δ Γ δ → Set
eval     : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ (t [ δ ]) ρ
eval*    : ∀ δ (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)

variable
  ρ ρ₁ ρ₂  : Env Δ Γ δ
  tⱽ uⱽ vⱽ uⱽ₁ uⱽ₂  : Val Γ A Δ δ t ρ
   

data Env where
  coe~ : ∀ Δ~ Γ~ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Env Δ₁ Γ₁ δ₁ → Env Δ₂ Γ₂ δ₂

  ε   : Env Δ ε ε
  _,_ : ∀ (ρ : Env Δ Γ δ) → Val Γ A Δ δ t ρ → Env Δ (Γ , A) (δ , t)

idℰ : Env Γ Γ id

uval : ∀ A {t} → Ne Δ (A [ δ ]T) t → Val Γ A Δ δ t ρ
qval : ∀ A {t} → Val Γ A Δ δ t ρ → Nf Δ (A [ δ ]T) t

_[_]ℰ : Env Δ Γ δ → Thin Θ Δ σ → Env Θ Γ (δ ⨾ σ)
_[_]𝒱 : Val Γ A Δ δ t ρ → ∀ (σᵀʰ : Thin Θ Δ σ) 
      → Val Γ A Θ (δ ⨾ σ) (t [ σ ]) (ρ [ σᵀʰ ]ℰ)

idℰ {Γ = ε}     = ε
idℰ {Γ = Γ , A} = (_[_]ℰ {σ = wk} idℰ wkᵀʰ) , uval A (` vz)

-- TODO: Prove these lemmas and stop using the mutual hack
postulate [id]ℰ : ρ [ idᵀʰ ]ℰ ≡ ρ
{-# REWRITE [id]ℰ #-}

if-Val : ∀ Γ (A B : Ty Γ) Δ (δ : Tms Δ Γ) {u[]} 
       → Tm Δ (if u[] (A [ δ ]T) (B [ δ ]T)) 
       → ∀ (ρ : Env Δ Γ δ) → Val Γ 𝔹 Δ δ u[] ρ → Set

Val Γ (coe~ Γ~ A) Δ δ t ρ 
  = Val _ A Δ (coe~ rfl~ (sym~ Γ~) δ) (coe~ rfl~ (sym~ coh [ coh ]T~) t) 
              (coe~ rfl~ (sym~ Γ~) coh ρ)
Val Γ 𝔹           Δ δ t ρ = 𝔹Val Δ t
Val Γ (Π A B)     Δ δ t ρ 
  = ∀ {Θ γ} (γᵀʰ : Thin Θ Δ γ) {u}
      (uⱽ : Val Γ A Θ (δ ⨾ γ) u (ρ [ γᵀʰ ]ℰ))
  → Val (Γ , A) B Θ ((δ ⨾ γ) , u) ((t [ γ ]) · u) ((ρ [ γᵀʰ ]ℰ) , uⱽ)
Val Γ (if b A B)  Δ δ t ρ = if-Val Γ A B Δ δ t ρ (eval b ρ)

-- Special case of |coe𝒱|
env-irr    : ∀ A {t} → Val Γ A Δ δ t ρ₁ → Val Γ A Δ δ t ρ₂
env-irr-if : ∀ A B {t} {uⱽ₁ : Val Γ 𝔹 Δ δ u ρ₁} {uⱽ₂ : Val Γ 𝔹 Δ δ u ρ₂}
           → Mut𝔹Val uⱽ₁ uⱽ₂
           → if-Val Γ A B Δ δ t ρ₁ uⱽ₁
           → if-Val Γ A B Δ δ t ρ₂ uⱽ₂

coe𝒱→ : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂)  
      → Tm~ Δ~ (A~ [ δ~ ]T~) t₁ t₂
      → Val Γ₁ A₁ Δ₁ δ₁ t₁ ρ₁ → Val Γ₂ A₂ Δ₂ δ₂ t₂ ρ₂

coe𝒱← : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂)  
      → Tm~ Δ~ (A~ [ δ~ ]T~) t₁ t₂
      → Val Γ₂ A₂ Δ₂ δ₂ t₂ ρ₂ → Val Γ₁ A₁ Δ₁ δ₁ t₁ ρ₁

if-Val Γ A B Δ δ {u[]} t ρ (TT u~)  
  = Val Γ A Δ δ (coe~ rfl~ (if u~ coh coh ∙~ ifTT ∙~ sym~ coh) t) ρ
if-Val Γ A B Δ δ {u[]} t ρ (FF u~)  
  = Val Γ B Δ δ (coe~ rfl~ (if u~ coh coh ∙~ ifFF ∙~ sym~ coh) t) ρ
if-Val Γ A B Δ δ {u[]} t ρ (ne _ _) 
  = Ne Δ (if u[] (A [ δ ]T) (B [ δ ]T)) t

env-irr (coe~ Γ~ A) tⱽ = env-irr A tⱽ  
env-irr 𝔹           tⱽ = tⱽ
env-irr (Π A B)     tⱽ γᵀʰ uⱽ = env-irr B (tⱽ γᵀʰ (env-irr A uⱽ))
env-irr (if b A B)  tⱽ = env-irr-if A B (mut𝔹Val bⱽ₁ bⱽ₂) tⱽ
  where bⱽ₁ = eval b _
        bⱽ₂ = eval b _

env-irr-if A B TT tⱽ = env-irr A tⱽ
env-irr-if A B FF tⱽ = env-irr B tⱽ
env-irr-if A B ne tⱽ = tⱽ

-- This will be a massive pain to implement, because we have to induct on both
-- types mutually and rule-out impossible cases like |Ty~ Γ~ 𝔹 (Π A B)|.
coe𝒱→ A~ δ~ t~ = {!!}
coe𝒱← A~ δ~ t~ = {!!}

shift𝒱₁ : ∀ A (δ : Tms Δ Γ) (σ : Tms Θ Δ) {ρ₁ ρ₂ t} 
        → Val Γ A Θ (δ ⨾ σ) t ρ₁ → Val Δ (A [ δ ]T) Θ σ t ρ₂
shift𝒱₂ : ∀ A (δ : Tms Δ Γ) (σ : Tms Θ Δ) {ρ₁ ρ₂ t} 
        → Val Δ (A [ δ ]T) Θ σ t ρ₁ → Val Γ A Θ (δ ⨾ σ) t ρ₂

shift𝒱₁ (coe~ Γ~ A) δ σ {ρ₁ = ρ₁} {ρ₂ = ρ₂} tⱽ
  = stⱽ′
  where tⱽ′ = coe𝒱→ {ρ₂ = (coe~ rfl~ (sym~ Γ~) (coh ⨾~ rfl~) ρ₁)} 
                    (rfl~ {A = A}) 
                    (sym~ coh ∙~ coh ⨾~ rfl~) coh tⱽ
        stⱽ = shift𝒱₁ A (coe~ rfl~ (sym~ Γ~) δ) σ 
                      {ρ₂ = ρ₂}
                      tⱽ′
        stⱽ′ = coe𝒱→ {A₁ = (A [ coe~ rfl~ (sym~ Γ~) δ ]T)} 
                     (coh [ sym~ coh ]T~)
                     rfl~ (sym~ coh ∙~ sym~ coh)
                     stⱽ
shift𝒱₁ 𝔹           δ σ tⱽ = tⱽ
shift𝒱₁ (Π A B)     δ σ tⱽ {_} {γ} γᵀʰ {u} uⱽ 
  = shift𝒱₁ B (δ ^ A) ((σ ⨾ γ) , u) 
            (tⱽ γᵀʰ (shift𝒱₂ A δ (σ ⨾ γ) uⱽ))
shift𝒱₁ (if b A B)  δ σ tⱽ = {!   !}

shift𝒱₂ (coe~ Γ~ A) δ σ tⱽ = {!   !}
shift𝒱₂ 𝔹           δ σ tⱽ = tⱽ
shift𝒱₂ (Π A B)     δ σ tⱽ {_} {γ} γᵀʰ {u} uⱽ 
  = shift𝒱₂ B (δ ^ A) ((σ ⨾ γ) , u) (tⱽ γᵀʰ (shift𝒱₁ A δ (σ ⨾ γ) uⱽ))
shift𝒱₂ (if b A B)  δ σ tⱽ = {!   !}

lookupℰ : ∀ (i : Var Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ (lookup i δ) ρ
lookupℰ (coe~ Γ~ A~ i)  ρ                 = {!   !}
lookupℰ i               (coe~ Δ~ Γ~ δ~ ρ) = {!   !}
lookupℰ (vz {A = A})    (_,_ {δ = δ} {t = u} ρ uⱽ) 
  = shift𝒱₁ A wk (δ , u) uⱽ
lookupℰ (vs {B = B} i)  (_,_ {δ = δ} {t = u} ρ uⱽ)  
  = shift𝒱₁ B wk (δ , u) (lookupℰ i ρ)

eval (coe~ Γ~ A~ t) ρ = coe𝒱→ A~ (sym~ coh) (coh [ sym~ coh ]~) tⱽ′
  where tⱽ′ = eval t (coe~ rfl~ (sym~ Γ~) coh ρ)
eval (` i)          ρ = lookupℰ i ρ
eval {A = Π A B} (ƛ t) ρ γᵀʰ {u} uⱽ
  = coe𝒱→ rfl~ rfl~ (sym~ (β {t = t [ (_ ⨾ _) ^ _ ]} {u = u})) tuⱽ
  where tuⱽ = eval t ((ρ [ γᵀʰ ]ℰ) , uⱽ)
eval {δ = δ} (_·_ {B = B} t u) ρ 
  = shift𝒱₁ B < u > δ (eval t ρ idᵀʰ (eval u ρ))
eval TT         ρ = TT rfl~
eval FF         ρ = FF rfl~
eval (if t u v) ρ = {!   !}

uval (coe~ Γ~ A) tᴺᵉ 
  = uval A (coe~ rfl~ (sym~ coh [ coh ]T~) coh tᴺᵉ)
uval 𝔹           tᴺᵉ            = ne rfl~ tᴺᵉ
uval (Π A B)     tᴺᵉ γᵀʰ {u} uⱽ = uval B ((tᴺᵉ [ γᵀʰ ]Ne) · qval A uⱽ)
uval (if b A B)  tᴺᵉ = {!   !}

qval (coe~ Γ~ A)     tⱽ = coe~ rfl~ (coh [ sym~ coh ]T~) (sym~ coh) tᴺᶠ
  where tᴺᶠ = qval A tⱽ
qval 𝔹               tⱽ = q𝔹Val tⱽ
qval {δ = δ }(Π A B) tⱽ = coe~ rfl~ rfl~ (sym~ η) tᴺᶠ 
  where vzⱽ = uval {δ = δ ⁺ (A [ δ ]T)} A (` vz)
        tvz = tⱽ wkᵀʰ vzⱽ
        tᴺᶠ = Nf.ƛ qval B tvz
qval (if b A B)      tⱽ = {!   !}

norm : ∀ t → Nf Γ A t
norm t = qval {δ = id} _ (eval t idℰ)

