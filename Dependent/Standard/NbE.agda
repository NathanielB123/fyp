{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

-- |Strict| or |StrictAlt| syntaxes work here
open import Dependent.Standard.Strict

-- Normalisation by Evaluation for dependent types
--
-- We skip proving preservation of conversion (in fact, we don't even define
-- convertability of normal/neutral forms or values) because the setoid
-- (congruence) boilerplate is boring. Instead, I plan on justifying
-- preservation of congruence in the report, considering only the
-- non-trivial cases.
--
-- Even without these preservation results, because we do at least ensure
-- normal/neutral forms are always convertible with their index, we can
-- still get through most of the proof without cheating. The problem
-- is |coe𝒱|.
module Dependent.Standard.NbE where 

variable
  Γ′ Ξ : Ctx

-- Extra rewrites
-- See https://github.com/agda/agda/issues/7602
rw₁ : ∀ {δ : Tms Γ Γ′} {σ : Tms Δ Γ} {γ : Tms Θ Δ}
        {t : Tm Γ (Π (A [ δ ]Ty) (B [ δ ^ A ]Ty))}
    → t [ σ ] [ γ ] ≡ t [ σ ⨾ γ ]
rw₁ {t = t} = [][] {t = t}
{-# REWRITE rw₁ #-}

rw₂ : lookup vz δ [ σ ] ≡ lookup vz (δ ⨾ σ)
rw₂ = lookup-⨾ {i = vz}
{-# REWRITE rw₂ #-}

data Ne : ∀ Γ A → Tm Γ A → Set
data Nf : ∀ Γ A → Tm Γ A → Set

data Ne where
  coe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Ne Γ₁ A₁ t₁ → Ne Γ₂ A₂ t₂

  `_  : ∀ i → Ne Γ A (` i)
  _·_ : Ne Γ (Π A B) t → Nf Γ A u → Ne Γ (B [ < u > ]Ty) (t · u)
  if  : ∀ A {t u v} 
      → Ne Γ 𝔹 t → Nf Γ (A [ < TT > ]Ty) u → Nf Γ (A [ < FF > ]Ty) v
      → Ne Γ (A [ < t > ]Ty) (if A t u v)

data Nf where
  coe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂

  ne𝔹  : Ne Γ 𝔹 t → Nf Γ 𝔹 t
  neIF : Ne Γ 𝔹 u → Ne Γ (IF u A B) t → Nf Γ (IF u A B) t
  ƛ_   : Nf (Γ ▷ A) B t → Nf Γ (Π A B) (ƛ t)
  TT   : Nf Γ 𝔹 TT
  FF   : Nf Γ 𝔹 FF

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
q𝔹Val (ne A~ tᴺᵉ) = coe~ _ _ rfl~ (ne𝔹 tᴺᵉ)

variable
  A~₁ A~₂ : Ty~ Γ~ A₁ A₂
  t~₁ t~₂ : Tm~ Γ~ A~ t₁ t₂
  tᴺᵉ₁ tᴺᵉ₂ : Ne Γ A t

-- We technically could use renamings rather than thinnings, but for SCDef
-- we definitely need thinnings, so might as well practice!
data Thin : ∀ Δ Γ → Tms Δ Γ → Set where
  coe~  : ∀ Δ~ Γ~ → Tms~ Δ~ Γ~ δ₁ δ₂ → Thin Δ₁ Γ₁ δ₁ → Thin Δ₂ Γ₂ δ₂

  ε     : Thin • • ε
  _^ᵀʰ_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A) (δ ^ A)
  _⁺ᵀʰ_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ A) Γ (δ ⨾ wk)

variable
  δᵀʰ σᵀʰ γᵀʰ : Thin Δ Γ δ

idᵀʰ : Thin Γ Γ id
idᵀʰ {Γ = •}     = ε
idᵀʰ {Γ = Γ ▷ A} = idᵀʰ ^ᵀʰ A

wkᵀʰ : Thin (Γ ▷ A) Γ wk
wkᵀʰ = idᵀʰ ⁺ᵀʰ _

_⨾ᵀʰ_ : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)

coe~ Δ~ Γ~ δ~ δᵀʰ ⨾ᵀʰ σᵀʰ 
  = coe~ rfl~ Γ~ (δ~ ⨾~ sym~ coh) 
         (δᵀʰ ⨾ᵀʰ coe~ rfl~ (sym~ Δ~) coh σᵀʰ)
ε ⨾ᵀʰ σᵀʰ 
  = coe~ rfl~ rfl~ εη σᵀʰ
(δᵀʰ ^ᵀʰ A) ⨾ᵀʰ (σᵀʰ ^ᵀʰ _) 
  = (δᵀʰ ⨾ᵀʰ σᵀʰ) ^ᵀʰ A
(δᵀʰ ⁺ᵀʰ A) ⨾ᵀʰ (_^ᵀʰ_ {δ = σ} σᵀʰ A) 
  = (δᵀʰ ⨾ᵀʰ σᵀʰ) ⁺ᵀʰ (A [ σ ]Ty)
δᵀʰ ⨾ᵀʰ (σᵀʰ ⁺ᵀʰ A)         
  = (δᵀʰ ⨾ᵀʰ σᵀʰ) ⁺ᵀʰ A 
(δᵀʰ ^ᵀʰ A) ⨾ᵀʰ coe~ Θ~ Δ~ σ~ σᵀʰ 
  = {!!}
(δᵀʰ ⁺ᵀʰ A) ⨾ᵀʰ coe~ Θ~ Δ~ σ~ σᵀʰ 
  = {!!}

_[_]Nf   : Nf Γ A t → Thin Δ Γ δ → Nf Δ (A [ δ ]Ty) (t [ δ ])
_[_]Ne   : Ne Γ A t → Thin Δ Γ δ → Ne Δ (A [ δ ]Ty) (t [ δ ])
_[_]𝔹Val : 𝔹Val Γ t → Thin Δ Γ δ → 𝔹Val Δ (t [ δ ])

coe~ Γ~ A~ t~ tᴺᶠ [ δᵀʰ ]Nf 
  = coe~ rfl~ (A~ [ sym~ coh ]Ty~) (t~ [ sym~ coh ]~) 
         (tᴺᶠ [ coe~ rfl~ (sym~ Γ~) coh δᵀʰ ]Nf)
ne𝔹 tᴺᵉ      [ δᵀʰ ]Nf = ne𝔹 (tᴺᵉ [ δᵀʰ ]Ne)
neIF uᴺᵉ tᴺᵉ [ δᵀʰ ]Nf = neIF (uᴺᵉ [ δᵀʰ ]Ne) (tᴺᵉ [ δᵀʰ ]Ne)
(ƛ tᴺᶠ)      [ δᵀʰ ]Nf = ƛ (tᴺᶠ [ δᵀʰ ^ᵀʰ _ ]Nf)
TT           [ δᵀʰ ]Nf = TT
FF           [ δᵀʰ ]Nf = FF

lookupᵀʰ : ∀ (i : Var Γ A) → Thin Δ Γ δ → Var Δ (A [ δ ]Ty)
lookupᵀʰ i      (δᵀʰ ⁺ᵀʰ A) = vs {B = _ [ _ ]Ty} (lookupᵀʰ i δᵀʰ)
lookupᵀʰ vz     (δᵀʰ ^ᵀʰ A) = vz
lookupᵀʰ (vs i) (δᵀʰ ^ᵀʰ A) = vs {B = _ [ _ ]Ty} (lookupᵀʰ i δᵀʰ)
lookupᵀʰ (coe~ Γ~ Δ~ i) δᵀʰ 
  = {!   !}
lookupᵀʰ i (coe~ Δ~ Γ~ δ~ δᵀʰ) 
  = {!   !}

lookupᵀʰ~ : ∀ (i : Var Γ A) (δᵀʰ : Thin Δ Γ δ)
          → Tm~ rfl~ rfl~ (lookup i δ) (` lookupᵀʰ i δᵀʰ)
lookupᵀʰ~ i      (δᵀʰ ⁺ᵀʰ A) = lookupᵀʰ~ i δᵀʰ [ wk~ rfl~ ]~
lookupᵀʰ~ vz     (δᵀʰ ^ᵀʰ A) = rfl~
lookupᵀʰ~ (vs i) (δᵀʰ ^ᵀʰ A) = lookupᵀʰ~ i δᵀʰ [ wk~ rfl~ ]~
lookupᵀʰ~ (coe~ Γ~ Δ~ i) δᵀʰ 
  = {!   !}
lookupᵀʰ~ i (coe~ Δ~ Γ~ δ~ δᵀʰ) 
  = {!   !}

coe~ Γ~ A~ t~ tᴺᵉ [ δᵀʰ ]Ne 
  = coe~ rfl~ (A~ [ sym~ coh ]Ty~) (t~ [ sym~ coh ]~) 
        (tᴺᵉ [ coe~ rfl~ (sym~ Γ~) coh δᵀʰ ]Ne)
(` i) [ δᵀʰ ]Ne = coe~ rfl~ rfl~ (sym~ (lookupᵀʰ~ i δᵀʰ)) (` lookupᵀʰ i δᵀʰ)
_[_]Ne {δ = δ} (_·_ {B = B} tᴺᵉ uᴺᶠ) δᵀʰ
  = _·_ {B = B [ δ ^ _ ]Ty} (tᴺᵉ [ δᵀʰ ]Ne) (uᴺᶠ [ δᵀʰ ]Nf)
if A {u = u} {v = v} tᴺᵉ uᴺᶠ vᴺᶠ [ δᵀʰ ]Ne 
  = if (A [ _ ^ 𝔹 ]Ty) (tᴺᵉ [ δᵀʰ ]Ne) 
       (_[_]Nf {t = u} uᴺᶠ δᵀʰ) (_[_]Nf {t = v} vᴺᶠ δᵀʰ)

TT t~     [ δᵀʰ ]𝔹Val = TT {Γ~ = rfl~} (t~ [ coh ]~)
FF t~     [ δᵀʰ ]𝔹Val = FF {Γ~ = rfl~} (t~ [ coh ]~)
ne A~ tᴺᵉ [ δᵀʰ ]𝔹Val = ne {Γ~ = rfl~} (A~ [ coh ]Ty~) (tᴺᵉ [ δᵀʰ ]Ne)

Env      : ∀ Δ Γ → Tms Δ Γ → Set
Val      : ∀ Γ A Δ δ → Env Δ Γ δ → Tm Δ (A [ δ ]Ty) → Set
eval     : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ ρ (t [ δ ])
eval*    : ∀ δ (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)

-- Motives
PCtx : Ctx → Set₁
PCtx Γ = ∀ Δ → Tms Δ Γ → Set

PTy : PCtx Γ → Ty Γ → Set₁
PTy Γᴾ A = ∀ Δ δ → Γᴾ Δ δ → Tm Δ (A [ δ ]Ty) → Set

PTm : ∀ (Γᴾ : PCtx Γ) → PTy Γᴾ A → Tm Γ A → Set
PTm Γᴾ Aᴾ t = ∀ Δ δ (ρ : Γᴾ Δ δ) → Aᴾ Δ δ ρ (t [ δ ]) 

PTms : ∀ (Δᴾ : PCtx Δ) (Γᴾ : PCtx Γ) → Tms Δ Γ → Set
PTms Δᴾ Γᴾ δ = ∀ Θ σ (ρ : Δᴾ Θ σ) → Γᴾ Θ (δ ⨾ σ)

pCtx : ∀ Γ → PCtx Γ
pCtx Γ Δ δ = Env Δ Γ δ

pTy : ∀ A → PTy (pCtx Γ) A
pTy A Δ δ ρ t = Val _ A Δ δ ρ t 

pTm : ∀ t → PTm (pCtx Γ) (pTy A) t
pTm t Δ δ ρ = eval t ρ

pTms : ∀ δ → PTms (pCtx Δ) (pCtx Γ) δ
pTms δ Θ σ ρ = eval* δ ρ

variable
  Γᴾ Δᴾ : PCtx Γ
  Aᴾ Bᴾ : PTy Γᴾ A

if-Val : ∀ Γ A B Δ δ (ρ : Env Δ Γ δ) {u[]} 
       → Tm Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) 
       → Val Γ 𝔹 Δ δ ρ u[] → Set

variable
  ρ ρ₁ ρ₂  : Env Δ Γ δ
  tⱽ uⱽ vⱽ uⱽ₁ uⱽ₂  : Val Γ A Δ δ ρ t

Env Δ •       δ = ⊤
Env Δ (Γ ▷ A) δ = Σ (Env Δ Γ (π₁ δ))
                  λ ρ → Val Γ A Δ (π₁ δ) ρ (π₂ δ)

idℰ : Env Γ Γ id

uval : ∀ A {t} → Ne Δ (A [ δ ]Ty) t → Val Γ A Δ δ ρ t
qval : ∀ A {t} → Val Γ A Δ δ ρ t → Nf Δ (A [ δ ]Ty) t

uval-if : ∀ A B {u[] t} (uⱽ : Val Γ 𝔹 Δ δ ρ u[])
        → Ne Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) t
        → if-Val Γ A B Δ δ ρ t uⱽ
qval-if : ∀ A B {u[] t} (uⱽ : Val Γ 𝔹 Δ δ ρ u[])
        → if-Val Γ A B Δ δ ρ t uⱽ
        → Nf Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) t

_[_]ℰ : Env Δ Γ δ → Thin Θ Δ σ → Env Θ Γ (δ ⨾ σ)
_∋_[_]𝒱 : ∀ A {t} → Val Γ A Δ δ ρ t → ∀ (σᵀʰ : Thin Θ Δ σ) 
        → Val Γ A Θ (δ ⨾ σ) (ρ [ σᵀʰ ]ℰ) (t [ σ ])

_[_]ℰ {Γ = •}     tt        σᵀʰ = tt
_[_]ℰ {Γ = Γ ▷ A} (ρ Σ, tⱽ) σᵀʰ 
  = ρ [ σᵀʰ ]ℰ Σ, (A ∋ tⱽ [ σᵀʰ ]𝒱)

idℰ {Γ = •}     = tt
idℰ {Γ = Γ ▷ A} = (_[_]ℰ {δ = id} {σ = wk} idℰ wkᵀʰ) Σ, uval A (` vz)

-- TODO: Prove these lemmas and stop using the mutual hack
postulate [id]ℰ : ∀ {ρ : Env Δ Γ δ} → ρ [ idᵀʰ ]ℰ ≡ ρ
{-# REWRITE [id]ℰ #-}
postulate [][]ℰ : ∀ {ρ : Env Δ Γ δ} {σᵀʰ : Thin Θ Δ σ} {γᵀʰ : Thin Ξ Θ γ}
                → ρ [ σᵀʰ ]ℰ [ γᵀʰ ]ℰ ≡ ρ [ σᵀʰ ⨾ᵀʰ γᵀʰ ]ℰ
{-# REWRITE [][]ℰ #-}

-- In a QII(R)T encoding, these coercions would merely be transports.
-- Of course, transporting would only be justified as long as we proved that
-- |Env|/|Val| preserves path constructors.
--
-- In our setoid-based setting, to prove preservation of the equivalence
-- relation our raw syntax, we need to explicitly define equivalence of
-- environments and values, which I am not super excited to do...
--
-- Therefore, I just postulate the coercions. We also don't ask for an equation
-- between environments because that would of course also require defining
-- an equivalence relation. Given values are unique up-to-coherence anyway,
-- I don't think this is such a big deal.
postulate
  coeℰ : ∀ Δ~ Γ~ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Env Δ₁ Γ₁ δ₁ → Env Δ₂ Γ₂ δ₂

  coe𝒱 : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂)  
        → Tm~ Δ~ (A~ [ δ~ ]Ty~) t₁ t₂
        → Val Γ₁ A₁ Δ₁ δ₁ ρ₁ t₁ → Val Γ₂ A₂ Δ₂ δ₂ ρ₂ t₂

Val Γ (coe~ Γ~ A) Δ δ ρ t 
  = Val _ A Δ (coe~ rfl~ (sym~ Γ~) δ) (coeℰ rfl~ (sym~ Γ~) coh ρ)
        (coe~ rfl~ (sym~ coh [ coh ]Ty~) t)     
Val Γ 𝔹           Δ δ ρ t = 𝔹Val Δ t
Val Γ (Π A B)     Δ δ ρ t 
  = ∀ {Θ γ} (γᵀʰ : Thin Θ Δ γ) {u}
      (uⱽ : Val Γ A Θ (δ ⨾ γ) (ρ [ γᵀʰ ]ℰ) u)
  → Val (Γ ▷ A) B Θ ((δ ⨾ γ) , u) ((ρ [ γᵀʰ ]ℰ) Σ, uⱽ) ((t [ γ ]) · u)
Val Γ (IF b A B)  Δ δ ρ t = if-Val Γ A B Δ δ ρ t (eval b ρ)

_∋_[_]𝒱 {δ = δ} {ρ = ρ} {σ = σ} (coe~ Γ~ A) {t = t} tⱽ σᵀʰ
  = coe𝒱 {t₁ = coe~ rfl~ (sym~ coh [ coh ]Ty~) t [ σ ]}
         {t₂ = coe~ rfl~ (sym~ coh [ coh ]Ty~) (t [ σ ])}
         --  coe~ rfl~ (sym~ Γ~) (coh ⨾~ sym~ coh)
         -- (ρ [ coe~ rfl~ (sym~ rfl~) coh σᵀʰ ]ℰ)
        --  {ρ₁ = coe~ rfl~ (sym~ Γ~) coh ρ [ σᵀʰ ]ℰ}
        --  {ρ₂ = coe~ rfl~ (sym~ Γ~) coh (ρ [ σᵀʰ ]ℰ)}
         rfl~ 
         (sym~ coh ⨾~ rfl~ ∙~ coh) 
         (sym~ (coh  {A~ = (sym~ coh [ coh ]Ty~)}) [ rfl~ ]~ ∙~ coh) 
         (A ∋ tⱽ [ σᵀʰ ]𝒱)
𝔹         ∋ tⱽ [ σᵀʰ ]𝒱 = tⱽ [ σᵀʰ ]𝔹Val
Π A B     ∋ tⱽ [ σᵀʰ ]𝒱 = λ γᵀʰ uⱽ → {!tⱽ (σᵀʰ ⨾ᵀʰ γᵀʰ) uⱽ!}
IF b A B  ∋ tⱽ [ σᵀʰ ]𝒱 = {!   !}

if-Val Γ A B Δ δ ρ {u[]} t (TT u~)  
  = Val Γ A Δ δ ρ (coe~ rfl~ (IF u~ coh coh ∙~ IF-TT ∙~ sym~ coh) t)
if-Val Γ A B Δ δ ρ {u[]} t (FF u~)  
  = Val Γ B Δ δ ρ (coe~ rfl~ (IF u~ coh coh ∙~ IF-FF ∙~ sym~ coh) t)
if-Val Γ A B Δ δ ρ {u[]} t (ne _ _) 
  = Ne Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) t

_,ᴾ_ : ∀ Γᴾ → PTy Γᴾ A → PCtx (Γ ▷ A)
Γᴾ ,ᴾ Aᴾ = λ Δ δ → Σ (Γᴾ Δ (wk ⨾ δ)) λ ρ → Aᴾ Δ (wk ⨾ δ) ρ ((` vz) [ δ ])

wkᴾ : ∀ {Aᴾ : PTy Γᴾ A} → PTms (Γᴾ ,ᴾ Aᴾ) Γᴾ (wk {A = A})
wkᴾ = λ θ σ ρ → ρ .fst

idᴾ : PTms Γᴾ Γᴾ id
idᴾ = λ θ σ ρ → ρ

_[_]ᴾ : PTy Γᴾ A → PTms Δᴾ Γᴾ δ → PTy Δᴾ (A [ δ ]Ty)
Aᴾ [ δᴾ ]ᴾ = λ Θ σ ρ t → Aᴾ Θ _ (δᴾ Θ σ ρ) t

-- We need that |Val| preserves substitution, and |eval*| preserves |id|
-- and |wk|. The nice way to solve this would be to define an eliminator for
-- the inductive-recursive syntax that allows specifying how non-canonical
-- elements should be interpreted, plus laws to ensure their computational
-- behaviour is preserved.
postulate
  -- These non-"rw" versions are just to illustrate what rewrites are doing.
  -- These are exactly the "methods" for |id|, |wk| and |_[_]Ty| that we would 
  -- give if we used an explicit eliminator. 
  id-pres  : pTms (id {Γ = Γ}) ≡ idᴾ
  wk-pres  : pTms (wk {A = A}) ≡ wkᴾ {Aᴾ = pTy A}
  []Ty-pres : ∀ {δ : Tms Δ Γ} → pTy (A [ δ ]Ty) ≡ pTy A [ pTms δ ]ᴾ

id-pres-rw  : ∀ {ρ : Env Δ Γ δ} → eval* id ρ ≡ ρ
id-pres-rw {ρ = ρ} = cong-app (cong-app (cong-app id-pres _) _) ρ
wk-pres-rw   : ∀ {ρ : Env Δ (Γ ▷ A) δ} → eval* wk ρ ≡ ρ .fst
wk-pres-rw {ρ = ρ} = cong-app (cong-app (cong-app wk-pres _) _) ρ
[]Ty-pres-rw  : Val Δ (A [ δ ]Ty) Θ σ ρ t ≡ Val Γ A Θ (δ ⨾ σ) (eval* δ ρ) t
[]Ty-pres-rw {ρ = ρ} {t = t}
  = cong-app (cong-app (cong-app (cong-app []Ty-pres _) _) ρ) t

{-# REWRITE id-pres-rw #-}
{-# REWRITE wk-pres-rw #-}
{-# REWRITE []Ty-pres-rw #-}

lookupℰ : ∀ (i : Var Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ ρ (lookup i δ)
lookupℰ (coe~ Γ~ A~ i)  ρ         
  = coe𝒱 A~ (sym~ coh) (lookup~ coh (sym~ coh)) 
         (lookupℰ i (coeℰ rfl~ (sym~ Γ~) coh ρ))
lookupℰ (vz {A = A})    (ρ Σ, uⱽ) = uⱽ
lookupℰ (vs {B = B} i)  (ρ Σ, uⱽ) = lookupℰ i ρ

eval* (coe~ Δ~ Γ~ δ) ρ 
  = coeℰ rfl~ Γ~ (coh ⨾~ sym~ coh) (eval* δ (coeℰ rfl~ (sym~ Δ~) coh ρ))
eval* ε               ρ = tt
eval* {σ = σ} (δ , t) ρ = eval* δ ρ Σ, eval t ρ

eval-if : ∀ A {t u v} (tⱽ : Val Γ 𝔹 Δ δ ρ t)
        → Val (Γ ▷ 𝔹) A Δ (δ , TT) (ρ Σ, TT rfl~) u
        → Val (Γ ▷ 𝔹) A Δ (δ , FF) (ρ Σ, FF rfl~) v
        → Val (Γ ▷ 𝔹) A Δ (δ , t) (ρ Σ, tⱽ) (if (A [ δ ^ 𝔹 ]Ty) t u v)
eval-if {δ = δ} A (TT {Γ~ = Γ~} t~)     uⱽ vⱽ 
  = coe𝒱 (rfl~ {A = A}) 
         (_,_ {A~ = 𝔹} (rfl~ {δ = δ}) (TT Γ~ ∙~ sym~ t~)) 
         (sym~ (𝔹β₁ (A [ δ ^ 𝔹 ]Ty)) 
            ∙~ if (rfl~ {A = A [ δ ^ 𝔹 ]Ty}) (TT Γ~ ∙~ sym~ t~) rfl~ rfl~)
         uⱽ
eval-if {δ = δ} A (FF {Γ~ = Γ~} t~) uⱽ vⱽ 
  = coe𝒱 (rfl~ {A = A}) 
         (_,_ {A~ = 𝔹} (rfl~ {δ = δ}) (FF Γ~ ∙~ sym~ t~)) 
         (sym~ (𝔹β₂ (A [ δ ^ 𝔹 ]Ty)) 
            ∙~ if (rfl~ {A = A [ δ ^ 𝔹 ]Ty}) (FF Γ~ ∙~ sym~ t~) rfl~ rfl~)
         vⱽ
eval-if {δ = δ} A (ne A~ tᴺᵉ) uⱽ vⱽ 
  = uval A (if (A [ δ ^ 𝔹 ]Ty) tᴺᵉ (qval A uⱽ) (qval A vⱽ))

eval (coe~ Γ~ A~ t) ρ 
  = coe𝒱 A~ (sym~ coh) (coh [ sym~ coh ]~)
         (eval t (coeℰ rfl~ (sym~ Γ~) coh ρ))
eval (` i)          ρ = lookupℰ i ρ
eval (ƛ t) ρ γᵀʰ {u = u} uⱽ 
  = coe𝒱 rfl~ rfl~ (sym~ (Πβ {t = t [ (_ ⨾ _) ^ _ ]} {u = u}))
         (eval {δ = (_ ⨾ _) , _} t ((ρ [ γᵀʰ ]ℰ) Σ, uⱽ))
eval (t · u)    ρ = eval t ρ idᵀʰ (eval u (ρ [ idᵀʰ ]ℰ))
eval TT         ρ = TT rfl~
eval FF         ρ = FF rfl~
eval {δ = δ} (if A t u v) ρ with eval t ρ | eval u ρ | eval v ρ
... | tⱽ | uⱽ | vⱽ = eval-if A tⱽ uⱽ vⱽ
    
uval (coe~ Γ~ A) tᴺᵉ 
  = uval A (coe~ rfl~ (sym~ coh [ coh ]Ty~) coh tᴺᵉ)
uval 𝔹           tᴺᵉ            = ne rfl~ tᴺᵉ
uval (Π A B)     tᴺᵉ γᵀʰ {u} uⱽ = uval B ((tᴺᵉ [ γᵀʰ ]Ne) · qval A uⱽ)
uval (IF b A B)  tᴺᵉ            = uval-if A B (eval b _) tᴺᵉ

uval-if A B (TT u~)     tᴺᵉ = uval A tᴺᵉ′
  where tᴺᵉ′ = coe~ rfl~ (IF u~ coh coh ∙~ IF-TT ∙~ sym~ coh) coh tᴺᵉ
uval-if A B (FF u~)     tᴺᵉ = uval B tᴺᵉ′
  where tᴺᵉ′ = coe~ rfl~ (IF u~ coh coh ∙~ IF-FF ∙~ sym~ coh) coh tᴺᵉ
uval-if A B (ne A~ uᴺᵉ) tᴺᵉ = tᴺᵉ

qval (coe~ Γ~ A)     tⱽ = coe~ rfl~ (coh [ sym~ coh ]Ty~) (sym~ coh) tᴺᶠ
  where tᴺᶠ = qval A tⱽ
qval 𝔹               tⱽ = q𝔹Val tⱽ
qval (Π A B)         tⱽ = coe~ rfl~ rfl~ (sym~ Πη) tᴺᶠ 
  where vzⱽ = uval {δ = _ ⨾ wk {A = (A [ _ ]Ty)}} A (` vz)
        tvz = tⱽ wkᵀʰ vzⱽ
        tᴺᶠ = ƛ qval B tvz
qval (IF b A B)      tⱽ = qval-if A B (eval b _) tⱽ

qval-if A B (TT {Γ~ = Γ~} u~) tⱽ 
  = coe~ rfl~ 
         (  coh {Γ~ = Γ~} ∙~ sym~ IF-TT 
         ∙~ IF (sym~ u~) (sym~ coh) (sym~ {Γ~ = Γ~} coh)) 
         (sym~ coh) tᴺᶠ
  where tᴺᶠ = qval A tⱽ
qval-if A B (FF {Γ~ = Γ~} u~) tⱽ
  = coe~ rfl~ 
         (  coh {Γ~ = Γ~} ∙~ sym~ IF-FF 
         ∙~ IF (sym~ u~) (sym~ {Γ~ = Γ~} coh) (sym~ coh)) 
         (sym~ coh) tᴺᶠ
  where tᴺᶠ = qval B tⱽ
qval-if A B (ne A~ uᴺᵉ) tⱽ = neIF uᴺᵉ tⱽ

norm : ∀ t → Nf Γ A t
norm t = qval {δ = id} _ (eval t idℰ)
