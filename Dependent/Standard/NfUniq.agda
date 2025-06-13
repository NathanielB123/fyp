{-# OPTIONS --rewriting --prop --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

open import Dependent.Standard.Strict

-- A sketch of how to prove uniqueness of normal forms using reduction
-- Very unfinished - just indicates the core ideas
module Dependent.Standard.NfUniq where

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

variable
  tᴺᶠ tᴺᶠ′ uᴺᶠ tᴺᶠ₁ tᴺᶠ₂ tᴺᶠ₃ : Nf Γ A t
  tᴺᵉ : Ne Γ A t
  t₁₂~ t₂₃~ : Tm~ _ _ t₁ t₂

⌜_⌝Nf : Nf Γ A t → Tm Γ A
⌜_⌝Ne : Ne Γ A t → Tm Γ A

⌜_⌝Nf~ : ∀ (tᴺᶠ : Nf Γ A t) → Tm~ rfl~ rfl~ ⌜ tᴺᶠ ⌝Nf t

⌜ coe~ Γ~ A~ t~ tᴺᶠ ⌝Nf = coe~ Γ~ A~ ⌜ tᴺᶠ ⌝Nf
⌜ ne𝔹 tᴺᵉ ⌝Nf = ⌜ tᴺᵉ ⌝Ne
⌜ neIF _ tᴺᵉ ⌝Nf = ⌜ tᴺᵉ ⌝Ne
⌜ ƛ tᴺᶠ ⌝Nf = ƛ ⌜ tᴺᶠ ⌝Nf
⌜ TT ⌝Nf = TT
⌜ FF ⌝Nf = FF


⌜ coe~ Γ~ A~ t~ tᴺᵉ ⌝Ne = coe~ Γ~ A~ ⌜ tᴺᵉ ⌝Ne
⌜ ` i              ⌝Ne = ` i
⌜ tᴺᵉ · uᴺᶠ        ⌝Ne 
  = coe~ rfl~ (rfl~ [ < ⌜ uᴺᶠ ⌝Nf~ >~ ]Ty~) (⌜ tᴺᵉ ⌝Ne · ⌜ uᴺᶠ ⌝Nf)
⌜ if A tᴺᵉ uᴺᶠ vᴺᶠ ⌝Ne = if A {!!} {!!} {!!}

data Nf~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂ → Prop
data Ne~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ →  Ne Γ₁ A₁ t₁ → Ne Γ₂ A₂ t₂ → Prop

variable
  Γᵁ Γᵁ₁ Γᵁ₂ : ℕ

data Nf~ where
  rfl~ : Nf~ rfl~ rfl~ rfl~ tᴺᶠ tᴺᶠ
  sym~ : Nf~ Γ~ A~ t~ tᴺᶠ₁ tᴺᶠ₂ → Nf~ (sym~ Γ~) (sym~ A~) (sym~ t~) tᴺᶠ₂ tᴺᶠ₁
  _∙~_ : Nf~ Γ₁₂~ A₁₂~ t₁₂~ tᴺᶠ₁ tᴺᶠ₂ → Nf~ Γ₂₃~ A₂₃~ t₂₃~ tᴺᶠ₂ tᴺᶠ₃
       → Nf~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) (t₁₂~ ∙~ t₂₃~) tᴺᶠ₁ tᴺᶠ₃

  coh : Nf~ Γ~ A~ t~ tᴺᶠ (coe~ Γ~ A~ t~ tᴺᶠ)

data UTm : ℕ → Set where
  `_ : Fin Γᵁ → UTm Γᵁ
  TT FF : UTm Γᵁ
  _·_ : UTm Γᵁ → UTm Γᵁ → UTm Γᵁ
  ƛ_ : UTm (su Γᵁ) → UTm Γᵁ
  if : UTm Γᵁ → UTm Γᵁ → UTm Γᵁ → UTm Γᵁ

variable
  tᵁ tᵁ′ uᵁ : UTm Γᵁ
  Γᵁ≡ : Γᵁ₁ ≡ Γᵁ₂

data _>_ : UTm Γᵁ → UTm Γᵁ → Set

_>*_ : UTm Γᵁ → UTm Γᵁ → Set
_>*_ = _[ _>_ ]*_

len : Ctx → ℕ
len •        = ze
len (Γ ▷ A)  = su (len Γ)

coeUTm : Γᵁ₁ ≡ Γᵁ₂ → UTm Γᵁ₁ → UTm Γᵁ₂
coeUTm p (tᵁ · uᵁ) =  coeUTm p tᵁ · coeUTm p uᵁ
coeUTm p TT        =  TT
coeUTm p FF        =  FF
coeUTm p tᵁ        = subst UTm p tᵁ

coeUTm-cancel :  coeUTm (sym Γᵁ≡) (coeUTm Γᵁ≡ tᵁ) ≡ tᵁ

len~ : Ctx~ Γ₁ Γ₂ → len Γ₁ ≡ len Γ₂

-- Hey look! It's the graph of a the function!
data CtxLen : Ctx → ℕ → Set

ctxLen : CtxLen Γ (len Γ)

ctxLen~ : Ctx~ Γ₁ Γ₂ → CtxLen Γ₁ Γᵁ → CtxLen Γ₂ Γᵁ

variable
  Γl Γl₁ Γl₂ : CtxLen Γ Γᵁ

projVar : CtxLen Γ Γᵁ → Var Γ A → Fin Γᵁ

proj : CtxLen Γ Γᵁ → Tm Γ A → UTm Γᵁ
proj p (coe~ Γ~ A~ t) = proj (ctxLen~ (sym~ Γ~) p) t
proj p (` i)          = ` projVar p i
proj p (ƛ t)          = ƛ proj {!!} t
proj p (t · u)        = proj p t · proj p u
proj p TT             = TT
proj p FF             = FF
proj p (if A t u v)   = if (proj p t) (proj p u) (proj p v)

nf-uniq : Tm~ rfl~ rfl~ ⌜ tᴺᶠ ⌝Nf ⌜ uᴺᶠ ⌝Nf
        → Nf~ rfl~ rfl~ rfl~ tᴺᶠ uᴺᶠ

record _<~>_ (tᵁ uᵁ : UTm Γᵁ) : Prop where 
  constructor conv
  pattern
  field
    reduct : UTm Γᵁ
    lhs>   : tᵁ >* reduct
    rhs>   : uᵁ >* reduct

-- Main trouble here is proving |<~>| is transitive. This requires confluence
-- |Πη| is also problematic, as I'm not sure this can easily be turned into
-- a reduction (at least while maintaining confluence). Probably need
-- to introduce an untyped equiv-modulo-η relation
<~>-pres : Tm~ Γ~ A~ t₁ t₂ → proj Γl₁ t₁ <~> proj Γl₂ t₂
<~>-pres rfl~ = {!   !}
<~>-pres (sym~ t~) = {!   !}
<~>-pres (t~₁ ∙~ t~₂) = {!   !}
<~>-pres coh = {!   !}
<~>-pres (` i) = {!   !}
<~>-pres (ƛ t~) = {!   !}
<~>-pres (t~ · u~) = {!   !}
<~>-pres (TT Γ~) = conv TT rfl* rfl*
<~>-pres (FF Γ~) = {!   !}
<~>-pres (if A~ t~ u~ v~) = {!   !}
<~>-pres (𝔹β₁ A) = {!   !}
<~>-pres (𝔹β₂ A) = {!   !}
<~>-pres Πβ = {!   !}
<~>-pres Πη = {!   !}

-- We prove this by induction on normal forms
nf-irr : ¬ proj Γl ⌜ tᴺᶠ ⌝Nf > tᵁ

nf>* :  proj Γl ⌜ tᴺᶠ ⌝Nf >* tᵁ → proj Γl ⌜ tᴺᶠ ⌝Nf ≡ tᵁ
nf>* rfl* = refl
nf>* {tᴺᶠ = tᴺᶠ} (p ∶> _) with () ← nf-irr {tᴺᶠ = tᴺᶠ} p

TT-not-ne : ¬ proj Γl ⌜ tᴺᵉ ⌝Ne ≡ TT
TT-not-ne {tᴺᵉ = coe~ Γ~ A~ t~ tᴺᵉ} p 
  = TT-not-ne {tᴺᵉ = tᴺᵉ} p

FF-not-ne : ¬ proj Γl ⌜ tᴺᵉ ⌝Ne ≡ FF
FF-not-ne {tᴺᵉ = coe~ Γ~ A~ t~ tᴺᵉ} p 
  = FF-not-ne {tᴺᵉ = tᴺᵉ} p

UTm≡ = cong UTm

-- We prove this by induction on normal forms
-- If we indexed contexts by their length, this would be a LOT easier
syn-coh : ∀ (tᴺᶠ : Nf Γ₁ A₁ t₁) (uᴺᶠ : Nf Γ₂ A₂ t₂)
        → proj Γl₁ ⌜ tᴺᶠ ⌝Nf ≡ proj Γl₂ ⌜ uᴺᶠ ⌝Nf → Nf~ Γ~ A~ t~ tᴺᶠ uᴺᶠ 
syn-coh (ne𝔹 tᴺᵉ) (ne𝔹 uᴺᵉ) = {!   !}
syn-coh (neIF p x₁) (neIF x₂ x₃) = {!   !}
syn-coh (ƛ tᴺᶠ) (ƛ uᴺᶠ) = {!   !}
syn-coh TT TT = {!   !}
syn-coh FF FF = {!   !}
syn-coh FF (ƛ uᴺᶠ) p = {!!}

-- Impossible cases (there are a lot of them...)
syn-coh (ne𝔹 tᴺᵉ) TT p with () ← TT-not-ne {tᴺᵉ = tᴺᵉ} p
syn-coh (ne𝔹 tᴺᵉ) FF p with () ← FF-not-ne {tᴺᵉ = tᴺᵉ} p
syn-coh TT (ne𝔹 uᴺᵉ) = {!   !}
syn-coh FF (ne𝔹 uᴺᵉ) = {!   !}
syn-coh (ne𝔹 x₁) (neIF x₂ x₃) p = {!!}
syn-coh (ne𝔹 x₁) (ƛ uᴺᶠ) p = {!!}
syn-coh (neIF x₁ x₂) (ne𝔹 x₃) p = {!!}
syn-coh (neIF x₁ x₂) (ƛ uᴺᶠ) p = {!!}
syn-coh (neIF x₁ x₂) TT p = {!!}
syn-coh (neIF x₁ x₂) FF p = {!!}
syn-coh (ƛ tᴺᶠ) (ne𝔹 x₁) p = {!!}
syn-coh (ƛ tᴺᶠ) (neIF x₁ x₂) p = {!!}
syn-coh TT (neIF x₁ x₂) p = {!!}
syn-coh FF (neIF x₁ x₂) p = {!!}

-- Coherence cases
syn-coh {t~ = t~} (coe~ Γ~′ A~′ t~′ tᴺᶠ) uᴺᶠ p
  = sym~ (coh {t~ = t~′}) ∙~ syn-coh {t~ = t~′ ∙~ t~} tᴺᶠ uᴺᶠ p
syn-coh tᴺᶠ (coe~ Γ~′ A~′ u~′ uᴺᶠ) = {!   !}

nf-uniq {tᴺᶠ = tᴺᶠ} {uᴺᶠ = uᴺᶠ} t~ 
  using conv red p q ← <~>-pres {Γl₁ = ctxLen} {Γl₂ = ctxLen} t~
  = syn-coh tᴺᶠ uᴺᶠ (nf>* {tᴺᶠ = tᴺᶠ} p ∙ sym (nf>* {tᴺᶠ = uᴺᶠ} q))

nf-uniq-gen : ∀ {tᴺᶠ₁ : Nf Γ₁ A₁ t₁} {tᴺᶠ₂ : Nf Γ₂ A₂ t₂} 
                (t~ : Tm~ Γ~ A~ ⌜ tᴺᶠ₁ ⌝Nf ⌜ tᴺᶠ₂ ⌝Nf)
            → Nf~ Γ~ A~ (sym~ ⌜ tᴺᶠ₁ ⌝Nf~ ∙~ t~ ∙~ ⌜ tᴺᶠ₂ ⌝Nf~) tᴺᶠ₁ tᴺᶠ₂
nf-uniq-gen {Γ~ = Γ~} {A~ = A~} {tᴺᶠ₁ = tᴺᶠ₁} {tᴺᶠ₂ = tᴺᶠ₂} t~ 
  = nf-uniq {tᴺᶠ = tᴺᶠ₁} 
            {uᴺᶠ = coe~ (sym~ Γ~) (sym~ A~) 
                        (sym~ ⌜ tᴺᶠ₂ ⌝Nf~ ∙~ sym~ t~ ∙~ ⌜ tᴺᶠ₁ ⌝Nf~) tᴺᶠ₂} 
            (t~ ∙~ coh) ∙~ sym~ coh
