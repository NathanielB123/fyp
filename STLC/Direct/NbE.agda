{-# OPTIONS --prop --rewriting #-}

import Agda.Builtin.Equality.Rewrite
open import Utils

-- NbE for STLC + Boolean rewrites, but now with respect to a concrete set of
-- rewrites, directly
--
-- Rewrite LHSs are assumed to be disjoint
--
-- Makes use of "stabilised neutrals" from Jon Sterling and Carlo Angiuli's 
-- "Normalization for Cubical Type Theory"
module STLC.Direct.NbE where

infix 5 _,_>rw_∣_

data Ctx : Set
data Ty  : Set
data Var : Ctx → Ty → Set
data Tm  : Ctx → Ty → Set

-- TODO, consider indexing |Val|, |Env|, |Ne|, |Nf|, |SNe| over their underlying
-- terms so we can write some proofs
Val : Ctx → Ty → Set
data Env (Δ : Ctx) : Ctx → Set

data Dir : Set where
  ↑ ↓ : Dir

-- β-normal neutrals and normal forms
data βNf[_] : Dir → Ctx → Ty → Set

βNf = βNf[ ↑ ]
βNe = βNf[ ↓ ]

-- Neutrals can be characterised positively or negatively
data NePred : Set where
  + - : NePred

-- We inductively define neutrals and normal forms for which a particular 
-- predicate holds for every neutral spine
NeP    : NePred → ∀ Γ A → βNe Γ A → Set
data NfP[_] : ∀ ↕ → NePred → ∀ Γ A → βNf[ ↕ ] Γ A → Set
NfP = NfP[ ↑ ]

Ne⁻ : Ctx → Ty → Set
Nf⁻ : Ctx → Ty → Set
Ne⁻ Γ A = Σ (βNe Γ A) (NeP - Γ A)
Nf⁻ Γ A = Σ (βNf Γ A) (NfP - Γ A)

data Tms (Δ : Ctx) : Ctx → Set
-- Todo: Should we use renamings or thinnings? I think either works
data Thin : Ctx → Ctx → Set

variable
  Γ Δ Θ       : Ctx
  A B C       : Ty
  i j k       : Var Γ A
  δ σ         : Thin Δ Γ
  b           : Bool
  ±           : NePred
  tᴺᵉ uᴺᵉ vᴺᵉ : βNe Γ A
  ↕           : Dir
  tᴺᶠ uᴺᶠ vᴺᶠ : βNf[ ↕ ] Γ A

data Ty where
  _⇒_ : Ty → Ty → Ty
  𝔹   : Ty

-- A neutral destabilises a context if it creates any critical pairs
destabilises : ∀ Γ → βNe Γ 𝔹 → Set

-- A neutral is unstable if any rewrites can apply to any sub-neutrals along the
-- spine
unstable : βNe Γ A → Set

-- A neutral wobbles a context if it doesn't destabilise it
wobbles : ∀ Γ → βNe Γ 𝔹 → Set
wobbles Γ tᴺᵉ = ¬ destabilises Γ tᴺᵉ

-- Stable neutrals are those that are not unstable
stable : βNe Γ A → Set
stable tᴺᵉ = ¬ unstable tᴺᵉ

-- Valid neutrals are ones that can be added as rewrite LHSs
valid : ∀ Γ → βNe Γ 𝔹 → Set
valid Γ tᴺᵉ = wobbles Γ tᴺᵉ × stable tᴺᵉ

_[_]βNf : βNf[ ↕ ] Γ A → Thin Δ Γ → βNf[ ↕ ] Δ A

-- The positively-characterised neutrals are those that are not unstable
-- The negatively-characterised neutrals are effectively as described in 
-- Jon Sterling and Carlo Angiuli's "Normalization for Cubical Type Theory"
-- Critically, negatively-characterised neutrals can be weakened
nePred : NePred → ∀ Γ A → βNe Γ A → Set
nePred + Γ A tᴺᵉ = stable tᴺᵉ
-- I would like to use |Val Δ A| here, but this breaks strict positivity
nePred - Γ A tᴺᵉ = ∀ {Δ} (δ : Thin Δ Γ) → unstable (tᴺᵉ [ δ ]βNf) → Nf⁻ Δ A

data Ctx where
  ε           : Ctx
  _,_         : Ctx → Ty → Ctx
              -- I think we need to change the neutrals here to special
              -- "neutrals that don't contain stabilised neutrals"  
  _,_>rw_∣_ : ∀ Γ (tᴺᵉ : βNe Γ 𝔹) → Bool → valid Γ tᴺᵉ → Ctx

data Var where
  vz   : Var (Γ , A) A
  vs   : Var Γ B → Var (Γ , A) B
  vsrw : ∀ {p} → Var Γ A → Var (Γ , tᴺᵉ >rw b ∣ p) A

-- If a neutral is unstable w.r.t. a context, it must also be unstable
-- w.r.t. larger contexts
_[_]𝒰 : unstable tᴺᵉ → ∀ (δ : Thin Δ Γ) → unstable (tᴺᵉ [ δ ]βNf)

-- If a neutral destabilises a context, it must also destabilise larger contexts
_[_]𝒟 : destabilises Γ tᴺᵉ → ∀ (δ : Thin Δ Γ) → destabilises Δ (tᴺᵉ [ δ ]βNf)

[_]𝒮⁻¹_ : ∀ (δ : Thin Δ Γ) → stable (tᴺᵉ [ δ ]βNf) → stable tᴺᵉ
([ δ ]𝒮⁻¹ ¬p[]) p = ¬p[] (p [ δ ]𝒰)

[_]𝒲⁻¹_ : ∀ (δ : Thin Δ Γ) → wobbles Δ (tᴺᵉ [ δ ]βNf) → wobbles Γ tᴺᵉ
([ δ ]𝒲⁻¹ ¬p[]) p = ¬p[] (p [ δ ]𝒟)

[_]𝒱⁻¹_ : ∀ (δ : Thin Δ Γ) → valid Δ (tᴺᵉ [ δ ]βNf) → valid Γ tᴺᵉ

data Thin where
  ε         : Thin ε ε
  _^_       : Thin Δ Γ → ∀ A → Thin (Δ , A) (Γ , A)
  _⁺_       : Thin Δ Γ → ∀ A → Thin (Δ , A) Γ
  _^rw_     : ∀ (δ : Thin Δ Γ) (p : valid Δ (tᴺᵉ [ δ ]βNf))
            → Thin (Δ , (tᴺᵉ [ δ ]βNf) >rw b ∣ p          ) 
                   (Γ , tᴺᵉ            >rw b ∣ [ δ ]𝒱⁻¹ p)
  -- Thinnings need to be able to add equations so we can go under |if|s
  _⁺rw_     : Thin Δ Γ → ∀ (p : valid Δ tᴺᵉ) 
            → Thin (Δ , tᴺᵉ >rw b ∣ p) Γ

idᵀʰ : Thin Γ Γ
wkᵀʰ : Thin (Γ , A) Γ

[id]βNf : tᴺᶠ [ idᵀʰ ]βNf ≡ tᴺᶠ

-- -- idᵀʰ {Γ = ε}                 = ε
-- -- idᵀʰ {Γ = Γ , A}             = idᵀʰ ^ A
-- -- idᵀʰ {Γ = Γ , tᴺᵉ >rw b ∣ p} = coe (cong₂ Thin eq₁ eq₂) rec
-- --   where rec = idᵀʰ {Γ = Γ} ^rw subst (valid _) (sym [id]Ne) p 
-- --         eq₁ = dcong₂ (Γ ,_>rw b ∣_) [id]Ne 
-- --                      (subst-subst-sym [id]Ne)
-- --         eq₂ = cong (Γ , tᴺᵉ >rw b ∣_) {!!} -- TODO


data Tm where
  `_  : Var Γ A → Tm Γ A
  
  _·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ƛ_  : Tm (Γ , A) B → Tm Γ (A ⇒ B)

  if  : Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A
  TT  : Tm Γ 𝔹
  FF  : Tm Γ 𝔹

data βNf[_] where
  `_  : Var Γ A → βNe Γ A
  _·_ : βNe Γ (A ⇒ B) → βNf Γ A → βNe Γ B
  if  : βNe Γ 𝔹 → βNf Γ A → βNf Γ A → βNe Γ A

  ne : βNe Γ 𝔹 → βNf Γ 𝔹
  FF : βNf Γ 𝔹
  TT : βNf Γ 𝔹
  ƛ_ : βNf (Γ , A) B → βNf Γ (A ⇒ B)

(` i)    [ δ ]βNf = {!   !}
(t · u)  [ δ ]βNf = (t [ δ ]βNf) · (u [ δ ]βNf)
if t u v [ δ ]βNf = if (t [ δ ]βNf) {!!} {!!}
ne t     [ δ ]βNf = ne (t [ δ ]βNf)
FF       [ δ ]βNf = FF
TT       [ δ ]βNf = TT
(ƛ t)    [ δ ]βNf = {!   !}

_⨾_ : Thin Δ Γ → Thin Θ Δ → Thin Θ Γ

[][]βNf : tᴺᶠ [ δ ]βNf [ σ ]βNf ≡ tᴺᶠ [ δ ⨾ σ ]βNf

occurs𝔹 : ∀ Γ → βNe Γ 𝔹 → Set
-- To avoid needing to strengthen, I think it would be nice to weaken all
-- LHSs in the context up to the current context
occurs𝔹 = {!!}

occurs : ∀ Γ A → βNe Γ A → Set
occurs Γ 𝔹       tᴺᵉ = occurs𝔹 Γ tᴺᵉ
occurs Γ (A ⇒ B) tᴺᵉ = ⊥

unstable-rec : βNe Γ A → Set

unstable tᴺᵉ = occurs _ _ tᴺᵉ ⊎ unstable-rec tᴺᵉ

unstable-rec (` i)            = ⊥
-- We can skip |occurs tᴺᵉ| because it is guaranteed to have a function type
unstable-rec (tᴺᵉ · uᴺᶠ)      = unstable-rec tᴺᵉ
unstable-rec (if tᴺᵉ uᴺᶠ vᴺᶠ) = unstable tᴺᵉ

data NfP[_] where
  `_  : ∀ i → NfP[ ↓ ] ± Γ A (` i)
  _·_ : ∀ tᴺᵉ → NfP ± Γ A uᴺᶠ → NfP[ ↓ ] ± Γ B (tᴺᵉ · uᴺᶠ)
  if  : ∀ tᴺᵉ → NfP ± Γ A uᴺᶠ → NfP ± Γ A vᴺᶠ 
      → NfP[ ↓ ] ± Γ A (if tᴺᵉ uᴺᶠ vᴺᶠ)

  ne : NeP ± Γ 𝔹 tᴺᵉ → NfP ± Γ 𝔹 (ne tᴺᵉ)
  TT : NfP ± Γ 𝔹 TT
  FF : NfP ± Γ 𝔹 FF
  ƛ_ : NfP ± (Γ , A) B tᴺᶠ → NfP ± Γ (A ⇒ B) (ƛ tᴺᶠ)

NeP ± Γ A tᴺᵉ = NfP[ ↓ ] ± Γ A tᴺᵉ × nePred ± Γ A tᴺᵉ

_[_]Ne⁻ : Ne⁻ Γ A → ∀ (δ : Thin Δ Γ) → Ne⁻ Δ A

Val Γ (A ⇒ B) = ∀ {Δ} → Thin Δ Γ → Val Δ A → Val Δ B
Val Γ 𝔹       = Nf⁻ Γ 𝔹

data Env Δ where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

_[_]E : Env Δ Γ → Thin Θ Δ → Env Θ Γ
_[_]V : Val Γ A → Thin Δ Γ → Val Δ A

uval : ∀ A (tᴺᵉ : βNe Γ A)
     → NfP[ ↓ ] - Γ A tᴺᵉ
     → (∀ {Δ} (δ : Thin Δ Γ) → unstable (tᴺᵉ [ δ ]βNf) → Val Δ A) 
     → Val Γ A
qval : ∀ A → Val Γ A → Nf⁻ Γ A

ifVal : Val Γ 𝔹 → Val Γ A → Val Γ A → Val Γ A
ifVal (TT Σ, TT) uⱽ vⱽ = uⱽ
ifVal (FF Σ, FF) uⱽ vⱽ = vⱽ
ifVal (ne tᴺᵉ Σ, ne (p Σ, c)) uⱽ vⱽ 
  = uval _ _ (if tᴺᵉ (qu .snd) (qv .snd))
    λ where δ (inl φ) → {!!} -- Whole term is substituted for a Boolean
            δ (inr φ) → ifVal (c δ φ) (uⱽ [ δ ]V) (vⱽ [ δ ]V)     
  where qu = qval _ uⱽ
        qv = qval _ uⱽ

-- NbE time!
eval : Env Δ Γ → Tm Γ A → Val Δ A
eval ρ TT         = TT Σ, TT
eval ρ FF         = FF Σ, FF
eval ρ (if t u v) = ifVal (eval ρ t) (eval ρ u) (eval ρ v)
eval ρ (ƛ t)      = λ δ uⱽ → eval ((ρ [ δ ]E) , uⱽ) t
eval ρ (` i)      = {!!}
eval ρ (t · u)    = (eval ρ t) idᵀʰ (eval ρ u)

uval (A ⇒ B) tᴺᵉ p c δ uⱽ 
  = uval B _ ((tᴺᵉ [ δ ]βNf) · qu .snd)
    λ where σ (inl φ) → {!!} -- Whole term is substituted for a Boolean
            σ (inr φ) → c (δ ⨾ σ) (subst unstable ([][]βNf {tᴺᶠ = tᴺᵉ}) (inr φ)) 
                          idᵀʰ (uⱽ [ σ ]V)
  where qu = qval A uⱽ
uval 𝔹       tᴺᵉ p  c = ne tᴺᵉ Σ, ne (p Σ, λ δ φ → qval 𝔹 (c δ φ))

vz-val : Val (Γ , A) A
vz-val = uval _ _ (` vz) 
         λ δ φ → {!!} -- Whole variable is substituted for a Boolean

qval (A ⇒ B) tⱽ = _ Σ, ƛ tuⱽ
  where tuⱽ = qval B (tⱽ wkᵀʰ vz-val) .snd
qval 𝔹       tⱽ = tⱽ

 