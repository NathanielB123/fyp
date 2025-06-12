%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils hiding (ε)
open import Utils.IdExtras

module Report.Final.c12_scdef where

\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Elaborating Smart Case}
\labch{scdef}

\section{A New Core Language}

\subsection{Syntax}

\subsection{Elaboration}

\subsection{Strictification}

data Def : Sig → Set where
  _⇒_if_then_else_ : ∀ (Γ : Ctx Ψ) A t 
                   → Tm (Γ , t >rw true)  (A [ wk𝒮 ])
                   → Tm (Γ , t >rw false) (A [ wk𝒮 ])
                   → Def Ψ 

data 𝒟Var : Sig → Def Ψ → Set where
  vz : 𝒟Var (Ψ ,def Γ ⇒ A if t then u else v) 
            ((Γ ⇒ A if t then u else v) [ wk𝒮 ])
  vs : 𝒟Var Ψ 𝒹
     → 𝒟Var (Ψ ,def _ ⇒ _ if _ then _ else _)
            (𝒹 [ wk𝒮 ])


call : 𝒟Var Ψ (Δ ⇒ A if t then u else v)
     → ∀ (δ : Tms Γ (Δ [ wk𝒮 ])) (t[] : Tm Γ 𝔹) 
     → t [ wk𝒮 ⨾ δ ] ≡ t[]
     → Tm Γ (A [ wk𝒮 ⨾ δ ])



\section{Normalisation by Evaluation}

For ordinary dependent type theory:

Env   : ∀ Δ Γ → Tms Δ Γ → Set
Val   : ∀ Γ (A : Ty Γ) Δ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]) → Env Δ Γ δ → Set
eval  : ∀ t ρ → Val Γ A Δ δ t ρ
eval* : ∀ (δ : Tms Δ Γ) (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)

For SCDef, it isn't too different.

SigEnv : Sig → Set
Env    : ∀ (φ : SigEnv Ψ) (Δ Γ : Ctx Ψ) → Tms Δ Γ → Set
Val    : ∀ (φ : SigEnv Ψ) (Γ : Ctx Ψ) (A : Ty) Δ (δ : Tms Δ Γ) 
       → Tm Δ (A [ δ ]) → Env φ Δ Γ δ → Set
eval   : ∀ φ t ρ → Val φ Γ A Δ δ t ρ
eval*  : ∀ φ (δ : Tms Δ Γ) (ρ : Env φ Θ Δ σ) → Env Θ Γ (δ ⨾ σ)

Importantly, we need to be able to weaken signatures, but these weakening
operations can be defined by recursion on the individual components.

_[_]𝒮ℰ : SigEnv Ψ → Wk Φ Ψ → SigEnv Φ
_[_]ℰ  : Env φ Δ Γ δ → ∀ (σ : Wk Φ Ψ) 
       → Env (φ [ σ ]𝒮ℰ) (Δ [ σ ]) (Γ [ σ ]) (δ [ σ ])
-- etc...
-- The only thing we really need to be careful of is to ensure exponential
-- objects are translated appropriately (i.e. account for extra weakening)
-- but I don't think that is too tricky.
--
-- In fact, a nice way to guarantee things work out would be to combine
-- signature weakening and context renaming (i.e. lists of variables) into
-- generalised renamings.

Val φ Γ (Π A B) Δ δ t ρ 
  = ∀ {Φ} {Θ : Ctx Φ} {u : Tm Θ (A [ δ [ γ ] ]} (γ : Ren Θ Δ)
      (uⱽ : Val (φ [ γ ]𝒮ℰ) (Γ [ γ ]) A Θ (δ [ γ ]) u (ρ [ γ ]𝒮ℰ))
  → Val (φ [ γ ]𝒮ℰ) (Γ [ γ ]) B Θ (δ [ γ ] , u) (t · u) (ρ [ γ ]𝒮ℰ , uⱽ)

-- Question: can we define
shift : Val φ Γ A Δ δ t ρ → Val φ Δ (A [ δ ]) Δ id t ρ

-- Some interesting cases
¬
-- TODO: Deciding whether to instantiate the substitutions of a |Val| with
-- |id| or not feels a bit like black magic...

lookupDefTT : 𝒟Var Ψ (Δ ⇒ A if t then u else v)
            → ∀ (φ : SigEnv Ψ)
            → Env φ Γ Δ δ
            → t [ δ ] ≡ TT
            → Val φ Δ A 

eval-call : ∀ (φ : SigEnv Ψ) (f : 𝒟Var Ψ (Δ ⇒ A if t then u else v))
          → (ρ : Env φ Γ Δ δ) → Val φ Δ 𝔹 Γ δ (t [ δ ]) ρ
          → Val φ Γ (A [ δ ]) Γ id (call f δ) id
eval-call φ f ρ (TT     , p) = lookupDef f φ
eval-call φ f ρ (FF     , p) = ...
eval-call φ f ρ (ne t[] , p) = uval (call f (uval* ρ) t[] {!!})

eval φ (call f δ t[] refl) ρ = eval-call φ f δⱽ t[]ⱽ
  where δⱽ   = eval* φ δ ρ 
        t[]ⱽ = eval φ t[] ρ





```




(technically "A Formalisation of a
 Dependently Typed Language as an
 Inductive-Recursive Family"

```
𝒫 : ∀ Γ A → Tm Γ A →  
𝒫 Γ (if b A B) u
```

--------------------------------------------------------------------------------























\section{Reduction}

IMPORTANT: We are working in 2LTT here (though sometimes I forget and end up
using setoid syntax). For the outer strict equality judgements, we use |_≡₁_|.
All other equality refers to inner equality.

We *really* should distinguish inner from outer types also |Set| vs |SSet|.


(Worth considering: maybe we should use ≈ for inner equality...)


>-sound  : t₁ > t₁ → Tm~ rfl~ rfl~ t₁ t₂
>s-sound : δ₁ >s δ₂ → Tms~ rfl~ rfl~ δ₁ δ₂

data _>s_ where
  ,₁ : ∀ (δ> : δ₁ >s δ₂) → δ₁ , t >s δ₂ , coe~ rfl~ (rfl~ [ >s-sound δ> ])
  ,₂ : t₁ > t₂  → δ , t₁ >s δ , t₂

data _>_ where
  -- All |call| cases assuming signature is of the form 
  -- |Ψ ,def Δ ⇒ A if t then u else v|
  call₁  : δ₁ >s δ₂ → call f δ₁ t[] p > call f δ₂ (t [ δ₂ ]) rfl~
  call₂  : ∀ (t[]> : t[]₁ >s t[]₂) 
         → call f δ t[]₁ p > call f δ t[]₂ (p ∙ >-sound t[]>)
  callTT : call {u = u} f δ TT ∣ p > u [ wk𝒮 ⨾ (δ ,rw p) ]
  callFF : call {v = v} f δ FF ∣ p > v [ wk𝒮 ⨾ (δ ,rw p) ]

  rw     : (Γ ⊢ t >rw u) → t > u


data WkTys : ∀ Δ Γ → Tms Δ Γ → Set where
  id  : WkTys Γ Γ id
  _⁺_ : WkTys Δ Γ δ → ∀ A → WkTys (Δ , A) Γ (δ ⁺ A)

data Vars : ∀ Δ Γ → Tms Δ Γ → Set
  wk*   : WkTys Δ Γ δ → Vars Δ Γ δ
  _,_   : Vars Δ Γ δ → ∀ (i : Var Δ (A [ δ ])) → Vars Δ (Γ , A) (δ , (` i))
  _,rw_ :

Ren : ∀ Δ Γ → Sub Δ Γ → Set
Ren Δ Γ δ = Vars Δ (Γ [ δ. πWk ])
  

\section{Strong Normalisation}

We define computability by recursion on types as usual.

\subsection{Computability}

\begin{spec}
𝒫 : ∀ Γ A → Tm Γ A → Set
𝒫 Γ 𝔹       t = SN t
𝒫 Γ (Π A B) t 
  -- Renamings are not allowed to introduce rewrites, but are allowed to
  -- introduce definitions (weaken the signature)
  = ∀ {Δ} {δ : Ren Δ Γ δ} {u} → 𝒫 (A [ δ ]) u → 𝒫 (B [ δ , u ]) (t · u)
-- TODO: Is this an appropriate computability predicate for large elim?
𝒫 Γ (if b A B) t
  = SN t 
  × ((b~ : b ≡ TT) → 𝒫 A (coe (if b~ rfl rfl ∙ ifTT) t))
  × ((b~ : b ≡ FF) → 𝒫 B (coe (if b~ rfl rfl ∙ ifFF) t))
-- Ehh this definition is a bit suspect
-- Types should be quotiented by conversion, but the contents of
-- |𝒫 Γ (if TT A B) t| is not equal to the |𝒫 Γ A|
-- If we assume propositional extensionality, then I think we can show a
-- bidirectional implication, but that feels a little handwavey
-- I don't know how else to do this though...
--
-- Maybe an more formal approach would be to define computability in the outer 
-- theory. Note that |SN| is defined in the outer theory

𝒫Def : Def → Set
𝒫Def (Γ ⇒ A if t then u else v)
  = ∀ {Δ} (ρ : 𝒫Tms Δ Γ δ) 
  → (t [ δ ] ≡ TT → 𝒫 Δ (A [ δ ]) (u [ δ ]))
  × (t [ δ ] ≡ FF → 𝒫 Δ (A [ δ ]) (v [ δ ]))

data 𝒫Sig : Sig → Set
  ε   : 𝒫Sig ε
  _,_ : 𝒫Sig Ψ → 𝒫Def (Γ ⇒ A if t then u else v) 
      → 𝒫Sig (Ψ ,def Γ ⇒ A if t then u else v)

data 𝒫Tms : ∀ Δ Γ → Tms Δ Γ → Set where
  ε   : 𝒫Tms Δ Γ ε
  _,_ : 𝒫Tms Δ Γ δ → 𝒫 Δ (A [ δ ]) (t [ δ ]) → 𝒫Tms Δ (Γ , A) (δ , t)
\end{spec}

\subsection{Fundamental Theorem}

\begin{spec}

fndThm-call : 𝒫Sig Ψ → 𝒫Tms Δ Γ δ → SNTms Δ Γ δ → 𝒫 Δ 𝔹 t[] → 𝒫 (call f δ t[] p)
fndThm-call φ δⱽ δˢⁿ t[]ⱽ = reflect _ (fndThm-call> δⱽ δˢⁿ t[]ⱽ)

fndThm-call> : 𝒫Sig Ψ → 𝒫Tms Δ Γ δ → SN Δ 𝔹 t[] → (call f δ t[] p) > t′ 
             → 𝒫 t′
-- One of the arguments reduces
fndThm-call φ δⱽ (acc δˢⁿ) t[]ⱽ (call₁ {δ₂ = δ₂} p) 
  = fndThm-call (𝒫Tms> p δⱽ) (δˢⁿ p) (eval φ id𝒫 (t [ δ₂ ]))
-- t[] reduces
-- Recall that |𝒫 Γ 𝔹 t = SN t|
fndThm-call φ δⱽ δˢⁿ (acc t[]ⱽ) (call₂ {t₂ = t₂} p) 
  = fndThm-call φ δⱽ δˢⁿ (t[]ⱽ p)
-- t[] is TT
fndThm-call φ δⱽ δˢⁿ t[]ⱽ callTT    = lookup𝒮 f φ δⱽ .fst p
-- t[] is FF
fndThm-call φ δⱽ δˢⁿ t[]ⱽ callFF    = lookup𝒮 f φ δⱽ .snd p
-- Call is stuck and rewrites to a closed Boolean
fndThm-call φ δⱽ δˢⁿ t[]ⱽ (rw p)    = boolSN

-- These are pretty-much identical to ordinary dependent types!
qval : ∀ A → 𝒫 Γ A t → SN t
uval : ∀ A → ¬lam t → (∀{u} → t > u → 𝒫 Γ A u) → 𝒫 Γ A t


uval 𝔹          _ uⱽ = acc uⱽ
uval (Π A B)    _ uⱽ = {!!} -- Same as usual
uval (if b A B) _ uⱽ 
  = acc (λ p → u^ p .fst)
  -- If large ``|if|'' is not stuck, then we recurse
  -- Note |p : t > coe ... u| here so we need that |¬lam| is stable under 
  -- coercions (hopefully unsurprising) 
  , (λ b~ → uval A _ (λ p → uⱽ p .snd)) 
  , (λ b~ → uval B _ (λ p → uⱽ p .trd))


qval 𝔹          tⱽ = tⱽ
-- This case is a little subtle, but ultimately no different to ordinary 
-- dependent types
-- We use the fact that we can go from |SN (t · u)| to |SN t|
-- Specifically, we weaken the function, apply it to a fresh variable, use
-- the fact that SN is stable under taking subterms and then use the fact 
-- that SN is stable under undoing renamings
--
-- Note |B [ wk , vz ] == B|
qval (Π A B)    tⱽ = [ wk ]sn⁻¹ (SN>l· (qval B (tⱽ wk vz-val)))
-- First component of computability at large ``|if|'' is just SN, so this is easy
qval (if b A B) tⱽ = tⱽ .fst 

fndThm : 𝒫Sig Ψ → 𝒫Tms Δ Γ δ → ∀ t → 𝒫 Δ (A [ δ ]) (t [ δ ])
fndThm φ ρ TT               = snTT
fndThm φ ρ FF               = snFF
fndThm φ ρ (` i)            = lookup i ρ
fndThm φ ρ (call f δ t[] p) = fndThm-call φ δⱽ (q* δⱽ) t[]ⱽ
  where δⱽ   = fndThm* φ ρ δ
        t[]ⱽ = fndThm φ ρ t[]

\end{spec}


