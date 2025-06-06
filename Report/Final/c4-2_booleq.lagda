%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils
open import Common.Sort

module Report.Final.c4-2_booleq where

infix 4 _>β_ _>!_ _>𝔹*_ _>nd_ _[_]>_ _>𝔹_
\end{code}
%endif

\pagebreak
\section{Strong Normalisation of Spontaneous Reduction}
\labsec{snspont}

All that remains then is strong normalisation of |_>!_|. We will prove this in
two steps, using an intermediary notion of ``non-deterministic'' reduction, 
|_>nd_|: a slightly
generalised version of β-reduction, where |if|-expressions can be
non-deterministically collapsed to the LHS or RHS branch irrespective
of the scrutinee.

\begin{itemize}
  \item First we will prove that strong normalisability w.r.t. 
        non-deterministic reduction, |SN _>nd_ t|, implies SN w.r.t. spontaneous 
        reduction, |SN _>!_ t|. We will actually show this on untyped terms
        (generalising |_>!_| appropriately) to simplify the presentation.
  \item Then we will show strong normalisation of typed terms w.r.t. |_>nd_|
        by the technique of computability/(unary) logical relations.
\end{itemize}

\subsection{An Untyped Reduction Proof}

In this section, we show that the untyped terms which are strongly-normalising
w.r.t. non-deterministic reduction are also strongly-normalising w.r.t.
spontaneous reduction.

We define untyped terms indexed by the number of variables in the context
(``intrinsically well-scoped''). Note that in this section, the symbols
|Γ|, |Δ|, |Θ| denote natural numbers rather than lists of types.

%if False
\begin{code}
variable
  Γ Δ Θ : ℕ

data Tm[_] : Sort → ℕ → Set

Var = Tm[ V ]
Tm  = Tm[ T ]

data Tm[_] where
\end{code}
%endif

\begin{code}
  vz  : Var (su Γ)
  vs  : Var Γ → Var (su Γ)

  `_  : Var Γ → Tm Γ 
  _·_ : Tm Γ → Tm Γ → Tm Γ
  ƛ_  : Tm (su Γ) → Tm Γ
  TT  : Tm Γ
  FF  : Tm Γ
  if  : Tm Γ → Tm Γ → Tm Γ → Tm Γ
\end{code}

%if False
\begin{code}
data Tms[_] (q : Sort) (Δ : ℕ) : ℕ → Set where
  ε   : Tms[ q ] Δ ze
  _▷_ : Tms[ q ] Δ Γ → Tm[ q ] Δ → Tms[ q ] Δ (su Γ)

Tms = Tms[ T ]

variable
  i j k : Var Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ
  δ σ   : Tms[ q ] Δ Γ

tm⊑ : q ⊑ r → Tm[ q ] Γ → Tm[ r ] Γ
tm⊑ {q = T} {r = T} _ t = t
tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = V} {r = V} _ i = i

wk : Tm[ q ] Γ → Tm[ q ] (su Γ)
_⁺ : Tms[ q ] Δ Γ → Tms[ q ] (su Δ) Γ
_^ : Tms[ q ] Δ Γ → Tms[ q ] (su Δ) (su Γ)
id : Tms[ q ] Γ Γ 
_[_] : Tm[ q ] Γ → Tms[ r ] Δ Γ → Tm[ q ⊔ r ] Δ

ε       ⁺ = ε
(δ ▷ t) ⁺ = (δ ⁺) ▷ wk t

δ ^ = (δ ⁺) ▷ tm⊑ V⊑ vz

(` i)    [ δ ]     = tm⊑ ⊑T (i [ δ ])
TT       [ δ ]     = TT
FF       [ δ ]     = FF
(t · u)  [ δ ]     = (t [ δ ]) · (u [ δ ])
if t u v [ δ ]     = if (t [ δ ]) (u [ δ ]) (v [ δ ])
(ƛ t)    [ δ ]     = ƛ (t [ δ ^ ])
vz       [ δ ▷ u ] = u
(vs i)   [ δ ▷ u ] = i [ δ ]

wk {q = V} i = vs i
wk {q = T} t = t [ id {q = V} ⁺ ]

id {Γ = ze}   = ε
id {Γ = su Γ} = id {Γ = Γ} ^

<_> : Tm Γ → Tms[ T ] Γ (su Γ)
< t > = id ▷ t
\end{code}
%endif

In this section, we will be dealing with quite a few distinct reduction
relations at a fine-grained level of detail. To assist with this, we
define generically the monotonic closure of term relations |_[_]>_|:

\begin{code}
_[_]>_  : Tm Γ → (∀ {Γ} → Tm Γ → Tm Γ → Set) 
        → Tm Γ → Set 
\end{code}

%if False
\begin{code}
data MonoClosure (_>_ : ∀ {Γ} → Tm Γ → Tm Γ → Set) {Γ} : Tm Γ → Tm Γ → Set
t [ r ]> u = MonoClosure r t u
data MonoClosure _>_ where
\end{code}
%endif

\begin{code}
  ⟪_⟫  : t₁ > t₂ → t₁ [ _>_ ]> t₂
  l·   : t₁ [ _>_ ]> t₂ → t₁ · u [ _>_ ]> t₂ · u
  ·r   : u₁ [ _>_ ]> u₂ → t · u₁ [ _>_ ]> t · u₂
  ƛ_   : t₁ [ _>_ ]> t₂ → ƛ t₁ [ _>_ ]> ƛ t₂
  if₁  : t₁ [ _>_ ]> t₂ → if t₁ u v [ _>_ ]> if t₂ u v
  if₂  : u₁ [ _>_ ]> u₂ → if t u₁ v [ _>_ ]> if t u₂ v
  if₃  : v₁ [ _>_ ]> v₂ → if t u v₁ [ _>_ ]> if t u v₂
\end{code}

%if False
\begin{code}
variable
  _>₁_ _>₂_ : ∀ {Γ} → Tm Γ → Tm Γ → Set
\end{code}
%endif

Monotonic closure is functorial mappings between closed-over reduction
relations.

\begin{code}
map>  : (∀ {Γ} {t u : Tm Γ} → t >₁ u → t >₂ u) 
      → t [ _>₁_ ]> u → t [ _>₂_ ]> u
\end{code}

Ordinary β-reduction can then just be defined as the monotonic closure
of the computation rules for |⇒| and |𝔹|:

\begin{code}
data β-step : Tm Γ → Tm Γ → Set where
  ⇒β   : β-step ((ƛ t) · u) (t [ < u > ])
  𝔹β₁  : β-step (if TT u v) u
  𝔹β₂  : β-step (if FF u v) v

_>β_ : Tm Γ → Tm Γ → Set
_>β_ = _[ β-step ]>_
\end{code}

Spontaneous reduction in this section refers to the relation which only
rewrites terms to closed Booleans (as long as the terms not already
syntactically equal to |TT| or |FF|) - it does not, by default, include
|β|-reductions as well:

%if False
\begin{code}
𝔹? : Tm Γ → Bool
𝔹? TT = true
𝔹? FF = true
𝔹? _  = false
\end{code}
%endif

\begin{code}
data !-step : Tm Γ → Tm Γ → Set where
  rwTT  : ¬is 𝔹? t → !-step t TT
  rwFF  : ¬is 𝔹? t → !-step t FF

_>!_ : Tm Γ → Tm Γ → Set
_>!_ = _[ !-step ]>_
\end{code}

Non-deterministic reduction treats |if|-expressions like non-deterministic
choices, ignoring the scrutinee.

\begin{code}
data nd-step : Tm Γ → Tm Γ → Set where
  ⇒β   : nd-step ((ƛ t) · u) (t [ < u > ])
  ndl  : nd-step (if t u v) u
  ndr  : nd-step (if t u v) v

_>nd_ : Tm Γ → Tm Γ → Set 
_>nd_ = _[ nd-step ]>_
\end{code}

We need one more monotonic relation on terms, |_>𝔹_|, where
|t >𝔹 u| holds when |u| is syntactically equal to |t| except for replacing
a single arbitrary subterm with |TT|/|FF|.

\begin{code}
_>𝔹_ : Tm Γ → Tm Γ → Set
_>𝔹_ = _[ (λ _ u → is 𝔹? u) ]>_
\end{code}

%if False
\begin{code}
_>𝔹*_ : Tm Γ → Tm Γ → Set
_>𝔹*_ = flip _[ flip _>𝔹_ ]*_
\end{code}
%endif

Our overall goal is to prove that all terms which are strongly-normalising
w.r.t. non-deterministic reduction are also strongly-normalising w.r.t.
spontaneous reduction plus β rules.

\begin{code}
_>β!_ : Tm Γ → Tm Γ → Set
_>β!_ = _[ _>β_ ∣ _>!_ ]_

snnd→snβ! : SN _>nd_ t → SN _>β!_ t
\end{code}

The key lemma we need to show is that |_>𝔹*_| (i.e. the relation defined
by replacements of arbitrary subterms of the LHS term with closed Booleans)
commutes with non-deterministic reduction:

\begin{code}
𝔹*/nd-comm> : t >𝔹* u → u >nd v → ∃[ w ] t >nd w × w >𝔹* v
\end{code}

Note that |_>nd_| does not commute with |_>!_| in the same way. 
Note that |_>nd_| includes the β-rule for functions, and so we require
reduction relations we commute with to be stable under substitution.
Spontaneous
reduction is not stable under substitution, because e.g. we can 
rewrite |` i >! TT|, but if we apply the substitution |FF / i| to both sides
then we are left with |FF >! TT| which is impossible (the LHS of |_>!_| cannot
be |TT| or |FF|).

We can prove this by checking all the cases for individual |nd-step|s/single
Boolean rewrites:
\begin{itemize}
  \item When the step is a |⇒β| contraction, then the Boolean rewrite
        must have occurred inside the lambda body or the argument, and so we can
        instead β-reduce before the rewrite and then rewrite to get back to 
        the same
        term (potentially multiple times, given the argument could have 
        been duplicated).
  \item When the step is a non-deterministic choice, the Boolean
        rewrite must have occurred inside the scrutinee, LHS or RHS of the if
        expression. We can instead perform the non-deterministic choice
        before the rewrite and then either get back to the term immediately
        (if the rewrite applied to the scrutinee or the dropped branch of
        the |if|) or apply the rewrite again to the retained branch.
\end{itemize}

\remarknote{|_[_]𝔹>*| witnesses a generalisation of |_>𝔹*_| being stable 
under substitution. Specifically, we allow the substitute terms to
also be reduced via |_>𝔹*_|.}

\begin{code}
data _>Tms𝔹*_ : Tms Δ Γ → Tms Δ Γ → Set where
  refl : δ >Tms𝔹* δ
  _,_  : δ >Tms𝔹* σ → t >𝔹* u → (δ ▷ t) >Tms𝔹* (σ ▷ u)

_[_]𝔹>* : t >𝔹* u → δ >Tms𝔹* σ → t [ δ ] >𝔹* u [ σ ]

𝔹/nd-comm : t >𝔹 u → nd-step u v → ∃[ w ] nd-step t w × w >𝔹* v
𝔹/nd-comm (l· (ƛ p))        ⇒β  
  = _ Σ, ⇒β Σ, ⟪ p ⟫* [ refl ]𝔹>*
𝔹/nd-comm (·r {t = ƛ t} p)  ⇒β  
  = _ Σ, ⇒β Σ, rfl* {x = t} [ refl {δ = id} , (p ∷ rfl*) ]𝔹>*
𝔹/nd-comm (if₁ p)  ndl = _ Σ, ndl  Σ, rfl*
𝔹/nd-comm (if₂ p)  ndl = _ Σ, ndl  Σ, ⟪ p ⟫*
𝔹/nd-comm (if₃ p)  ndl = _ Σ, ndl  Σ, rfl*
𝔹/nd-comm (if₁ p)  ndr = _ Σ, ndr  Σ, rfl*
𝔹/nd-comm (if₂ p)  ndr = _ Σ, ndr  Σ, rfl*
𝔹/nd-comm (if₃ p)  ndr = _ Σ, ndr  Σ, ⟪ p ⟫*
\end{code}

We can also prove that spontaneous reduction alone is strongly normalising by
structural induction on terms (once we rewrite a term to a Boolean, it cannot
reduce further).

\begin{code}
sn! : ∀ (t : Tm Γ) → SN _>!_ t
\end{code}

Using our commuting lemma to ensure we keep making progress w.r.t.
non-deterministic reduction, we can prove by mutual well-founded induction on
non-deterministic and spontaneous reduction that the strongly normalising
terms w.r.t. |_>nd_| are exactly those which are strongly normalising
w.r.t. |_>nd!_| (interleaved |_>nd_| and |_>!_|).
 
\sideremark{Note that we generalise the
inductive hypothesis over |_>𝔹*_| here to account for subterms
getting rewritten to Booleans. Spontaneous reduction being included in
|_>𝔹_|, |!𝔹>| can be easily proven by considering |!-step| cases and
|map>|.}

\begin{code}
_>nd!_ : Tm Γ → Tm Γ → Set
_>nd!_ = _[ _>nd_ ∣ _>!_ ]_

!𝔹> : t >! u → t >𝔹 u

snnd!   : t >𝔹* u → SN _>nd_ t → SN _>!_ u → SN _>nd!_ u
snnd!>  : t >𝔹* u → SN _>nd_ t → SN _>!_ u → u >nd! v 
        → SN _>nd!_ v

snnd! p ndᴬ !ᴬ = acc (snnd!> p ndᴬ !ᴬ)

snnd!> p (acc ndᴬ)  !ᴬ        (inl q) 
  using v Σ, q′ Σ, p′ ← 𝔹*/nd-comm> p q
  = snnd! p′ (ndᴬ q′) (sn! _)
snnd!> p ndᴬ        (acc !ᴬ)  (inr q) 
  = snnd! (p <∶ !𝔹> q) ndᴬ (!ᴬ q)

snnd→snnd! : SN _>nd_ t → SN _>nd!_ t
snnd→snnd! ndᴬ = snnd! rfl* ndᴬ (sn! _)
\end{code}

Finally, we recover our original goal

\begin{spec}
snnd→snβ! : SN _>nd_ t → SN _>β!_ t
\end{spec}

from |_>β!_| reduction being included inside |_>nd!_|.

\begin{code}
β→nd : β-step t u → nd-step t u
β→nd ⇒β   = ⇒β
β→nd 𝔹β₁  = ndl
β→nd 𝔹β₂  = ndr

snnd→snβ! ndᴬ 
  = accessible (map⊎ (map> β→nd) (λ p → p)) (snnd→snnd! ndᴬ)
\end{code}
