%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils
open import Common.Sort

module Report.Final.c4-1_booleq where

infixr 5 _⇒_
infixl 4  _,_
infix  5  ƛ_
infixl 6  _·_
infix  7  `_


infix 4 _~_ _⊢_~_ _⊢_>′_ _⊢_>′*_ _⊢_>_ _⊢_>*_ _>!_
infixr 4 _∙~_
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{STLC Modulo Equations}
\labch{simply}

In this chapter, we prove decidability of conversion for STLC modulo 
a fixed (global) set of Boolean
equations via rewriting to completion. We end by discussing the challenges in
adapting this proof to a setting where these equations can be introduced
locally.

\section{STLC with Boolean Equations}
\labsec{simplebooleq}

We begin our exploration of \SC/local equality reflection by
studying convertibility of STLC terms modulo equations.
We will focus on equations of a restricted form:
|t == b|, where |t| is a |𝔹|-typed term and |b| is a closed
Boolean.

We use an intrinsically-typed syntax
with recursive substitutions following \refsec{stlcrec}, containing
|⇒| and |𝔹| type formers, with their standard introduction and elimination
rules.
Note that simply-typed ``|if|''-expressions require the left and right branches to 
have exactly the same type.

\begin{spec}
if : Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A
\end{spec}

%if False
\begin{code}
data Ty : Set where
  _⇒_  : Ty → Ty → Ty
  𝔹    : Ty
  
data Ctx : Set where
  •    : Ctx
  _▷_  : Ctx → Ty → Ctx

variable
  A B C : Ty
  Γ Δ Θ : Ctx

open import Common.Sort

data Tm[_] : Sort → Ctx → Ty → Set
Var = Tm[ V ]
Tm  = Tm[ T ]

data Tm[_] where
  vz  : Var (Γ ▷ A) A
  vs  : Var Γ B → Var (Γ ▷ A) B

  `_     : Var Γ A → Tm Γ A
  ƛ_     : Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  _·_    : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  TT FF  : Tm Γ 𝔹
  if     : Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A

data Tms[_] : Sort → Ctx → Ctx → Set where
  ε    : Tms[ q ] Δ •
  _,_  : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ ▷ A)

Ren = Tms[ V ]
Sub = Tms[ T ]  
 
_[_] : Tm[ q ] Γ A → Tms[ r ] Δ Γ → Tm[ q ⊔ r ] Δ A

tm⊑  : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
_^_  : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ ▷ A) (Γ ▷ A)

vz          [ δ , t ]  = t
vs i        [ δ , t ]  = i [ δ ]
(` i)       [ δ ]      = tm⊑ ⊑T (i [ δ ])
(t · u)     [ δ ]      = (t [ δ ]) · (u [ δ ])
(ƛ t)       [ δ ]      = ƛ (t [ δ ^ _ ])
TT          [ δ ]      = TT
FF          [ δ ]      = FF
if t u v    [ δ ]      = if (t [ δ ]) (u [ δ ]) (v [ δ ])

id      : Tms[ q ] Γ Γ
_⁺_     : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ ▷ A) Γ
suc[_]  : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ ▷ A) B
_⨾_     : Tms[ q ] Δ Γ → Tms[ r ] Θ Δ → Tms[ q ⊔ r ] Θ Γ
wk      : Ren (Γ ▷ A) Γ
<_>     : Tm[ q ] Γ A → Tms[ q ] Γ (Γ ▷ A)

id {Γ = •}      = ε
id {Γ = Γ ▷ A}  = id ^ A

suc[ V  ] = vs
suc[ T  ] = _[ id {q = V} ⁺ _ ]
 
ε        ⁺ A = ε
(δ , t)  ⁺ A = (δ ⁺ A) , suc[ _ ] t

δ ^ A = (δ ⁺ A) , tm⊑ V⊑ vz

ε        ⨾ σ = ε
(δ , t)  ⨾ σ = (δ ⨾ σ) , (t [ σ ])

wk     = id ⁺ _
< t >  = id , t

tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = V} {r = V} _ i = i
tm⊑ {q = T} {r = T} _ t = t

variable
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ : Tms[ q ] Δ Γ


⌜_⌝𝔹 : Bool → Tm Γ 𝔹
⌜ true   ⌝𝔹 = TT
⌜ false  ⌝𝔹 = FF
\end{code}
%endif

The computation rules then just select the appropriate branch.

%if False
\begin{code}
data _~_ : Tm Γ A → Tm Γ A → Set where
\end{code}
%endif

\begin{code}
  𝔹β₁  : if TT  u v ~ u
  𝔹β₂  : if FF  u v ~ v
\end{code}

We will package the set of equations with which we decide conversion modulo into
\emph{equational contexts}. For our restricted class of equations, these take
the form of lists of pairs of |𝔹|-typed terms
and closed Booleans.

\begin{code}
data Eqs (Γ : Ctx) : Set where
  •        : Eqs Γ
  _▷_>eq_  : Eqs Γ → Tm Γ 𝔹 → Bool → Eqs Γ 
\end{code}

Substituting equational contexts folds
substitution over the LHS terms.

\begin{code}
_[_]Eq : Eqs Γ → Tms[ q ] Δ Γ → Eqs Δ
•              [ δ ]Eq = •
(Ξ ▷ t >eq b)  [ δ ]Eq = (Ξ [ δ ]Eq) ▷ (t [ δ ]) >eq b
\end{code}

%if False
\begin{code}
variable
  Ξ Ψ Φ Ξ₁ Ξ₂ Ξ₃ Ψ₁ Ψ₂ Ψ₃ Ξ′ Ψ′ Φ′ : Eqs Γ
  b b₁ b₂ : Bool
\end{code}
%endif

Conversion relative to a set of in-scope equations can then be defined
inductively. Our starting point is to copy over the definition of β-conversion
given in \refsec{redconv} (specialised to our pair of type formers).

%if False
\begin{code}
data EqVar :  Eqs Γ → Tm Γ 𝔹 → Bool → Set where
  ez  : EqVar (Ξ ▷ t >eq b) t b
  es  : EqVar Ξ t b₁ → EqVar (Ξ ▷ u >eq b₂) t b₁
\end{code}
%endif

\begin{code}
data _⊢_~_ (Ξ : Eqs Γ) : Tm Γ A → Tm Γ A → Set where
  -- Equivalence
  rfl~ : Ξ ⊢ t ~ t
  sym~ : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ t₂ ~ t₁
  _∙~_ : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ t₂ ~ t₃ → Ξ ⊢ t₁ ~ t₃
  -- Congruence
  ƛ_   : Ξ [ wk ]Eq ⊢ t₁ ~ t₂ → Ξ ⊢ ƛ t₁ ~ ƛ t₂ 
  _·_  : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ u₁ ~ u₂ → Ξ ⊢ t₁ · u₁ ~ t₂ · u₂
  if   : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ u₁ ~ u₂ → Ξ ⊢ v₁ ~ v₂
       → Ξ ⊢ if t₁ u₁ v₁ ~ if t₂ u₂ v₂
  -- Computation
  ⇒β   : Ξ ⊢ (ƛ t) · u   ~ t [ < u > ]
  𝔹β₁  : Ξ ⊢ if TT  u v  ~ u
  𝔹β₂  : Ξ ⊢ if FF  u v  ~ v
\end{code}

We account for local equations by defining a type of evidence that 
a particular equation, |t >eq b|, occurs in an equational
context, |Ξ|: |EqVar Ξ t b|.

\begin{spec}
data EqVar :  Eqs Γ → Tm Γ 𝔹 → Bool → Set where
  ez  : EqVar (Ξ ▷ t >eq b) t b
  es  : EqVar Ξ t b₁ → EqVar (Ξ ▷ u >eq b₂) t b₁
\end{spec}

\begin{code}
  eq   : EqVar Ξ t b → Ξ ⊢ t ~ ⌜ b ⌝𝔹
\end{code}

Note that the congruence rule for ``|if|'' here is not \smart in the sense 
of \SC: we
do not introduce equations on the scrutinee in the branches.

\begin{spec}
  if  : Ξ ⊢ t₁ ~ t₂ → Ξ ▷ t₁ >eq true ⊢ u₁ ~ u₂ → Ξ ▷ t₁ >eq false ⊢ v₁ ~ v₂
      → Ξ ⊢ if t₁ u₁ v₁ ~ if t₂ u₂ v₂
\end{spec}

We will study the effect of locally introducing equations with rules like this 
later in section \refsec{localext}.

% Setoid reasoning combinators

%if False
\begin{code}
infixr 2 _~⟨_⟩~_
infix  3 _∎~

pattern _~⟨_⟩~_ x p q = _∙~_ {t₁ = x} p q
pattern _∎~ x = rfl~ {t = x}
\end{code}
%endif

Before moving on, we give a couple important definitions.

\begin{definition}[Definitional Inconsistency] \phantom{a}
\labdef{defincon}

We define definitionally inconsistent equational contexts
identically to the dependently typed setting (\refremark{eqcollapse}).
That is, contexts in which |TT| and |FF| are convertible.

\begin{code}
def-incon : Eqs Γ → Set
def-incon Ξ = Ξ ⊢ TT ~ FF
\end{code}
\end{definition}

Again, under definitionally-inconsistent contexts, all terms are convertible.

\begin{code}
collapse : def-incon Ξ → Ξ ⊢ u ~ v
collapse {u = u} {v = v} tf~ = 
  u
  ~⟨ sym~ 𝔹β₁ ⟩~
  if TT u v
  ~⟨ if tf~ rfl~ rfl~ ⟩~
  if FF u v
  ~⟨ 𝔹β₂ ⟩~
  v ∎~
\end{code}

However, because of the lack of computation at the level of types in
STLC (that is, the absence of large elimination), we do not get a 
type-level equality collapse. Definitional inconsistency is therefore a bit less
dangerous in the setting of STLC, but we must still keep the consequences it in 
mind when deciding conversion.

\begin{definition}[Equational Context Equivalence] \phantom{a}

We define equivalence of equational contexts observationally: two equational
contexts |Ξ₁| and |Ξ₂| are equivalent if they equate the same sets of
terms via conversion |_⊢_~_|.

\begin{code}
record _Eqs~_ (Ξ₁ Ξ₂ : Eqs Γ) : Set where field
    to    : Ξ₁ ⊢ t₁ ~ t₂ → Ξ₂ ⊢ t₁ ~ t₂
    from  : Ξ₂ ⊢ t₁ ~ t₂ → Ξ₁ ⊢ t₁ ~ t₂
\end{code}
\end{definition}

%if False
\begin{code}
open _Eqs~_

rflEqs~ : Ξ Eqs~ Ξ
rflEqs~ .to   t~ = t~
rflEqs~ .from t~ = t~

symEqs~ : Ξ₁ Eqs~ Ξ₂ → Ξ₂ Eqs~ Ξ₁
symEqs~ Ξ~ .to   = Ξ~ .from
symEqs~ Ξ~ .from = Ξ~ .to

_∙Eqs~_ : Ξ₁ Eqs~ Ξ₂ → Ξ₂ Eqs~ Ξ₃ → Ξ₁ Eqs~ Ξ₃
(Ξ~₁ ∙Eqs~ Ξ~₂) .to    t~ = Ξ~₂ .to    (Ξ~₁ .to    t~)
(Ξ~₁ ∙Eqs~ Ξ~₂) .from  t~ = Ξ~₁ .from  (Ξ~₂ .from  t~)
\end{code}
%endif

\subsection{Difficulties with Reduction}

Rewriting gives a nice intuition for the operational behaviour of 
these
equations (in the context |Γ ▷ t >eq true|, |t| should reduce to
|TT|), but declarative conversion being an equivalence by definition
makes it perhaps more powerful than we might initially expect.

For example, if we try to directly translate this definition of conversion 
into a small-step reduction relation 

\begin{code}
data _⊢_>′_ (Ξ : Eqs Γ) : Tm Γ A → Tm Γ A → Set where
  -- Computation
  ⇒β   : Ξ ⊢ (ƛ t) · u  >′ t [ < u > ]
  𝔹β₁  : Ξ ⊢ if TT u v  >′ u 
  𝔹β₂  : Ξ ⊢ if FF u v  >′ v
  
  -- Rewriting
  rw : EqVar Ξ t b → Ξ ⊢ t >′ ⌜ b ⌝𝔹

  -- Monotonicity
  ƛ_   : Ξ [ wk ]Eq  ⊢ t₁  >′ t₂  → Ξ ⊢ ƛ t₁       >′ ƛ t₂ 
  l·   : Ξ           ⊢ t₁  >′ t₂  → Ξ ⊢ t₁ · u     >′ t₂ · u
  ·r   : Ξ           ⊢ u₁  >′ u₂  → Ξ ⊢ t · u₁     >′ t · u₂
  if₁  : Ξ           ⊢ t₁  >′ t₂  → Ξ ⊢ if t₁ u v  >′ if t₂ u v
  if₂  : Ξ           ⊢ u₁  >′ u₂  → Ξ ⊢ if t u₁ v  >′ if t u₂ v
  if₃  : Ξ           ⊢ v₁  >′ v₂  → Ξ ⊢ if t u v₁  >′ if t u v₂
\end{code}

%if False
\begin{code}
_⊢_>′*_ : Eqs Γ → Tm Γ A → Tm Γ A → Set 
Ξ ⊢ t₁ >′* t₂ = t₁ [ Ξ ⊢_>′_ ]* t₂

postulate
\end{code}
%endif

while we do at least stay conservative over conversion

\begin{code}
  pres>′ : Ξ ⊢ t₁ >′ t₂ → Ξ ⊢ t₁ ~ t₂
\end{code}

we find that the induced notion of algorithmic convertibility is much weaker
than our declarative specification. Problems arise from how the LHS
terms in contextual equations need not themselves be irreducible, so e.g.
in the equational context |• ▷ if TT TT v >eq false|, we can derive 
|TT ~ FF|, but not |TT >* FF| (or |FF >* TT|)

\begin{code}
ex1 : • ▷ if TT TT v >eq false ⊢ TT ~ FF
ex1 {v = v} =
  TT
  ~⟨ sym~ 𝔹β₁ ⟩~
  if TT TT v
  ~⟨ eq ez ⟩~
  FF ∎~

ex2 : ¬ • ▷ if TT FF v >eq true ⊢ TT >′* FF
ex2 (rw (es ()) ∶> _)
\end{code}

This reduction relation has other problems as well. In the
context |• ▷ TT >eq true|, reduction is not well-founded\remarknote{There is an
infinite chain of reduction |TT > TT > TT > ...|.} and in
the context |• ▷ TT >eq false|, reduction is non-confluent\remarknote{We can
pick two terms |u| and |v| such that |¬ u > v|, e.g. 
the Church Booleans |u = ƛ x y. x| and |v = ƛ x y. y|, and then start with the
term |if TT u v|. We can either reduce with |β𝔹₁| directly and get
|if TT u v > u| or we can apply the rewrite and follow up with |β𝔹₂|,
obtaining |if TT u v > if FF u v > v|.}.

The situation is slightly improved by explicitly preventing rewriting
of terms that are syntactically equal to closed Booleans:

\begin{code}
𝔹? : Tm Γ A → Bool
𝔹? TT = true
𝔹? FF = true
𝔹? _  = false
\end{code}

%if False
\begin{code}
data _⊢_>_ (Ξ : Eqs Γ) : Tm Γ A → Tm Γ A → Set where
  -- Computation
  ⇒β   : Ξ ⊢ (ƛ t) · u  > t [ < u > ]
  𝔹β₁  : Ξ ⊢ if TT u v  > u 
  𝔹β₂  : Ξ ⊢ if FF u v  > v

  -- Monotonicity
  ƛ_   : Ξ [ wk ]Eq  ⊢ t₁  > t₂  → Ξ ⊢ ƛ t₁       > ƛ t₂ 
  l·   : Ξ           ⊢ t₁  > t₂  → Ξ ⊢ t₁ · u     > t₂ · u
  ·r   : Ξ           ⊢ u₁  > u₂  → Ξ ⊢ t · u₁     > t · u₂
  if₁  : Ξ           ⊢ t₁  > t₂  → Ξ ⊢ if t₁ u v  > if t₂ u v
  if₂  : Ξ           ⊢ u₁  > u₂  → Ξ ⊢ if t u₁ v  > if t u₂ v
  if₃  : Ξ           ⊢ v₁  > v₂  → Ξ ⊢ if t u v₁  > if t u v₂
\end{code} 
%endif

\begin{code}
  rw : ¬is 𝔹? t → EqVar Ξ t b → Ξ ⊢ t > ⌜ b ⌝𝔹
\end{code}

%if False
\begin{code}
_⊢_>*_ : Eqs Γ → Tm Γ A → Tm Γ A → Set 
Ξ ⊢ t₁ >* t₂ = t₁ [ Ξ ⊢_>_ ]* t₂

postulate pres>* : Ξ ⊢ t₁ >* t₂ → Ξ ⊢ t₁ ~ t₂
\end{code}
%endif

|_⊢_>_| is now even weaker, and is still non-confluent, but
as it turns out, it is strongly normalising! More significantly, we will
show that this reduction stays strongly normalising 
even without the |EqVar Ξ t b| pre-condition on |rw|\sideremark{Removing this
pre-condition is equivalent to being allowed to ``swap'' the equational
context after every reduction.
\nocodeindent
\begin{code}
_>swap_  : Tm Γ A → Tm Γ A 
         → Set
_>swap_ {Γ = Γ} t₁ t₂ 
  = Σ⟨ Ξ ∶ Eqs Γ ⟩× Ξ ⊢ t₁ > t₂
\end{code}
\resetcodeindent
Intuitively, this is a useful property, because it allows us to freely
modify the equational context while performing well-founded induction.
}. 
Intuitively, closed Booleans
are irreducible, so reduction chains which collapse the entire |𝔹|-typed term
to a closed Boolean with |rw| must terminate at that point, but of course
replacing subterms in some large expression with |TT| or |FF| can unlock new
reductions, so well-foundedness is not completely trivial.

\pagebreak
\section{Normalisation via Completion}
\labsec{simplenormcompl}

In the prior section, we ended by gesturing at a reduction relation similar to
|_⊢_>_|, but without a pre-condition on Boolean rewriting (beyond the LHS not 
already being a closed Boolean). We will now make this
notion concrete, and name it \emph{spontaneous reduction} (|𝔹|-typed terms may
``spontaneously'' collapse to |TT| or |FF|).

\sideremark{Recall that |¬is 𝔹?| here 
ensures that |t| is not
already a closed Boolean, preventing reductions like |TT >! TT|.}

\begin{code}
data _>!_ : Tm Γ A → Tm Γ A → Set where
  -- Computation
  ⇒β   : (ƛ t) · u  >! t [ < u > ]
  𝔹β₁  : if TT u v  >! u 
  𝔹β₂  : if FF u v  >! v
  
  -- Spontaneous rewriting
  rw : ¬is 𝔹? t → t >! ⌜ b ⌝𝔹

  -- Monotonicity
  ƛ_   : t₁  >! t₂  → ƛ t₁       >! ƛ t₂ 
  l·   : t₁  >! t₂  → t₁ · u     >! t₂ · u
  ·r   : u₁  >! u₂  → t · u₁     >! t · u₂
  if₁  : t₁  >! t₂  → if t₁ u v  >! if t₂ u v
  if₂  : u₁  >! u₂  → if t u₁ v  >! if t u₂ v
  if₃  : v₁  >! v₂  → if t u v₁  >! if t u v₂
\end{code}

In \refsec{snspont} we will prove that |_>!_| is strongly normalising. Before
we dive into that proof though, we will show how to derive a normalisation 
algorithm using this result.

% TODO: Cite Knuth-Bendix somewhere?
The key idea here will be \emph{completion}. We call equational contexts where
every LHS is irreducible w.r.t. all other equations 
\emph{complete}\remarknote{Slightly confusingly, equational contexts being 
\emph{complete} is required to prove \emph{soundness}
of normalisation (to ensure we appropriately identify
all convertible terms and do not miss any reductions),
rather than completeness (which will ultimately be provable by 
|Ξ ⊢_>_| being contained in |Ξ ⊢_~_|).}.

\begin{code}
Stk : Eqs Γ → Tm Γ A → Set
Stk Ξ t = ∀ u → ¬ Ξ ⊢ t > u 

_-_ : ∀ (Ξ : Eqs Γ) → EqVar Ξ t b → Eqs Γ
(Ξ ▷ t >eq b)   - ez    = Ξ
(Ξ ▷ u >eq b′)  - es e  = (Ξ - e) ▷ u >eq b′

data AllStk (Ξ : Eqs Γ) : Eqs Γ → Set where
  •    : AllStk Ξ •
  _▷_  : AllStk Ξ Ψ 
       → ∀ (e : EqVar Ξ t b) → ¬is 𝔹? t
       → Stk (Ξ - e) t → AllStk Ξ (Ψ ▷ t >eq b)

Complete : Eqs Γ → Set
Complete Ξ = AllStk Ξ Ξ
\end{code}

%if False
\begin{code}
postulate 
  _[_]Eqsᶜ : Complete Ξ → ∀ (δ : Ren Δ Γ) → Complete (Ξ [ δ ]Eq) 
\end{code} 
%endif

Under complete equational contexts |Ξ|, there are no critical pairs
w.r.t. |Ξ ⊢_>_| (LHSs cannot overlap). Therefore, we can prove that 
reduction is 
confluent (ordinary
β-reduction cases are dealt with by switching to parallel reduction
\sidecite{takahashi1995parallel} - we know the new |rw| case can only apply if 
the term is otherwise irreducible from |Stk (Ξ - e) t|).

\begin{code}
  compl-confl  : Complete Ξ → Ξ ⊢ t >* u → Ξ ⊢ t >* v
               → Σ⟨ w ∶ Tm Γ A ⟩× (Ξ ⊢ u >* w × Ξ ⊢ v >* w)
\end{code} 

We can define algorithmic conversion and, via confluence, prove that declarative
conversion is preserved.

\begin{code}
record _⊢_<~>_ (Ξ : Eqs Γ) (t₁ t₂ : Tm Γ A) : Set where 
  constructor _∣_
  field
    {common}  : Tm Γ A
    reduces₁  : Ξ ⊢ t₁ >* common
    reduces₂  : Ξ ⊢ t₂ >* common
\end{code} 

%if False
\begin{code}
open _⊢_<~>_
\end{code} 
%endif

\begin{code}
<~>-trans : Complete Ξ → Ξ ⊢ t₁ <~> t₂ → Ξ ⊢ t₂ <~> t₃ → Ξ ⊢ t₁ <~> t₃
<~>-trans Ξᶜ (t₁> ∣ t₂>) (t₂>′ ∣ t₃>) 
  using w Σ, t₁>′ Σ, t₃>′ ← compl-confl Ξᶜ t₂> t₂>′
  = (t₁> ∘* t₁>′) ∣ (t₃> ∘* t₃>′) 

<~>-pres : Complete Ξ → Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ t₁ <~> t₂
\end{code}

Algorithmic convertibility of stuck terms implies syntactic equality 
(|Stk<~>|), so 
we can further derive uniqueness of normal forms (stuck terms under complete
equational context reduction).

\begin{code}
Stk>* : Stk Ξ t₁ → Ξ ⊢ t₁ >* t₂ → t₁ ≡ t₂
Stk>* ¬t₁> rfl*           = refl
Stk>* ¬t₁> (t₁> ∶> t₁>*)  = ⊥-elim (¬t₁> _ t₁>)

Stk<~> : Stk Ξ t₁ → Stk Ξ t₂ → Ξ ⊢ t₁ <~> t₂ → t₁ ≡ t₂
Stk<~> ¬t₁> ¬t₂> (t₁>* ∣ t₂>*) = Stk>* ¬t₁> t₁>* ∙ sym (Stk>* ¬t₂> t₂>*)

nf-uniq : Complete Ξ → Stk Ξ t₁ → Stk Ξ t₂ → Ξ ⊢ t₁ ~ t₂ → t₁ ≡ t₂
nf-uniq Ξᶜ ¬t₁> ¬t₂> t~ = Stk<~> ¬t₁> ¬t₂> (<~>-pres Ξᶜ t~)
\end{code}

%if False
\begin{code}
postulate
  ƛ<~>   : (Ξ [ wk ]Eq) ⊢ t₁ <~> t₂ → Ξ ⊢ (ƛ t₁) <~> (ƛ t₂)
  ·<~>   : Ξ ⊢ t₁ <~> t₂ → Ξ ⊢ u₁ <~> u₂ → Ξ ⊢ (t₁ · u₁) <~> (t₂ · u₂)
  if<~>  : Ξ ⊢ t₁ <~> t₂ → Ξ ⊢ u₁ <~> u₂ → Ξ ⊢ v₁ <~> v₂
         → Ξ ⊢ if t₁ u₁ v₁ <~> if t₂ u₂ v₂
  Complete¬𝔹 : Complete Ξ → EqVar Ξ t b → ¬is 𝔹? t

<~>-sym : Ξ ⊢ t₁ <~> t₂ → Ξ ⊢ t₂ <~> t₁
<~>-sym (t₁> ∣ t₂>) = t₂> ∣ t₁>

<~>-pres Ξᶜ rfl~ = rfl* ∣ rfl*
<~>-pres Ξᶜ (sym~ t~) = <~>-sym (<~>-pres Ξᶜ t~)
<~>-pres Ξᶜ (t~₁ ∙~ t~₂) = <~>-trans Ξᶜ (<~>-pres Ξᶜ t~₁) (<~>-pres Ξᶜ t~₂)
<~>-pres Ξᶜ ⇒β = ⟪ ⇒β ⟫* ∣ rfl*
<~>-pres Ξᶜ 𝔹β₁ = ⟪ 𝔹β₁ ⟫* ∣ rfl*
<~>-pres Ξᶜ 𝔹β₂ = ⟪ 𝔹β₂ ⟫* ∣ rfl*
<~>-pres Ξᶜ (eq i) = ⟪ rw (Complete¬𝔹 Ξᶜ i) i ⟫* ∣ rfl*
<~>-pres Ξᶜ (ƛ t~) = ƛ<~> (<~>-pres (Ξᶜ [ wk ]Eqsᶜ) t~)
<~>-pres Ξᶜ (t~ · u~) = ·<~> (<~>-pres Ξᶜ t~) (<~>-pres Ξᶜ u~)
<~>-pres Ξᶜ (if t~ u~ v~) 
  = if<~> (<~>-pres Ξᶜ t~) (<~>-pres Ξᶜ u~) (<~>-pres Ξᶜ v~)
\end{code}
%endif

We now specify the completion algorithm as a function that completes equational
contexts while preserving equivalence.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  complete′        : Eqs Γ → Eqs Γ
  complete-pres′   : Ξ Eqs~ complete′ Ξ
  complete-compl′  : Complete (complete′ Ξ) 
\end{code}

Under complete equational contexts |Ξ|, we have shown that 
algorithmic
conversion induced by |Ξ ⊢_>eq_| is equivalent to declarative conversion
|Ξ ⊢_~_|. Therefore, we can obtain a sound and complete normalisation
algorithm from completion and the existence of a function which fully reduces 
terms w.r.t. |Ξ ⊢_>eq_|.

%if False
\begin{code}
≡~ : t₁ ≡ t₂ → Ξ ⊢ t₁ ~ t₂
≡~ refl = rfl~

postulate
\end{code}
%endif

\sideremark{Decidability of convertibility normal forms (terms which are |Stk| 
w.r.t. |Complete| equational contexts) follows from decidability of syntactic
equality on first-order datatypes.}

\sideremark{``|reduce|'' fully reduces terms w.r.t. |_⊢_>_|.}

\begin{code}
  reduce          : Eqs Γ → Tm Γ A → Tm Γ A
  reduce-reduces  : Ξ ⊢ t >* reduce Ξ t 
  reduce-Stk      : Stk Ξ (reduce Ξ t)
\end{code}
\begin{code}
norm′ : Eqs Γ → Tm Γ A → Tm Γ A
norm′ Ξ t = reduce (complete′ Ξ) t

reduce-pres : Ξ ⊢ t ~ reduce Ξ t
reduce-pres = pres>* reduce-reduces

norm-sound′ : Ξ ⊢ t₁ ~ t₂ → norm′ Ξ t₁ ≡ norm′ Ξ t₂
norm-sound′ {Ξ = Ξ} {t₁ = t₁} {t₂ = t₂} t~
  =  nf-uniq complete-compl′ reduce-Stk reduce-Stk (
     norm′ Ξ t₁
     ~⟨ sym~ reduce-pres ⟩~
     t₁ 
     ~⟨ complete-pres′ .to t~ ⟩~
     t₂
     ~⟨ reduce-pres ⟩~
     norm′ Ξ t₂ ∎~)

norm-pres′ : Ξ ⊢ t ~ norm′ Ξ t 
norm-pres′ = complete-pres′ .from reduce-pres

norm-compl′ : norm′ Ξ t₁ ≡ norm′ Ξ t₂ → Ξ ⊢ t₁ ~ t₂
norm-compl′ {Ξ = Ξ} {t₁ = t₁} {t₂ = t₂} t≡ = 
  t₁
  ~⟨ norm-pres′ ⟩~
  norm′ Ξ t₁
  ~⟨ ≡~ t≡ ⟩~ 
  norm′ Ξ t₂
  ~⟨ sym~ norm-pres′ ⟩~
  t₂ ∎~
\end{code}

There is a remaining subtlety: completion as specified cannot be implemented
on definitionally inconsistent contexts. 
Specifically, it is provable that in all equational contexts satisfying
|Complete|, deriving |Ξ ⊢ TT ~ FF| is impossible, so clearly completion
cannot preserve context equivalence in these cases.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  complete-not-incon : Complete Ξ → ¬ Ξ ⊢ TT ~ FF
\end{code}

\begin{code}
contradiction : ⊥
contradiction 
  = complete-not-incon (complete-compl′ {Ξ = Ξ⊥}) (complete-pres′ .to (eq ez))
  where Ξ⊥ = • ▷ TT {Γ = •} >eq false
\end{code}

It follows that completion in our setting should be \textit{partial}. 
We will either
complete an equational environment, or discover a syntactically
inconsistent equation like |TT >eq false|
and conclude that it is definitionally inconsistent.

Our corrected specification of completion is (we fuse the
correctness conditions with the definition to simplify the spec)

\begin{code}
data Complete? (Ξ : Eqs Γ) : Set where
  compl  : ∀ Ξ′ → Ξ Eqs~ Ξ′ → Complete Ξ′ → Complete? Ξ
  !!     : def-incon Ξ → Complete? Ξ

complete  : ∀ (Ξ : Eqs Γ) → Complete? Ξ
\end{code}

We also have to update our definition of normal forms. In definitionally
inconsistent contexts, all terms are convertible, so our normal forms 
be characterised by the unit type.


\sideremark{Note that these normal forms do not cleanly embed back into
the STLC terms (all information about the structure of the term is lost
in the case of inconsistent contexts) but we can still decide equality
by first completing the context, and then either syntactically comparing
stuck terms (the |Stk| part is proof-irrelevant and so can be ignored)
or immediately returning reflexivity.}

\begin{code}
Nf : ∀ Γ (Ξ : Eqs Γ) → Ty → Complete? Ξ → Set
Nf Γ Ξ A (compl Ξ′ _ _)  = Σ⟨ t ∶ Tm Γ A ⟩× Stk Ξ′ t
Nf Γ Ξ A (!! _)          = ⊤

norm           : ∀ (Ξ : Eqs Γ) → Tm Γ A → Nf Γ Ξ A (complete Ξ) 
\end{code}
%if False
\begin{code}
postulate
\end{code}
%endif
\begin{code}
  norm-sound     : Ξ ⊢ t₁ ~ t₂ → norm Ξ t₁ ≡ norm Ξ t₂
  norm-complete  : norm Ξ t₁ ≡ norm Ξ t₂ → Ξ ⊢ t₁ ~ t₂
\end{code}

Normalisation can then be implemented as before in the case completion succeeds
(i.e. returns |compl ...|) or otherwise can just return |tt|.

\begin{code}
norm Ξ t with complete Ξ
... | compl Ξ′ _ _  = reduce Ξ′ t Σ, reduce-Stk
... | !! _          = tt
\end{code}

Of course, this normalisation function is only actually implementable
if we can define |complete| and |reduce| with all appropriate correctness
conditions. Given well-foundedness of |_>!_|, |reduce| can be defined 
very similarly to naive normalisation as in \refsec{naive} (recurse
over the term, contracting redexes where possible, now additionally checking
for rewrites by syntactically comparing subterms to LHSs in the equational
context). |complete| then can be implemented by repeatedly reducing LHS terms,
with termination justified by extending |_>!_| lexicographically over the
% TODO: We have written some of the Agda for this, might be worth adding
equational context.

%if False
\begin{code}
-- TODO: I want to eventually put a real implementation of |complete| here
-- in terms of |reduce| - I don't think it will be too hard.
postulate complete-impl : ∀ (Ξ : Eqs Γ) → Complete? Ξ

complete = complete-impl
\end{code}
%endif
