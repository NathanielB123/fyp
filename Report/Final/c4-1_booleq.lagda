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


infix 4 _~_ _⊢_~_ _⊢_>′_ _⊢_>′*_ _⊢_>_ _⊢_>*_ _>!_ _Eqs>!_ EqsClosure
infixr 4 _∙~_
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{STLC Modulo Equations}
\labch{simply}





\section{STLC with Boolean Equations}

We begin our exploration of \SC or local equality reflection by
studying convertability of STLC terms modulo equations.
We will start with an extremely restricted set of equations, being only
those of the form |t == b| where |t| is a |𝔹|-typed term and |b| is a closed
Boolean.

We will use an intrinsically-typed syntax
with recursive substitutions following \refsec{stlcrec}, containing
|⇒| and |𝔹| type formers, with their standard introduction and elimination
rules.
Note that simply-typed |if|-expressions require the left and right branches to 
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

We will package the set of equations we decide conversion modulo into
``equational contexts''. For our restricted set of equations, these take
the form of lists of pairs of |𝔹|-typed terms
and closed Booleans. Substitutions on equational contexts folds
substitution over the LHS terms.

\begin{code}
data Eqs (Γ : Ctx) : Set where
  •        : Eqs Γ
  _▷_>eq_  : Eqs Γ → Tm Γ 𝔹 → Bool → Eqs Γ 

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
inductively.

\begin{code}
data EqVar :  Eqs Γ → Tm Γ 𝔹 → Bool → Set 
data _⊢_~_ (Ξ : Eqs Γ) : Tm Γ A → Tm Γ A → Set

data EqVar where
  ez  : EqVar (Ξ ▷ t >eq b) t b
  es  : EqVar Ξ t b₁ → EqVar (Ξ ▷ u >eq b₂) t b₁
  
data _⊢_~_ Ξ where
    -- Equivalence
  rfl~ : Ξ ⊢ t ~ t
  sym~ : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ t₂ ~ t₁
  _∙~_ : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ t₂ ~ t₃ → Ξ ⊢ t₁ ~ t₃

  -- Computation
  ⇒β   : Ξ ⊢ (ƛ t) · u   ~ t [ < u > ]
  𝔹β₁  : Ξ ⊢ if TT  u v  ~ u
  𝔹β₂  : Ξ ⊢ if FF  u v  ~ v

  -- Local equations
  eq   : EqVar Ξ t b → Ξ ⊢ t ~ ⌜ b ⌝𝔹

  -- Congruence
  ƛ_   : Ξ [ wk ]Eq ⊢ t₁ ~ t₂ → Ξ ⊢ ƛ t₁ ~ ƛ t₂ 
  _·_  : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ u₁ ~ u₂ → Ξ ⊢ t₁ · u₁ ~ t₂ · u₂
  if   : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ u₁ ~ u₂ → Ξ ⊢ v₁ ~ v₂
       → Ξ ⊢ if t₁ u₁ v₁ ~ if t₂ u₂ v₂
\end{code}

Note that the rule for |if| here is not ``smart'' in the sense of \SC: we
do not introduce equations on the scrutinee in the branches.

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

We define definitionally inconsistent equational contexts
% I don't think we have a definition of this yet - should probably go
% in preliminaries
identically to the dependently typed setting (TODO REF HERE)

\begin{code}
def-incon : Eqs Γ → Set
def-incon Ξ = Ξ ⊢ TT ~ FF
\end{code}

Again, under definitionally-inconsistent contexts, all terms are convertible
(``equality collapse'' \sidecite{conor2010wtypes}).

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
\end{definition}

\begin{definition}[Equational Context Equivalence] \phantom{a}
\labdef{defincon}

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
symEqs~ : Ξ₁ Eqs~ Ξ₂ → Ξ₂ Eqs~ Ξ₁
_∙Eqs~_ : Ξ₁ Eqs~ Ξ₂ → Ξ₂ Eqs~ Ξ₃ → Ξ₁ Eqs~ Ξ₃
\end{code}
%endif

\subsection{Difficulties with Reduction}

Rewriting gives a nice intution for the operational behaviour of 
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
\end{code}
%endif

we do at least stay conservative over conversion

\begin{code}
pres>′ : Ξ ⊢ t₁ >′ t₂ → Ξ ⊢ t₁ ~ t₂
\end{code}

we find that the induced notion of algorithmic convertability is much weaker
that our declarative specification. Note that the LHS
terms in contextual equations need not themselves be irreducible, so e.g.
in the equational context |• ▷ if TT TT v >eq false|, we can derive 
|TT ~ FF|, but not |TT >* FF| (or |FF >* TT|)

\begin{code}
ex1 : • ▷ if TT TT v >eq false ⊢ TT ~ FF
ex1 = sym~ 𝔹β₁ ∙~ eq ez

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

We can slightly improve the situation by explicitly preventing rewriting
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

pres>* : Ξ ⊢ t₁ >* t₂ → Ξ ⊢ t₁ ~ t₂
\end{code}
%endif

|_⊢_>_| is now even weaker, and is still non-confluent, but
as it turns out, it is strongly normalising! More significantly, we will
show that this reduction stays strongly normalising 
even without the |EqVar Ξ t b| pre-condition on |rw|\sideremark{Removing this
pre-condition is equivalent to being allowed to ``swap out'' the equational
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

\section{Normalisation via Completion}

In the prior section, we ended by gesturing at a reduction relation similar to
|_⊢_>_|, but without a pre-condition on rewriting. We will now make this
notion concrete, and name it ``spontaneous reduction'' (|𝔹|-typed terms may
``spontaneously'' collapse to |TT| or |FF|).

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
The key idea here will be ``completion''. We call equational contexts for
which every LHS is irreducible w.r.t. all other equations 
``complete''\remarknote{Slightly confusingly, equational contexts being 
``complete'' is required to prove \textit{soundness}
of normalisation (i.e. to ensure we appropriately identify
all convertible terms and not miss any reductions),
rather than completeness (which will ultimately be provable by 
|Ξ ⊢_>*_| being contained in |Ξ ⊢_~_|). 
I think this is ultimately just down to
terminology arising from slightly different fields happening to conflict.}.

\begin{code}
Stk : Eqs Γ → Tm Γ A → Set
Stk Ξ t = ∀ u → ¬ Ξ ⊢ t > u 

_-_ : ∀ (Ξ : Eqs Γ) → EqVar Ξ t b → Eqs Γ
(Ξ ▷ t >eq b)  - ez   = Ξ
(Ξ ▷ u >eq b′) - es e = (Ξ - e) ▷ u >eq b′

data AllStk (Ξ : Eqs Γ) : Eqs Γ → Set where
  •   : AllStk Ξ •
  _▷_ : AllStk Ξ Ψ 
      → ∀ (e : EqVar Ξ t b) 
      → ¬is 𝔹? t
      → Stk (Ξ - e) t → AllStk Ξ (Ψ ▷ t >eq b)

Complete : Eqs Γ → Set
Complete Ξ = AllStk Ξ Ξ
\end{code}

Under complete equational contexts, there are no critical pairs (terms do not
overlap), so we can prove that reduction is confluent (ordinary
β-reduction cases are dealt with by switching to parallel reduction
\sidecite{takahashi1995parallel} - we know the new |rw| case can only apply if 
the term is otherwise irreducible from |Stk (Ξ - e) t|).

\begin{code}
compl-confl  : Complete Ξ → Ξ ⊢ t >* u → Ξ ⊢ t >* v
             → Σ⟨ w ∶ Tm Γ A ⟩× (Ξ ⊢ u >* w × Ξ ⊢ v >* w)
\end{code} 

Therefore, we can define algorithmic conversion and prove that declarative
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

Algorithmic of convertability of stuck terms implies syntactic equality 
(|Stk<~>|), so 
we can further derive uniqueness of normal forms (stuck terms under complete
equational context reduction).

\begin{code}
Stk>* : Stk Ξ t₁ → Ξ ⊢ t₁ >* t₂ → t₁ ≡ t₂
Stk>* ¬t₁> ε              = refl
Stk>* ¬t₁> (t₁> ∶> t₁>*)  = ⊥-elim (¬t₁> _ t₁>)

Stk<~> : Stk Ξ t₁ → Stk Ξ t₂ → Ξ ⊢ t₁ <~> t₂ → t₁ ≡ t₂
Stk<~> ¬t₁> ¬t₂> (t₁>* ∣ t₂>*) = Stk>* ¬t₁> t₁>* ∙ sym (Stk>* ¬t₂> t₂>*)

nf-uniq : Complete Ξ → Stk Ξ t₁ → Stk Ξ t₂ → Ξ ⊢ t₁ ~ t₂ → t₁ ≡ t₂
nf-uniq Ξᶜ ¬t₁> ¬t₂> t~ = Stk<~> ¬t₁> ¬t₂> (<~>-pres Ξᶜ t~)
\end{code}

%if False
\begin{code}
<~>-pres Ξᶜ rfl~ = {!   !}
<~>-pres Ξᶜ (sym~ t~) = {!   !}
<~>-pres Ξᶜ (t~₁ ∙~ t~₂) = <~>-trans Ξᶜ (<~>-pres Ξᶜ t~₁) (<~>-pres Ξᶜ t~₂)
<~>-pres Ξᶜ ⇒β = {!   !}
<~>-pres Ξᶜ 𝔹β₁ = {!   !}
<~>-pres Ξᶜ 𝔹β₂ = {!   !}
<~>-pres Ξᶜ (eq x) = {!   !}
<~>-pres Ξᶜ (ƛ t~) = {!   !}
<~>-pres Ξᶜ (t~ · t~₁) = {!   !}
<~>-pres Ξᶜ (if t~ t~₁ t~₂) = {!   !}

compl¬𝔹 : Complete Ξ → EqVar Ξ t b → ¬is 𝔹? t
\end{code}
%endif

We now specify the completion algorithm as a function that completes equational
contexts whiile preserving equivalence.

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
\end{code}
%endif

\sideremark{Decidability of normal forms (terms which are |Stk| w.r.t.
|Complete| equational environments) follows from decidability of syntactic
equality on first-order datatypes.}

\begin{code}
-- |reduce| fully reduces terms w.r.t. |_⊢_>_|
reduce          : Eqs Γ → Tm Γ A → Tm Γ A
reduce-reduces  : Ξ ⊢ t >* reduce Ξ t 
reduce-Stk      : Stk Ξ (reduce Ξ t)

norm : Eqs Γ → Tm Γ A → Tm Γ A
norm Ξ t = reduce (complete′ Ξ) t

reduce-pres : Ξ ⊢ t ~ reduce Ξ t
reduce-pres = pres>* reduce-reduces

norm-sound : Ξ ⊢ t₁ ~ t₂ → norm Ξ t₁ ≡ norm Ξ t₂
norm-sound {Ξ = Ξ} {t₁ = t₁} {t₂ = t₂} t~
  =  nf-uniq complete-compl′ reduce-Stk reduce-Stk (
     norm Ξ t₁
     ~⟨ sym~ reduce-pres ⟩~
     t₁ 
     ~⟨ complete-pres′ .to t~ ⟩~
     t₂
     ~⟨ reduce-pres ⟩~
     norm Ξ t₂ ∎~)

norm-pres : Ξ ⊢ t ~ norm Ξ t 
norm-pres = complete-pres′ .from reduce-pres

norm-compl : norm Ξ t₁ ≡ norm Ξ t₂ → Ξ ⊢ t₁ ~ t₂
norm-compl {Ξ = Ξ} {t₁ = t₁} {t₂ = t₂} t≡ = 
  t₁
  ~⟨ norm-pres ⟩~
  norm Ξ t₁
  ~⟨ ≡~ t≡ ⟩~ 
  norm Ξ t₂
  ~⟨ sym~ norm-pres ⟩~
  t₂ ∎~
\end{code}

There is a remaining subtlety: completion as specified cannot be implemented
on definitionally inconsistent contexts. 
Specifically, it is provable that in all equational contexts satisfying
|Complete|, deriving |Ξ ⊢ TT ~ FF| is impossible, so clearly completion
cannot preserve context equivalence in these cases.

\begin{code}
complete-not-incon : Complete Ξ → ¬ Ξ ⊢ TT ~ FF

contradiction : ⊥
contradiction 
  = complete-not-incon (complete-compl′ {Ξ = Ξ⊥}) (complete-pres′ .to (eq ez))
  where Ξ⊥ = • ▷ TT {Γ = •} >eq false
\end{code}

Completion in our setting should be \textit{partial}. We will either
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


\remark{Note that these normal forms do not cleanly embed back into
the terms syntax (all information about the structure of the term is lost
in the case of inconsistent contexts) but we can still decide equality
by first completing the context, and then either syntactically comparing
stuck terms (the |Stk| part is proof-irrelevant and so can be ignored)
or immediately returning reflexivity.}

\begin{code}
Nf : ∀ Γ (Ξ : Eqs Γ) → Ty → Complete? Ξ → Set
Nf Γ Ξ A (compl Ξ′ _ _)  = Σ⟨ t ∶ Tm Γ A ⟩× Stk Ξ′ t
Nf Γ Ξ A (!! _)          = ⊤

norm′           : ∀ (Ξ : Eqs Γ) → Tm Γ A → Nf Γ Ξ A (complete Ξ) 
norm-sound′     : Ξ ⊢ t₁ ~ t₂ → norm Ξ t₁ ≡ norm Ξ t₂
norm-complete′  : norm Ξ t₁ ≡ norm Ξ t₂ → Ξ ⊢ t₁ ~ t₂
\end{code}

Normalisation can then be implemented as before in the case completion succeeds
(i.e. returns |compl ...|) or otherwise can just return |tt|.

\begin{code}
norm′ Ξ t with complete Ξ
... | compl Ξ′ _ _  = reduce Ξ′ t Σ, reduce-Stk
... | !! _          = tt
\end{code}

Of course, this normalisation function is only actually implementable
if we can define |complete| and |reduce| with all appropriate correctness
conditions. Given well-foundedness of |_>!_|, |reduce| can be defined 
very similarly to naive normalisation as in \refsec{naive} (recurse
over the term, contracting redexes where possible, now additionally checking
for rewrites by syntactically comparing subterms to LHSs in the equational
context). |complete| then can be implemented by repeatedly reducing terms,
with termination justified by extending |_>!_| lexicographically over the
% TODO: We have written some of the Agda for this, might be worth adding
equational context.
