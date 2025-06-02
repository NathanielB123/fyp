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

\chapter{Simply Typed Lambda Calculus with Closed Boolean Rewrites}
\labch{simply}

\section{Conversion Modulo Equations}

We begin our exploration of local rewriting by looking at a simply-typed
analogue of the problem: coming up with a more powerful conversion relation
for STLC with Booleans. Our starting point is an intrinsically-typed syntax
with recursive substitutions following \refsec{stlcrec}.
Simply-typed |if|-expressions require the left and right branches to have
exactly the same type.

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

With computation rules

%if False
\begin{code}
data _~_ : Tm Γ A → Tm Γ A → Set where
\end{code}
%endif

\begin{code}
  𝔹β₁  : if TT  u v ~ u
  𝔹β₂  : if FF  u v ~ v
\end{code}

With β-equality alone, we quickly get stuck if the scrutinee is a variable.
E.g. equations like |if t u u ~ u| or |if t t u ~ TT|. As mentioned in
(TODO REFERENCE RELATED WORK), strict η for Booleans can make such
such equations derivable.

\begin{code}
𝔹η : u [ < t > ] ~ if t (u [ < TT > ]) (v [ < FF > ])
\end{code}

However, I claim that |𝔹η| is too strong. Existing normalisation algorithms
all rely on effectively splitting on every Boolean neutral, requiring
re-normalising on the order of $2^n$ times, where $n$ is the number 
of distinct neutral Boolean subterms. 

%TODO Finish writing this

We define equational contexts as a lists of pairs of |𝔹|-typed terms
and closed Booleans. Substitutions on equational contexts are folds of
substitution on terms.

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
\end{code}

Congruence over |if| is a bit more subtle. The direct congruence rule is
valid:
\begin{spec}
  if  : Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ u₁ ~ u₂ → Ξ ⊢ v₁ ~ v₂
      → Ξ ⊢ if t₁ u₁ v₁ ~ if t₂ u₂ v₂
\end{spec}

But is not quite what we want: |_⊢_~_| should not only identify
terms modulo a fixed set of Boolean equations. We should be introducing
new equations in the branches of each |if| expression, i.e.

\begin{code}
  if  : Ξ ⊢ t₁ ~ t₂ → Ξ ▷ t₁ >eq true ⊢ u₁ ~ u₂ → Ξ ▷ t₁ >eq false ⊢ v₁ ~ v₂
      → Ξ ⊢ if t₁ u₁ v₁ ~ if t₂ u₂ v₂
\end{code}

We somewhat arbitrarily insert |t₁|, rather than |t₂|, into the equational
context. From stability of conversion over
weakening the
equational context
(i.e. adding new equations), we find the
choice here is ultimately irrelevant:


\begin{code}
data WkEqs {Γ} : Eqs Γ → Eqs Γ → Set where
  ε        : WkEqs • •
  _⁺_>eq_  : WkEqs Φ Ψ → Tm Γ 𝔹 → Bool → WkEqs (Φ ▷ t >eq b) (Ψ ▷ t >eq b)

wkeq : WkEqs (Ξ ▷ t >eq b) Ξ

_[_]Wk~ : Ψ ⊢ t₁ ~ t₂ → WkEqs Φ Ψ → Φ ⊢ t₁ ~ t₂

swapEqVar  : Ξ ⊢ t₁ ~ t₂ → EqVar (Ξ ▷ t₁ >eq true) u b 
           → Ξ ▷ t₂ >eq true ⊢ u ~ ⌜ b ⌝𝔹
swapEqVar t~ ez      = t~ [ wkeq ]Wk~ ∙~ eq ez
swapEqVar t~ (es e)  = eq (es e)
\end{code}

%if False
\begin{code}
_[_]~ : Ξ ⊢ t₁ ~ t₂ → ∀ (δ : Tms[ q ] Δ Γ) → Ξ [ δ ]Eq ⊢ t₁ [ δ ] ~ t₂ [ δ ]


-- I think we need an IH that equational contexts are equivalent...

swapEq : Ξ ⊢ t₁ ~ t₂ → (Ξ ▷ t₁ >eq true) ⊢ u₁ ~ u₂
       → (Ξ ▷ t₂ >eq true) ⊢ u₁ ~ u₂
swapEq t~ (eq e)            = swapEqVar t~ e
swapEq t~ (ƛ u~)            = ƛ swapEq (t~ [ wk ]~) u~

swapEq t~ (if u₁~ u₂~ u₃~)  = {!!}
  -- if (swapEq t~ u₁~) (swapEq {!   !} {!  u₂~ !}) {!!}

swapEq t~ ⇒β = {!   !}
swapEq t~ 𝔹β₁ = {!   !}
swapEq t~ 𝔹β₂ = {!   !}
swapEq t~ rfl~ = {!   !}
swapEq t~ (sym~ u~) = {!   !}
swapEq t~ (u~₁ ∙~ u~₂) = {!   !}
swapEq t~ (u~₁ · u~₂) = {!   !}
\end{code}
%endif

% TODO Find a place for these definitions

% Setoid reasoning combinators

%if False
\begin{code}
infixr 2 _~⟨_⟩~_
infix  3 _∎~

pattern _~⟨_⟩~_ x p q = _∙~_ {t₁ = x} p q
pattern _∎~ x = rfl~ {t = x}
\end{code}
%endif

\begin{definition}[Definitional Inconsistency] \phantom{a}

We define equational contexts where |Ξ ⊢ TT ~ FF| to be ``definitionally
inconsistent''.
\begin{code}
def-incon : Eqs Γ → Set
def-incon Ξ = Ξ ⊢ TT ~ FF
\end{code}

Under definitionally-inconsistent contexts, all terms are convertible. In
the setting of dependent types, this phenomenon is sometimes called
``equality collapse'' \sidecite{conor2010wtypes}.

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
\end{code}
%endif

\subsection{A First Attempt at Reduction}

Note that while rewriting gives a nice intution for the operational behaviour of 
these
equations (in the context |Γ ▷ t >eq true|, we have that |t|
reduces to |TT|), declarative conversion being an equivalence by definition
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

we find that the induced notion of algorithmic convertability is much weaker
that our declarative specification. One complication comes from how the LHS
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
the Church Booleans |u = λ x y → x| and |v = λ x y → y|, and then start with the
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

The reduction relation is now even weaker, and is still non-confluent, but
as it turns out, it is strongly normalising! More significantly, we will
show that this reduction stays strongly normalising 
even without the |EqVar Ξ t b| pre-condition\sideremark{Removing this
pre-condition is equivalent to being allowed to ``swap out'' the equational
context after every reduction.
\nocodeindent
\begin{code}
_>swap_ : Tm Γ A → Tm Γ A → Set
_>swap_ {Γ = Γ} t₁ t₂ 
  = Σ⟨ Ξ ∶ Eqs Γ ⟩× Ξ ⊢ t₁ > t₂
\end{code}
\resetcodeindent
Intuitively, this is a useful property, because it allows us to freely
modify the equational context while performing well-founded induction.
}. 
Intuitively, closed Booleans
are irreducible, so clearly reduction chains which collapse |𝔹|-typed terms
to closed Booleans with |rw| must terminate there, but of course
replacing subterms in some large expression with |TT| or |FF| can unlock new
reductions, so the proof is not completely trivial.


\section{Normalisation via Completion}

In the prior section, we gestured at a reduction relation similar to
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

In (TODO REF HERE) we will prove that |_>!_| is strongly normalising. Before
we dive into that proof though, we will show how to derive a normalisation 
algorithm using this result.

% TODO: Cite Knuth-Bendix somewhere?
The key idea here will be ``completion''. We call equational contexts for
which every LHS is irreducible w.r.t. all other equations 
``complete''\remarknote{Slightly confusingly, equational contexts being 
complete is required
to prove \textit{soundness} of normalisation as defined 
in \refdef{norm} (i.e. to appropriately identify
all convertible terms and not miss any reductions), not \textit{completeness}
(which instead follows from completion preserving equivalence of equational
contexts).}.

\begin{code}
stk : Eqs Γ → Tm Γ A → Set
stk Ξ t = ∀ u → ¬ Ξ ⊢ t > u 

_-_ : ∀ (Ξ : Eqs Γ) → EqVar Ξ t b → Eqs Γ
(Ξ ▷ t >eq b)  - ez   = Ξ
(Ξ ▷ u >eq b′) - es e = (Ξ - e) ▷ u >eq b′

data AllStk (Ξ : Eqs Γ) : Eqs Γ → Set where
  •   : AllStk Ξ •
  _▷_ : AllStk Ξ Ψ 
      → ∀ (e : EqVar Ξ t b) 
      → ¬is 𝔹? t
      → stk (Ξ - e) t → AllStk Ξ (Ψ ▷ t >eq b)

Complete : Eqs Γ → Set
Complete Ξ = AllStk Ξ Ξ
\end{code}

The completion algorithm can then be specified as a mapping between
equational contexts that preserves equivalence.

\begin{code}
complete′       : Eqs Γ → Eqs Γ
complete-pres′  : Ξ Eqs~ complete′ Ξ
complete-compl′ : Complete (complete′ Ξ) 
\end{code}

Under complete equational contexts |Ξ|, we can prove that the algorithmic
conversion induced by |Ξ ⊢_>eq_| is equivalent to declarative conversion
|Ξ ⊢_~_|, and so being able to reduce w.r.t. |Ξ ⊢_>eq_| yields a 
normalisation algorithm.

%if False
\begin{code}
_⊢_>*_ : Eqs Γ → Tm Γ A → Tm Γ A → Set 
Ξ ⊢ t₁ >* t₂ = t₁ [ Ξ ⊢_>_ ]* t₂
\end{code} 
%endif

%if False
\begin{code}
≡~ : t₁ ≡ t₂ → Ξ ⊢ t₁ ~ t₂
≡~ refl = rfl~
\end{code}
%endif

\begin{code}
pres>* : Ξ ⊢ t >* u → Ξ ⊢ t ~ u


-- |reduce| fully reduces terms w.r.t. |_⊢_>_|
reduce : Eqs Γ → Tm Γ A → Tm Γ A

reduce-reduces : Ξ ⊢ t >* reduce Ξ t 

reduce-pres : Ξ₁ Eqs~ Ξ₂ → Ξ₁ ⊢ t ~ reduce Ξ₂ t
reduce-pres Ξ~ = Ξ~ .from (pres>* reduce-reduces)

reduce-stk   : ∀ u → ¬ Ξ ⊢ reduce Ξ₁ t > u


norm : Eqs Γ → Tm Γ A → Tm Γ A
norm Ξ t = reduce (complete′ Ξ) t

norm-pres : Ξ ⊢ t ~ norm Ξ t 
norm-pres {Ξ = Ξ} {t = t} = reduce-pres complete-pres′

norm-compl : norm Ξ t₁ ≡ norm Ξ t₂ → Ξ ⊢ t₁ ~ t₂
norm-compl {Ξ = Ξ} {t₁ = t₁} {t₂ = t₂} t≡ = 
  t₁
  ~⟨ norm-pres ⟩~
  norm Ξ t₁
  ~⟨ ≡~ t≡ ⟩~ 
  norm Ξ t₂
  ~⟨ sym~ norm-pres ⟩~
  t₂ ∎~

norm-sound : Ξ ⊢ t₁ ~ t₂ → norm Ξ t₁ ≡ norm Ξ t₂
norm-sound = {!!} 
\end{code}

There is a remaining subtlety: completion as specified cannot be implemented
on definitionally inconsistent contexts. 
Specifically, given all contexts satisfying |Complete| are definitionally 
consistent (i.e.
|Ξ ⊢ TT ~ FF| cannot be derived in |Complete Ξ|), 
preservation of context equvalence impossible.

\begin{code}
complete-not-incon : Complete Ξ → ¬ Ξ ⊢ TT ~ FF

contradiction : ⊥
contradiction 
  = complete-not-incon (complete-compl′ {Ξ = Ξ⊥}) (complete-pres′ .to (eq ez))
  where Ξ⊥ = • ▷ TT {Γ = •} >eq false
\end{code}

The problem is that completion must be \textit{partial}. We either
complete an equational environment, or discover a |TT >eq false| equation
and know that it is definitionally inconsistent.

Our corrected specification of completion should be (we now fuse the
correctness conditions with the definition to simplify the spec)

\begin{code}
complete : Eqs Γ 
         → (Σ⟨ Ξ′ ∶ Eqs Γ ⟩× Ξ Eqs~ Ξ′ × Complete Ξ′)
         ⊎ def-incon Ξ
\end{code}

Our normal forms can no longer be ordinary terms either. In a definitionally
inconsistent context, we must ensure that all terms are equal. We can ensure
this syntactically with the following normal form structure.







reducing
terms to closed Booleans means they are no longer

 - i.e. reducing |𝔹|-typed terms
to |TT|/|FF| always makes them smaller the particular equational
context is irrelevant 

More significantly, 
we can (and will, in the next section) prove that the specific equational
context is irrelevant

even if we swap the
equational context for a completely new one after every reduction

the reduction relation is \textit{still} strongly normalising (in other words, 
the well-foundedness of reduction is entirely independent of the set of
equations). We will take advantage
of this in the next section to derive a normalisation algorithm via
the technique of ``completion''.



Arguably, the reason reduction relations had problems was due to
equational contexts being so unconstrainted. There is nothing to
prevent us from assuming
reducible (e.g. |if TT u v >eq b|), redundant (e.g. |TT >eq true|) or even
inconsistent (e.g. |TT >eq false|) equations.


Unfortunately, having to deal with such equations is, in a sense, forced upon
us by our goal of introducing equations locally via |if|-expressions.
We could try to place syntactic restrictions on the scrutinees of |if|s, but 
this would make our language less flexible\remarknote{We also would have to
ensure whatever restrictions we attempt are stable under substitution,
as |if|-expressions can of course occur under |λ|s which might be β-reduced. 
With this requirement, I suspect this train of thought is a complete dead end:
note that even equations of the form |` i >eq b| are problematic, as |i| might
get substituted for the opposite Boolean}.

Hope is not lost, however! We will aim to derive normalisation via
\textit{completion}. Intuitively, our normalisation algorithm
will work by first completing the equational context |Ξ|
(reducing all LHS terms and pruning redundant equations while checking
for definitional inconsistency) and then will normalise terms following
|Ξ′ ⊢_>_| (where |Ξ′| is the completed equational context). Of course, every
time normalisation recurses into the branches of an |if|-expression, new
equations are added, and so we must re-run completion.

As mentioned in the prior section, as long as we prevent reduction of
closed Booleans, reduction following equations in the equational context is
strongly normalising. The equational context itself is irrelevant -
we can construct a more general reduction relation in which |𝔹|-typed
terms can be ``spontaneously'' reduced to |TT| or |FF| as long as they are
not already closed Booleans, and show that this relation is strongly
normalising.


%if False
\begin{code}
_>!*_ : Tm Γ A → Tm Γ A → Set
_>!*_ = _[ _>!_ ]*_
\end{code}
%endif

We will prove well-foundedness of spontaneous reduction |_>!_| in
section (TODO REF SECTION HERE). Of course, rewriting arbitrari

it fails confluence and is unsound
w.r.t. declarative conversion |_⊢_~_|, so we will not rewrite arbitrarily
w.r.t. it, but we will use the strong normalisation result to justify
termination via well-founded induction. Specifically,
termination of reducing terms w.r.t. |_⊢_>_| can be justified
via |_>!_| and completion of equational contexts can be justified by
extending |_>!_| over the list of LHSs in the equational context 
lexicographically.



% We note that in the absense of syntactically\remarknote{We identify
% syntactically inconsistent/redundant equations exactly with those where the
% LHS is syntactically equal to a closed Boolean.
% E.g.
% equations such as |if TT TT v >eq FF| are \textit{definitionally} inconsistent, 
% because under them we can derive |def-incon| (\refdef{defincon}), but
% not \textit{syntactically}. The absense of synactically 
% redundant/inconsistent equations is a weaker property than absense
% of definitionally redundant/inconsistent ones.}
% redundant or inconsistent equations, |_⊢_>_| is contained inside |_>!_|.
% Detecting if a term is syntactically a closed Boolean is easy 
% (i.e. we just case split), and so
% termination of reducing terms w.r.t. |_⊢_>_| can therefore be justified via 
% |_>!_|, and completion can be justified by extending |_>!_| over the list of
% LHSs in the equational context lexicographically.




The trick is thus: 
\begin{itemize}
\item We define completed term rewriting systems as the
      a predicate on equational contexts |Ξ| where every LHS not a closed 
      Boolean
      and is irreducible w.r.t.
      |Ξ′ ⊢_>_|, where |Ξ′| is |Ξ| with that particular rewrite removed. 
      Under a completed TRS, |_⊢_>_| is confluent and a subset of |_⊢_~>_|.
\item We define a completion procedure on equational contexts, which is
      well-founded by |_⊢_~>_| extended lexicographically over the list of
      LHS terms. Completion either produces completed TRS equivalent
      to the starting equational context, or concludes that the equational
      context is definitionally inconsistent.
\item Normalisation of terms is then also justified by well-foundedness of
      |_⊢_~>_|




