% TODO: I think I want to try and move this all into background
% Except for the typechecking stuff at the end, which can go into SCBool

%if False
\begin{code}
{-# OPTIONS --prop #-}
open import Utils

module Report.Final.c6_nbe where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Normalisation by Evaluation}
\labch{nbe}

Normalisation by Evaluation (NbE) 
\sidecite[*25]{berger1991inverse, altenkirch1995categorical}
is a normalisation algorithm for lambda
calculus terms, which operates by first evaluating terms into a semantic domain 
(specifically, the ``presheaf model''), and then inverting
the evaluation function to ``quote'' back normal forms. It can be motivated
from multiple directions: 
\begin{itemize}
\item \textbf{No reliance on small-step reductions:} NbE is structurally
      recursive, and is therefore not reliant on a separate strong normalisation
      result to justify termination. This can be especially useful in settings 
      where a strongly normalising set of small-step reductions is difficult to 
      identify (e.g. dealing with η-expansion).
\item \textbf{Applicability to quotiented syntax:} Following on from the first
      point, unlike term-rewriting-based approaches to normalisation, NbE does
      not rely on distinguishing βη-convertible terms (the algorithm can be
      structured in such a way as to simply map families of convertible terms
      to values \sidecite[*14.25]{altenkirch2017normalisation}). This enables 
      working with more ``semantic'' \sidecite[*16]{kaposi2025type} definitions 
      of type theory (e.g. Categories with Families, or CwFs) where terms are 
      quotiented by conversion, 
      providing 
      soundness ``for free''.\sideremark[*-3]{Quotienting by conversion is 
      especially 
      attractive in the setting of dependent types, where intrinsically-typed
      syntax must otherwise be defined mutually with conversion to account for
      definitional equality \sidecite[*12]{danielsson2006formalisation, 
      kovacs2023setoid}.}
\item \textbf{Efficiency:} NbE avoids repeated expensive
      single-substitutions (which need to traverse the whole syntax tree
      each time to possibly replace variables with the substitutee) 
      \sidecite[*15.5]{kovacs2023smalltt}. 
      Instead, the 
      mappings between variables
      and semantic values are tracked in a persistent map (the ``environment''), 
      such that variables can be looked up exactly when they are evaluated.
\end{itemize}

For the application on NbE in this project, only the last of these points is
truly relevant. Specifically, we do not plan to directly prove
normalisation of type theory with local equational assumptions via NbE,
primarily because I am unaware of a good way to justify rewriting-to-completion
without going down to the level of an ordering on terms. 

Instead, following \sidecite[*7]{coquand1996algorithm}, we shall employ NbE as 
the algorithm to decide conversion in our prototype Haskell typechecker. 
On top of the efficiency benefits, NbE is also relatively simple to implement, 
and as we shall see, is quite compatible with \textbf{smart case} in the sense 
that the extensions necessary to support local equations are minimal.

To introduce NbE, we will begin by deriving the algorithm for the Simply-Typed
Lambda Calculus (STLC), staying within our Agda-flavoured ITT meta-theory. We
will  then move on to discuss how the algorithm extends to dependently-typed 
object languages, and the optimisations that become available when implementing 
inside a non-total metalanguage. Finally, we will cover the extensions 
to NbE necessary to support \textbf{smart case}.

\pagebreak

SYNTAX SECTION MOVED TO BACKGROUND!!!

\section{Naive Normalisation}

As a warm-up to NbE, we will start by implementing ``naive'' normalisation,
i.e. recursing on a term, contracting β-redexes where possible by applying 
single-substitutions. As we are implementing the algorithm in the total
language of Agda, we will detail how termination can be justified in terms
of strong normalisation.

We first define our goal: β-normal forms, |Nf Γ A|, inductively (mutually 
recursively with stuck,
neutral terms, |Ne Γ A|) along with the obvious injections back into ordinary 
terms, |⌜_⌝|, |⌜_⌝ne|.

\sideremark{Note that neutrals are comprised of spines of elimination forms 
while introduction rules are restricted to |Nf|, to rule-out β-redexes 
syntactically.}

\begin{code}
data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  `_   : Var Γ A → Ne Γ A
  _·_  : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
  π₁   : Ne Γ (A * B) → Ne Γ A
  π₂   : Ne Γ (A * B) → Ne Γ B
\end{code}

\pagebreak

\sideremark{To enforce η-normality for |_⇒_|, |_*_| and |𝟙|, we could restrict 
embedded neutrals in |Nf| to only those of empty type, |𝟘|. βη-normal forms
accounting for |⊥|-η are more complicated \sidecite[*2]{scherer2017deciding}.}

\begin{code}
data Nf where
  ne   : Ne Γ A → Nf Γ A
  ƛ_   : Nf (Γ , A) B → Nf Γ (A ⇒ B) 
  _,_  : Nf Γ A → Nf Γ B → Nf Γ (A * B)
  ⟨⟩   : Nf Γ 𝟙

⌜_⌝    : Nf Γ A → Tm Γ A
⌜_⌝ne  : Ne Γ A → Tm Γ A
\end{code}

%if False
\begin{code}
⌜ ƛ t    ⌝ = ƛ ⌜ t ⌝ 
⌜ t , u  ⌝ = ⌜ t ⌝ , ⌜ u ⌝
⌜ ⟨⟩     ⌝ = ⟨⟩
⌜ ne t   ⌝ = ⌜ t ⌝ne

⌜ ` i    ⌝ne = ` i
⌜ t · u  ⌝ne = ⌜ t ⌝ne · ⌜ u ⌝
⌜ π₁ t   ⌝ne = π₁ ⌜ t ⌝ne
⌜ π₂ t   ⌝ne = π₂ ⌜ t ⌝ne
\end{code}
%endif

We can then attempt to define normalisation by recursion on terms, relying on
substitution to contract β-redexes (for now focusing only on the cases for
abstraction and application):

\begin{spec}
norm   : Tm Γ A → Nf Γ A
nf-app : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

norm (ƛ t)    = ƛ (norm t)
norm (t · u)  = nf-app (norm t) (norm u)

nf-app (ne t)  u = ne (t · u)
nf-app (ƛ t)   u = norm (⌜ t ⌝ [ < ⌜ u ⌝ > ])
\end{spec}

\sideremark{Note that normal forms are
not stable under substitution (i.e. substitution can create new β-redexes), so 
we cannot easily define substitution on normal forms to resolve this. 
It is perhaps worth mentioning though, that if one is more careful
with the representation of neutral spines (among other things), pushing in
this direction can lead to another structurally recursive normalisation
algorithm known as \textit{hereditary substitution}
\sidecite[*17]{keller2010hereditary}. Unfortunately, it is currently unknown
whether this technique extends to dependent types.}

In a partial language, when applied to normalising terms, this definition
is sufficient! The single substitutions are less efficient on terms with
multiple β-redexes than the NbE approach of tracking all variable mappings
in a single environment, but it can be optimised with memoisation
and annotating subterms with the sets of variables which are actually used (i.e.
to avoid unnecessary traversals during substitution).

In a total setting, unfortunately, naive normalisation is clearly not 
well-founded by structural recursion. 
|⌜ t ⌝ [ < ⌜ u ⌝ > ]| is not necessarily structurally smaller than |t| or |u|.

%if False
\begin{code}
variable
  t u v t₁ t₂ t₃ u₁ u₂ u₃ : Tm[ q ] Γ A

infix 4 _>β_
infix 4 _>β*_
infix 4 _>s_
infix 4 _>βs_
infix 4 _>βs*_
infix 4 _>βs+_
\end{code}
%endif

Making naive normalisation total relies on a strong normalisation result: we 
need to know that β-reduction, |_>β_|, is well-founded. 
\sideremark{Classically, strong normalisation can be defined as there 
existing no infinite chains of reductions. To justify
induction w.r.t. reduction order constructively, we must instead use
accessibility predicates. |Acc R x| can be thought of as the type of
finite-depth trees starting at |x|, with branches corresponding to single steps
along |_>_| and minimal elements w.r.t. relation |R| at the leaves.}
Actually, we will make use of 
the accessibility of typed terms w.r.t. interleaved structural ordering, |_>s_|, 
and β-reduction, but luckily obtaining this from traditional
strong normalisation is not too difficult \sidecite[*11]{zulip2024combining}. 
Note that |_>β_| commutes with
|_>s_| in the sense that |t >s u → u >β v → ∃[ w ] t >β w × w >s v|, or as a 
diagram:

\begin{tikzcd}[scaleedge cd=1.25, sep=huge]
|t| \arrow[r, "|_>s_|"] \arrow[d, swap, dashrightarrow, "|_>β_|"]
& |u| \arrow[d, "|_>β_|"] \\
|w| \arrow[r, swap, dashrightarrow, "|_>s_|"]
& |v|
\end{tikzcd}

We therefore skip ahead to defining a single |_>_| relation on terms 
encompassing both structural and reduction orderings, and assume we have a proof
that this combined order is well-founded.

\pagebreak

\begin{code}
data _>β_ : Tm Γ A → Tm Γ A → Set where
  -- Congruence
  l·  : t₁ >β t₂ → t₁ · u >β t₂ · u
  ·r  : u₁ >β u₂ → t · u₁ >β t · u₂
  ƛ_  : t₁ >β t₂ → ƛ t₁ >β ƛ t₂
  -- etc...

  -- Reductions
  β   : (ƛ t) · u >β t [ < u > ]
  π₁β  : π₁ (t , u) >β t
  π₂β  : π₂ (t , u) >β u

data _>s_ : Tm Γ A → Tm Δ B → Set where
  -- Structural ordering
  l·>  : t · u >s t
  ·r>  : t · u >s u
  ƛ>   : ƛ t >s t
\end{code}

%if False
\begin{code}
-- Bundled term
record BTm : Set where
  constructor ⟪_⟫
  field
    {ctx} : Ctx
    {ty}  : Ty
    tm    : Tm ctx ty
\end{code}
%endif

\begin{code}
data _>βs_ : BTm → BTm → Set where
  β> : t >β u → ⟪ t ⟫ >βs ⟪ u ⟫
  s> : t >s u → ⟪ t ⟫ >βs ⟪ u ⟫

-- All terms are strongly normalisable w.r.t. |_>βs_|
wf : ∀ (t : Tm Γ A) → SN _>βs_ ⟪ t ⟫
\end{code}

%if False
\begin{code}
_>β*_ : Tm Γ A → Tm Γ A → Set 
_>β*_ = _[ _>β_ ]*_

_>βs*_ : BTm → BTm → Set 
_>βs*_ = _[ _>βs_ ]*_

_>βs+_ : BTm → BTm → Set
_>βs+_ = _[ _>βs_ ]+_

ƛ* : t₁ >β* t₂ → ƛ t₁ >β* ƛ t₂
ƛ* = map* ƛ_ ƛ_

_·*_ : t₁ >β* t₂ → u₁ >β* u₂ → t₁ · u₁ >β* t₂ · u₂ 
p ·* q = map* _ l· p ∘* map* _ ·r q
\end{code}
%endif

Normalisation can then be made total by consistently returning evidence that
there exists a (possibly empty) chain of reductions |_>β*_| to go from the
input term to the resulting normal form.

\sideremark{We denote the transitive closure and reflexive-transitive closures
of orders with |_+| and |_*| respectively.}

\begin{code}
Nf> : ∀ Γ A → Tm Γ A → Set
Nf> Γ A t = Σ (Nf Γ A) (λ tᴺᶠ → t >β* ⌜ tᴺᶠ ⌝)
\end{code}

Actually using our accessibility predicate in naive normalisation
gets quite cluttered, but the main idea is to ensure that we are always 
making progress with respect to |_>βs_|.

\sideremark{We again skip the cases for pairs and the unit type here as they
are routine.}

\begin{code}
norm    : ∀ (t : Tm Γ A) → SN _>βs+_ ⟪ t ⟫ → Nf> Γ A t

nf-app  : ∀ (tᴺᶠ : Nf Γ (A ⇒ B)) (uᴺᶠ : Nf Γ A) 
        → SN _>βs+_ ⟪ t · u ⟫ → t · u >β* ⌜ tᴺᶠ ⌝ · ⌜ uᴺᶠ ⌝
        → Nf> Γ B (t · u)

norm (` i)    a     = ne (` i) Σ, ε
norm (ƛ t)    (acc a) 
  using tᴺᶠ  Σ, t>tᴺᶠ  ← norm t (a ⟪ s> ƛ> ⟫) 
  = (ƛ tᴺᶠ)  Σ, ƛ* t>tᴺᶠ
norm (t · u)  (acc a) 
  using  tᴺᶠ  Σ, t>tᴺᶠ  ← norm t (a ⟪ s> l·> ⟫)
      |  uᴺᶠ  Σ, u>uᴺᶠ  ← norm u (a ⟪ s> ·r> ⟫)
  = nf-app tᴺᶠ uᴺᶠ (acc a) (t>tᴺᶠ ·* u>uᴺᶠ)

nf-app (ne t)  u _ tu>tuᴺᶠ    
  = ne (t · u) Σ, tu>tuᴺᶠ
nf-app (ƛ t)   u (acc a) ε       
  using tuᴺᶠ Σ, tu>tuᴺᶠ ← norm (⌜ t ⌝ [ < ⌜ u ⌝ > ]) (a ⟪ β> β ⟫) 
  = tuᴺᶠ Σ, β ∷ tu>tuᴺᶠ
nf-app (ƛ t)   u (acc a) (p ∷ q) 
  using tuᴺᶠ Σ, tu>tuᴺᶠ ← norm  (⌜ t ⌝ [ < ⌜ u ⌝ > ]) 
                                (a (β> p ∷+ (map* _ β> q ∘* ⟪ β> β ⟫*)))
  = tuᴺᶠ Σ, (p ∷ q ∘* ⟪ β ⟫* ∘* tu>tuᴺᶠ)
\end{code}

\pagebreak

\section{The Standard Model}
\labsec{standard}

If our aim is to derive an algorithm which reduces terms while staying 
structurally recursive, our focus should be the case for application.
i.e. when aiming to produce |Nf Γ A|s directly by recursion on our syntax,
we failed to derive a structurally recursive algorithm because there is no
analogue of |_·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B| for normal forms.

As a step towards deriving an improved normalisation algorithm that gets around
this problem, we will look at the similar but slightly easier problem of
merely evaluating closed STLC terms. The key idea here will be to interpret
STLC types into their metatheoretic (i.e. in |Set|) counterparts. This
way, function-typed terms will be evaluated into meta-level functions, which 
can be directly applied to their evaluated arguments, while still satisfying
expected β-equalities.
This idea is known as the standard model of type theory (also the 
``meta-circular interpretation'').

As values will not contain free variables, we will also interpret contexts as 
left-nested pair types (environments). 

\begin{code}
-- Closed values
⟦_⟧ᵗʸ  : Ty → Set
⟦ 𝟘      ⟧ᵗʸ = ⊥
⟦ A ⇒ B  ⟧ᵗʸ = ⟦ A ⟧ᵗʸ → ⟦ B ⟧ᵗʸ
⟦ A * B  ⟧ᵗʸ = ⟦ A ⟧ᵗʸ × ⟦ B ⟧ᵗʸ
⟦ 𝟙      ⟧ᵗʸ = ⊤

-- Environments
⟦_⟧ᶜᵗˣ : Ctx → Set
⟦ ε      ⟧ᶜᵗˣ = ⊥
⟦ Γ , A  ⟧ᶜᵗˣ = ⟦ Γ ⟧ᶜᵗˣ × ⟦ A ⟧ᵗʸ
\end{code}

Terms are then interpreted as functions from environments to closed values, so
in non-empty contexts, variables can pick out their associated values.
In other words, we can \textit{evaluate} a term of type 
|A| in
context |Γ| into a closed value of type |A|, |⟦ A ⟧ᵗʸ|, given an environment
|ρ : ⟦ Γ ⟧ᶜᵗˣ|. Application
directly applies values using application of the meta-theory and abstraction
extends environments with new values, using abstraction of the meta.
Given we are working inside of a constructive type theory, meta-functions are 
computable-by-construction
and so termination is ensured merely by structural recursion on our syntax.

\begin{code}
lookup : Var Γ A → ⟦ Γ ⟧ᶜᵗˣ → ⟦ A ⟧ᵗʸ
lookup vz      (ρ Σ, x) = x
lookup (vs i)  (ρ Σ, x) = lookup i ρ

⟦_⟧ᵗᵐ  : Tm Γ A → ⟦ Γ ⟧ᶜᵗˣ → ⟦ A ⟧ᵗʸ
⟦ ƛ t    ⟧ᵗᵐ ρ = λ uⱽ → ⟦ t ⟧ᵗᵐ (ρ Σ, uⱽ)
⟦ t · u  ⟧ᵗᵐ ρ = (⟦ t ⟧ᵗᵐ ρ) (⟦ u ⟧ᵗᵐ ρ)
⟦ t , u  ⟧ᵗᵐ ρ = (⟦ t ⟧ᵗᵐ ρ) Σ, (⟦ u ⟧ᵗᵐ ρ)
⟦ π₁ t   ⟧ᵗᵐ ρ = proj₁ (⟦ t ⟧ᵗᵐ ρ)
⟦ π₂ t   ⟧ᵗᵐ ρ = proj₂ (⟦ t ⟧ᵗᵐ ρ)
⟦ ⟨⟩     ⟧ᵗᵐ ρ = tt
⟦ ` i    ⟧ᵗᵐ ρ = lookup i ρ
\end{code}

Of course, this algorithm is not sufficient for normalisation. Without an
environment of closed values to evaluate with respect to, we cannot hope to
inspect the structure of evaluated terms (i.e. at the meta-level, functions like 
|⟦ Γ ⟧ᶜᵗˣ → ⟦ A ⟧ᵗʸ| are opaque). Similarly, even with an environment, 
we cannot inspect the structure of higher order (|⇒|-typed) values beyond
testing their behaviour on particular inputs given these are 
again opaque meta-language functions. The ``problem'' we are 
encountering is that our values have no first-order representation of variables.

It turns out, by carefully defining a similar model, based on presheaves, we can
embed stuck, 
first-order variables into 
values\remarknote{In fact, we are forced to include general, stuck neutral 
terms to support application where the LHS is a variable.}
, implement evaluation in open contexts
and even \textit{invert} evaluation, ``quoting'' back into
normalised first-order terms (i.e. our normal forms). This \textit{evaluation} 
followed by \textit{quoting} is exactly normalisation by evaluation.

\section{The Presheaf Model}

Central to the presheaf model (perhaps unsurprisingly) is the concept of a
presheaves: contravariant functors into |Set|. 
\sideremark{The objects in the category of renamings are contexts |Ctx| and
the morphisms are renamings |Ren Δ Γ|.} We will specifically focus on
presheaves on the category of renamings. Being able to weaken 
values (i.e. introduce new fresh variables) via renamings will be critical when
defining quotation into normal forms.

\sideremark{Note that renamings are not the only option here. ``Thinnings''
are a subset of renamings where variables of the target can only be retained 
or dropped (not permuted or duplicated) and yet still form a category and 
encompass weakenings.}

\begin{code}
-- Presheaves on the category of renamings
record PshRen (F : Ctx → Set) : Set where
  field
    ren     : Ren Δ Γ → F Γ → F Δ
    
    ren-id  : ∀ {x} → ren (id {Γ = Γ}) x ≡ x
    ren-⨾   : ∀ {x} → ren δ (ren σ x) ≡ ren (δ ⨾ σ) x 
\end{code}

The standard model can be seen as interpreting object-level types into
the corresponding objects in the category |Set| (i.e. where |Set|s are 
objects and functions are morphisms). In the presheaf model, we instead
interpret into corresponding objects in the category of presheaves (a
category where objects are presheaves, and morphisms are natural 
transformations).

For example, the unit presheaf (i.e. the terminal object in the category of 
presheaves) is simply |𝟙ᴾˢʰ = λ Γ → ⊤|. Similarly, the products in the
category of presheaves can be constructed as |F ×ᴾˢʰ G = λ Γ → F Γ × G Γ|.

The exponential object in the category of presheaves is a bit more
subtle. We might try to follow the pattern and define 
|F →ᴾˢʰ G = λ Γ → F Γ →ᴾˢʰ G Γ| but this doesn't quite work. When trying
to implement\\|ren : Ren Δ Γ → (F →ᴾˢʰ G) Γ → (F →ᴾˢʰ G) Δ| we
only have access to an |F Δ| and a function which accepts |F Γ|s\remarknote{
Note the |Ren Δ Γ| renaming can only transform |F Γ|s into |F Δ|s, not the other
way around.
}.
The solution is to quantify over renamings, i.e. 
|F →ᴾˢʰ G = λ Γ → ∀ {Δ} → Ren Δ Γ → F Δ → G Δ| \sidecite{1lab2025exponentials}.

% The presheaf model is so-named because central to our ability to invert
% evaluation is ensuring that values form a presheaf on the 
% ``category of renamings''.
% NbE values, rather than merely being indexed by types (as in the 
% standard model, |⟦ A ⟧ᵗʸ|) must now be also indexed by a context, so
% we denote them with |Val Γ A|. This dependence on a context is required
% to enable us to
% first order variables (which themselves are only meaningful with respect to 
% a context). This presheaf condition therefore merely means that 
% our values must support an operation
% |renVal : Ren Δ Γ → Val Γ A → Val Δ B|,
% satisfying the expected identity and composition laws. Generically:

These are (almost) all the ingredients we need to define NbE values. Types
in a context |Γ| are merely interpreted as the corresponding constructs in
the category of presheaves.

\begin{code}
⟦_⟧ᴾˢʰ : Ty → Ctx → Set
⟦ A ⇒ B  ⟧ᴾˢʰ Γ = ∀ {Δ} → Ren Δ Γ → ⟦ A ⟧ᴾˢʰ Δ → ⟦ B ⟧ᴾˢʰ Δ
⟦ A * B  ⟧ᴾˢʰ Γ = ⟦ A ⟧ᴾˢʰ Γ × ⟦ B ⟧ᴾˢʰ Γ
⟦ 𝟙      ⟧ᴾˢʰ Γ = ⊤
⟦ 𝟘      ⟧ᴾˢʰ Γ = ⊥
\end{code}

\pagebreak

A final subtlety arises with the empty type |𝟘|. While |λ Γ → ⊥| does satisfy 
all the necessary laws of an initial object, 
\sideremark{This issue is not unique to the empty type. 
All ``positive'' types, e.g. booleans, coproducts, natural numbers etc...
experience a similar problem. \sidecite[*8]{altenkirch2001normalization} 
explores using a model based on sheaves (instead of presheaves) to fix this more
elegantly in the case of coproducts, but in general (e.g. for natural numbers)
deciding ``categorical'' (βη) equivalence is undecidable.}
and terms of type |𝟘| can only occur inside empty contexts (i.e. contexts 
containing |𝟘|), when evaluating a variable of type |𝟘|, we cannot hope to 
produce a proof of |⊥| (i.e. the context containing the empty type does not mean
evaluation can give up - normalisation requires evaluating in all contexts).

To solve this, we must embed neutrals into the model. E.g. we could interpret 
|𝟘| as |λ Γ → Ne Γ 𝟘|. |λ Γ → Ne Γ 𝟘| is obviously not an initial object
in the category of presheaves, so by doing this we have slightly broken our
model, but it turns out that only the |η| laws for |𝟘| are actually lost
(which lines up exactly with the consequences of embedding neutrals to |Nf|).
We are aiming only to β-normalise terms, and will actually take a more
extreme option, embedding neutrals of all types as to line up more closely with
our β-normal forms.

\begin{code}
Val     : Ctx → Ty → Set
PshVal  : Ctx → Ty → Set

Val Γ A = PshVal Γ A ⊎ Ne Γ A

PshVal Γ (A ⇒ B)  = ∀ {Δ} → Ren Δ Γ → Val Δ A → Val Δ B 
PshVal Γ (A * B)  = Val Γ A × Val Γ B
PshVal Γ 𝟙        = ⊤
PshVal Γ 𝟘        = ⊥
\end{code}

Note that although we are mixing inductively (i.e. |Ne|) and recursively
(i.e. |PshVal|) defined type families here, the construction remains
well-founded.

Renaming can now be implemented for |PshVal Γ A| by recursion on the type |A|,
and renaming of values in general, |renVal|, can merely delagate renaming
on |PshVal Γ A|s and |Ne Γ A|s as appropriate. 

% TODO: Renaming for neutrals
%if False
\begin{code}
postulate 
  renNe : Ren Δ Γ → Ne Γ A → Ne Δ A
\end{code}
%endif

\begin{code}
renVal : Ren Δ Γ → Val Γ A → Val Δ A
renPshVal : ∀ A → Ren Δ Γ → PshVal Γ A → PshVal Δ A

renVal δ (inl  t) = inl  (renPshVal _  δ t)
renVal δ (inr  t) = inr  (renNe        δ t)

renPshVal (A ⇒ B)  δ f         = λ σ t → f (δ ⨾ σ) t
renPshVal (A * B)  δ (t Σ, u)  = renVal δ t Σ, renVal δ u
renPshVal 𝟙        δ tt        = tt
\end{code}

To implement NbE, we need to define both evaluation from terms to values and
``quotation'' from values to normal forms. We start with evaluation, which
is quite similar to |⟦_⟧ᵗᵐ| in section \refsec{standard}, but needs to deal
with the cases for stuck neutrals appropriately.

We start by defining NbE environments, which unlike the standard model are now
parameterised by two contexts, similarly to |Ren|/|Sub|: first, the context
each of the values exist in and second the list of types of the
values themselves.

\begin{code}
data Env : Ctx → Ctx → Set where
  ε    : Env Δ ε
  _,_  : Env Δ Γ → Val Δ A → Env Δ (Γ , A)
\end{code}

Note that environments can be renamed by simply folding |renVal|.

\begin{code}
renEnv : Ren Θ Δ → Env Δ Γ → Env Θ Γ
\end{code}

%if False
\begin{code}
renEnv δ ε        = ε
renEnv δ (ρ , x)  = renEnv δ ρ , renVal δ x
\end{code}
%endif

Evaluation then proceeds by recursion on the target term. The main subtlety
is in application of values, where the LHS is neutral. In this case
we need to turn quote the RHS back to an |Nf| via |qval| to apply 
|_·_ : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B| (i.e. evaluation actually depends on
quotation).

\begin{code}
qval : ∀ A → Val Γ A → Nf Γ A

lookupVal : Var Γ A → Env Δ Γ → Val Δ A
lookupVal vz      (ρ , x) = x
lookupVal (vs i)  (ρ , x) = lookupVal i ρ

appVal : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
appVal (inl  f  ) x = f id x
appVal (inr  t  ) x = inr (t · qval _ x)

π₁Val : Val Γ (A * B) → Val Γ A
π₁Val (inl  (t Σ, u))  = t
π₁Val (inr  t)         = inr (π₁ t)    

π₂Val : Val Γ (A * B) → Val Γ B
π₂Val (inl  (t Σ, u))  = u
π₂Val (inr  t)         = inr (π₂ t)
 
eval : Tm Γ A → Env Δ Γ → Val Δ A
eval (` i)    ρ = lookupVal i ρ
eval (ƛ t)    ρ = inl λ δ u → eval t (renEnv δ ρ , u)
eval (t · u)  ρ = appVal (eval t ρ) (eval u ρ)
eval (t , u)  ρ = inl (eval t ρ Σ, eval u ρ)
eval (π₁ t)   ρ = π₁Val (eval t ρ)
eval (π₂ t)   ρ = π₂Val (eval t ρ)
eval ⟨⟩       ρ = inl tt
\end{code}

To implement |qval|, we instead proceed by recursion on types. Being able
to rename values is critical to quoting back function
values, where to inspect their structure, we need to be able to apply them to a
fresh variable |vz|.

\begin{code}
qval A        (inr  t)         = ne t 
qval (A ⇒ B)  (inl  f)         = ƛ qval B (f wk (inr (` vz)))
qval (A * B)  (inl  (t Σ, u))  = qval A t , qval B u
qval 𝟙        (inl tt)         = ⟨⟩
\end{code}

Normalisation of open terms now only needs a way to construct identity
environments (effectively lists of increasing variables):

\begin{code}
idEnv : Env Γ Γ
idEnv {Γ = ε}      = ε
idEnv {Γ = Γ , A}  = renEnv wk idEnv , inr (` vz)

nbe : Tm Γ A → Nf Γ A
nbe t = qval _ (eval t idEnv)
\end{code}

We are done! Of course, to verify our normalisation algorithm is correct, we
need to do more work, checking soundness and completeness. 
One way to achieve this is start with a syntax quotiented by conversion
(guaranteeing soundness) and refine values into 
proof-relevant predicates indexed by the unnormalised term, paired with
the relevant correctness conditions 
\sidecite{altenkirch2017normalisation}. 

\subsection{NbE for Dependent Types}

In the setting of dependent types, the main difference is of course that types
may contain terms. \cite{altenkirch2017normalisation} implements quotation on
non-normalised types, though extending this approach to more involved
type-level computation (their syntax includes only |El : Tm Γ U → Ty Γ| with
no additional equations) requires a bit of extra work. 
E.g. if we were in a dependent type
theory featuring large elimination of booleans and encountered the type
|if t then A else B| while quoting, we must first evaluate |t|, and potentially
recursively quote at type |A| or |B| if |t| turns out to reduce to a closed 
boolean 
(if the type ends up a stuck neutral, we are at least guaranteed that the only 
possible  values are neutral).

Luckily, NbE in this project is merely employed as an algorithm for implementing
typechecking, in the partial language of Haskell. We can therefore define NbE on
an untyped syntax, relying on the external invariant that, in practice, we will 
only call |eval| on terms we have already been type-checked.
In the next section, we will cover the tweaks we can make to NbE in
this partial setting, retaining equivalent operational behaviour but making
the algorithm more convenient to implement and more efficient.

\section{NbE in Haskell: Optimisations and Design Decisions}

TODO!

\subsection{``Inductively''-defined Values}

TODO! The general idea is defining values as a non-positive datatype
with e.g. constructors like |VLam : Ren → Val → Val| instead of by recursion 
on object types (which isn't really possible in a non-dependently-typed
setting).

\subsection{Avoiding Quotation during Evaluation}

TODO! The general idea is to define ``neutral values'', which are also
non-positive, but by examining the algorithm we can see that the operational 
behaviour ends up the same.

Should probably also discuss how it is possible to decide conversion on
values directly (i.e. fusing conversion-checking and quoting).

\subsection{Renamings vs Thinnings}

TODO! The general idea is that for quoting, it is actually sufficient for NbE
values to form a presheaf on the category of ``thinnings'' (a subset of
renamings where new variables are only inserted between existing ones - i.e.
no permuting or duplicating variables etc...). Thinnings (especially the 
variant where identity is made a constructor) can be applied more
efficiently than renamings (check easily check for |id| and short-circuit).

\subsection{De Bruijn Levels}

TODO! General idea is to represent variables in values with de Bruijn 
\textit{levels} rather than \textit{indices}, such that variables count the
number of binders between their binding site and the root of the term (rather
than their binding site and their use). This makes inserting fresh variables
(i.e. the presheaf stuff we needed for quoting to work) no longer require
a full traversal of the value.

\subsection{Explicit Closures}

TODO! I don't currently plan on implementing this optimisation, but it
is still probably worth mentioning.
It turns out the operational behaviour of the NbE algorithm can be replicated
without meta-language closures entirely! Closures can be represented in
a first-order fashion by pairing un-evaluated terms and captured environments.
This variation is no longer structurally recursive (we need to |eval| the
closure bodies during applications, similarly to naive normalisation)
but can be faster on than relying on meta-closures depending on implementation
language/runtime.

\section{NbE in Haskell: Local Equations}
 
TODO! The general idea is just to track a map of neutrals to values and
lookup neutrals in the map when necessary. Function values need to be
parameterised by updated maps to reduce properly in contexts with new equations.
 