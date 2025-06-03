%if False
\begin{code}
{-# OPTIONS --prop --rewriting --mutual-rewriting #-}

open import Utils renaming (ε to [])
open import Utils.IdExtras

open import Report.Final.c2-2_background
 
module Report.Final.c2-6_background where

\end{code}
%endif

\pagebreak
\section{Normalisation by Evaluation}
\labsec{nbe}

Normalisation by Evaluation (NbE) 
\sidecite{berger1991inverse, altenkirch1995categorical}
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
      to values \sidecite{altenkirch2017normalisation}). 
      % This enables 
      % working with more ``semantic'' \sidecite{kaposi2025type} definitions 
      % of type theory (e.g. Categories with Families, or CwFs) where terms are 
      % quotiented by conversion, 
      % providing 
      % soundness ``for free''.
      % \sideremark{Quotienting by conversion is 
      % especially 
      % attractive in the setting of dependent types, where intrinsically-typed
      % syntax must otherwise be defined mutually with conversion to account for
      % definitional equality \sidecite[*4]{danielsson2006formalisation, 
      % kovacs2023setoid}.}
\item \textbf{Efficiency:} NbE avoids repeated expensive
      single-substitutions (which need to traverse the whole syntax tree
      each time to possibly replace variables with the substitutee) 
      \sidecite{kovacs2023smalltt}. 
      Instead, the 
      mappings between variables
      and semantic values are tracked in a persistent map (the ``environment''), 
      such that variables can be looked up exactly when they are evaluated.
\end{itemize}

This all means that NbE is useful both as a technique to prove normalisation
for type theory, and as an algorithm in typechecker implementations for
deciding convertability of types. We will use NbE for both purposes in this
project, and will discuss the shortcuts we can take when implementing NbE
%TODO reference section
in a partial programming language (specifically Haskell) in 
(TODO SECTION REFERENCE HERE).

% For the application on NbE in this project, only the last of these points is
% truly relevant. Specifically, we do not plan to directly prove
% normalisation of type theory with local equational assumptions via NbE,
% primarily because I am unaware of a good way to justify rewriting-to-completion
% without going down to the level of an ordering on terms. 

% Instead, following \sidecite[*7]{coquand1996algorithm}, we shall employ NbE as 
% the algorithm to decide conversion in our prototype Haskell typechecker. 
% On top of the efficiency benefits, NbE is also relatively simple to implement, 
% and as we shall see, is quite compatible with \textbf{smart case} in the sense 
% that the extensions necessary to support local equations are minimal.

To introduce NbE, we will begin by deriving the algorithm for the
the recursive substitution STLC syntax given in \refsec{stlcrec}, 
and sketch how to prove its correctness. We
will then extend the technique to dependent type theory following
\sidecite{altenkirch2017normalisation}.

\subsection{Naive Normalisation}
\labsec{naive}

As a warm-up to NbE, we will start by implementing ``naive'' normalisation,
i.e. recursing on a term, contracting β-redexes where possible by applying 
single-substitutions. Using this approach, termination can only be justfied
by a separate strong normalisation result.

We first define our goal: β-normal forms, |Nf Γ A|, inductively (mutually 
recursively with stuck,
neutral terms, |Ne Γ A|) along with the obvious injections back into ordinary 
terms, |⌜_⌝|, |⌜_⌝ne|.

\sideremark{To enforce η-normality for |⇒|, |*| and |𝟙|, we could restrict 
embedded neutrals in |Nf| to only those of positive types, 
|𝟘| and |+|. βη-normal forms
accounting for positive types more complicated 
\sidecite[*3.5]{scherer2017deciding} (and actually |βη| normalisation for
STLC with positive inductive types like |ℕ| is undecidable).}

\begin{code}
data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  `_    : Var Γ A → Ne Γ A
  _·_   : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
  π₁    : Ne Γ (A * B) → Ne Γ A
  π₂    : Ne Γ (A * B) → Ne Γ B
  case  : Ne Γ (A + B) → Nf (Γ ▷ A) C → Nf (Γ ▷ B) C → Ne Γ C

data Nf where
  ne   : Ne Γ A → Nf Γ A
  ƛ_   : Nf (Γ ▷ A) B → Nf Γ (A ⇒ B) 
  _,_  : Nf Γ A → Nf Γ B → Nf Γ (A * B)
  ⟨⟩   : Nf Γ 𝟙
  in₁  : ∀ B → Nf Γ A → Nf Γ (A + B)
  in₂  : ∀ A → Nf Γ B → Nf Γ (A + B)

⌜_⌝Nf  : Nf Γ A → Tm Γ A
⌜_⌝Ne  : Ne Γ A → Tm Γ A
\end{code}

%if False
\begin{code}
⌜ ƛ t      ⌝Nf = ƛ ⌜ t ⌝Nf
⌜ t , u    ⌝Nf = ⌜ t ⌝Nf , ⌜ u ⌝Nf
⌜ ⟨⟩       ⌝Nf = ⟨⟩
⌜ in₁ B t  ⌝Nf = in₁ B ⌜ t ⌝Nf
⌜ in₂ A t  ⌝Nf = in₂ A ⌜ t ⌝Nf
⌜ ne t     ⌝Nf = ⌜ t ⌝Ne

⌜ ` i         ⌝Ne = ` i
⌜ t · u       ⌝Ne = ⌜ t ⌝Ne · ⌜ u ⌝Nf
⌜ π₁ t        ⌝Ne = π₁ ⌜ t ⌝Ne
⌜ π₂ t        ⌝Ne = π₂ ⌜ t ⌝Ne
⌜ case t u v  ⌝Ne = case ⌜ t ⌝Ne ⌜ u ⌝Nf ⌜ v ⌝Nf
\end{code}
%endif

We can now attempt to define normalisation by direct recursion on terms, relying
on substitution to contract β-redexes. For the rest of this section, we
will restrict our attention to the cases for |_⇒_| types, for simplicity.

\begin{spec}
norm   : Tm Γ A → Nf Γ A
nf-app : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

norm (ƛ t)    = ƛ (norm t)
norm (t · u)  = nf-app (norm t) (norm u)

nf-app (ne t)  u = ne (t · u)
nf-app (ƛ t)   u = norm (⌜ t ⌝Nf [ < ⌜ u ⌝Nf > ])
\end{spec}

\sideremark{Note that normal forms are
not stable under substitution (i.e. substitution can create new β-redexes), so 
we cannot easily define substitution on normal forms to resolve this. 
It is perhaps worth mentioning though, that if one is more careful
with the representation of neutral spines (among other things), pushing in
this direction can lead to another structurally recursive normalisation
algorithm known as ``hereditary substitution''
\sidecite[*4]{keller2010hereditary}. Unfortunately, it is currently 
unclear whether this technique scales to dependent types.}

In a partial language, when applied to normalising terms, this definition
is works! The single substitutions are less efficient on terms with
multiple β-redexes than the NbE approach of tracking all variable mappings
in a single environment, but with effort, it can be optimised
(e.g. we could annotate subterms with the sets of variables that are 
actually used, to avoid unnecessary traversals during substitution).

In a total setting, unfortunately, naive normalisation is clearly not 
well-founded by structural recursion. 
|⌜ norm t ⌝Nf [ < ⌜ norm u ⌝Nf > ]| is not structurally smaller than |t · u|.

%if False
\begin{code}
infix 4 _>s_
infix 4 _>βs_
infix 4 _>βs*_
infix 4 _>βs⁺_
\end{code}
%endif

Making naive normalisation total relies on a strong normalisation result: we 
need to know that β-reduction, |_>β_|, is well-founded. 
\sidedef[*2]{Accessibility}{
Classically, strong normalisation can be defined as there 
existing no infinite chains of reductions. To induct w.r.t. reduction order
constructively, we instead use accessibility predicates.
\nocodeindent
%if False
\begin{code}
module _ {A : Set} where
\end{code}
%endif
\begin{spec}
  data Acc  (_>_ : A → A → Set) 
            (x : A) : Set where
    acc  : ( ∀ {y} → x > y 
             → Acc _>_ y) 
         → Acc _>_ x
\end{spec}
\resetcodeindent
Intuitively, |Acc _>_ x| can be thought of as the type of
finite-depth trees starting at |x|, with branches corresponding to single steps
along |_>_| and minimal elements w.r.t. |_>_| at the leaves.\\\\
We use |SN| as a synonymn for |Acc| when the ordering is a small-step reduction
relation that proceeds underneath abstractions.
}
Actually, we will make use of 
the accessibility of typed terms w.r.t. interleaved structural ordering, |_>s_|, 
and β-reduction, but luckily obtaining this from traditional
strong normalisation is not too difficult \sidecite[*21]{zulip2024combining}. 
Note that |_>β_| commutes with
|_>s_| in the sense that |t >s u → u >β v → ∃[ w ] t >β w × w >s v|, or as a 
diagram:

\begin{tikzcd}[scaleedge cd=1.25, sep=huge]
|t| \arrow[r, "|_>s_|"] \arrow[d, swap, dashrightarrow, "|_>β_|"]
& |u| \arrow[d, "|_>β_|"] \\
|w| \arrow[r, swap, dashrightarrow, "|_>s_|"]
& |v|
\end{tikzcd}

We therefore skip ahead to defining a single |_>βs_| relation on terms 
encompassing both structural and reduction orderings, and assume we have a proof
that this combined order is well-founded.

\begin{code}
data _>s_ : Tm Γ A → Tm Δ B → Set where
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
_>βs*_ : BTm → BTm → Set 
_>βs*_ = _[ _>βs_ ]*_

_>βs⁺_ : BTm → BTm → Set
_>βs⁺_ = _[ _>βs_ ]+_

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
of orders with $^{+}$ and $^{*}$ respectively.}

\begin{code}
Nf> : ∀ Γ A → Tm Γ A → Set
Nf> Γ A t = Σ⟨ tᴺᶠ ∶ Nf Γ A ⟩× (t >β* ⌜ tᴺᶠ ⌝Nf)
\end{code}

Actually using our accessibility predicate to justify naive normalisation
gets quite cluttered, but the main idea is to ensure that we are always 
making progress with respect to |_>βs_|.

\begin{code}
norm    : ∀ (t : Tm Γ A) → SN _>βs⁺_ ⟪ t ⟫ → Nf> Γ A t

nf-app  : ∀ (tᴺᶠ : Nf Γ (A ⇒ B)) (uᴺᶠ : Nf Γ A) 
        → SN _>βs⁺_ ⟪ t · u ⟫ → t · u >β* ⌜ tᴺᶠ ⌝Nf · ⌜ uᴺᶠ ⌝Nf
        → Nf> Γ B (t · u)

norm (` i)    a     = ne (` i) Σ, []
norm (ƛ t)    (acc a) 
  using tᴺᶠ  Σ, t>tᴺᶠ  ← norm t (a ⟪ s> ƛ> ⟫) 
  = (ƛ tᴺᶠ)  Σ, ƛ* t>tᴺᶠ
norm (t · u)  (acc a) 
  using  tᴺᶠ  Σ, t>tᴺᶠ  ← norm t (a ⟪ s> l·> ⟫)
      |  uᴺᶠ  Σ, u>uᴺᶠ  ← norm u (a ⟪ s> ·r> ⟫)
  = nf-app tᴺᶠ uᴺᶠ (acc a) (t>tᴺᶠ ·* u>uᴺᶠ)

nf-app (ne t)  u _ tu>tuᴺᶠ    
  = ne (t · u) Σ, tu>tuᴺᶠ
nf-app (ƛ t)   u (acc a) []      
  using tuᴺᶠ Σ, tu>tuᴺᶠ ← norm (⌜ t ⌝Nf [ < ⌜ u ⌝Nf > ]) (a ⟪ β> ⇒β ⟫) 
  = tuᴺᶠ Σ, ⇒β ∷ tu>tuᴺᶠ
nf-app (ƛ t)   u (acc a) (p ∷ q) 
  using tuᴺᶠ Σ, tu>tuᴺᶠ ← norm  (⌜ t ⌝Nf [ < ⌜ u ⌝Nf > ]) 
                                (a (β> p ∷+ (map* _ β> q ∘* ⟪ β> ⇒β ⟫*)))
  = tuᴺᶠ Σ, (p ∷ q ∘* ⟪ ⇒β ⟫* ∘* tu>tuᴺᶠ)

normalise : Tm Γ A → Nf Γ A
normalise t = norm t (sn⁺ (wf t)) .fst
\end{code}

Soundness and completeness of |normalise| follows from equivalence between
algorithmic and declarative conversion (completeness relies on confluence of 
reduction).

\subsubsection{From the Standard Model to Presheaves}

To derive a structurally-recursive normalisation algorithm,
our focus should be the case for application.
I.e. when aiming to produce |Nf Γ A|s directly by recursion on our syntax,
we failed to derive a structurally recursive algorithm because there is no
analogue of |_·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B| on normal forms.

For inspiration on how to solve this, we recall the definition of the standard
model. There, we were able to write a structurally-recursive interpreter
for closed terms by interpreting object-level functions, abstractions
and applications into their meta-level counterparts. E.g. we implemented
application in the model merely with meta-level application (plus threading
of environments.)

\begin{spec}
⟦ t · u  ⟧ᵗᵐ ρ = (⟦ t ⟧ᵗᵐ ρ) (⟦ u ⟧ᵗᵐ ρ)
\end{spec}

We cannot recover normalisation from the standard model, however. 
Without an
environment of closed values to evaluate with respect to, we cannot hope to
inspect the structure of evaluated terms (i.e. meta-level functions like 
|⟦ Γ ⟧ᶜᵗˣ → ⟦ A ⟧ᵗʸ| are opaque).
Similarly, even with an environment, 
we cannot inspect the structure of interpreted |⇒|-typed values beyond
testing their behaviour on particular inputs given these are 
again opaque meta-language functions.
The ``problem'' we are 
encountering is that our values have no first-order representation of variables.

It turns out, by carefully defining a similar model, based on presheaves, we can
embed stuck, 
first-order variables into 
values\remarknote{In fact, we are forced to include general, stuck neutral 
terms to support application where the LHS is a variable.}
, implement evaluation in open contexts
and, critically, \textit{invert} evaluation, ``quoting'' back into
normalised first-order terms (i.e. our normal forms). This \textit{evaluation} 
followed by \textit{quoting} is exactly normalisation by evaluation.

\subsection{The Presheaf Model}

Central to the presheaf model (perhaps unsurprisingly) is the concept of a
presheaf: contravariant functors into |Set| \refdef{presheaf}.
We actually have a choice about which category to take presheaves
over, with the key restrictions being that it must be a subset of
substitutions, normal/neutral forms must be stable w.r.t. it and it must
include the single-weakening |wk : Tms (Γ ▷ A) Γ| (we will see why these
latter two restrictions are important later).
The two standard choices are renamings |Ren Δ Γ|, which we have seen already
and thinnings |Thin Δ Γ|. We will use thinnings (also known as
order-preserving embeddings) because type
theories we will consider later in this report will actually not feature
renaming-stable normal/neutral forms.

We define thinnings concretely as
\begin{code}
data Thin : Ctx → Ctx → Set where
  ε      : Thin • •
  _^ᵀʰ_  : Thin Δ Γ → ∀ A → Thin (Δ ▷ A) (Γ ▷ A)
  _⁺ᵀʰ_  : Thin Δ Γ → ∀ A → Thin (Δ ▷ A) Γ
\end{code}

%if False
\begin{code}
variable
  δᵀʰ σᵀʰ γᵀʰ : Thin Δ Γ
\end{code}
%endif

We can show these are indeed a category by deriving the identity thinning and
composition, and proving the relevant laws

\begin{code}
idᵀʰ   : Thin Γ Γ
_⨾ᵀʰ_  : Thin Δ Γ → Thin Θ Δ → Thin Θ Γ

id⨾ᵀʰ  : idᵀʰ ⨾ᵀʰ δᵀʰ ≡ δᵀʰ
⨾idᵀʰ  : δᵀʰ ⨾ᵀʰ idᵀʰ ≡ δᵀʰ
⨾⨾ᵀʰ   : (δᵀʰ ⨾ᵀʰ σᵀʰ) ⨾ᵀʰ γᵀʰ ≡ δᵀʰ ⨾ᵀʰ (σᵀʰ ⨾ᵀʰ γᵀʰ)
\end{code}

And indeed thinning encompass weakenings

\begin{code}
wkᵀʰ : Thin (Γ ▷ A) Γ
wkᵀʰ = idᵀʰ ⁺ᵀʰ _
\end{code}

For their action, we can take a shortcut for now and rely on their embedding
into renamings.

\begin{code}
⌜_⌝Th : Thin Δ Γ → Ren Δ Γ
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
|F →ᴾˢʰ G = λ Γ → F Γ → G Γ| but this doesn't quite work. When trying
to implement\\|thin : Thin Δ Γ → (F →ᴾˢʰ G) Γ → (F →ᴾˢʰ G) Δ| we
only have access to an |F Δ| and a function which accepts |F Γ|s\remarknote{
Note the |Thin Δ Γ| thinning can only transform |F Γ|s into |F Δ|s, not the 
other way around.
}.
The solution is to quantify over thinnings, i.e. 
|F →ᴾˢʰ G = λ Γ → ∀ {Δ} → Thin Δ Γ → F Δ → G Δ|. 
%. Specifically
%|F Δ → G Δ| should be a natural transformation.
%\begin{code}
%⟦_⟧ᴾˢʰ   : Ty → Ctx → Set
%_[_]Psh  : Thin Δ Γ → ⟦ A ⟧ᴾˢʰ Δ → ⟦ A ⟧ᴾˢʰ Γ
%eval     : Tm Γ A → ⟦ A ⟧ᴾˢʰ
%\end{code}
%
%f :  Thin Δ Γ → F Δ → G Δ
%
%f (δᵀʰ ⨾ᵀʰ σᵀʰ) (eval δ

% \begin{tikzcd}[scaleedge cd=1.25, sep=huge]
% |A| \arrow[r, "|⟦_⟧ᴾˢʰ|"] \arrow[d, swap, "|_[ δ ]Ty|"]
% & |⟦ A ⟧ᴾˢʰ| \arrow[d, "|_[ δᵀʰ ]Psh|"]
% \\ |A [ δ ]Ty| \arrow[r, swap, "|⟦_⟧ᴾˢʰ|"]
% & |⟦ A [ δ ] ⟧ᴾˢʰ ≡' ⟦ A ⟧ᴾˢʰ [ δ ]Psh|
% \end{tikzcd}


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
the category of presheaves. The presheaf action |_[_]Psh| is defined by
recursion on types.

\begin{code}
⟦_⟧ᴾˢʰ : Ty → Ctx → Set
⟦ A ⇒  B  ⟧ᴾˢʰ Γ = ∀ {Δ} → Thin Δ Γ → ⟦ A ⟧ᴾˢʰ Δ → ⟦ B ⟧ᴾˢʰ Δ
⟦ A *  B  ⟧ᴾˢʰ Γ = ⟦ A ⟧ᴾˢʰ Γ × ⟦ B ⟧ᴾˢʰ Γ
⟦ A +  B  ⟧ᴾˢʰ Γ = ⟦ A ⟧ᴾˢʰ Γ ⊎ ⟦ B ⟧ᴾˢʰ Γ
⟦ 𝟙       ⟧ᴾˢʰ Γ = ⊤
⟦ 𝟘       ⟧ᴾˢʰ Γ = ⊥
\end{code}
\begin{code}
_[_]Psh : ⟦ A ⟧ᴾˢʰ Γ → Thin Δ Γ → ⟦ A ⟧ᴾˢʰ Δ
\end{code}

\begin{remark}[Naturality of Presheaf Exponentials] \phantom{a}
\labremark{funvalnat}

Technically, our presheaf exponentials are still not quite right here. We also 
need a naturality condition \sidecite{1lab2025exponentials}:
thinning the argument should be equivalent to thinning the result
of the application.

%if False
\begin{code}
⟦_⟧ᴾˢʰ′ : Ty → Ctx → Set
\end{code}
%endif

\begin{code}
⟦ A ⇒  B ⟧ᴾˢʰ′ Γ 
  =  Σ⟨ f ∶ (∀ {Δ} → Thin Δ Γ → ⟦ A ⟧ᴾˢʰ Δ → ⟦ B ⟧ᴾˢʰ Δ)
     ⟩× (  ∀ {Δ Θ} uⱽ (δᵀʰ : Thin Δ Γ) (σᵀʰ : Thin Θ Δ) 
           →  f (δᵀʰ ⨾ᵀʰ σᵀʰ) (uⱽ [ σᵀʰ ]Psh) ≡ (f δᵀʰ uⱽ) [ σᵀʰ ]Psh)
\end{code}

To merely implement NbE algorithm for (unquotiented) STLC, 
allowing unnatural |⇒|-typed values does not cause any trouble.
However, when proving soundness, this refinement is essential
\sidecite{kovacs2017machine}
(specifically, when showing preservation of substitution). For simplicity,
we will ignore the naturality condition for now.
\end{remark}

A final subtlety arises with the ``positive'' type formers
|_+_| and |𝟘|.
E.g. While |λ Γ → ⊥| does satisfy 
all the necessary laws of an initial object, 
\sideremark{\sidecite[*6.5]{altenkirch2001normalization} 
explores NbE using model based on sheaves (instead of presheaves) to fix this 
more
elegantly and in doing so decides |η| (as well as |β|) equivalence for sums, 
but the cost is a much less efficient
% TODO: Maybe mention how the same trick cannot be played with ℕ, or how
% extending the idea to dependent types is still a WIP.
algorithm.}
and terms of type |𝟘| can only occur inside empty contexts (i.e. contexts 
containing |𝟘|), when it comes to evaluating a variable of type |𝟘|, we 
cannot hope to 
produce a proof of |⊥| (i.e. the context containing the empty type does not mean
evaluation can give up - normalisation requires evaluating under all contexts).

To solve this, we must embed neutrals into the model. E.g. we could interpret 
|𝟘| as |λ Γ → Ne Γ 𝟘|. |λ Γ → Ne Γ 𝟘| is obviously not an initial object
in the category of presheaves, so by doing this we have slightly broken the
model, but it turns out that only the |η| laws for |𝟘| are actually lost
(which lines up exactly with the consequences of embedding neutrals in |Nf|).
We are aiming only to β-normalise terms for now, and will therefore actually 
take a more
extreme option, embedding neutrals of all types as to line up more closely with
our β-normal forms.

\begin{code}
Val     : Ctx → Ty → Set
PshVal  : Ctx → Ty → Set

Val Γ A = PshVal Γ A ⊎ Ne Γ A

PshVal Γ (A ⇒ B)  = ∀ {Δ} → Thin Δ Γ → Val Δ A → Val Δ B 
PshVal Γ (A * B)  = Val Γ A × Val Γ B
PshVal Γ (A + B)  = Val Γ A ⊎ Val Γ B
PshVal Γ 𝟙        = ⊤
PshVal Γ 𝟘        = ⊥
\end{code}

Note that although we are mixing inductively (i.e. |Ne|) and recursively
(i.e. |PshVal|) defined type families here, the combination remains
well-founded.

Thinning can now be implemented for |PshVal Γ A| by recursion on the type |A|.
For thinning of values in general, we can delegate to thinning
on |PshVal Γ A|s and |Ne Γ A|s as appropriate. 

% TODO: Thinning for neutrals
%if False
\begin{code}
postulate 
  _[_]Ne : Ne Γ A → Thin Δ Γ → Ne Δ A
\end{code}
%endif

\begin{code}
_[_]Val     : Val Γ A →  Thin Δ Γ → Val Δ A
thinPshVal  : ∀ A → Thin Δ Γ → PshVal Γ A → PshVal Δ A

inl tⱽ   [ δᵀʰ ]Val = inl (thinPshVal _ δᵀʰ tⱽ) 
inr tᴺᵉ  [ δᵀʰ ]Val = inr (tᴺᵉ [ δᵀʰ ]Ne)

thinPshVal (A ⇒ B) δᵀʰ tⱽ          = λ σᵀʰ uⱽ → tⱽ (δᵀʰ ⨾ᵀʰ σᵀʰ) uⱽ
thinPshVal (A * B) δᵀʰ (tⱽ Σ, uⱽ)  = tⱽ [ δᵀʰ ]Val Σ, uⱽ [ δᵀʰ ]Val
thinPshVal (A + B) δᵀʰ (inl tⱽ)    = inl (tⱽ [ δᵀʰ ]Val)
thinPshVal (A + B) δᵀʰ (inr tⱽ)    = inr (tⱽ [ δᵀʰ ]Val)
thinPshVal 𝟙       δᵀʰ tt          = tt
\end{code}

To implement NbE, we need to define both evaluation from terms to values and
``quotation'' from values to normal forms. 

\begin{code}
data Env : Ctx → Ctx → Set

qval  : ∀ A → Val Γ A → Nf Γ A
eval  : Tm Γ A → Env Δ Γ → Val Δ A
\end{code}

We start with evaluation, which
is quite similar to |⟦_⟧ᵗᵐ| in the standard model, but needs to deal
with the cases for stuck neutrals appropriately.
Evaluation is done w.r.t. an environment, which unlike the standard model is now
parameterised by two contexts, similarly to |Thin|/|Tms|: first, the context
each of the values exist in and second the list of types of the
values themselves.

\begin{code}
data Env where
  ε    : Env Δ •
  _,_  : Env Δ Γ → Val Δ A → Env Δ (Γ ▷ A)
\end{code}

Note that environments can be thinned by simply folding |_[_]Val|, and
identity environments can be constructed by lifting over context extension and
embedding variables by composing |`_ : Var Γ A → Ne Γ A| and
|inr : Ne Γ A → Val Γ A|.

\begin{code}
_[_]ℰ  : Env Δ Γ → Thin Θ Δ → Env Θ Γ
_^ℰ_   : Env Δ Γ → ∀ A → Env (Δ ▷ A) (Γ ▷ A)
idℰ    : Env Γ Γ
\end{code}

%if False
\begin{code}
ε         [ δᵀʰ ]ℰ = ε
(ρ , tⱽ)  [ δᵀʰ ]ℰ = (ρ [ δᵀʰ ]ℰ) , (tⱽ [ δᵀʰ ]Val)
\end{code}
%endif


Evaluation then proceeds by recursion on the target term. The main subtlety
is in application of values, where the LHS is neutral. In this case
we need to turn quote the RHS back to an |Nf| via |qval| to apply 
|_·_ : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B| (i.e. evaluation actually depends on
quotation).

\begin{code}


lookupVal : Var Γ A → Env Δ Γ → Val Δ A
lookupVal vz      (ρ , tⱽ) = tⱽ
lookupVal (vs i)  (ρ , tⱽ) = lookupVal i ρ

appVal : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
appVal (inl  tⱽ   ) uⱽ = tⱽ idᵀʰ uⱽ
appVal (inr  tᴺᵉ  ) uⱽ = inr (tᴺᵉ · qval _ uⱽ)

π₁Val : Val Γ (A * B) → Val Γ A
π₁Val (inl  (tⱽ Σ, uⱽ))  = tⱽ
π₁Val (inr  tᴺᵉ)         = inr (π₁ tᴺᵉ)    

π₂Val : Val Γ (A * B) → Val Γ B
π₂Val (inl  (tⱽ Σ, uⱽ))  = uⱽ
π₂Val (inr  tᴺᵉ)         = inr (π₂ tᴺᵉ)
 
caseVal  : Val Γ (A + B) 
         → (Val Γ A → Val Γ C) → Nf (Γ ▷ A) C
         → (Val Γ B → Val Γ C) → Nf (Γ ▷ B) C
         → Val Γ C
caseVal (inl (inl tⱽ))  uⱽ uᴺᶠ vⱽ vᴺᶠ = uⱽ tⱽ
caseVal (inl (inr tⱽ))  uⱽ uᴺᶠ vⱽ vᴺᶠ = vⱽ tⱽ
caseVal (inr tᴺᵉ)       uⱽ uᴺᶠ vⱽ vᴺᶠ = inr (case tᴺᵉ uᴺᶠ vᴺᶠ)

eval (` i)         ρ = lookupVal i ρ
eval (ƛ t)         ρ = inl λ δᵀʰ uⱽ → eval t ((ρ [ δᵀʰ ]ℰ) , uⱽ)
eval (t · u)       ρ = appVal (eval t ρ) (eval u ρ)
eval (t , u)       ρ = inl (eval t ρ Σ, eval u ρ)
eval (π₁ t)        ρ = π₁Val (eval t ρ)
eval (π₂ t)        ρ = π₂Val (eval t ρ)
eval (in₁ B t)     ρ = inl (inl (eval t ρ))
eval (in₂ A t)     ρ = inl (inr (eval t ρ))
eval ⟨⟩            ρ = inl tt
eval (case t u v)  ρ 
  = caseVal  (eval t ρ) 
             (λ tⱽ → eval u  (ρ , tⱽ)) (qval _ (eval u  (ρ ^ℰ _))) 
             (λ tⱽ → eval v  (ρ , tⱽ)) (qval _ (eval v  (ρ ^ℰ _))) 
\end{code}

To implement |qval|, we instead proceed by recursion on types. 
Being able to weaken values is critical to quoting back |⇒|-typed
values, where to inspect their structure, we need to be able to apply them to a
fresh variable |vz|.

\begin{code}
qval A        (inr  t)         = ne t 
qval (A ⇒ B)  (inl  f)         = ƛ qval B (f wkᵀʰ (inr (` vz)))
qval (A * B)  (inl  (t Σ, u))  = qval A t , qval B u
qval (A + B)  (inl  (inl t))   = in₁ B (qval A t)
qval (A + B)  (inl  (inr t))   = in₂ A (qval B t)
qval 𝟙        (inl  tt)        = ⟨⟩
\end{code}

Normalisation can now be implemented by evaluation followed by quoting.

\begin{code}
nbe : Tm Γ A → Nf Γ A
nbe t = qval _ (eval t idℰ)
\end{code}

We are done! Of course, to verify our normalisation algorithm is correct
(actually \textit{prove} normalisation for STLC), we
need to do more work, checking soundness and completeness
as defined in \refdef{norm}.
We refer to \sidecite{kovacs2017machine} for the details, but in short, 
we can prove:
\begin{itemize}
  \item \textbf{Soundness} by proving that |eval| preserves conversion by 
  induction on terms, and that |qval| preserves propositional equality.
  We also need to enforce naturality of |⇒|-typed values as mentioned in
  \refremark{funvalnat}.
  \item \textbf{Completeness} by defining a logical relation between terms
  and values by induction on types, showing |t [ δ ]| and |eval t ρ| are 
  logically related given the terms in |δ| are all logically related 
  to the values in |ρ| and finally proving that |qval| preserves the logical
  relation.
\end{itemize}

