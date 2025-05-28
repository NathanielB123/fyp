%if False
\begin{code}
{-# OPTIONS --prop --rewriting --termination-depth=10 #-}

open import Utils hiding (Bool; true; false)
module Report.Final.c3-2_background where

\end{code}
%endif

\section{Simply Typed Lambda Calculus}

Having established our metatheory informally, it is time to start studying type
theory more rigorously. As a warm-up, we begin by covering the theory of
simply-typed lambda calculus (STLC), and then will later cover the extension
necessary to support dependent types.

\subsection{Syntax}
\labsec{stlcrec}

\epigraph{There is no such thing as a free variable. There are only variables
bound in the context.}{\textit{Conor McBride \cite{mcbride2025free}}}

In this report, we will present type theories following the 
\textit{intrinsically-typed} discipline. That is,
rather than first defining a grammar of terms and then separately,
the typing relation (i.e. inference rules), we will define terms as an 
inductive family such that only
well-typed terms can be constructed. 

\begin{remark}[Syntax Directed Typing] \phantom{a}
Intrinsic typing enforces a one-to-one correspondence between term formers and 
typing rules (i.e. in the language of separate syntax and typing judgements, our
inference rules must all be ``syntax-directed''). However, features that appear 
in conflict with this restriction (such as subtyping
or implicit coercions) can still be formalised via ``elaboration'': 
i.e. in the core type theory, all coercions must be explicit, but this
does not prevent defining also an untyped surface language along with a partial
mapping into core terms (the ``elaborator'').
\end{remark}

In STLC, the only necessary validity criteria on types and contexts 
is syntactic in nature, so we define these as usual.
% \sideremark{Object-level constructs are distinguished from the meta-level
% (in |Set|) counterparts by not being formatted in bold.}
We include type formers for functions |A ⇒ B|, pairs |A * B|,
sums |A + B|, unit |𝟙| and the 
empty type |𝟘|, and define contexts as backwards lists of types.

\begin{code}
data Ty : Set where
  _⇒_  : Ty → Ty → Ty
  _*_  : Ty → Ty → Ty
  _+_  : Ty → Ty → Ty
  𝟙    : Ty
  𝟘    : Ty

data Ctx : Set where
  •    : Ctx
  _▷_  : Ctx → Ty → Ctx
\end{code}

%if False
\begin{code}
variable
  A B C : Ty
  Γ Δ Θ : Ctx
\end{code}
%endif

Variables can be viewed as proofs that a particular type occurs in the context.
Trivially, the type |A| occurs in the context |Γ ▷ A|, and recursively
if the type |B| occurs in context |Γ|, then the type |B| also occurs in
the context |Γ ▷ A|.

\begin{spec}
data Var : Ctx → Ty → Set where 
  vz  : Var (Γ ▷ A) A
  vs  : Var Γ B → Var (Γ ▷ A) B
\end{spec}

After erasing the indexing, we are effectively left with de Bruijn variables
\sidecite{de1972lambda}, natural numbers counting the number of binders between 
the use of a variable and the location it was bound.

We avoid named representations of variables in order
to dodge complications arising from variable capture and α-equivalence.
For legibility and convienience, when writing
example programs internal to a particular type theory, we will used named
variables, assuming the existence of an algorithm which can translate to
de Bruijn style.
% TODO Citation

Terms embed variables, and then also include the standard introduction and
elimination rules for |_⇒_|, |_*_|, |_+_|, |𝟙|.

\sideremark{To distinguish applications and abstractions of the meta-theory 
with those of the object language, we annotate |λ|s with a hat and 
use the binary operator |_·_| instead of plain juxtaposition.}

\begin{spec}
data Tm : Ctx → Ty → Set where
  `_   : Var Γ A → Tm Γ A
  ƛ_   : Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  _·_  : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  _,_  : Tm Γ A → Tm Γ B → Tm Γ (A * B)
  π₁   : Tm Γ (A * B) → Tm Γ A
  π₂   : Tm Γ (A * B) → Tm Γ B
  in₁  : Tm Γ A → Tm Γ (A + B)
  in₂  : Tm Γ B → Tm Γ (A + B)
  case : Tm Γ (A + B) → Tm (Γ ▷ A) C → Tm (Γ ▷ B) C → Tm Γ C
  ⟨⟩   : Tm Γ 𝟙
\end{spec}

%TODO we probably want to delay discussion of quotienting...
% Note that while our syntax is instrinsically-typed and to some extent
% CwF-inspired, we have not gone so far as to actually quotient by conversion
% (we won't even define a conversion relation explicitly). This is merely for
% practical convenience - i.e. to avoid getting bogged down in the details, we 
% will implement NbE, and in-doing-so prove termination and type-preservation, but
% for constraints of time, leave the full proof that NbE decides conversion to
% cited work (e.g. \sidecite{kovacs2017machine}).

\subsection{Substitution and Renaming}

We define parallel renaming and 
substitution operations by recursion on our syntax. 
Following \sidecite{altenkirch2025copypaste}, we avoid duplication between
renaming and substitution by factoring via a boolean algebra of |Sort|s, 
valued either |V : Sort| or |T : Sort| with |V ⊏ T|. 
We will skip over most of the details of
how to encode this in Agda but explicitly define |Sort|-parameterised
terms:

\begin{spec}
Tm[_] : Sort → Ctx → Ty → Set
Tm[ V ] = Var
Tm[ T ] = Tm
\end{spec}

%if False
\begin{code}
open import Common.Sort
\end{code}
%endif

%if False
\begin{code}
data Tm[_] : Sort → Ctx → Ty → Set
Var = Tm[ V ]
Tm  = Tm[ T ]

data Tm[_] where
  vz  : Var (Γ ▷ A) A
  vs  : Var Γ B → Var (Γ ▷ A) B

  `_   : Var Γ A → Tm Γ A
  ƛ_   : Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  _·_  : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  _,_  : Tm Γ A → Tm Γ B → Tm Γ (A * B)
  π₁   : Tm Γ (A * B) → Tm Γ A
  π₂   : Tm Γ (A * B) → Tm Γ B
  in₁  : ∀ B → Tm Γ A → Tm Γ (A + B)
  in₂  : ∀ A → Tm Γ B → Tm Γ (A + B)
  case : Tm Γ (A + B) → Tm (Γ ▷ A) C → Tm (Γ ▷ B) C → Tm Γ C
  ⟨⟩   : Tm Γ 𝟙
\end{code}
%endif

and lists of terms (parameterised by the sort of the terms, the context they
exist in, and the list of types of each of the terms themselves).

\begin{code}
data Tms[_] : Sort → Ctx → Ctx → Set where
  ε    : Tms[ q ] Δ •
  _,_  : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ ▷ A)
\end{code}

We can simultaneously interpret lists of variables as renamings, 
|Ren = Tms[ V ]| and lists of terms as full substitutions |Sub = Tms[ T ]|, 
with the following recursively defined substitution operation:


% TODO: Actually fill in the definitions of these substitution operations...
\begin{code}
_[_] : Tm[ q ] Γ A → Tms[ r ] Δ Γ → Tm[ q ⊔ r ] Δ A
\end{code}

Note that |ε : Sub Δ ε| gives us the substitution that weakens a term defined in 
the empty context into |Δ|, and |_,_ : Sub Δ Γ → Tm Δ A → Tms Δ (Γ ▷ A)|
expresses the principle that to map from a term in a context |Γ| extended with
|A| into a context |Δ|, we need a term in |Δ| to substite the zero 
de Bruijn variable for, |Tm Δ A|, and a substitution to recursively apply to all
variables greater than zero, |Sub Δ Γ|.

\sideremark{We refer to \cite{altenkirch2025copypaste} for the details 
of how to define these operations.}

To implement the compuational behaviour of substitution, we need to be able
to coerce up the sort of terms (terms are functorial over sort ordering |_⊑_|) 
and we need to be able
to lift substitutions over context extensions (substitutions are functorial
over context extension\remarknote{Concretely, we can take the category of
context extension as dual to the category of weakenings
|Wk : Ctx → Ctx → Set}| where |ε : Wk • •| and
|_⁺_ : Wk Δ Γ → ∀ A → Wk (Δ ▷ A) Γ|.}): 

\begin{code}
tm⊑  : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
_^_  : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ ▷ A) (Γ ▷ A)

vz          [ δ , t ]  = t
vs i        [ δ , t ]  = i [ δ ]
(` i)       [ δ ]      = tm⊑ ⊑T (i [ δ ])
(t · u)     [ δ ]      = (t [ δ ]) · (u [ δ ])
(ƛ t)       [ δ ]      = ƛ (t [ δ ^ _ ])
⟨⟩          [ δ ]      = ⟨⟩
in₁ B t     [ δ ]      = in₁ B (t [ δ ])
in₂ A t     [ δ ]      = in₂ A (t [ δ ])
case t u v  [ δ ]      = case (t [ δ ]) (u [ δ ^ _ ]) (v [ δ ^ _ ])
π₁ t        [ δ ]      = π₁ (t [ δ ])
π₂ t        [ δ ]      = π₂ (t [ δ ])
(t , u)     [ δ ]      = (t [ δ ]) , (u [ δ ])
\end{code}

We also define a number of recursively-defined operations to build and 
manipulate renamings/substitutions, including |id : Ren Γ Γ| to build
identity renamings (a backwards list of increasing variables), 
single weakenings |wk : Ren (Γ ▷ A) Γ|, single
substitutions |<_> : Tm[ q ] Γ A → Tms[ q ] Γ (Γ ▷ A)|, and
composition |_⨾_ : Tms[ q ] Δ Γ → Tms[ r ] Θ Δ → Tms[ q ⊔ r ] Θ Γ|.

\begin{code}

\end{code}

%if False
\begin{code}
Ren = Tms[ V ]
Sub = Tms[ T ]  
-- ...
id     : Tms[ q ] Γ Γ
_⁺_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ ▷ A) Γ
suc[_] : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ ▷ A) B

id {Γ = •} = ε
id {Γ = Γ ▷ A} = id ^ _

suc[ V ] = vs
suc[ T ] = _[ id {q = V} ⁺ _ ]
 
ε       ⁺ A = ε
(δ , t) ⁺ A = (δ ⁺ A) , suc[ _ ] t

δ ^ A = (δ ⁺ A) , tm⊑ V⊑ vz

tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = V} {r = V} _ i = i
tm⊑ {q = T} {r = T} _ t = t

_⨾_ : Tms[ q ] Δ Γ → Tms[ r ] Θ Δ → Tms[ q ⊔ r ] Θ Γ
ε       ⨾ σ = ε
(δ , t) ⨾ σ = (δ ⨾ σ) , (t [ σ ])

wk : Ren (Γ ▷ A) Γ
wk = id ⁺ _

<_> : Tm[ q ] Γ A → Tms[ q ] Γ (Γ ▷ A)
< t > = id , t

variable
  δ σ : Tms[ q ] Δ Γ
\end{code}
%endif

\subsection{Soundness}

In this report, we will not only specify the syntax of type theories; we will
also prove properties of them. A nice warm-up proof that we will attempt now
is to show ``soundness''.


\sideremark{Soundness expresses that STLC as a \curry{logic} is 
\curry{consistent}
relative to our metatheory (Agda).
From a \howard{PL} perspective, constructing the ``standard model'' effectively 
entails writing
\howard{interpreter}/\howard{evaluator} for STLC \howard{programs}, and 
soundness
is strongly related to STLC being a ``\howard{total}'' 
programming language - it does not admit \howard{general recursion} or 
\howard{unchecked exceptions}.}

\begin{definition}[Soundness of a Type Theory] \phantom{a}
\labremark{sound1}

A type theory with an empty type |𝟘| is sound if there are no |𝟘|-typed terms
in the empty context.

\begin{code}
stlc-sound : ¬ Tm • 𝟘
\end{code}
\end{definition}

Our strategy to prove this will be based on giving ``denotational''
semantics to STLC: we will interpret STLC constructs as objects in some other
theory (i.e. construct a model). 
A natural choice is to interpret into objects in our metatheory (Agda),
developing what is known as the ``standard model'' or ``meta-circular
interpretation''.

In the standard model, we interpret object-theory types into their counterparts
in |Set|. We call the inhabitants of these interpreted types ``values'' -
i.e. |⟦ A ⟧ᵗʸ| is the type of closed values of type |A|.

\begin{code}
⟦Ty⟧ : Set₁
⟦Ty⟧ = Set

⟦_⟧ᵗʸ : Ty → ⟦Ty⟧
⟦ A ⇒  B  ⟧ᵗʸ = ⟦ A ⟧ᵗʸ  →  ⟦ B ⟧ᵗʸ
⟦ A *  B  ⟧ᵗʸ = ⟦ A ⟧ᵗʸ  ×  ⟦ B ⟧ᵗʸ
⟦ A +  B  ⟧ᵗʸ = ⟦ A ⟧ᵗʸ  ⊎  ⟦ B ⟧ᵗʸ
⟦ 𝟙       ⟧ᵗʸ = ⊤
⟦ 𝟘       ⟧ᵗʸ = ⊥
\end{code}

Contexts are interpreted as nested pairs of values. We call inhabitants of
these nested pairs ``environments'' - i.e. |⟦ Γ ⟧ᶜᵗˣ| is the type of
environments at type |Γ|.

\begin{code}
⟦Ctx⟧ : Set₁
⟦Ctx⟧ = Set

⟦_⟧ᶜᵗˣ : Ctx → ⟦Ctx⟧
⟦ •      ⟧ᶜᵗˣ = ⊤
⟦ Γ ▷ A  ⟧ᶜᵗˣ = ⟦ Γ ⟧ᶜᵗˣ × ⟦ A ⟧ᵗʸ
\end{code}

Terms are then interpreted as functions from environments to values, so
in non-empty contexts, variables project out their associated values.
In other words, we can \textit{evaluate} a term of type 
|A| in
context |Γ| into a closed value of type |A|, |⟦ A ⟧ᵗʸ|, given an environment
|ρ : ⟦ Γ ⟧ᶜᵗˣ|. Application
directly applies values using application of the meta-theory and abstraction
extends environments with new values, using abstraction of the meta.
Given we are working inside of a constructive type theory, meta-functions are 
computable-by-construction
and so well-foundedness is ensured by structural recursion on our syntax.

%if False
\begin{code}
variable
  ⟦Γ⟧ ⟦Δ⟧ : ⟦Ctx⟧
  ⟦A⟧ ⟦B⟧ : ⟦Ty⟧
  t u v : Tm Γ A
\end{code}
%endif

\begin{code}
⟦Tm⟧ : ⟦Ctx⟧ → ⟦Ty⟧ → Set
⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ = ⟦Γ⟧ → ⟦A⟧ 

⟦Var⟧ = ⟦Tm⟧

lookup : Var Γ A → ⟦Var⟧ ⟦ Γ ⟧ᶜᵗˣ ⟦ A ⟧ᵗʸ
lookup vz      (ρ Σ, tⱽ) = tⱽ
lookup (vs i)  (ρ Σ, tⱽ) = lookup i ρ

⟦_⟧ᵗᵐ  : Tm Γ A → ⟦Tm⟧ ⟦ Γ ⟧ᶜᵗˣ ⟦ A ⟧ᵗʸ
⟦ ` i    ⟧ᵗᵐ ρ = lookup i ρ
⟦ ƛ t    ⟧ᵗᵐ ρ = λ x → ⟦ t ⟧ᵗᵐ (ρ Σ, x)
⟦ t · u  ⟧ᵗᵐ ρ = (⟦ t ⟧ᵗᵐ ρ) (⟦ u ⟧ᵗᵐ ρ)

⟦ t , u       ⟧ᵗᵐ ρ = (⟦ t ⟧ᵗᵐ ρ) Σ, (⟦ u ⟧ᵗᵐ ρ)
⟦ π₁ t        ⟧ᵗᵐ ρ = ⟦ t ⟧ᵗᵐ ρ .fst
⟦ π₂ t        ⟧ᵗᵐ ρ = ⟦ t ⟧ᵗᵐ ρ .snd
⟦ in₁ B t     ⟧ᵗᵐ ρ = inl (⟦ t ⟧ᵗᵐ ρ)
⟦ in₂ A t     ⟧ᵗᵐ ρ = inr (⟦ t ⟧ᵗᵐ ρ)
⟦ case t u v  ⟧ᵗᵐ ρ with ⟦ t ⟧ᵗᵐ ρ
... | inl tⱽ = ⟦ u ⟧ᵗᵐ (ρ Σ, tⱽ)
... | inr tⱽ = ⟦ v ⟧ᵗᵐ (ρ Σ, tⱽ)
⟦ ⟨⟩          ⟧ᵗᵐ ρ = tt
\end{code}

Soundness of STLC can now be proved by evaluating the |𝟘|-typed program in the 
empty context.

\begin{code}
stlc-sound t = ⟦ t ⟧ᵗᵐ tt
\end{code}

The standard model is useful for more than just soundness. Note that
after interpreting, computationaly-equivalent closed terms become
definitionally equal.

\begin{code}
β-example : ⟦ (ƛ ` vz) · ⟨⟩ ⟧ᵗᵐ ≡ ⟦ ⟨⟩ {Γ = •} ⟧ᵗᵐ
β-example = refl 
\end{code}

This makes sense, given the definitional equality of our metatheory (Agda)
encompasses β-equality. Computationally-equivalent terms in general can be 
described as those which are propositionally equal after interpreting.
E.g. 

\begin{code}
⟦β⟧ : ⟦ (ƛ t) · u ⟧ᵗᵐ ≡ ⟦ t [ < u > ] ⟧ᵗᵐ
\end{code}

Though, to prove |⟦β⟧|, we need to show that substitution is preserved
appropriately by the standard model - i.e. substitution is sound
w.r.t. our denotational semantics.

\begin{definition}[Soundness of Operations] \phantom{a}
\labdef{sound2}

An operation |f : A → B| is sound w.r.t. some semantics on |A| and |B| if its 
action respects those semantics. 

The nature of this respect depends somewhat
on the semantics in question: for a model, we show that it admits an 
analagous operation ⟦f⟧ such that the following diagram commutes

\begin{tikzcd}[scaleedge cd=1.25, sep=huge]
|x| \arrow[r, "|⟦_⟧ᴬ|"] \arrow[d, swap, "|f|"]
& |⟦ x ⟧ᴬ| \arrow[d, "|⟦f⟧|"] \\
|f x| \arrow[r, swap, "|⟦_⟧ᴮ|"]
& |⟦ f x ⟧ᴮ ≡' ⟦f⟧ ⟦ x ⟧ᴬ|
\end{tikzcd}

% \begin{tikzcd}[scaleedge cd=1.25, sep=huge]
% |x| \arrow[r, "|f|"] \arrow[d, swap, "|⟦_⟧ᴬ|"]
% & |f x| \arrow[d, "|⟦_⟧ᴮ|"] \\
% |⟦ x ⟧ᴬ| \arrow[r, swap, dashrightarrow, "|⟦f⟧|"]
% & |⟦ f x ⟧ᴮ ≡ ⟦f⟧ ⟦ x ⟧ᴬ|
% \end{tikzcd}

For an equational semantics (TODO reference later), we instead show that |f| 
preserves equivalence.

% Soundness of \textit{operations} on syntax (e.g. type-checking 
% algorithms) are instead defined as those which respect conversion. This is 
% exactly the sense in 
% which ``soundness'' is used in the original \SC slides, specifically convertible
% terms (defined declaratively) must be equivalent with respect to algorithmic
% conversion (reduction followed by syntactic comparison).
\end{definition}

\subsubsection{Soundness of Substitution}

Substitutions that map terms from
context |Γ| to context |Δ| can be interpreted as functions from
|Δ|-environments to |Γ|-environments.

\begin{code}
⟦Sub⟧ : ⟦Ctx⟧ → ⟦Ctx⟧ → Set
⟦Sub⟧ ⟦Δ⟧ ⟦Γ⟧ = ⟦Δ⟧ → ⟦Γ⟧

⟦_⟧ˢᵘᵇ : Sub Δ Γ → ⟦Sub⟧ ⟦ Δ ⟧ᶜᵗˣ ⟦ Γ ⟧ᶜᵗˣ
⟦ ε     ⟧ˢᵘᵇ ρ = tt
⟦ δ , t ⟧ˢᵘᵇ ρ = ⟦ δ ⟧ˢᵘᵇ ρ Σ, ⟦ t ⟧ᵗᵐ ρ
\end{code}

The contravariant ordering of |Sub|'s indices is now justified! |Γ|-terms being
interpreted into functions from |Γ|-environments makes them contravariant
functors on environment mappings. This allows us to define the semantic
action of substitution (i.e. substitution inside the model) by function
composition.

\begin{code}
⟦[]⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ → ⟦Sub⟧ ⟦Δ⟧ ⟦Γ⟧ → ⟦Tm⟧ ⟦Δ⟧ ⟦A⟧
⟦[]⟧ ⟦t⟧ ⟦δ⟧ ρ = ⟦t⟧ (⟦δ⟧ ρ)
\end{code}

Soundness of |_[_]| w.r.t. the standard model can now be stated as:

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  []-sound : ⟦ t [ δ ] ⟧ᵗᵐ ≡ ⟦[]⟧ ⟦ t ⟧ᵗᵐ ⟦ δ ⟧ˢᵘᵇ
\end{code}

The case for e.g. |t = ⟨⟩| is trivial |[]-sound {t = ⟨⟩} = refl|, but
to prove this law general, we also need to implement semantic versions of our 
other substitution operations (i.e. |_^_|, |_⁺_|, etc...) and mutually
show preservation of all them.

After all of this work, we can finally prove |⟦β⟧| using |[]-sound|
and also preservation of |<_>|, |<>-sound|.

%if False
\begin{code}
⟦▷⟧ : ⟦Ctx⟧ → ⟦Ty⟧ → ⟦Ctx⟧
⟦▷⟧ ⟦Γ⟧ ⟦A⟧ = ⟦Γ⟧ × ⟦A⟧

⟦<>⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ → ⟦Sub⟧ ⟦Γ⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧)
⟦<>⟧ ⟦t⟧ ρ = ρ Σ, ⟦t⟧ ρ

postulate
\end{code}
%endif

\begin{code}
  <>-sound : ⟦ < t > ⟧ˢᵘᵇ ≡ ⟦<>⟧ ⟦ t ⟧ᵗᵐ
\end{code}

\begin{code}
⟦β⟧ {t = t} {u = u} = 
  ⟦ (ƛ t) · u ⟧ᵗᵐ
  ≡⟨ refl ⟩≡
  (λ ρ → ⟦ t ⟧ᵗᵐ (ρ Σ, ⟦ u ⟧ᵗᵐ ρ))
  ≡⟨ refl ⟩≡
  ⟦[]⟧ ⟦ t ⟧ᵗᵐ (⟦<>⟧ ⟦ u ⟧ᵗᵐ)
  ≡⟨ cong (⟦[]⟧ ⟦ t ⟧ᵗᵐ) (sym (<>-sound {t = u})) ⟩≡
  ⟦[]⟧ ⟦ t ⟧ᵗᵐ ⟦ < u > ⟧ˢᵘᵇ
  ≡⟨ sym ([]-sound {t = t}) ⟩≡
  ⟦ t [ < u > ] ⟧ᵗᵐ ∎
\end{code}

\subsection{Reduction and Conversion}
\labsec{redconv}

Constructing a model is not the only way to give a semantics to a type theory.
We can also give ``operational'' and
``equational'' semantics to STLC using inductive relations named 
``reduction'' and ``conversion'' respectively.

We arrive at (strong) one-step β-reduction by taking the smallest monotonic 
relation on terms which includes our computation rules:

%if False
\begin{code}
infix 4 _>β_ _>β*_ _~_

variable
  t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
\end{code}
%endif

\begin{code}
data _>β_ : Tm Γ A → Tm Γ A → Set where
  -- Computation
  ⇒β   : (ƛ t) · u           >β t [ < u > ]
  +β₁  : case (in₁ B t) u v  >β u [ < t > ]
  +β₂  : case (in₂ A t) u v  >β v [ < t > ]
  *β₁  : π₁ (t , u)          >β t
  *β₂  : π₂ (t , u)          >β u

  -- Monotonicity
  ƛ_     : t₁  >β t₂  → ƛ t₁         >β ƛ t₂ 
  l·     : t₁  >β t₂  → t₁ · u       >β t₂ · u
  ·r     : u₁  >β u₂  → t · u₁       >β t · u₂
  in₁    : t₁  >β t₂  → in₁ B t₁     >β in₁ B t₂
  in₂    : t₁  >β t₂  → in₂ A t₁     >β in₂ A t₂
  case₁  : t₁  >β t₂  → case t₁ u v  >β case t₂ u v
  case₂  : u₁  >β u₂  → case t u₁ v  >β case t u₂ v
  case₃  : v₁  >β v₂  → case t u v₁  >β case t u v₂
  ,₁     : t₁  >β t₂  → t₁ , u       >β t₂ , u
  ,₂     : u₁  >β u₂  → t , u₁       >β t , u₂
  π₁     : t₁  >β t₂  → π₁ t₁        >β π₁ t₂
  π₂     : t₁  >β t₂  → π₂ t₁        >β π₂ t₂
\end{code}

We say a term |t₁| reduces to |t₂| if |t₁ >β* t₂|, where 
|_>β*_ : Tm Γ A → Tm Γ A → Set| is the reflexive-transitive closure of
|_>β_|.
Using this relation, we define ``algorithmically convertible'' terms as those
which have a common reduct.

Reduction as a concept becomes much more useful when the
relation in question is well-founded. For a full one-step reduction relation 
that 
proceeds under λ-abstractions, we call this property ``strong normalisation'',
because we can define an algorithm which takes a term |t| and
by induction on the well-founded order, produces
an equivalent (w.r.t. algorithmic conversion) but irreducible term |tᴺᶠ|,
|t|'s ``normal form''\remarknote{Technically, if reduction is not 
confluent, it might be possible to reduce a term |t| to multile distinct
normal forms. In principle, we can still explore all 
possible reduction
chains in parallel and compare sets of irreducible terms 
to decide conversion. In this scenario, we can consider the sets 
of irreducible terms themselves to be the normal forms (with
equivalence defined as whether any pair of terms in the Cartesian product 
are equal syntactically).
%
}.

\sideremark{Note that we do not enforce that normal forms are subset of
the original type, which is sometimes
useful flexibility - see e.g. \sidecite[*9.5]{altenkirch2001normalization}.\\\\
If we have an embedding |⌜_⌝ : Nfᴬ → A|, then completeness is equivalent to
the property |⌜ norm x ⌝ ≡ x|: if we assume |norm x ≡ norm y|, then
by congruence |⌜ norm x ⌝ ≡ ⌜ norm y ⌝|, which simplifies to |x ≡ y|.}

\begin{definition}[Normalisation] \phantom{a}
\labdef{norm}

In this report, we define normalisation algorithms as sound and complete 
mappings from some type |A|
to a type of ``normal forms'' with decidable equality. 

%if False
\begin{code}
module _ (A : Set) (Nfᴬ : Set) (dec : ∀ (xᴺᶠ yᴺᶠ : Nfᴬ) → Dec (xᴺᶠ ≡ yᴺᶠ)) where
  variable x y : A
\end{code}
%endif

\begin{code}
  record Norm : Set where
    field
      norm   : A → Nfᴬ
      sound  : x ≡ y → norm x ≡ norm y
      compl  : norm x ≡ norm y → x ≡ y
\end{code}

Soundness here
is defined as usual (i.e. the mapping preserves equivalence), while we define
completeness as the converse property, that that equal normal forms
implies the starting objects are equivalent.
\end{definition}

%if False
\begin{code}
_>β*_ : Tm Γ A → Tm Γ A → Set
_>β*_ = _[ _>β_ ]*_
\end{code}
%endif

\begin{code}
record _<~>_ (t₁ t₂ : Tm Γ A) : Set where
  field
    {common}  : Tm Γ A
    reduces₁  : t₁ >β* common
    reduces₂  : t₂ >β* common
\end{code}
 
If we instead take the smallest congruent equivalence relation which includes 
the computation rules, we arrive at ``declarative'' conversion.

\begin{code}
data _~_ : Tm Γ A → Tm Γ A → Set where
  -- Equivalence
  rfl~ : t ~ t
  sym~ : t₁ ~ t₂ → t₂ ~ t₁
  _∙~_ : t₁ ~ t₂ → t₂ ~ t₃ → t₁ ~ t₃

  -- Computation
  ⇒β   : (ƛ t) · u           ~ t [ < u > ]
  +β₁  : case (in₁ B t) u v  ~ u [ < t > ]
  +β₂  : case (in₂ A t) u v  ~ v [ < t > ]
  *β₁  : π₁ (t , u)          ~ t
  *β₂  : π₂ (t , u)          ~ u

  -- Congruence
  ƛ_    : t₁ ~ t₂ → ƛ t₁ ~ ƛ t₂ 
  _·_   : t₁ ~ t₂ → u₁ ~ u₂ → t₁ · u₁ ~ t₂ · u₂
  in₁   : t₁ ~ t₂ → in₁ B t₁ ~ in₁ B t₂
  in₂   : t₁ ~ t₂ → in₂ A t₁ ~ in₂ A t₂
  case  : t₁ ~ t₂ → u₁ ~ u₂ → v₁ ~ v₂ → case t₁ u₁ v₁ ~ case t₂ u₂ v₂
  _,_   : t₁ ~ t₂ → u₁ ~ u₂ → t₁ , u₁ ~ t₂ , u₂
  π₁    : t₁ ~ t₂ → π₁ t₁ ~ π₁ t₂
  π₂    : t₁ ~ t₂ → π₂ t₁ ~ π₂ t₂
\end{code}

We now have three distinct semantics-derived equivalence relations on
terms.
To study the relations between these equivalences, we introduce
some extra terminology.

Given two equivalence relations on terms |r₁ r₂ : Tm Γ A → Tm Γ A → Set|:

% Sometimes in the literature, e.g. \sidecite{altenkirch2011case} 
% this conservativity property is 
% referred to as
% ``soundness''. E.g. algorithmic conversion is sound if |t₁ <~> t₂ → t₁ ~ t₂|.
% We avoid this terminology because of how it interacts counter-intuitively with
% soundness of functions on syntax. Note that |⟦_⟧ᵗᵐ| being sound
% w.r.t. |_~_|, |t₁ ~ t₂ → ⟦ t₁ ⟧ᵗᵐ ≡ ⟦ t₂ ⟧ᵗᵐ|, implies completeness of the 
% interpretation-equivalence, but not conservativity.

\sideremark{When applied to specific choices of semantics - for example,
|r₁ = _~_| and |r₂ = _<~>_|, sometimes conservativity is referred to
as soundness, and preservation as completeness, 
e.g. \sidecite[*5]{altenkirch2011case}. We avoid this, because of how it
conflicts with functions on syntax being defined as sound if they preserve
equivalence.}

\begin{itemize}
  \item \textbf{Conservativity:} We say |r₂| is conservative 
           over |r1| if |r₂ t₁ t₂ → r₁ t₁ t₂|.
  \item \textbf{Preservation:} We say |r₂| preserves |r₁| 
           if |r₁ t₁ t₂ → r₂ t₁ t₂|.
  \item \textbf{Equivalence:} We say |r₁| and |r₂|
           are equivalent if we have that |r₂| preserves and is conservative
           over |r₁|.
\end{itemize}

We note that while our definitions of declarative and algorithmic conversion
above are equivalent and equality in the standard model preserves 
convertability, standard model equality is not conservative. 
The model also validates
various |η| equalities, including

\begin{code}
⟦𝟙η⟧ : ∀ {t : Tm Γ 𝟙} → ⟦ t ⟧ᵗᵐ ≡ ⟦ ⟨⟩ ⟧ᵗᵐ
⟦𝟙η⟧ = refl
\end{code}
and
%if False
\begin{code}
postulate
\end{code}
%endif
\begin{code}
  ⟦⇒η⟧  : ∀ {t : Tm Γ (A ⇒ B)} 
        → ⟦ t ⟧ᵗᵐ ≡ ⟦ ƛ ((t [ wk ]) · (` vz)) ⟧ᵗᵐ
\end{code}
(though the latter requires an inductive proof).

%TODO what happened here???
Updating declarative conversion with such η-equalities is pretty easy, but

Generally, declarative conversion is a nice choice for such a ``default'' 
semantics, 
given it is purely inductively defined and does not invite dangers of inheriting
unwanted properties of the model (as opposed to the denotational style) and is
cleanly separated from implementation choices (for some type theories,
e.g. with η laws, or a sort of strict propositions,
a well-founded reduction order on terms might require
some ingenuity to derive \sidecite{lindley2007extensional}, or may not 
exist \sidecite{abel2020failure} at all). 
Therefore, whenever
we refer to ``conversion'' unqualified in this report, the intended meaning
is the declarative variant.

Propositional equality of interpreted terms is actually unsound w.r.t.
conversion.


soundness of the standard model w.r.t. conversion can be shown
by checking interpreting preserves conversion |t₁ ~ t₂ → ⟦ t₁ ⟧ᵗᵐ ≡ ⟦ t₂ ⟧ᵗᵐ|,
soundness of reduction w.r.t. conversion 

 we can show that interpreting terms into the standard model preserves the 
conversion relation |t₁ ~ t₂ → ⟦ t₁ ⟧ᵗᵐ ≡ ⟦ t₂ ⟧ᵗᵐ|, we can show that |_>_|
is conservative

% Delay discussing quotienting - we can introduce at the end of explicit
% substitutions instead!
Conversion gives us a framework for defining sound operations
on terms (i.e. exactly those which preserve conversion) and also yields
a more flexible interpretation of normalisation: to find a conversion-preserving
map from terms into some other type that has decidable 
equality\remarknote{This type does not necessarily need to syntactically mirror
terms, which is sometimes useful. E.g. a nice normal forms for integer 
arithmetic expressions built out of |+|, |-| and |×| is a pair of an integer
and a map from variables to their coefficients. 
\sidecite[*6]{altenkirch2001normalization} and 
\sidecite[*8]{sterling2021normalization} analagously define normal forms
of their respective typed lambda calculi which don't embed cleanly back into
ordinary term syntax.
%
}.

We show that our equational semantics are compatible with denotational ones
by showing that the standard model preserves conversion.


It turns out that non-trivial laws hold definitionally!
