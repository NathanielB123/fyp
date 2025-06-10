%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils
open import Utils.IdExtras

module Report.Final.c6-1_scdef where

\end{code}
%endif

% https://discord.com/channels/427551550089723915/1378514733518553179/1378715303235682445

\setchapterpreamble[u]{\margintoc}

\chapter{Elaborating Smart Case}
\labch{scdef}

\section{A New Core Language}

To recap the findings of the previous chapter, 
locally-introduced equations caused two main issues
\begin{itemize}
\item Any restrictions on equations (enforced in order to retain decidability) 
      must
      be stable under substitution (to support introducing equations
      under λ-abstractions without losing subject reduction).
\item Any proofs by induction on the syntax must account for weakening
      the context with new equations. This is problematic for normalisation
      proofs, because neutral terms are not stable under introducing equations.
\end{itemize}

The latter of these issues is, in principle, solved if we give up
congruence of conversion over \SIF (or in general, whatever piece of syntax
happens to introduce equations). Specifically, if we give up

%if False
\begin{code}
module Cooked where
  open import Dependent.SCBool.Syntax hiding (if[]; 𝔹β₁; 𝔹β₂)

  wkeq : Tms (Γ ▷ t >eq b) Γ
  wkeq = π₁eq id

  wkeq~ :  ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
        →  Tms~ (Γ~ ▷ t~ >eq) Γ~ (wkeq {b = b}) wkeq
  wkeq~ t~ = π₁eq t~ id
\end{code}
%endif

\begin{code}
  if~  : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
       → Tm~ (Γ~ ▷ t~ >eq) (A~ [ wkeq~ t~ ]) u₁ u₂
       → Tm~ (Γ~ ▷ t~ >eq) (A~ [ wkeq~ t~ ]) v₁ v₂
       → Tm~ Γ~ A~ (if t₁ u₁ v₁) (if t₂ u₂ v₂)
\end{code}

then normalisation no longer needs to recurse into the LHS/RHS branches of
|if| expressions until the scrutinee actually reduces to |TT| or |FF|.

The first issue can also be fixed by carefully relaxing the substitution law
for |if|, |if[]|.

\begin{code}
  if[]  : Tm~ rfl~ rfl~  (if t u v [ δ ]) 
                         (if (coe~ rfl~ 𝔹[] (t [ δ ])) 
                         (coe~ rfl~ wk^eq (u [ δ ^eq t ])) 
                         (coe~ rfl~ wk^eq (v [ δ ^eq t ])))
\end{code}

Intuitively, we want substitutions to apply recursively to the scrutinee
(so we check if it reduces to |TT| or |FF|), but stack up on the LHS/RHS 
(so we do not invalidate the equation in each branch). One way we can achieve
this is by outright throwing away |if[]|, and generalising the
β-laws |𝔹β₁| and |𝔹β₂|

\begin{code}
  wk,Ty : Ty~ rfl~ (A [ δ ]) (A [ wkeq ] [ δ ,eq t~ ])

  𝔹β₁  : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) TT)
       → Tm~ rfl~ wk,Ty (if t u v [ δ ]) (u [ δ ,eq t~ ])
  𝔹β₂  : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) FF)
       → Tm~ rfl~ wk,Ty (if t u v [ δ ]) (v [ δ ,eq t~ ])
\end{code}

Using these new laws, the equational theory for |if| somewhat resembles
that of
a weak-head reduction strategy. That is, normalisation may halt as soon as
it hits a stuck |if| expression, instead of recursing into the branches.

This seems like an exciting route forwards: in practice, losing 
congruence of definitional equality
over case splits is not a huge deal, as the proof in question can always just
repeat the same case split, proving the desired equation in each 
branch separately. 
Unfortunately, from a metatheoretical standpoint,
non-congruent conversion is somewhat hard to justify. QIIT and GAT signatures,
for example,
bake-in congruence of the equational theory (we used an 
explicit conversion relation, |Tm~|, above for a reason).

The key insight in solving this comes in the form of
\emph{lambda lifting}.
For context, Agda's core language only supports pattern-matching at the
level of definitions, but it can still support
|with|-abstractions \sidecite{agda2024with} and 
pattern-matching lambdas \sidecite{agda2024data} via elaboration:
new top-level definitions are created for ``local'' every pattern-match.
Because definitions are \emph{generative}, from the perspective of the surface
language, Agda also loses congruence of conversion (actually, even
reflexivity of conversion) for pattern-matching
lambdas. For example, consider the equation between these two
seemingly-equal implementations of Boolean negation.

\begin{code}
not-eq : _≡_ {A = Bool → Bool}
             (λ where  true   → false 
                       false  → true) 
             (λ where  true   → false 
                       false  → true) 
\end{code}

Attempting to prove |not-eq| with reflexivity (|refl|) returns the error:

\begin{spec}
(λ { true → false ; false → true }) x !=
(λ { true → false ; false → true }) x of type Bool
Because they are distinct extended lambdas: one is defined at
   /home/nathaniel/agda/fyp/Report/Final/c6-1_scdef.lagda:110.15-111.37
and the other at
   /home/nathaniel/agda/fyp/Report/Final/c6-1_scdef.lagda:112.15-113.37,
so they have different internal representations.
\end{spec}

This provides a natural strategy for our use-case also. We can rigorously study
a core type theory which introduces equations via top-level definitions
(proving e.g. soundness and normalisation), and then describe an elaboration
algorithm to take a surface language with an \SC-like construct, and
compile it into the core (by lifting \smart case-splits into
top-level definitions).
We call this new core type theory \SCDef. 

\subsection{Syntax}

To support global definitions, we introduce an additional 
sort: \emph{signatures} (|Sig|).
Signatures are similar to contexts in that they effectively store lists
of terms that we can reuse, but unlike contexts, signatures also store the
concrete implementation of every definition, and do not allow for
arbitrary substitution.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  Sig  : Set
  Ctx  : Sig → Set
\end{code}

We associate with |Sig| a set of morphisms, |Wk|, forming a
category of signature weakenings. |Ctx| is a presheaf on this category,and substitutions (|Tms|) are 
appropriately generalised to map between contexts paired with their signature
(we will embed signature weakenings into |Tms|).

We consider all signature weakenings to be equal (i.e. every morphism is
unique).

%if False
\begin{code}
variable Ψ Φ Ξ : Sig
postulate
\end{code}
%endif

\begin{code}
  Ty   : Ctx Ψ → Set
  Tm   : ∀ (Γ : Ctx Ψ) → Ty Γ → Set
  Wk   : Sig → Sig → Set
  Tms  : Ctx Φ → Ctx Ψ → Set
\end{code}

%if False
\begin{code}
variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx Ψ
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  φ ψ ξ : Wk Φ Ψ
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  b b₁ b₂ : Bool

Ty≡ : Γ₁ ≡ Γ₂ → Ty Γ₁ ≡ Ty Γ₂
Ty≡ = cong Ty

Tm≡ : ∀ Γ≡ → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂ 
Tm≡ = dcong₂ Tm

postulate
\end{code}
%endif

Similarly to \SCBool, we allow extending contexts with equations, and include
the relevant substitution combinators (we elide projections and equations
for brevity).


\begin{code}
  id𝒲   : Wk Ψ Ψ
  _⨾𝒲_  : Wk Φ Ψ → Wk Ξ Φ → Wk Ξ Ψ

  id   : Tms Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  
  _[_]Ctx  : Ctx Ψ → Wk Φ Ψ → Ctx Φ
  _[_]Ty   : Ty Γ → Tms Δ Γ → Ty Δ
  _[_]     : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty)

  •       : Ctx Ξ
  _▷_     : ∀ (Γ : Ctx Ξ) → Ty Γ → Ctx Ξ
  _▷_~_   : ∀ (Γ : Ctx Ξ) {A} → Tm Γ A → Tm Γ A → Ctx Ξ

  ε      : Tms Δ (• {Ξ = Ξ}) 
  _,_    : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty) → Tms Δ (Γ ▷ A) 
  _,eq_  : ∀ (δ : Tms Δ Γ) → t₁ [ δ ] ≡ t₂ [ δ ]
         → Tms Δ (Γ ▷ t₁ ~ t₂)

\end{code}

%if False
\begin{code}
  π₁     : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₁eq   : Tms Δ (Γ ▷ t₁ ~ t₂) → Tms Δ Γ

wkeq : Tms (Γ ▷ t₁ ~ t₂) Γ
wkeq = π₁eq id

postulate
\end{code}
%endif

Signatures are lists of definitions. Our first approximation for these 
definitions is a bundle of a \emph{telescope} of
argument types |Γ : Ctx Ξ| (recall that without local equations, 
a context is really just a list of types), a return 
type |A : Ty Γ|, and a body |Tm Γ A|.

\begin{code}
  •𝒮       : Sig
  _▷_⇒_≔_  : ∀ Ξ (Γ : Ctx Ξ) A → Tm Γ A → Sig
\end{code}

Intuitively, to call a definition with argument
telescope |Γ| while in a context |Δ|, we must provide an appropriate list of
arguments, specifically a list |Δ|-terms matching each type in |Γ|.
This is exactly |Tms Δ Γ|.

Of course, our 
contexts also able to contain equational assumptions, and corresponding 
substitutions hold convertibility evidence.
Rather than shying away, and defining specific argument
telescope/argument list types, we commit to our extended notions of
context and substitution, and take full advantage of this flexibility.

Specifically, placing equations in argument telescopes gives
us a way to preserve definitional equalities across definition-boundaries.
Intuitively, to call a definition that asks for a definitional equality
between |t₁| and |t₂| (i.e. its argument telescope contains |t₁ ~ t₂|),
we provide evidence that {|t₁ [ δ ] == t₂ [ δ ]|}
(where |δ| is the list of arguments prior to the equation). In other words,
to call a function that asks for a definitional equality, that equation
must also hold definitionally at the call-site.

Note that |•𝒮| should be a terminal object in the category of signature 
weakenings. After we define single-weakenings, we can derive the associated
morphism |Wk Φ •𝒮| by composing them. 

For now though, we will spend some time refining our notion of definition.
Currently, definitions are only really useful for code-reuse. Analogously
to e.g. let-bindings, we could inline the body of every definition
and retain a well-typed program.
Our objective with \SCDef is to allow definitions to not just preserve
definitional
equations from their call-site, but reflect new ones. We account for
this by letting each definition explicitly block on a propositional equality.

\begin{code}
  Id : ∀ A → Tm Γ A → Tm Γ A → Ty Γ
  
  _▷_⇒_reflect_≔_  : ∀ Ξ (Γ : Ctx Ξ) A {B t₁ t₂} → Tm Γ (Id B t₁ t₂)
                   → Tm (Γ ▷ t₁ ~ t₂) (A [ wkeq ]Ty)
\end{code}

Note that the return type of the definition, |A|, must still be valid without
the equational assumption, and therefore weakened when typing the body. 
If this were not the case, the result of calling definitions could
be ill-typed

it would be impossible to call the definition
in a type-correct way 

without the blocking equational also holding at
call-site, essentially making the point of reflection redundant.




%TODO Move this stuff up
\begin{remark}[Specialised Substitutions] \phantom{a}

We could alternatively build a syntax out of |Wk| and non-generalised
(or ``specialised'')
substitutions (i.e. {|Tms : Ctx Ψ → Ctx Ψ → Set|}). Following this approach,
we would add two presheaf actions to |Ty| and |Tm| (one for each
category), and also ensure |Tms| itself is a displayed presheaf on |Wk|.
Our category of generalised substitutions can then be derived by pairing
{|φ : Wk Φ Ψ|} and {|δ : Tms Δ Γ|} morphisms to construct generalised
{|Sub (Δ [ γ ]) Γ|}s.

We take exactly this approach in the strictified syntax, where it is
desirable for signature weakenings embedded in generalised substitutions
compute automatically. For the explicit substitution style though,
defining generalised substitutions directly leads to a more concise
definition.
\end{remark}


...

We call the list of arguments to a definition its argument \emph{telescope}.
Note that while each individual definition can only reflect one equation
at a time, definitions can depend on each other linearly, and 
preserve definitional equalities (by asking for them in their
argument telescopes), so nesting multiple invocations of equality reflection
remains possible.


\subsubsection{Returning to Booleans}

For closer comparison with \SCBool, and frankly, to simplify the coming
normalisation proof, we return to only supporting Boolean equations.

\begin{code}
  𝔹        : Ty Γ
  _▷_>eq_  : ∀ (Γ : Ctx Ξ) → Tm Γ 𝔹 → Bool → Ctx Ξ
  π₁>eq    : Tms Δ (Γ ▷ t >eq b) → Tms Δ Γ
\end{code}

\begin{code}
wk>eq : Tms (Γ ▷ t >eq b) Γ
wk>eq = π₁>eq id
\end{code}

We could now retain the existing |_▷_⇒_reflect_≔_|-style definition,
only restriction the propositional equation appropriately (i.e. the RHS must
be the result of embedding a closed Boolean). Together with the ordinary
% TODO : Ref splitters
dependent |if|, we can recover a ``smart'' |if| by splitting on the 
scrutinee |t : Tm Γ 𝔹| and calling the appropriate definition with 
the propositional evidence {|Tm Γ (Id 𝔹 t TT|)|}/{|Tm Γ (Id 𝔹 t FF|)|}
in each branch.

% TODO: Repeating "definition" here is kinda cringe
For simplicity, we instead fuse the splitter with our signature
definitions. Intuitively, definitions block on a |𝔹|-typed scrutinee,
and reduce to the LHS or RHS when the substituted
scrutinee is convertible to |TT| or |FF|.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  _▷_⇒_if_≔_∣_  : ∀ Ξ (Γ : Ctx Ξ) A (t : Tm Γ 𝔹) 
                → Tm (Γ ▷ t >eq true)   (A [ wk>eq ]Ty) 
                → Tm (Γ ▷ t >eq false)  (A [ wk>eq ]Ty)
                → Sig
  
  wk𝒲   : Wk (Ψ ▷ Γ ⇒ A if t ≔ u ∣ v) Ψ
\end{code}

This also, conveniently, removes the dependence on having propositional 
equality type.

\subsection{Soundness}

We construct a model

Generalised substitutions are interpreted as pairs 
signature environment and context environment mappings.



