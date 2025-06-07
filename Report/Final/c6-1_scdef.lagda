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

To recap, locally introduced equations caused two main issues
\begin{itemize}
\item Any restrictions on equations (enforced to retain decidability) must
      be stable under substitution (to support introducing equations
      under λ-abstractions without losing subject reduction).
\item Any proofs by induction on the syntax must account for weakening
      the context with new equations. This is problematic for normalisation
      proofs, because neutral terms are not stable under introducing equations.
\end{itemize}

We solve both of these by pivoting to a new language, which relegates reflection
to global definitions, which we call \SCDef. We then simulate
local equality reflection via \emph{elaboration}.

\subsection{Syntax}

To support global definitions, we introduce a sort \emph{signatures}.
Signatures are similar to contexts in that they store lists
of terms that we can reuse, but unlike contexts, signatures also store the
concrete implementation of every definition, and do not allow
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

Instead, we associate with |Sig|, the set of morphisms |Wk|, forming a
category of signature weakenings. |Ctx| is a presheaf on this category,and substitutions (|Tms|) are 
appropriately generalised to map between contexts paired with their signature
(we will embed signature weakenings into |Tms|).

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

postulate
\end{code}
%endif

Similarly to \SCDef, we allow extending contexts with equations, and provide
the same substitution combinators.

We consider all signature weakenings to be equal

\begin{code}
  id𝒲   : Wk Ψ Ψ
  _⨾𝒲_  : Wk Φ Ψ → Wk Ξ Φ → Wk Ξ Ψ

  id   : Tms {Ψ = Ψ} Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  
  _[_]Ctx : Ctx Ψ → Wk Φ Ψ → Ctx Φ
  _[_]Ty  : Ty Γ → Tms Δ Γ → Ty Δ



  •       : Ctx Ξ
  _▷_     : ∀ (Γ : Ctx Ξ) → Ty Γ → Ctx Ξ
  _▷_~_   : ∀ (Γ : Ctx Ξ) {A} → Tm Γ A → Tm Γ A → Ctx Ξ

  π₁   : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₁eq : Tms Δ (Γ ▷ t₁ ~ t₂) → Tms Δ Γ


wkeq : Tms (Γ ▷ t₁ ~ t₂) Γ
wkeq = π₁eq id
\end{code}

%if False
\begin{code}
postulate
\end{code}
%endif

Signatures are lists of definitions. Our first approximation for these 
definitions is a bundle of an argument telescope |Γ : Ctx Ψ|, a return 
type |A : Ty Γ|, and a body |Tm Γ A|.

\begin{code}
  •𝒮       : Sig
  _▷_⇒_≔_  : ∀ Ξ (Γ : Ctx Ξ) A → Tm Γ A → Sig
\end{code}

Intuitively, to call a definition with argument
telescope |Γ| while in a context |Δ|, we must provide an appropriate list of
arguments, specifically a list |Δ|-terms matching each type in |Γ|,
or |Tms Δ Γ|.

With contexts also able to contain equational assumptions, and corresponding 
substitutions holding evidence of convertibility, this immediately gives
us a way to preserve definitional equalities across definition-boundaries.
Intuitively, to call a definition that asks for a definitional equality
between |t₁| and |t₂| (i.e. its argument telescope contains |t₁ ~ t₂|),
{|t₁ [ δ ] == t₂ [ δ ]|} must hold definitionally at the call site
(where |δ| is the list of arguments up until the equations). In other words,
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
If this were not the case, it would be impossible to call the definition
in a type-correct way without the blocking equational also holding at
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



