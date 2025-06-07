%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Strict

module Report.Final.c6-2_scdef where

\end{code}
%endif

\pagebreak
\section{Normalisation}

\subsection{Normal and Neutral Forms}

We define \SCDef normal forms as usual, assuming some definition of neutrals
(like in |depnbe|, we will skip over cases pertaining to coercion along
the conversion relation for a cleaner presentation).

\begin{code}
data Nf  : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set 
Ne       : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set

data Nf where
  ne𝔹   : Ne Γ 𝔹 t → Nf Γ 𝔹 t
  neIF  : Ne Γ 𝔹 u → Ne Γ (IF u A B) t → Nf Γ (IF u A B) t
  ƛ_    : Nf (Γ ▷ A) B t → Nf Γ (Π A B) (ƛ t)
  TT    : Nf Γ 𝔹 TT
  FF    : Nf Γ 𝔹 FF
\end{code}

\SCDef neutrals, however, are a little more tricky. We define
\emph{pre-neutrals} as β-neutral terms where all subterms are fully 
normal/neutral.

\begin{code}
data PreNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set where
  `_   : ∀ i → PreNe Γ A (` i)
  _·_  : Ne Γ (Π A B) t → Nf Γ A u
       → PreNe Γ (B [ < u > ]Ty) (t · u)

  callNe  : Ne Δ 𝔹 (lookup𝒮 Ψ f .scrut [ δ ]) 
          → PreNe Δ (A [ δ ]Ty) (call {A = A} f δ)
\end{code}

However, these cannot be used as the definition of ordinary neutral terms, as
modulo contextual equations, they might be convertible to |TT| or |FF|
(and therefore not fully block β-reduction, as we would expect).

Our solution is to pair the neutral term with explicit evidence that it is
not convertible to a closed Boolean.

\begin{code}
predNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set
predNe Γ A t = ∀ {Γ′} b Γ~ A~ → ¬ Box (Tm~ {Γ₂ = Γ′} Γ~ A~ t ⌜ b ⌝𝔹)

Ne Γ A t = PreNe Γ A t × predNe Γ A t
\end{code}

Of course, this definition relies heavily on the form of equations we
support. The same trick cannot easily be played in the presence of e.g.
equations between neutrals. Because such rewriting along such equations 
cannot possibly unblock β-reductions though, we equivalence modulo
neutral equations (assuming a completed set of rewrites) can be delayed
until after β-normalisation. We could therefore
leave neutrals as-is and define a neutral-rewriting relation
in terms of the completed TRS (i.e. such as \refsec{scdeftrs}) and
ultimately reduce neutrals w.r.t. this, following some well-founded
term ordering.


Note these are just the neutral/normal forms in definitionally
consistent contexts. In definitionally inconsistent contexts, we can
% TODO: We could probably break this chapter up into more sections, and then
% make this reference more specific.
collapse all terms to |⊤| as in \refsec{simplenormcompl}.

\subsection{Sound and Complete TRSs}
\labsec{scdeftrs}

Given we still do not have a well-founded order to justify completion with,
we still cannot deal with arbitrary equations. Luckily, because stability
under substitution is no longer a concern, we have a lot more freedom in
how to restrict equations. For example, we could require that all Boolean
equation LHSs are mutually irreducible (and check this syntactically),
such that our equation set is completed by definition.

% Tying our proof to any particular restriction is undesirable though. Our
% eventual goal is a language that supports as powerful local equality
% reflection is possible. To stay generic then, we introduce a notion of 
% a TRS as a list of equations from neutrals to values, a

We delay the actual details of performing this syntactic check and
recovering the required semantic information for later. For now, 
we specify the semantic requirement only: either the context is
definitionally inconsistent, or there must be a completed
TRS, equivalent to the equational context.

\begin{code}
data TRS (Γ : Ctx Ψ) : Set where
  •       : TRS Γ
  _▷_>rw_ : TRS Γ → PreNe Γ 𝔹 t → Bool → TRS Γ
\end{code}

%if False
\begin{code}
variable
  Γᶜ : TRS Γ
  tᴾᴺᵉ uᴾᴺᵉ : PreNe Γ A t
  tᴺᵉ       : Ne Γ A t
  tᴺᶠ       : Nf Γ A t
\end{code}
%endif

\begin{code}
data RwVar : TRS Γ → PreNe Γ 𝔹 t → Bool → Set where
  rz : RwVar (Γᶜ ▷ tᴾᴺᵉ >rw b) tᴾᴺᵉ b
  rs : RwVar Γᶜ tᴾᴺᵉ b₁ → RwVar (Γᶜ ▷ uᴾᴺᵉ >rw b₂) tᴾᴺᵉ b₁

record ValidTRS (Γ : Ctx Ψ) : Set where field
  trs    : TRS Γ
  sound  : RwVar {t = t} trs tᴾᴺᵉ b → Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹
  compl  : EqVar Γ t b → ∀ (tᴾᴺᵉ : PreNe Γ 𝔹 t) → RwVar trs tᴾᴺᵉ b

def-incon : Ctx Ψ → Prop
def-incon Γ = Tm~ (rfl~ {Γ = Γ}) rfl~ TT FF

data ComplTRS (Γ : Ctx Ψ) : Set where
  compl  : ValidTRS Γ → ComplTRS Γ
  !!     : def-incon Γ → ComplTRS Γ

\end{code}

\subsection{Normalisation by Evaluation}

\section{Elaboration}


% TODO: Not sure where to put this
The global definitions in \SCDef exist only to justify this apparent
lack of congruence (definition variables explicitly
identify the unique source of each case split). 
It would perhaps be interesting to try and prove
normalisation for this surface language directly.

\subsection{Syntactic Restrictions for Generating TRSs}

\subsection{Elaborating Case Splits}


