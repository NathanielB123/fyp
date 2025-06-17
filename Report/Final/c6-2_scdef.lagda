%if False
\begin{code}
{-# OPTIONS --prop --rewriting --cumulativity --mutual-rewriting --show-irrelevant #-}

open import Utils
open import Utils.IdExtras

open import Dependent.SCDef.Strict

module Report.Final.c6-2_scdef where

\end{code}
%endif

\pagebreak
\section{Normalisation}
\labsec{normscdef}

In the below section, we switch to use a strictified \SCDef syntax.
Compared to the presentation with explicit substitutions, the 
main differences (beyond substitution equations holding definitionally) are 
as follows:
\begin{itemize}
  \item |Tms Δ Γ| now refers only to specialised substitutions 
        (\refremark{scdefspecsub}).
  \item We have dedicated types for representing indexing into
        signatures (|DefVar Ξ Γ A|) and picking out equations from
        the context (|EqVar Γ t b|).
        \sideremark{These datatypes also need |coe|
        constructors, corresponding to their role as setoid fibrations.} 
        \begin{spec}
data EqVar  : ∀ (Γ : Ctx Ξ) {A} → Tm Γ A → Bool → Set where
  ez    : EqVar (Γ ▷ t >eq b) (t [ wkeq ]) b
  es    : EqVar Γ t b → EqVar (Γ ▷ A) (t [ wk ]) b
  eseq  : EqVar Γ t b₁ → EqVar (Γ ▷ u >eq b₂) (t [ wkeq ]) b₁

data DefVar where
  fz  : DefVar (Ξ ▷ Γ ⇒ A if t ≔ u ∣ v) (Γ [ wk𝒲 ]𝒲Ctx) (A [ wk𝒲 ]𝒲Ty)
  fs  : DefVar Ξ Γ A → DefVar  (Ξ ▷ Δ ⇒ B if t ≔ u ∣ v) 
                               (Γ [ wk𝒲 ]𝒲Ctx) (A [ wk𝒲 ]𝒲Ty)
        \end{spec}
  \item |DefVar|s have an associated |lookup𝒮| operation.
        \begin{spec}
record Def Ξ (Γ : Ctx Ξ) (A : Ty Γ) : Set where
  constructor if
  field
    scrut  : Tm Γ 𝔹
    lhs    : Tm (Γ ▷ scrut >eq true)  (A [ wkeq ]Ty)
    rhs    : Tm (Γ ▷ scrut >eq false) (A [ wkeq ]Ty) 

lookup𝒮 : ∀ Ξ {Γ A} → DefVar Ξ Γ A → Def Ξ Γ A
        \end{spec}
  \item ``|call|''s are now explicitly bundled with their list of arguments.
        \begin{spec}
call  : ∀ (f : DefVar Ξ Γ A) (δ : Tms Δ Γ)
      → Tm Δ (A [ δ ]Ty)
        \end{spec}
\end{itemize}

\subsection{Conversion and Coherence}

% TODO: Discuss difference between convertibility and equivalence up to
% coherence.
% TODO (Traditional NbE can be designed such that conversion is preserved
% through all steps. As far as I can tell, this is not really possible in
% \SC NbE, so we need
% an equivalence relation on terms that corresponds to syntactic equality
% of the untyped projections - equality up to coherence).

When presenting NbE for dependent types in \refsec{depnbe}, we were able
to preserve the conversion relation at every step.
This justified us playing quite ``fast and loose'' with details relating 
to coercion/coherence:
using setoids was ultimately just an implementation detail and
we could have achieved the same result using a quotiented syntax instead
\sidecite{altenkirch2017normalisation}.

In \SCDef, the situation gets a bit trickier. I do not know how to deal
with contextual equations other than via term rewriting, but 
rewriting is an inherently very syntactic procedure.

Luckily, setoids give us a framework for working with multiple distinct
equivalence relations. Indexing of the syntax itself must still be up to 
conversion in order
to account for definitional equality, but this does not stop us from
writing functions that e.g. project out raw untyped terms.
I will sometimes refer to equality
\emph{up-to-coherence} merely referring to the smallest congruence
relation including |coh|. Applied to the syntax of type theory,
this aligns exactly with syntactic equality of untyped projections.

For simplicity of the presentation in the report, we still try to avoid
getting too bogged-down in encoding details 
associated with these different equivalence relations,
but it is important to keep in mind that some portions of the below
algorithm (especially those parts which directly refer to
term rewriting concepts) do not respect conversion alone.

\subsection{Normal and Neutral Forms}


We define \SCDef normal forms as usual, assuming some
appropriate definition of neutrals.
Like in \refsec{depnbe}, normal forms form a setoid fibration on
conversion, so the term we index by only needs to be convertible to the
normal form.

\begin{code}
data Nf  : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set 
Ne       : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set

data Nf where
  coe~  : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂
  ne𝔹   : Ne Γ 𝔹 t → Nf Γ 𝔹 t
  neIF  : Ne Γ 𝔹 u → Ne Γ (IF u A B) t → Nf Γ (IF u A B) t
  ƛ_    : Nf (Γ ▷ A) B t → Nf Γ (Π A B) (ƛ t)
  TT    : Nf Γ 𝔹 TT
  FF    : Nf Γ 𝔹 FF
\end{code}

%if False
\begin{code}
\end{code}
%endif 

\SCDef neutrals are a little more tricky. Boolean equations
mean we can no longer define these purely inductively, as modulo
contextual equations, any 𝔹-typed term can in principle be convertible 
to |TT| or |FF| (which are of course non-neutral - |TT| and |FF| do not
block β-reduction).
We start, therefore, by defining
\emph{pre-neutrals} as β-neutral terms where all subterms are fully 
normal/neutral.

\begin{code}
data PreNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set where
  coe~  : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → PreNe Γ₁ A₁ t₁ → PreNe Γ₂ A₂ t₂
  `_    : ∀ i → PreNe Γ A (` i)
  _·_   : Ne Γ (Π A B) t → Nf Γ A u
        → PreNe Γ (B [ < u > ]Ty) (t · u)

  callNe  : Ne Δ 𝔹 (lookup𝒮 Ψ f .scrut [ δ ]) 
          → PreNe Δ (A [ δ ]Ty) (call {A = A} f δ)
\end{code}

%if False
\begin{code}
\end{code}
%endif

We then define the ``true'' neutrals by pairing the pre-neutral term 
with explicit evidence that it is
not convertible to a closed Boolean.

\sideremark{As conversion (|Tm~ Γ~ A~ t₁ t₂|) lies in |Prop|, we normally
would need to ``box'' the proof here. To hide these encoding details, we rely
on cumulativity, which includes |Prop <: Set| subtyping.}

\begin{code}
predNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set
predNe Γ A t = ∀ {Γ′} b Γ~ A~ → ¬ Tm~ {Γ₂ = Γ′} Γ~ A~ t ⌜ b ⌝𝔹

Ne Γ A t = PreNe Γ A t × predNe Γ A t
\end{code}

\begin{remark}[Stability Under Thinnings vs Renamings] \phantom{a}
\labremark{scdefneutstab}

These neutral forms are not stable under arbitrary renamings. For example, 
in the context |Γ = x ∶ 𝔹 , y ∶ 𝔹 , x >eq true|, the variable |y| 
is neutral. However, if we
apply the renaming |y / x|, the context becomes 
\mbox{|Γ [ y / x ] == y ∶ 𝔹 , y >eq true|}, and |y| is now convertible 
to a closed Boolean. We therefore make sure to take presheaves over the
category of thinnings (which does not encounter this problem) when
proving normalisation.
\end{remark}


\begin{remark}[Beyond Booleans] \phantom{a}

This definition relies heavily on the fact that all of our equations
are of the form |t ~ ⌜ b ⌝𝔹|. If equations e.g. between neutral terms
were to be allowed, then these normal forms would no longer be 
unique (up to coherence).

As in \hyperref[sec:finitaryrw]{Section 5.3.2 - Finitary Types}
I think there are at least two possible solutions to here:
\begin{itemize}
  \item We could keep the same definition of neutrals as above, and give
        up on uniqueness of normal forms. Instead, equivalence
        of neutrals can be defined modulo a set of neutral equations.
        Note that rewriting neutral subterms to other neutrals cannot 
        unblock β-reductions 
        (the whole motivation for neutral terms is that they block reduction),
        so NbE still makes progress (it fully decides the β-equality).
        % TODO CITE?
        To actually decide equality of normal forms, we then can use standard
        term rewriting approaches such as ground completion or E-Graphs
        (the equational theory on β-normal forms is, up to coherence, a ground
        TRS).
\sideremark{When I refer to β-equality/β-normality here, I am also
implicitly including
η for Π types. Actually, accounting for η equality in the second
approach is a little subtle: we rely on the fact that the result of η-expanding 
any neutral is never
considered \emph{smaller} than the original. I argue this is a pretty
reasonable expectation (e.g. it follows from monotonicity),
but alternatively, we could
just require that |tᴺᵉ| not be larger than any alternative β-neutral
(|tᴺᵉ′ ∶ βNe Γ A t|) and combine this
with the statement that |t| is also not convertible to a closed 
Boolean given prior.}
  \item Alternatively, we could attempt to fully normalise terms during NbE,
        by integrating ground completion directly.
        Specifically, we can define a term ordering on 
        β-normal/neutral terms such that |TT| and |FF| are minimal, and then
        generalise |predNe| to the non-existence of normal forms (of the same
        term) smaller than the given neutral.

        To avoid getting bogged down in accounting for
        conversion/coherence, we concretely define the term ordering on
        untyped terms.
        \begin{code}
UTm : Set
βNe : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set
βNf : ∀ Γ A → Tm {Ξ = Ξ} Γ A → Set

projβNe : βNe Γ A t → UTm
projβNf : βNf Γ A t → UTm

_>UTm_ : UTm → UTm → Set

predNe′ : ∀ Γ A t → βNe {Ξ = Ξ} Γ A t → Set
predNe′ Γ A t tᴺᵉ 
  = ∀ (tᴺᶠ : βNf Γ A t) → ¬ projβNe tᴺᵉ >UTm projβNf tᴺᶠ
        \end{code}
\end{itemize}

We will stick with |t ~ ⌜ b ⌝𝔹| equations for
simplicity. In either of the above approaches, I suspect the 
extra difficulties will primarily
relate to needing to be careful with exactly which types/relations are setoid
fibrations on either coherence or conversion.
\end{remark}


Note that all the definitions of normal/neutrals forms presented here
are assuming definitionally consistent contexts. In definitionally inconsistent contexts, we can
% TODO: We could probably break this chapter up into more sections, and then
% make this reference more specific.
collapse all terms to |⊤| as in \refsec{simplenormcompl}. 

\subsection{Sound and Complete TRSs}
\labsec{scdeftrs}

Justifying \emph{completion} with a well-founded order 
(also taking reduction into account) 
is hard\remarknote{Recall from \refsec{scboolnormfail} that our trick involving
\emph{spontaneous reduction} \refsec{simplenormcompl}
does not extend to dependent types).}.
Luckily, because stability
under substitution is no longer a requirement, we have a lot more freedom in
how to restrict equations such that completion is not
necessary. For example, we could require that all Boolean
equation LHSs are mutually irreducible (and check this syntactically),
ensuring that our equation set is completed by definition.

% Tying our proof to any particular restriction is undesirable though. Our
% eventual goal is a language that supports as powerful local equality
% reflection is possible. To stay generic then, we introduce a notion of 
% a TRS as a list of equations from neutrals to values, a

We delay the actual details of this syntactic check and
recovering the required semantic properties for 
\refsec{synrestrs}. For now, 
we specify the semantic requirement on completed contexts only: 
either the context should be
definitionally inconsistent, or there must be a completed
TRS, equivalent to the equational context.

Raw TRSs are just lists of paired pre-neutral LHSs and Boolean RHSs.

\begin{code}
data TRS (Γ : Ctx Ψ) : Set where
  •        : TRS Γ
  _▷_>rw_  : TRS Γ → PreNe Γ 𝔹 t → Bool → TRS Γ
\end{code}

%if False
\begin{code}
variable
  Γᵀᴿ : TRS Γ
  tᴾᴺᵉ uᴾᴺᵉ : PreNe Γ A t
  tᴺᵉ       : Ne Γ A t
  tᴺᶠ       : Nf Γ A t
\end{code}
%endif

We then define TRSs to be valid (for a particular context) if rewrites
imply convertibility and vice versa on pre-neutral terms. This is similar
in spirit to
the observational equivalence property of equational contexts in 
\refsec{simplenormcompl}, but instead of between contexts,
we define the equivalence between
the \SCDef context (which induces a declarative notion of conversion)
and a concrete set of rewrites (where the induced notion of
conversion is operational).

\pagebreak
\sideremark{Technically, |RwVar|s here should be defined up 
to coherence-equivalence.
To account for this, we must to index by pre-neutrals of arbitrary type, |A|
(rather than |𝔹|) and then generalise ``|from|'' and
``|to|'' appropriately. 
In ``|from|'' specifically, we need to specify the
coherence equation |CohTy~ _ A 𝔹| to satisfy the indexing of |Tm~|
(either at the declaration, or when applying it). We can either
index |RwVar| directly by the coherence equation or project out the proof
by recursion.}
\begin{code}
data RwVar : TRS Γ → PreNe Γ 𝔹 t → Bool → Set where
  rz : RwVar (Γᵀᴿ ▷ tᴾᴺᵉ >rw b) tᴾᴺᵉ b
  rs : RwVar Γᵀᴿ tᴾᴺᵉ b₁ → RwVar (Γᵀᴿ ▷ uᴾᴺᵉ >rw b₂) tᴾᴺᵉ b₁

record ValidTRS (Γ : Ctx Ξ) : Set where field
  trs   : TRS Γ
  to    : Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹 → ∀ (tᴾᴺᵉ : PreNe Γ 𝔹 t) 
        → RwVar trs tᴾᴺᵉ b
  from  : RwVar {t = t} trs tᴾᴺᵉ b → Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹

def-incon : Ctx Ξ → Prop
def-incon Γ = Tm~ (rfl~ {Γ = Γ}) rfl~ TT FF

data TRS? (Γ : Ctx Ξ) : Set where
  compl  : ValidTRS Γ   → TRS? Γ
  !!     : def-incon Γ  → TRS? Γ
\end{code}

%if False
\begin{code}
open ValidTRS

collapse : def-incon Γ → Ty~ rfl~ A₁ A₂
\end{code}
%endif

\begin{remark}[Alternative Definition of TRS ``|to|''] \phantom{a}
\labremark{alttrscompl}

Note that the ``|to|'' condition above is equivalent to

\begin{code}
to′  : ∀ (Γᵀᴿ : TRS Γ) → EqVar Γ t b 
     → ∀ (tᴾᴺᵉ : PreNe Γ 𝔹 t) → RwVar Γᵀᴿ tᴾᴺᵉ b
\end{code}

given the following lemma, which should be provable by introducing 
reduction and algorithmic conversion, showing the equivalence with
declarative conversion (via confluence of reduction) and then taking
advantage of how the only possible reduction which can apply to
a pre-neutral term is a rewrite targetting the whole thing (recall that 
all subterms of pre-neutrals
are fully neutral/normal).

\begin{code}
inv-lemma : PreNe Γ A t → Tm~ Γ~ A~ t ⌜ b ⌝𝔹 → EqVar Γ (coe~ Γ~ A~ t) b
\end{code}

We rely on this lemma in \refsec{synrestrs}, however,
this is a lot of work for a small and quite technical result, so we will
not prove this in detail. Finding an easier way to prove this (or avoid
relying on it entirely) could be interesting future work.
\end{remark}

\subsection{Normalisation by Evaluation}

We now extend normalisation by evaluation for dependent types (as
initially presented in \refsec{depnbe} to \SCDef.

As before, the core of the normalisation argument will hinge on 
neutral/normal forms 
being presheaves on a category of thinnings\remarknote{We will
also require stability of completion evidence w.r.t. thinning,
which follows from applying the thinning
pointwise to the underlying |TRS|, and then taking advantage of how
thinnings can be inverted.}. To account for local equational assumptions
in contexts, we extend thinnings with lifting
over contexts extended by equations
(i.e. so it is still possible to construct identity thinnings) but 
critically do not include equation-weakenings
(\mbox{|Thin (Δ ▷ t >eq b) Γ (δ ⨾ wkeq)|}), which destabilise neutral
terms (and destroy completion evidence).

\begin{code}
data Thin {Ξ} : ∀ Δ Γ → Tms {Ξ = Ξ} Δ Γ → Set where
  ε          : Thin • • ε
  _^ᵀʰ_      : Thin Δ Γ δ → ∀ A 
             → Thin (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A) (δ ^ A)
  _^ᵀʰ_>eq_  : Thin Δ Γ δ → ∀ t b
             → Thin (Δ ▷ t [ δ ] >eq b) (Γ ▷ t >eq b) (δ ^ t >eq b)
  _⁺ᵀʰ_      : Thin Δ Γ δ 
             → ∀ A → Thin (Δ ▷ A) Γ (δ ⨾ wk)
\end{code}

%if False
\begin{code}
wkᵀʰ : Thin (Γ ▷ A) Γ wk

_[_]ᶜ   : ValidTRS Γ → Thin Δ Γ δ → ValidTRS Δ
_[_]𝒲ᶜ  : ValidTRS Γ → ∀ (φ : Wk Φ Ψ) → ValidTRS (Γ [ φ ]𝒲Ctx)

_[_]?⁺    : TRS? Γ → ∀ (φ : Wk Φ Ψ) → TRS? (Γ [ φ ]𝒲Ctx)

coeNe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Ne Γ₁ A₁ t₁ → Ne Γ₂ A₂ t₂
coeNf~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂
\end{code}
%endif

When defining
environments and values, we require a valid TRS associated with
the target context (recall that normalisation in definitionally
inconsistent contexts is trivial, so we focus only on the definitionally
consistent case here). Throughout the normalisation algorithm,
we will never add new equations to the target context, so we can
preserve the |ValidTRS| the whole way through.
%  A neat consequence of \SCDef normalisation
%  never needing to recurse into the body of definitions until the calls
%  themselves reduce is that we only need a single |ValidTRS| for the context we
%  evaluate into (as opposed to e.g. needing to have |ValidTRS|s

\begin{code}
Env    : ∀ Ξ Δ Γ → ValidTRS Δ → Tms {Ξ = Ξ} Δ Γ → Set
Val    : ∀ Γ A Δ Δᶜ δ
       → Env Ξ Δ Γ Δᶜ δ → Tm Δ (A [ δ ]Ty) → Set
eval   : ∀ Δᶜ (t : Tm Γ A) (ρ : Env Ξ Δ Γ Δᶜ δ) 
       → Val Γ A Δ Δᶜ δ ρ (t [ δ ])
eval*  : ∀ Θᶜ δ (ρ : Env Ξ Θ Δ Θᶜ σ) → Env Ξ Θ Γ Θᶜ (δ ⨾ σ)
\end{code}

Perhaps surprisingly, and unlike when constructing the standard model, 
we do not associate an environment with the signature. We can get away
with simply recursively evaluating definitions every time we hit
a |call|.
% \remarknote{This is perhaps not the most \emph{efficient} evaluation
% strategy. For example, if the same definition is called multiple times, 
% we cannot share any work. On the other hand, our approach to elaboration
% will generate a single definition for every
% case split, and call each of these
% definitions exactly once (\refsec{scdefsplitelab}), so this does not
% really matter in our use-case.}.

%if False
\begin{code}
variable
  Γᶜ Δᶜ Θᶜ : ValidTRS Γ
  ρ : Env Ξ Δ Γ Δᶜ δ

idℰ : Env Ξ Γ Γ Γᶜ id

postulate
  coe𝒱 : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} (A~ : Ty~ rfl~ A₁ A₂)
       → Tm~ Δ~ (A~ [ rfl~ ]Ty~) t₁ t₂
       → Val Γ A₁ Δ Δᶜ δ ρ t₁ → Val Γ A₂ Δ Δᶜ δ ρ t₂
  
lookupℰ : ∀ (i : Var Γ A) (ρ : Env Ξ Δ Γ Δᶜ δ) → Val Γ A Δ Δᶜ δ ρ (lookup i δ)

idᵀʰ : Thin Γ Γ id
_⨾ᵀʰ_  : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)

_[_]ℰ  : Env Ξ Δ Γ Δᶜ δ → ∀ (σᵀʰ : Thin Θ Δ σ) 
       → Env Ξ Θ Γ (Δᶜ [ σᵀʰ ]ᶜ) (δ ⨾ σ)

≡~ : t₁ ≡ t₂ → Tm~ rfl~ rfl~ t₁ t₂
≡~ refl = rfl~
\end{code}
%endif

We define a specialised version of unquoting on pre-neutrals, |uvalpre|. 
The intuition here is that |uvalpre| first syntactically compares the given
neutral with all LHSs of the TRS to see if it can be reduced, and then
if it is still stuck, delegates to |uval|, which unquotes as usual.

\begin{code}
uvalpre  : ∀ A {t} → PreNe Δ (A [ δ ]Ty) t → Val Γ A Δ Δᶜ δ ρ t
uval     : ∀ A {t} → Ne Δ (A [ δ ]Ty) t → Val Γ A Δ Δᶜ δ ρ t
qval     : ∀ A {t} → Val Γ A Δ Δᶜ δ ρ t → Nf Δ (A [ δ ]Ty) t
\end{code}

%if False
\begin{code}
variable
  δᵀʰ σᵀʰ : Thin Δ Γ δ

postulate
  [id]ᶜ : Γᶜ [ idᵀʰ ]ᶜ ≡ Γᶜ
  [][]ᶜ : Γᶜ [ δᵀʰ ]ᶜ [ σᵀʰ ]ᶜ ≡ Γᶜ [ δᵀʰ ⨾ᵀʰ σᵀʰ ]ᶜ
{-# REWRITE [id]ᶜ [][]ᶜ #-}

variable
  Τ : Ctx Ξ

postulate
  [id]ℰ  : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} → ρ [ idᵀʰ ]ℰ ≡ ρ
  [][]ℰ  : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} 
             {σᵀʰ : Thin Θ Δ σ} {γᵀʰ : Thin Τ Θ γ}
         → ρ [ σᵀʰ ]ℰ [ γᵀʰ ]ℰ ≡ ρ [ σᵀʰ ⨾ᵀʰ γᵀʰ ]ℰ
{-# REWRITE [id]ℰ #-}
{-# REWRITE [][]ℰ #-}
\end{code}
%endif

Like in \refsec{depnbe}, we will cheat a bit, and assume functor laws for
thinning environments hold definitionally (to avoid excessive transport
clutter). Actually, for these laws to typecheck, we now also need to
assume functor laws for thinning completed TRSs.

\begin{spec}
Γᶜ [ idᵀʰ ]ᶜ == Γᶜ
Γᶜ [ δᵀʰ ]ᶜ [ σᵀʰ ]ᶜ == Γᶜ [ δᵀʰ ⨾ᵀʰ σᵀʰ ]ᶜ
ρ [ idᵀʰ ]ℰ == ρ
ρ [ σᵀʰ ]ℰ [ γᵀʰ ]ℰ == ρ [ σᵀʰ ⨾ᵀʰ γᵀʰ ]ℰ
\end{spec}

The definition of environments now needs to account for local equations. 
We take inspiration from the standard model constructions for \SCBool and
\SCDef, and require environments to hold evidence of convertibility
of the LHS and RHS values.

\begin{spec}
⌜_⌝𝔹Nf : ∀ b → Nf Γ 𝔹 ⌜ b ⌝𝔹
⌜ true   ⌝𝔹Nf = TT
⌜ false  ⌝𝔹Nf = FF

Env Ξ Δ (Γ ▷ t >eq b) Δᶜ δ
  =  Σ⟨ ρ ∶ Env Ξ Δ Γ Δᶜ (π₁eq δ) ⟩× 
     Nf~ rfl~ rfl~ (π₂eq δ) (eval Δᶜ t ρ) ⌜ b ⌝𝔹Nf
\end{spec}

%if False
\begin{code}

>eqEnv  : ∀ (t : Tm Γ 𝔹) (b : Bool) δ
        → Env Ξ Δ Γ Δᶜ (π₁eq {t = t} {b = b} δ) → Set

Env Ξ Δ •       Δᶜ δ = ⊤
Env Ξ Δ (Γ ▷ A) Δᶜ δ 
  = Σ⟨ ρ ∶ Env Ξ Δ Γ Δᶜ (π₁ δ) ⟩× Val Γ A Δ Δᶜ (π₁ δ) ρ (π₂ δ)
Env Ξ Δ (Γ ▷ t >eq b) Δᶜ δ
  = Σ⟨ ρ ∶ Env Ξ Δ Γ Δᶜ (π₁eq δ) ⟩× >eqEnv t b δ ρ

postulate
  id-pres-rw    : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} 
                → eval* {σ = δ} Δᶜ id ρ ≡ ρ
  wk-pres-rw    : ∀ {ρ : Env Ξ Δ (Γ ▷ A) Δᶜ δ} 
                → eval* Δᶜ wk ρ ≡ ρ .fst

  wkeq-pres-rw  : ∀ {ρ : Env Ξ Δ (Γ ▷ t >eq b) Δᶜ δ} 
                → eval* {σ = δ} Δᶜ (wkeq {t = t} {b = b}) ρ ≡ ρ .fst
  []Ty-pres-rw  : ∀ {ρ : Env Ξ Θ Δ Θᶜ σ}
                → Val Δ (A [ δ ]Ty) Θ Θᶜ σ ρ t 
                ≡ Val Γ A Θ Θᶜ (δ ⨾ σ) (eval* {σ = σ} Θᶜ δ ρ) t

{-# REWRITE id-pres-rw #-}
{-# REWRITE wk-pres-rw #-}
{-# REWRITE wkeq-pres-rw #-}
{-# REWRITE []Ty-pres-rw #-}

Val Γ (coe~ Γ~ A) Δ Δᶜ δ ρ t 
  = {!!}
Val Γ 𝔹          Δ Δᶜ δ ρ t = Nf Δ 𝔹 t
Val Γ (IF b A B) Δ Δᶜ δ ρ t = {!if-Val Γ A B Δ δ ρ t (eval b ρ)!}
Val Γ (Π A B)    Δ Δᶜ δ ρ t 
  = ∀ {Θ γ} (γᵀʰ : Thin Θ Δ γ) {u}
      (uⱽ : Val Γ A Θ (Δᶜ [ γᵀʰ ]ᶜ) (δ ⨾ γ) (_[_]ℰ {Γ = Γ} ρ γᵀʰ) u)
  → Val (Γ ▷ A) B Θ (Δᶜ [ γᵀʰ ]ᶜ) ((δ ⨾ γ) , u) 
        ((_[_]ℰ {Γ = Γ} ρ γᵀʰ) Σ, uⱽ) ((t [ γ ]) · u)

⌜_⌝𝔹Nf : ∀ b → Nf Γ 𝔹 ⌜ b ⌝𝔹
⌜ true   ⌝𝔹Nf = TT
⌜ false  ⌝𝔹Nf = FF

data Nf~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂ → Prop where
  rfl~ : Nf~ rfl~ rfl~ rfl~ tᴺᶠ tᴺᶠ

>eqEnv t b δ ρ = Nf~ rfl~ rfl~ (π₂eq δ) (eval _ t ρ) ⌜ b ⌝𝔹Nf

eval* Δᶜ (coe~ Δ~ Γ~ δ)  ρ = {!!}
eval* Δᶜ ε               ρ = tt
eval* Δᶜ (δ , t)         ρ = eval* Δᶜ δ ρ Σ, eval Δᶜ t ρ
eval* Δᶜ (δ ,eq t~)      ρ = eval* Δᶜ δ ρ Σ, {!!}
\end{code}
%endif

Values are defined entirely as usual. Evaluation of substitutions, |eval*|,
now needs to produce the proof of normal-form equality. This is achievable
via mutually proving soundness of evaluation.

For evaluation, we focus just on the new case for |call|s. We split on
the evaluated scrutinee in a top-level helper, |eval-call|.

\begin{code}
eval-call  : ∀  {f : DefVar Ξ Γ A} (ρ : Env Ξ Δ Γ Δᶜ δ)
                (tⱽ : Nf Δ 𝔹 t) 
                (t~ : Tm~ rfl~ rfl~ t (lookup𝒮 Ξ f .scrut [ δ ]))
           →  (∀ t~′ → Nf~ rfl~ rfl~ (t~ ∙~ t~′) tⱽ TT 
              → Val Γ A Δ Δᶜ δ ρ (lookup𝒮 Ξ f .lhs [ δ ,eq t~′ ]))
           →  (∀ t~′ → Nf~ rfl~ rfl~ (t~ ∙~ t~′) tⱽ FF 
              → Val Γ A Δ Δᶜ δ ρ (lookup𝒮 Ξ f .rhs [ δ ,eq t~′ ]))
           → Val Γ A Δ Δᶜ δ ρ (call f δ)
eval-call {f = f} ρ TT t~ uⱽ vⱽ 
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-TT {f = f} (sym~ t~))) uⱽ′
  where uⱽ′ = uⱽ (sym~ t~) rfl~
eval-call {f = f} ρ FF t~ uⱽ vⱽ
  = coe𝒱 {ρ = ρ} rfl~ (sym~ (call-FF {f = f} (sym~ t~))) vⱽ′
  where vⱽ′ = vⱽ (sym~ t~) rfl~
eval-call {f = f} ρ (ne𝔹 tᴺᵉ) t~ uⱽ vⱽ 
  = uvalpre _ (callNe {f = f} (coeNe~ rfl~ rfl~ t~ tᴺᵉ))
\end{code}

Unlike evaluation of dependent ``|if|'' (|eval-if| in \refsec{depnbe}), we
do not rely on quoting here. When producing stuck |call|s,
we have no reason to the normalise the branches.

%if False
\begin{code}
-- Terminating pragma is avoided in the actual mechanisation by playing
-- some tricks with |with|-abstraction. We assert termination here to
-- keep the presentation simpler.
{-# TERMINATING #-}

eval Δᶜ (coe~ _ _ _) ρ = {!!}
eval Δᶜ (` i)    ρ = lookupℰ i ρ
eval Δᶜ (t · u)  ρ = eval Δᶜ t ρ idᵀʰ (eval Δᶜ u ρ)
eval Δᶜ TT       ρ = TT
eval Δᶜ FF       ρ = FF
eval {δ = δ} Δᶜ (ƛ t) ρ {γ = γ} γᵀʰ {u = u} uⱽ 
  = coe𝒱  rfl~ (sym~ (Πβ {t = t [ (_ ⨾ _) ^ _ ]} {u = u}))
          (eval  {δ = (_ ⨾ _) , u} (Δᶜ [ γᵀʰ ]ᶜ) t 
                 ((_[_]ℰ {δ = δ} ρ γᵀʰ) Σ, uⱽ))
\end{code}
%endif

To actually make use of |eval-call|, we need to evaluate the scrutinee, and
the LHS and RHS branch under the appropriate convertibility
assumptions.

\sideremark{We can ensure this case of evaluation stays structurally
recursive by ``Fording''. For example, |lookup𝒮 _ f .scrut| is not
obviously structurally smaller than |call f δ|, but if we ``Ford''
by adding an extra term parameter to |call|, |t ∶ Tm Γ 𝔹| and
the propositional equation |t ≡ lookup𝒮 _ f .scrut|, the induction
here becomes structurally well-founded.}

\begin{code}
eval {δ = σ} Δᶜ (call f δ) ρ 
  = eval-call {f = f} δⱽ tⱽ (≡~ refl) uⱽ vⱽ
  where  δⱽ  = eval* Δᶜ δ ρ
         tⱽ  = eval Δᶜ (lookup𝒮 _ f .scrut) δⱽ 
         uⱽ  = λ t~ tᴺᶠ~ →  eval  {δ = (δ ⨾ σ) ,eq t~} Δᶜ (lookup𝒮 _ f .lhs) 
                                  (δⱽ Σ, tᴺᶠ~)
         vⱽ  = λ t~ tᴺᶠ~ →  eval  {δ = (δ ⨾ σ) ,eq t~} Δᶜ (lookup𝒮 _ f .rhs) 
                                  (δⱽ Σ, tᴺᶠ~)
\end{code}

We should make sure to check soundness. |call-TT| and |call-FF| are preserved
up-to-coherence just by computation of |eval|. |π₂eq| instead requires us to
prove

\begin{spec}
Nf~  rfl~ rfl~ (π₂eq δ [ rfl~ ]~)  
     (eval Θᶜ (t [ π₁eq δ ]) ρ) (eval Θᶜ ⌜ b ⌝𝔹 ρ)
\end{spec}

This is why we had to embed equations into environments.
After splitting on the Boolean, the RHS reduces to |TT|/|FF|, and if we project
our the convertibility evidence the environment, specifically 
|eval* Θᶜ δ ρ| (focusing
on the |TT| case WLOG), we obtain

\begin{spec}
Tm~ rfl~ rfl~ (eval Θᶜ t (eval* Θᶜ δ ρ .fst)) TT
\end{spec}

So it remains to prove equality of |eval Θᶜ (t [ π₁eq δ ]) ρ|
and |eval Θᶜ t (eval* Θᶜ δ ρ .fst)|, which is just preservation of |π₁eq|.

%if False
\begin{code}
eval-π₂eq  : ∀ (δ : Tms Δ (Γ ▷ t >eq b)) (ρ : Env Ξ Θ Δ Θᶜ σ)
           → Nf~ rfl~ rfl~ (π₂eq δ [ rfl~ ]~)  
                 (eval Θᶜ (t [ π₁eq δ ]) ρ) (eval Θᶜ ⌜ b ⌝𝔹 ρ)
eval-π₂eq {b = true}   δ ρ = {!eval* _ δ ρ .snd!}
eval-π₂eq {b = false}  δ ρ = {!eval* _ δ ρ .snd!}
\end{code}
%endif

The core unquoting (|uval|) and quoting (|qval|) operations stay
mostly unchanged from
ordinary NbE for dependent types\remarknote{I say ``mostly'' because
technically we do need to call |uvalpre| rather than |uval| in a couple of
places to build new stuck neutrals, but other than that, 
the definitions are identical.}, but we do of course need to 
implement |uvalpre|.

We first define a procedure for checking if any TRS rewrites possibly
apply to a given pre-neutral term.

\sideremark{Note that as we are working with plain |TRS|s here, we need
to work with terms up to coherence rather than up to conversion.
We can prove that overall conversion is preserved using the correctness
criteria associated with |ValidTRS|s after we are done.}

\begin{code}
data CheckRwResult (Γᵀᴿ : TRS Γ) : PreNe Γ A t → Set where
  rw   : RwVar Γᵀᴿ (coe~ rfl~ A~ coh tᴾᴺᵉ) b → CheckRwResult Γᵀᴿ tᴾᴺᵉ
  stk  : (∀ A~ b → ¬ RwVar Γᵀᴿ (coe~ rfl~ A~ coh tᴾᴺᵉ) b) 
       → CheckRwResult Γᵀᴿ tᴾᴺᵉ

checkrw  : ∀ (Γᵀᴿ : TRS Γ) (tᴾᴺᵉ : PreNe Γ A t) 
         → CheckRwResult Γᵀᴿ tᴾᴺᵉ
\end{code}

%if False
\begin{code}
⌜⌝𝔹~ : Tm~ Γ~ 𝔹 ⌜ b ⌝𝔹 ⌜ b ⌝𝔹
⌜⌝𝔹~ {b = true}   = TT _
⌜⌝𝔹~ {b = false}  = FF _


  -- TODO: Justify this... somehow
postulate
  coe𝒱′ : ∀ {ρ : Env Ξ Δ Γ Δᶜ δ} (A~ : Ty~ rfl~ A₁ (A₂ [ δ ]Ty))
        → Tm~ Δ~ A~ t₁ t₂
        → Val Δ A₁ Δ Δᶜ id idℰ t₁ → Val Γ A₂ Δ Δᶜ δ ρ t₂

\end{code}
%endif

We then implement |uvalpre| by splitting on the result of |checkrw|,
and either returning the closed Boolean, or the stuck neutral, depending
on the result. We need the ``|from|'' and ``|to|'' properties of our TRS here
to translate between evidence about the existence or lack of rewrites
and convertibility.

\begin{code}
uvalpre {Δᶜ = Δᶜ} A tᴾᴺᵉ with checkrw (Δᶜ .trs) tᴾᴺᵉ 
... | rw {A~ = A~} {b = b} r  
  = coe𝒱′ (sym~ A~) (sym~ (Δᶜ .from r) ∙~ sym~ coh) ⌜ b ⌝𝔹Nf
... | stk ¬r        
  = uval A  (tᴾᴺᵉ Σ, λ b Γ~ A~ t~ → 
                     ¬r  (A~ ∙~ 𝔹 {Γ~ = sym~ Γ~}) b 
                         (Δᶜ .to  (sym~ coh ∙~ t~ ∙~ ⌜⌝𝔹~ {Γ~ = sym~ Γ~}) 
                                  (coe~ _ _ _ tᴾᴺᵉ)))
\end{code}

Soundness of |uvalpre| also follows from ``|from|'' and ``|to|'', so we are
done!

\begin{code}
nbe : ValidTRS Γ → ∀ t → Nf Γ A t
nbe Γᶜ t = qval {δ = id} _ (eval Γᶜ t idℰ)
\end{code}

Of course, we can only call into |nbe| if we have a |ValidTRS|, so we
move on to the topic of constructing these now.

\pagebreak
\section{Elaboration}
\labsec{elabscdef}

We first consider the task of generating |ValidTRS|s from a set of
equational assumptions in a context, and then move on to presenting
an elaboration algorithm which can turn \SC into \SCDef calls.

\subsection{Syntactic Restrictions for Generating TRSs}
\labsec{synrestrs}

As mentioned in \refsec{scdeftrs},
justifying completion is hard (because finding a well-founded order is hard). 
Luckily, completion is also no longer necessary. In \SCDef, we can
place essentially arbitrary restrictions on equations, without endangering
subject reduction (stability under substitutions is no longer necessary).

One such restriction, for example, could be to require that the LHS of every
reflected equation is syntactically a variable, 
essentially recovering dependent
pattern matching (\refsec{deppatmatch}). Checking equality of
variables is easy, so we can iterate through the set of equations |i >eq b|
and in the case of overlaps, either remove the offending equation
(if it is redundant - i.e. the RHSs are equal Booleans) or report a 
definitional inconsistency (if it is
definitionally inconsistent - i.e. the RHSs are not equal).
Of course, the resulting theory 
would not be super exciting, given dependent pattern matching that is
restricted in this way is standard (and the limitations therein ultimately
motivated this entire project).

A more interesting strategy would be iterate over the set of equations,
normalising each LHS, |t ∶ Tm Γ 𝔹|, w.r.t. the prior equation set,
building a |ValidTRS| as we 
go. Before
moving on to the next equation, we inspect the 
reduced LHS, |t|, and:
\begin{itemize}
  \item If |t| is a closed Boolean, we compare it to the RHS and either
        remove the redundant equation or immediately report the definitional
        inconsistency.
  \item If |t| is a neutral term, we check that it does not occur as a
        subterm of any of the prior neutral LHSs. If it does (the new
        rewrite \emph{destabilises} the TRS so-far) then we can just report
        an error and ask the programmer to rewrite their program (doing 
        a better job here really does require completion).
\end{itemize}

To justify this approach is sensible, we need to actually derive the
``|from|'' and ``|to|'' conditions associated with
the |TRS| we construct. Attempting these proofs formally in Agda gets
extremely painful, so we will give just the main ideas:
\begin{itemize}
\item[(A)] We say a neutral \emph{destabilises} a TRS if it occurs as a subterm 
      of (or equals) any of the LHSs of that TRS.
\item[(B)] Given a |ValidTRS| for a context |Γ| and a proof that a particular
      neutral \mbox{|tᴺᵉ ∶ Ne Γ 𝔹 t|} does not destabilise the underlying TRS,
      and a proof that |tᴺᵉ| does not occur as a subterm of (or equals) 
      \mbox{|uᴺᵉ ∶ Ne Γ 𝔹 u|}, we can obtain an\linebreak
      \mbox{|Ne (Γ ▷ t >eq b) 𝔹 (u [ wkeq ])|}. 
\item[(C)] Given |tᴺᵉ| cannot occur as a subterm of any of |tᴺᵉ|'s direct
      subterms, we can also obtain 
      \mbox{|PreNe (Γ ▷ >eq b) 𝔹 (t [ wkeq ])|}.
\item[(D)] (B) and (C) are sufficient to construct the |TRS (Γ ▷ t >eq b)|,
      including a rewrite corresponding to the new equation.
\item[(E)] ``|from|'' for this new TRS can be proven by cases. If the |RwVar|
      is |rz| (i.e. the rewrite makes use of the last rewrite in the TRS), 
      then |eq ez| proves the required equivalence (the last rewrite
      in the TRS maps exactly from the \linebreak 
      \mbox{|PreNe (Γ ▷ >eq b) 𝔹 (t [ wkeq ])|}
      to |b|).
\item[(F)] If the |RwVar| instead is of the form |rs r|, then we know
      the LHS is some neutral that was already present in the TRS, so
      we can reuse the existing evidence of |from|.
\item[(H)] Finally, to prove ``|to|'', we assume some way of getting our hands
      on a concrete |EqVar| corresponding to the convertibility evidence 
      (recall that we should be able obtain this, albeit painfully,
      via introducing reduction \refremark{alttrscompl}).
      We then perform a similar case split: |ez| maps to |rz| and |es e|
      can be dealt with using the prior ``|to|'' result.
\end{itemize}

I leave a full Agda mechanisation of this proof for future work. Most of
the pain arises from parts (F) and (H), where we need to invert the
the weakening of neutrals to account for the new equation.


%if False
\begin{code}
variable
  uᴺᵉ : Ne Γ A t
\end{code}

\begin{code}
¬destabilises  : TRS Γ → Ne Γ A t → Set
extTR          : ∀ (Γᵀᴿ : TRS Γ) (tᴺᵉ : Ne Γ 𝔹 t) → ¬destabilises Γᵀᴿ tᴺᵉ
               → TRS (Γ ▷ t >eq b)
extPreNe       : ∀ (tᴺᵉ : Ne Γ 𝔹 t) → PreNe (Γ ▷ t >eq b) 𝔹 (t [ wkeq ])
extInvRwVar    : ∀ {p : ¬destabilises Γᵀᴿ tᴺᵉ}
               → RwVar (extTR Γᵀᴿ tᴺᵉ p) uᴾᴺᵉ b 
               → Σ⟨ uᴾᴺᵉ′ ∶ PreNe Γ 𝔹 u ⟩× RwVar Γᵀᴿ uᴾᴺᵉ′ b

buildTRS  : ∀ (Γᶜ : ValidTRS Γ) (tᴺᵉ : Ne Γ 𝔹 t) 
     → ¬destabilises (Γᶜ .trs) tᴺᵉ
     → ValidTRS (Γ ▷ t >eq b)
buildTRS {b = b} Γᶜ tᴺᵉ p .trs      
  = extTR (Γᶜ .trs) tᴺᵉ p ▷ extPreNe tᴺᵉ >rw b
buildTRS Γᶜ (tᴾᴺᵉ Σ, ¬𝔹) p .from rz      = eq ez
buildTRS Γᶜ (tᴾᴺᵉ Σ, ¬𝔹) p .from (rs r)  = {!!}
buildTRS Γᶜ (tᴾᴺᵉ Σ, ¬𝔹) p .to u~ uᴾᴺᵉ with inv-lemma uᴾᴺᵉ u~
... | e = {!Γᶜ .to _ _!}
\end{code}
%endif

\subsection{Elaborating Case Splits}
\labsec{scdefsplitelab}

We now quickly outline how to elaborate from an untyped surface language
that appears to feature local \SC, to \SCDef. Concretely, we will work
with an untyped syntax resembling \SCBool, and write the algorithm
in bidirectional style (\sidecite{dunfield2022bidir}), 
with a mutually recursive |check| and |infer| (as in
\sidecite{coquand1996algorithm}, and also my Haskell \SCBool typechecker
\refsec{typecheckingsc}).


To account for local case splits being turned into new top level definitions,
we consistently return a signature weakening along with elaborated
\SCDef term. To be able to normalise types and check conversion, we also
require the existence of a |ValidTRS| associated with the given context.

%if False
\begin{code}
data PreTm : Set where
  ƛ_   : PreTm → PreTm
  _·_  : PreTm → PreTm → PreTm
  if   : PreTm → PreTm → PreTm → PreTm
\end{code}
%endif

\sideremark{We also assume the existence of a definition of \emph{normal types}
(|NfTy|) here. The only difference between these are ordinary \SCDef types
(with strictified substitution) is that large |IF| must always be blocked on a
neutral term.}

\begin{code}
data NfTy : ∀ Γ → Ty {Ξ = Ξ} Γ → Set

record InfTm (Γ : Ctx Ξ) : Set where
  constructor inf
  pattern
  field
    {infSig}  : Sig
    infWk     : Wk infSig Ξ
    infTy     : Ty (Γ [ infWk ]𝒲Ctx)
    infTyᴺᶠ   : NfTy (Γ [ infWk ]𝒲Ctx) infTy
    infTm     : Tm (Γ [ infWk ]𝒲Ctx) infTy

record ChkTm (Γ : Ctx Ξ) (A : Ty Γ) : Set where
  constructor chk
  pattern
  field
    {chkSig}  : Sig
    chkWk     : Wk chkSig Ξ
    chkTm     : Tm (Γ [ chkWk ]𝒲Ctx) (A [ chkWk ]𝒲Ty)

check  : ValidTRS Γ → NfTy Γ A → PreTm → Maybe (ChkTm Γ A)
infer  : ValidTRS Γ → PreTm → Maybe (InfTm Γ)
\end{code}

%if False
\begin{code}
data NfTy where
  Π : NfTy Γ A → NfTy (Γ ▷ A) B → NfTy Γ (Π A B)
  𝔹 : NfTy Γ 𝔹

normTy : ValidTRS Γ → ∀ A → NfTy Γ A
convTy : ValidTRS Γ → ∀ A₁ A₂ → Maybe (Σ⟨ Γ~ ∶ Ctx~ Γ₁ Γ₂ ⟩× Ty~ Γ~ A₁ A₂)
complete : ∀ (Γ : Ctx Ξ) → Maybe (TRS? Γ)
\end{code}
%endif

%if False
\begin{code}
open import Data.Maybe using (_>>=_)

check? : TRS? Γ → ∀ (A : Ty Γ) → PreTm → Maybe (ChkTm Γ A)
\end{code}
%endif

Because our input is untyped, |check| and |infer| can fail
(if the term is not typeable with the given type, or the type of the term
is not inferrable, respectively). We use |do|-notation \sidecite{agda2024sugar}
to avoid excessive boilerplate matching on the results of recursive calls
(elaboration should fail if any recursive call fails).

\sideremark{Elaborated terms being parameterised by a signature weakening,
and needing to compose these for every recursive call, also feels quite
monadic in nature (though the relevant category is no longer |Set|). 
It would perhaps be interesting for future work to explore
how to eliminate this boilerplate.}

|check| and |infer| for ordinary lambda calculus constructs (application,
abstraction, etc.) is relatively standard. We just need to make sure to 
account for new top-level definitions generated during elaboration of
subterms by composing the returned signature weakenings.

(Un-annotated) λ-abstractions are not inferrable
\begin{code} 
infer Γᶜ (ƛ t)    = nothing
\end{code}


However, we can infer applications by first inferring the LHS, ensuring that 
the synthesised
type of the LHS is headed with |Π|, and checking
also that the argument has the appropriate type
\sideremark{Technically we should also account for the case where the 
synthesised type of |t| is headed with a coercion here.}
\begin{code} 
infer Γᶜ (t · u)  = do
  inf φ₁ (Π A B) (Π Aᴺᶠ Bᴺᶠ) t′ ← infer Γᶜ t
    where _ → nothing
  let Γᶜ′    = Γᶜ [ φ₁ ]𝒲ᶜ
  chk φ₂ u′  ← check Γᶜ′ Aᴺᶠ u
  just (inf  (φ₁ ⨾𝒲 φ₂) 
             _
             (normTy (Γᶜ′ [ φ₂ ]𝒲ᶜ) ((B [ φ₂ ]𝒲Ty) [ < u′ > ]Ty))
             ((t′ [ φ₂ ]𝒲) · u′))
\end{code}

We can also check (un-annotated) λ-abstractions by checking the body has 
the expected type
(in the context extended by the domain)
\begin{code} 
check Γᶜ (Π Aᴺᶠ Bᴺᶠ)  (ƛ t) = do
  chk φ t′ ← check (Γᶜ [ wkᵀʰ ]ᶜ) Bᴺᶠ t
  just (chk φ (ƛ t′))
\end{code}

Of course, λ-abstractions are only typeable at Π-types
\begin{code} 
check Γᶜ _            (ƛ t) = nothing
\end{code}

We can check applications by first inferring a type, and then checking it
matches the expected one.
Actually, all inferrable terms can be checked using this approach.
\begin{code} 
check {A = A} Γᶜ Aᴺᶠ  (t · u) = do
  inf φ A′ _ tu′  ← infer Γᶜ (t · u)
  Γ~ Σ, A~        ← convTy Γᶜ A′ (A [ φ ]𝒲Ty)
  just (chk φ (coe~ Γ~ A~ tu′))
\end{code}

The interesting case here is really elaboration of \SIF.
We first recursively check the subterms, then construct
a new definition using these, and finally return a |call|
expression which simply calls the definition.

\sideremark{Note that as we would expect for \SIF, we do not need 
a motive! Instead the
LHS and RHS terms are just checked at the same type of the overall ``|if|''
expression, with dependent elimination coming from the new equations added to
the context.}

\begin{code}
check {A = A} Γᶜ Aᴺᶠ (if t u v) = do
  chk φ₁ t′  ← check Γᶜ 𝔹 t
  Γttᶜ       ← complete ((_ [ φ₁ ]𝒲Ctx) ▷ t′ >eq true)
  Γffᶜ       ← complete ((_ [ φ₁ ]𝒲Ctx) ▷ t′ >eq false)
  chk φ₂ u′  ← check? Γttᶜ (A [ φ₁ ]𝒲Ty [ wkeq ]Ty) u
  chk φ₃ v′  ← check? (Γffᶜ [ φ₂ ]?⁺) (A [ φ₁ ⨾𝒲 φ₂ ]𝒲Ty [ wkeq ]Ty) v
  let φ₁₂₃   = φ₁ ⨾𝒲 (φ₂ ⨾𝒲 φ₃)
  let Ξ′     = _  ▷   _ ⇒ (A [ φ₁₂₃ ]𝒲Ty) 
                  if  (t′ [ φ₂ ]𝒲 [ φ₃ ]𝒲) ≔ u′ [ φ₃ ]𝒲 ∣ v′
  just (chk (φ₁₂₃ ⨾𝒲 wk𝒲) (call {Ξ = Ξ′} fz id))
\end{code}

We rely on a few helpers here. |complete| is a partial implementation of
completion (capable of either returning a |ValidTRS|, evidence of a
definitional inconsistency, or failing). We described some possible
implementations of this in \refsec{synrestrs}.

We also need a slightly generalised version of |check|, to account for
implementations of |complete| that sometimes return 
evidence of definitional inconsistency.

\begin{spec}
check? : TRS? Γ → Ty Γ A → PreTm → Maybe (ChkTm Γ A)
\end{spec}

In a definitionally inconsistent context, all types and terms are convertible,
so we can arbitrarily elaborate everything to |TT| (the inhabitant of the
unit type is perhaps more appropriate, but any term will ultimately do).

\begin{code}
check? (compl Γᶜ)  A t = check Γᶜ (normTy Γᶜ A) t
check? (!! Γ!)     A t = just (chk id𝒲 (coe~ rfl~ (collapse Γ!) TT))
\end{code}

By working with intrinsically-typed syntax, this algorithm must be 
\emph{sound} in at least the sense that it only produces well-typed 
\SCDef terms.
However, in principle, we would probably expect a stronger soundness condition
on elaboration, expressing in some sense that the semantic meaning of the input
|PreTm| is preserved\remarknote{The first step here, naturally, would
be to actually give some semantic meaning to untyped pre-terms.}. 
Furthermore, we might also expect a
completeness property, expressing that if a pre-term is sufficiently
annotated and typeable, then elaboration should succeed. 
Ideas from \sidecite{kovacs2024elab} are likely to be highly relevant here.
We leave the work of defining and checking such additional correctness
criteria to future work. 
