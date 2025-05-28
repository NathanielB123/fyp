%if False
\begin{code}
{-# OPTIONS --prop --rewriting --mutual-rewriting #-}

open import Utils hiding (ε)
open import Utils.IdExtras

module Report.Final.c3-6_background where

\end{code}
%endif

\subsection{Extending to Dependent Types}

When applying NbE for dependent types, we need to deal with terms embedded
inside types. As a first approximation, we might try and keep a similar
type for |Val| and construct identity environments to evaluate
embedded terms in on demand:
\begin{spec}
Val : ∀ Γ → Ty Γ → Set
Val Γ (if t A B) with eval t idℰ
... | TT      = Val Γ A
... | FF      = Val Γ B
... | ne tᴺᵉ  = Ne Γ (if t A B)
\end{spec}

However, this definition poses difficulties for the case of |Π-types|, where
we need to recurse at types |A [ δ ]| and |B [ δ , u ]|.

\begin{spec}
Val Γ (Π A B)
  = ∀ {Δ δ} (δᵀʰ : Thin Δ Γ δ) (uⱽ : Val Δ (A [ δ ]))
  → Val Δ (B [ δ , u ])
\end{spec}

Unfortunately, multiple things go wrong here:
\begin{itemize}
  \item |A [ δ ]| and |B [ δ , u ]| are not structurally smaller than |Π A B|,
  so it is not obvious that |Val| as defined above is well-founded. 
  The case for |A| can be
  fixed by relying on how thinnings do not structurally alter
  (substitution-normal) types in a meaningful way. However, |B [ δ , u ]| is 
  harder In the presense of large elimination \refremark{condisj}, there is no
  easy structurally-derived order on types which is
  also stable w.r.t. substitution\remarknote{
  Consider e.g. recursing on a natural number to build an iterated |Π|-types,
  as is sometimes done in dependently-typed languages to achieve
  arity-polymorphism.}
  \item It turns out
  that some of the cases in |qval|/|uval| depend on completeness of the
  NbE algorithm. We could attempt to
  mutually prove correctness, but this does not appear to work 
  in practice, as explained in \sidecite{altenkirch2017normalisation}.
\end{itemize}

To solve the latter issue, we need to fuse NbE values with the correctness
proof, and therefore index values by the term which we are evaluating.
To solve the former, we can additionally parameterise types by a substitution,
and the corresponding environment in which to evaluate embedded terms.

\begin{code}
Env  : ∀ Δ Γ → Tms Δ Γ → Set
Val  : ∀ Γ A Δ δ → Env Δ Γ δ → Tm Δ (A [ δ ]Ty) → Set
\end{code}

% |B [ < u > ]| is not structurally smaller than |Π A B|. If the large elimination
% on types is suitably restricted, it is possible to justify |Val| by recursion
% on spines as suggested in \sidecite{danielsson2006formalisation}
% \begin{spec}
% data Sp : Set where
%   𝔹  : Sp
%   Π  : Sp → Sp → Sp
% 
% sp : Ty Γ → Sp
% sp 𝔹       = 𝔹
% sp (Π A B) = Π (sp A) (sp B)
% \end{spec}

% but adapting this approach to a theory with large elimination
% seems impossible. To recurse at |A| in |if t A B|, we require 
% |sp A| to be structurally smaller than |sp (if t A B)|, but we also need
% to ensure conversion is preserved, i.e. |sp (if TT A B) ≡ sp A|.
% These goals are incompatible\remarknote{Adding a new spine
% constructor for |if|, |if : Sp → Sp → Sp| and quotienting
% with |if sA sB ≡ sA|, |if sA sB ≡ sB| does not work, because after being
% quotiented in this way, |if| is not injective, so we cannot rule out
% the spine of |if t A B| being merely |sp A|.}.

Evaluating both terms and substitutions can then be specified like so:

\begin{code}
eval   : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ ρ (t [ δ ])
eval*  : ∀ δ (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)
\end{code}

TODO: COPY IN DETAILS FROM MY AGDA PROOF THAT ARE RELEVANT HERE

\section{Dependent Pattern Matching}
\labsec{matching}

We have also liberally used pattern-matching in our metatheory.

In general, pattern-matching acts as syntactic sugar for elimination
rules. It covers a number of convieniences, including generalising
induction patterns (e.g. recursing on on any subterm of a pattern,
lexicographic orders \sidecite{abel2002recursion}). 

In a non-dependent type theory, pattern-matching as syntax sugar for
recursors is sufficient. When terms can occur in types, we also want to
be able to take advantage of information learnt over the course of the
match. For example: (go to old background section for examples...)


For a full formal treatment, we refer to \sidecite{cockx2017dependent}
but 

%TODO
 