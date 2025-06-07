%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

open import Report.Final.c4-1_booleq hiding (_⊢_~_)

module Report.Final.c4-4_booleq where

infix 4 _⊢_~_
\end{code}
%endif

\section{Locally Introducing Equations}
\labsec{localext}

Back in \refsec{simplebooleq}, we discussed potentially enhancing our
notion of conversion-modulo-equations by introducing new equations
on the scrutinee if the LHS and RHS branches of |if|-expressions.

%if False
\begin{code}
data _⊢_~_ (Ξ : Eqs Γ) : Tm Γ A → Tm Γ A → Set where
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
%endif

\begin{code}
  if  : Ξ ⊢ t₁ ~ t₂ → Ξ ▷ t₁ >eq true ⊢ u₁ ~ u₂ → Ξ ▷ t₁ >eq false ⊢ v₁ ~ v₂
      → Ξ ⊢ if t₁ u₁ v₁ ~ if t₂ u₂ v₂
\end{code}

I would argue this rule is about as close as we can get to a simply-typed
analogue of Boolean \SC. Of course, typeability is STLC is independent
of conversion, so this rule does not expand the expressivity of the language
(i.e. make more terms typeable)
like dependent \SC does, but it does still expand our notion of convertibility.

% TODO: Examples

When comparing terms in the empty equational context, the result is a 
definition of conversion with power somewhere between mere |β|-convertibility
and extending with full strict Boolean |η|. Of course, strict Boolean
|η| has a significant efficiency downside: normalisation must in general
split on every neutral |𝔹|-typed 
subterm, |t|, and re-normalise for the cases |t ~ TT| 
and |t ~ FF|, (in general, terms must be re-normalised
$2^n$ times, where $n$ is the number of distinct neutral Boolean subterms).

|_⊢_~_| seems like it should be better: we only split on Boolean neutrals
at |if|-expressions, and normalise the left and right branch once under only
the corresponding equation (e.g. given |if t u v|, we normalise |u| under
|t ~ TT|, but not |t ~ FF|).

Normalisation for this theory is quite subtle, however. The idea of
first completing the equational context and then reducing seems promising, 
but we hit a new case in reduction where, after recursing into the LHS or
RHS of an |if| expression, we must call back into completion again. Even though
this process only adds one equations at a time, completion might have to run for
many iterations (i.e. if the new equation unblocks existing neutral LHSs) so
the termination metric here is very-non-obvious (if indeed this algorithm does
actually terminate).


I am using effectively this algorithm (extended to deal with dependent types)
in my Haskell typechecker for \SCBool (covered in the next chapter TODO REF 
% TODO: We will probably list contributions in intro, so maybe am repeating
% myself here
HERE), and so, at risk of spoiling \textit{that} chapter's conclusion early: 
I do not even know
how to prove termination for the simply-typed case (in TODO REF HERE we will
explore how dependent types come with additional complications).

% Given therefore, that I am going to leave normalisation of STLC w.r.t.
% local Boolean equations open, I will quickly note down one possible idea
% (which I have not explored in detail, and may very-well be horribly misguided):
% the number of distinct equational contexts we ever need to consider reducing 
% under should be bounded by 
% $2 \times$ the total number of |if| expressions (in all LHSs of the equational
% context and the term we are normalising). Note that if we reduce scrutinee of 
% an |if|
% expression, the completed equational context in the LHS and RHS branch
% should not change, as completion would reduce that equation LHS anyway,
% and while β-reduction can duplicate terms, the scrutinee will be duplicated
% also. Completion of some equational contexts (i.e. ones containing 
% |if|-expressions in some of their LHSs) depends on completion of others, but
% ultimately, at the leaves of this dependency graph, we should have equational
% contexts where all LHSs do not contain |if|s. Therefore, perhaps we could 
% justify slowly filling this dependency graph bottom-up, eventually completing
% every single equational context we might require during reduction.

\section{Beyond Booleans}

We also spend some time now considering STLC modulo more interesting equations.

% NEUTRAL EQUATIONS!
% SUM-TYPE EQUATIONS!
% HIGHER-ORDER EQUATIONS (OH DEAR)!


