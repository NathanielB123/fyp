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

\pagebreak
\section{Locally Introducing Equations}
\labsec{localext}

Back in \refsec{simplebooleq}, we discussed potentially enhancing our
notion of conversion-modulo-equations by introducing new equations
on the scrutinee inside the LHS and RHS branches of ``|if|''-expressions.

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
analogue of Boolean \SC. Of course, typeability of STLC is independent
of conversion, so this rule does not expand the expressivity of the language
(i.e. make more terms typeable)
like dependent \SC does, but it does still expand our notion of convertibility
to somewhere between pure β-equivalence and adding in full η-equality of
Booleans.

For example, in the empty equational context, we have |if t t t ~ if t TT FF|
but we cannot simplify further to just |t|. We also cannot derive commuting
conversions.
We argue that this more limited notion of conversion can be advantageous
though. As mentioned in \refsec{coprodeta}, known algorithms which can decide 
η-equality for positive types are quite inefficient (e.g. 
renormalising terms $2^n$ times where $n$ is the number of distinct neutral
Boolean subterms). I claim that we can take a smarter approach
with |_⊢_~_|. Specifically, we can split on Boolean neutrals only
at stuck ``|if|''-expressions, and normalise the left and right branch
just once under the corresponding equation (e.g. given |if t u v|, we must
normalise  |u| under |t ~ TT|, but not |t ~ FF|).

\sideremark{Mutually calling into completion during normalisation when
recursing under stuck ``|if|''-expressions is exactly the approach I 
am employing in my \SCBool typechecker (\refsec{typecheckingsc}).}

Justifying normalisation for this theory is quite subtle, however.
Retaining our strategy of
first completing the equational context and then reducing seems promising, 
but we now hit a new case in reduction where, after recursing into the LHS or
RHS of an ``|if|'' expression, we must call back into completion again. Even though
``|if|''-expressions only add equations one-at-a-time, completion might have to run 
for many iterations (i.e. if the new equation unblocks existing neutral LHSs) so
the termination metric here is non-obvious (if indeed this algorithm does
actually terminate).

\begin{remark}[Adding One Equation to a Complete Equational Context 
Triggers an Arbitrary Number of Completion Iterations] \phantom{a}

To show that we cannot meaningfully take advantage of prior completion evidence
and the fact we only introduce one equation at a time, we construct an
example pair of Boolean equations which requires an arbitrarily high number of
iterations to complete.

Concretely, let us first consider the equation |x >eq TT| (in a context where
|x ∶ 𝔹|). Clearly
the equational context containing only this equation is complete.
If we then add the equation {|if x y i >rw TT|} (in this example,
the letters |x, y, z| and |i, j, k| all stand for distinct |𝔹|-typed variables 
in the context),
clearly, the LHS is reducible {|if x y i > if TT y i > y|}, so
the completed set of equations becomes

\begin{spec}
x >eq TT
y >eq TT
\end{spec}

Now let us instead consider the pair of equations
\begin{spec}
if (if x y i) x j >eq TT
if x y i >eq TT
\end{spec}

The first equation's LHS is now reducible (to |x|), but then this returns us
to the original equation pair:

\begin{spec}
x >eq TT
if x y i >eq TT
\end{spec}

To clarify the pattern, we repeat it once more, now considering the pair
of equations:

\begin{spec}
if (if x y i) x j >eq TT
if (if (if x y i) x j) (if x y i) k >eq TT
\end{spec}

The second equation's LHS is now the immediately-reducible
(to |if x y i|). The general construction we are employing here is to 
repeatedly replace the
smaller LHS, |u|, with |if t u v| where |t| is the larger LHS and |v|
is some arbitrary |𝔹|-typed term. Given the other equation must be of the
form |t >eq TT|, this new LHS must reduce down to |u|. 

The equational context containing only the smallest equation is always
be complete, but to complete the extended equational context,
completion must
alternate between reducing each of the LHSs exactly as many times as
we have repeated the construction.
\end{remark}

I leave the question of decidability of |_⊢_~_|, with the
local-equation-introducing ``|if|'' rule, open. 

We also leave discussion of how to deal
with more general classes of equations (e.g. at types other than |𝔹|) 
for the coming chapters, as there is not too much insight to be gained
by focusing on the special case of simple types 
(in some ways, STLC
makes such extensions more challenging, as the expressivity of dependent types
gives us ways to encode many type formers in terms of simpler ones - e.g.
coproducts in terms of Booleans and large elimination).

% I am using effectively this algorithm (extended to deal with dependent types)
% in my Haskell typechecker for \SCBool (covered in the next chapter 
% ), and so, at risk of spoiling \textit{that} chapter's conclusion early: 
% I do not even know
% how to prove termination for the simply-typed case (in TODO REF HERE we will
% explore how dependent types come with additional complications).

% Given therefore, that I am going to leave normalisation of STLC w.r.t.
% local Boolean equations open, I will quickly note down one possible idea
% (which I have not explored in detail, and may very-well be horribly misguided):
% the number of distinct equational contexts we ever need to consider reducing 
% under should be bounded by 
% $2 \times$ the total number of ``|if|'' expressions (in all LHSs of the equational
% context and the term we are normalising). Note that if we reduce scrutinee of 
% an ``|if|''
% expression, the completed equational context in the LHS and RHS branch
% should not change, as completion would reduce that equation LHS anyway,
% and while β-reduction can duplicate terms, the scrutinee will be duplicated
% also. Completion of some equational contexts (i.e. ones containing 
% ``|if|''-expressions in some of their LHSs) depends on completion of others, but
% ultimately, at the leaves of this dependency graph, we should have equational
% contexts where all LHSs do not contain ``|if|''s. Therefore, perhaps we could 
% justify slowly filling this dependency graph bottom-up, eventually completing
% every single equational context we might require during reduction.

