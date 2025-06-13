% TODO: This should probably turn into an SCDef chapter...
% (Specifically, given SCDisj in the sense I originally intended here doesn't 
% appear to be a sound idea)

%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils

module Report.Final.c10_scdisj where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Disjoint Smart Case}
\labch{disj}

In this section, we describe a dependent type theory featuring a subset of 
\textbf{smart case} where LHSs of rewrites do not overlap and RHSs can only be 
closed booleans. We name this theory $\textsf{SC}^{\mathbb{B}}_{\textsf{disj}}$.

\section{Admissible and Inconsistent Equations}

When we attempt to add an equation to the context, there are three key 
possibilities:
\begin{itemize}
  \item \textbf{Admissible:} The equation is already definitionally true. 
  In the case of equations targetting closed booleans, this occurs when the LHS
  and RHS reduce to the same closed boolean value.
  \item \textbf{Inconsistent:} The LHS and RHS of the equation definitionally
  anti-unify. In the case of boolean equations, this occurs when the LHS and
  RHS reduce to opposite boolean values.
  \item \textbf{Consistent:} The equation is neither admissible nor 
  inconsistent.
\end{itemize}

Only when an equation is consistent should we actually orient the equation to 
map from the stuck neutral to the closed boolean and insert it into the context.
Admissible equations can simply be ignored, while terms in inconsistent
contexts can be ruled-out at the points in the syntax where equations are
introduced.

A somewhat natural way to encode these three possibilities are convertibility
premises. Given a term and a closed boolean, we can have cases for
|t ~t ⌜ b ⌝𝔹|, |t ~t ⌜ not b ⌝𝔹| and |t ~t tᴺᵉ| (where |tᴺᵉ| is some stuck 
neutral).

Unfortunately, embedding convertibility premises into the syntax like this 
causes issues when defining substitutions. Substitutions must preserve
definitional equality, so admissibility and inconsistency are preserved, but
consistency is very-much not, and substitutions on neutral terms are not
structurally recursive. Therefore, we introduce yet another case for when 
the status of the equation is currently unknown, which we name 
``superposition''. We prevent reductions below superpositions to stop
reductions in potentially-inconsistent contexts.


\section{Substitutions}

Because our contexts have been extended with rewrites, substitutions (which map
between contexts) now need to account for these. As a recap, parallel 
substitutions for ordinary dependent types can be defined as lists of terms,
indexed first by the context all the terms are in, and second by the list of
types of the terms themselves.

\begin{spec}
data Tms (Δ : Ctx) : Ctx → Set where
  ε    : Tms Δ ε
  _,_  : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]T) → Tms Δ (Γ , A)
\end{spec}

Note that the target context of the substitution, |Δ|, is fixed "up-front", 
while the domain |Γ| grows with each term appended to the list. To fit with this
pattern, we propose adding a single extra rule which appends a rewrite to 
|Γ|, as long as it is definitional in |Δ|\remarknote{Convertibility w.r.t.
|Γ| must be a subset of convertibility w.r.t. |Δ| to ensure substitutions
preserve the structure of terms - i.e. otherwise substitution might have to
insert manual coercions, in the worst-case essentially having to elaborate from
\textsf{SC} to a dependent type theory without it.}.

\begin{spec}
  rw  :  ∀ (δ : Tms Δ Γ) p → (⌜ tᴺᵉ ⌝Ne [ δ ]t) ~t (⌜_⌝𝔹 {Γ = Γ} b) 
      →  Tms Δ (Γ , tᴺᵉ >rw b ∣ p)
\end{spec}

i.e. substitutions are now interleaved lists of terms and convertibility
premises.

Note that the convertibility premise requirement is weaker than requiring
every rewrite in |Δ| be exactly contained in |Γ|. This is important, as we
will need to apply substitutions like |TT / b| even in contexts where
|b >rw true|. For example, consider the term:

\begin{spec}
(λ b. if b the u else v) true
\end{spec}

When contracting this β-redex, we need to substitute |true / b| inside |u|,
where the rewrite |b >rw true| used to hold. Note that |u| will no longer
introduce a rewrite (i.e. it will be embedded using the |admis| rule rather than
|intro|, because |b [ true / b ]| is already be convertible to |true|).

On the other hand, it does not make sense to apply the substitution in |v|, 
(definitionally identifying |true| and |false| is dangerous) - i.e. substitution
can simply turn |v| into |incon|.

% TODO: Does substitution rely on normalisation/deciding convertibility to make
% these decisions??
