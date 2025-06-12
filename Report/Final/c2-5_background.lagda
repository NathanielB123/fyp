%if False
\begin{code}
{-# OPTIONS --prop --rewriting --mutual-rewriting #-}

open import Utils renaming (ε to [])
open import Utils.IdExtras
open import Report.Final.c3-4_background

module Report.Final.c2-5_background where

\end{code}
%endif

\subsection{From Quotients to Setoids}
\labsec{quotsetfibre}

As previously mentioned 
in \hyperref[sec:equivquot]{Section 1.1 - Equivalence Relations, Quotients and Setoids}, 
support for quotient types in modern proof assistants 
is somewhat hit-or-miss. 
\sideremark{In a two-level metatheory \cite{annenkov2023two}
it is possible to simultaneously work with quotients up to equivalence
when convenient and then go down to a 
raw syntactic level when required. The key idea behind 2LTT 
is to have both an
\emph{inner} and \emph{outer} propositional equality, which differ in
their degrees of extensionality.
Indeed some exploration has been done
on using this framework to formalise \emph{elaboration} 
\cite{kovacs2024elab}, a somewhat inherently syntactic 
algorithm.\\\\
2LTT also comes with some restrictions
on eliminators mapping between the two levels though, which I expect to be
problematic in proving e.g. strong normalisation.
A pertinent question arises here: why not just scrap intrinsically-typed
syntax and use inductive typing relations on untyped terms? Perhaps
if our \textit{only} aim was proving strong normalisation, this would 
be a sensible course of action.}\sideblankcite{annenkov2023two, kovacs2024elab}
Quotienting by conversion also prevents us
from performing more
fine-grained ``intensional'' analysis on terms 
\sidecite{kovacs2022staged} or using more ``syntactic''
proof techniques such as reduction. 
Therefore, when mechanising in Agda, we prefer to work
with setoids rather than QIITs directly.

We follow essentially the translation as outlined in
\cite{kovacs2022staged}.
Contexts become a setoid, types become a setoid fibration on contexts,
substitutions become a setoid fibration on pairs of contexts and terms
become a setoid fibration on types paired with their contexts.

We start by declaring the equivalence relations. We place these
in a universe of strict propositions |Prop|
% TODO explain |Prop| (maybe earlier)
for convenience.

\begin{code}
data Ctx~  : Ctx → Ctx → Prop
data Ty~   : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂ → Prop
data Tm~   : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂ 
           → Prop
data Tms~  : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂ 
           → Prop
\end{code}

%if False
\begin{code}
variable
  Γ~ Δ~ Θ~ Γ₁₂~ Γ₂₃~ Δ₁₂~ Δ₂₃~ Γ₁~ Γ₂~ Γ₃~ Γ₄~ : Ctx~ Γ₁ Γ₂
  A~ B~ A₁₂~ A₂₃~ A₁~ A₂~ A₃~ A₄~ : Ty~ _ A₁ A₂
  t~ t₁~ t₂~ : Tm~ _ _ t₁ t₂

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  _▷~_    : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ ▷ A₁) (Γ₂ ▷ A₂)
\end{code}
%endif

We add constructors to these relations corresponding to equivalence,
congruence and computation (the latter of correspond to the propositional
equations that we explicitly quotient by in a QIIT syntax).

\begin{code}
data Ty~ where
  -- Equivalence
  rfl~ : Ty~ rfl~ A A
  sym~ : Ty~ Γ~ A₁ A₂ → Ty~ (sym~ Γ~) A₂ A₁
  _∙~_ : Ty~ Γ₁₂~ A₁ A₂ → Ty~ Γ₂₃~ A₂ A₃ → Ty~ (Γ₁₂~ ∙~ Γ₂₃~) A₁ A₃

  -- Congruence
  𝔹~     : Ty~ Γ~ 𝔹 𝔹
  Π~     : ∀ A~ → Ty~ (Γ~ ▷~ A~) B₁ B₂ → Ty~ Γ~ (Π A₁ B₁) (Π A₂ B₂)
  _[_]~  : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
         → Ty~ Δ~ (A₁ [ δ₁ ]Ty) (A₂ [ δ₂ ]Ty)
  IF~    : Tm~ Γ~ 𝔹~ t₁ t₂ → Ty~ Γ~ A₁ A₂ → Ty~ Γ~ B₁ B₂ 
         → Ty~ Γ~ (IF t₁ A₁ B₁) (IF t₂ A₂ B₂)

  -- Computation
  IF-TT~  : Ty~ rfl~ (IF TT A B) A
  IF-FF~  : Ty~ rfl~ (IF FF A B) B

  𝔹[]~    : Ty~ rfl~ (𝔹 [ δ ]Ty) 𝔹
  Π[]~    : Ty~ rfl~ (Π A B [ δ ]Ty) (Π (A [ δ ]Ty) (B [ δ ^ A ]Ty))
  
  [id]~   : Ty~ rfl~ (A [ id ]Ty) A
  [][]~   : Ty~ rfl~ (A [ δ ]Ty [ σ ]Ty) (A [ δ ⨾ σ ]Ty)
\end{code}

%if False
\begin{code}
postulate
\end{code}
%endif

We are missing the computation rule for substitutions applied to
|IF|:

\begin{spec}
IF[]   :  IF t A B [ δ ]Ty 
       ≡  IF (subst (Tm Δ) 𝔹[] (t [ δ ])) (A [ δ ]Ty) (B [ δ ]Ty)
\end{spec}

The transport here is essential. |t [ δ ]| only has type |𝔹 [ δ ]Ty|, but
|IF| requires a term of type |𝔹|. Typeability in dependent type theory must
account for conversion. We can achieve this by adding constructors
to each indexed sort (|Ty|, |Tm| and |Tms|)
corresponding to coercion over the equivalence:

\begin{code}
  coeTy   : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂

  coeTm   : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂

  coeTms  : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂
\end{code}

|IF[]~| can now be written with an explicit coercion on the scrutinee:

\begin{code}
  if[]~  : Ty~ rfl~  (IF t A B [ δ ]Ty) 
                     (IF (coeTm rfl~ 𝔹[]~ (t [ δ ])) (A [ δ ]Ty) (B [ δ ]Ty))
\end{code}

The final ingredient to make this work
is \emph{coherence}: coercion must respect the equivalence.

\begin{code}
  cohTy   : Ty~   Γ~  A (coeTy Γ~ A)
  cohTms  : Tms~  Δ~  Γ~  δ  (coeTms Δ~ Γ~ δ)
  cohTm   : Tm~   Γ~  A~  t  (coeTm Γ~ A~ t)
\end{code}

\subsection{Strictification}
\labsec{strict}

Whether quotiented or based on setoids, explicit-substitution syntaxes can be 
painful to work with in practice. We have already seen how
many of the substitution laws for terms require manual coercion over
the corresponding laws for types, e.g.

\begin{spec}
if[]  :   if A t u v [ δ ] 
      ≡[ Tm≡ refl (sym <>-commTy ∙ [][]coh {q = refl}) ]≡
          if  (A [ subst (λ □ → Tms (Δ ▷ □) (Γ ▷ 𝔹)) 𝔹[] (δ ^ 𝔹) ]Ty) 
              (subst (Tm Δ) 𝔹[] (t [ δ ])) 
              (subst (Tm Δ) (sym <>-commTy ∙ [][]coh {q = TT[]  }) (u [ δ ])) 
              (subst (Tm Δ) (sym <>-commTy ∙ [][]coh {q = FF[]  }) (v [ δ ])) 
\end{spec}

If substitution instead computed recursively, 
|𝔹[] : 𝔹 [ δ ]Ty ≡ 𝔹|, |TT[] : TT [ δ ] ≡ TT|
and |FF[] : FF [ δ ] ≡ FF| would hold
definitionally, enabling the substantially simpler
\begin{spec}
if[]  :   if A t u v [ δ ] 
      ≡[ Tm≡ refl (sym (<>-commTy {B = A})) ]≡
          if  (A [ δ ^ 𝔹 ]Ty) (t [ δ ]) 
              (subst (Tm Δ) (sym (<>-commTy {B = A})) (u [ δ ])) 
              (subst (Tm Δ) (sym (<>-commTy {B = A})) (v [ δ ])) 
\end{spec}
Of course, the rule still requires some transport to account for commuting
of substitutions
\begin{spec}
<>-commTy : B [ δ ^ A ]Ty [ < t [ δ ] > ]Ty ≡ B [ < t > ]Ty [ δ ]Ty
\end{spec}
which does not hold by mere computation. If somehow this law were made
strict as well, we could write the substitution law for ``|if|'' as
\begin{spec}
if[]  :  if A t u v [ δ ] 
      ≡  if (A [ δ ^ 𝔹 ]Ty) (t [ δ ]) (u [ δ ])) (v [ δ ])) 
\end{spec}

This excessive transporting can get especially painful when constructing
displayed models of syntax\remarknote{In other words, \textit{inducting} on
syntax rather than merely \textit{recursing}.}, e.g. when proving properties 
like canonicity or
normalisation. Issues of this sort were severe enough that the
Agda mechanisation of \sidecite{altenkirch2017normalisation} was never fully
finished.

Luckily, there has been some significant progress recently
towards taking a well-understood explicit substitution syntax as primitive and 
then \emph{strictifying}
various substitution equations, as to construct something easier to work with.
\sidecite{kaposi2023towards} illustrates one strategy towards achieving this, 
where
operations intended to compute are redefined recursively and then a new
induction principle is derived which refers to these recursive operations.

Unfortunately, while this approach can make substitution equations
arising from direct computation such as |𝔹 [ δ ]Ty ≡' 𝔹| definitional,
the functor laws remain propositional.
\sidecite{kaposi2025type} presents a much more involved construction
based on presheaves, in which
all substitution laws, except
the η law for context extension |▷η : δ ≡ π₁ δ , π₂ δ| /
|id▷ : id {Γ = Γ ▷ A} ≡ wk , vz|,
are eventually strictified. When implemented in Agda, both approaches only 
allow induction via explicit eliminators, rather than pattern matching.

Some proof assistants also support
reflecting a subset propositional equations into definitional ones 
via global |REWRITE| rules
(e.g. Dedukti \sidecite{assaf2016dedukti}, 
Agda \sidecite{cockx2020type} and Rocq
\sidecite{leray2024rewster}). Global rewrite rules can be though of a
restricted version of equality reflection from extensional type theory
(in which transports/coercions 
are fully relegated to the typing derivations), and
\sidecite{hofmann1995conservativity, oury2005extensionality, 
winterhalter2019eliminating} show that ETT is ultimately
conservative over ITT.

So, if we start with a QIIT definition of type theory, we have few possible
routes towards strictifying equations. There remain problems though:
\begin{itemize}
  \item Strictification can produce a more convenient induction principle for
  the syntax, but this is still just an induction principle. 
  Directly-encoded inductive-recursive types in Agda allow for pattern
  matching, which is often more convenient (e.g. when pattern matching, 
  we do not have to explicitly give cases for how to interpret the recursive 
  operations).
  \item As mentioned in the previous section, Agda's support for quotient
  types is somewhat unsatisfactory, so we would rather use setoids.
  Rewriting via setoid equations is unsound (because setoid 
  constructors are still provably disjoint w.r.t. propositional equality).
  \item Rewrite rules as implemented in Agda struggle somewhat with
  indexed types \sidecite{burke2024agda}.
\end{itemize}

The ultimate goal of this project is to explore new type theories with
local equational assumptions, not to provide a watertight Agda mechanisation.
Therefore, in the proofs of normalisation, where, frankly,
we need all the help we can get,
I axiomatise \emph{strict}, implicit-substitution syntaxes,
using a combination of |POSTULATE|s, |REWRITE| rules, |NON_TERMINATING| and
|NON_COVERING| definitions, and even a new flag which re-enables
\sidecite{amelia2023rewrite} (these are of course very unsafe features, but
the idea is to simulate working in a ``nicer'' metatheory where 
``transport-hell'' is less of an issue).
Critically, while substitution is strict, we still deal with
|β|/|η| convertibility 
via an explicit equivalence relation, so the syntax remains
setoid-based.

% TODO: Maybe mention we will use a quotiented syntax rather than equivalence
% relation for the report, if indeed we will...
For presentation in the report,
going over the entire syntax of dependent
type theory again, switching |_≡_| signs to |_=_| is probably not a
super valuable use of anyone's time. I will quickly given
the definition of variables though, given these are new to the strict
presentation (though very similar to STLC).

\begin{spec}
data Var where
  coeVar : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Var Γ₁ A₁ → Var Γ₂ A₂

  vz : Var (Γ , A) (A [ wk ]Ty)
  vs : Var Γ B → Var (Γ , A) (B [ wk ]Ty)
\end{spec}

We also return to \emph{pointful} application:

\begin{spec}
_·_  : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ < u > ]Ty)
\end{spec}
