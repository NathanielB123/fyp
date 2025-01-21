%if False
\begin{code}
{-# OPTIONS --prop --guardedness #-}

open import Utils
open import Common.Sort

module Report.Interim.c2_background where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Background and Related Work}
\labch{background}

% Plan
% - Eta conversion vs extensionality vs equational assumptions
%   - Eta for STLC
%   - Eta for dependent types
% - Type theories with equational assumptions
%   - GHC Haskell
%   - Zombie
%   - Andromeda
% - Global Rewrite Rules
%   - Dedukti
%   - Agda
% - Decidability of Conversion
%   - Normalisation approaches

% Higher order rewrite systems??? Most of the research here doesn't look
% at ground systems though

% Mentioning RHS/LHS unification might be nice but I don't think it is
% strictly necessary

% Green slime should probably go in the introduction...




% \section{Dependent Pattern Matching and LHS Unification}
% 
% Proof assistents like Agda that feature both metavariables and dependent pattern
% matching benefit from using two different unification algorithms 
% \sidecite[*6]{norell2007towards}: One often referred to as "RHS unification" 
% designed to solve metavariables and the other "LHS unification" to deal with
% pattern-matching.
% 
% The motivation for this distinction is that the desired properties of each
% unification procedure are different. RHS unification is allowed to fill
% metavariables whenever they are unique up to definitional equality, meaning
% e.g. neutral equations like |f x = f ?0| can be solved with |?0 = x|.
% 
% LHS unification needs to be more careful.
% 
% In fact RHS unification can be even bolder: e.g. lossily solving 
% |pred x = pred ?0| with |?0 = x|
% 
% Agda's approach the LHS unification then is to ...
% 
% \subsection{Green Slime}
% 
% ....

We begin this section looking at related type-system features and end with
a discussion on different approaches to proving decidability of conversion.

\section{Related Systems}

\subsection{Type Theories with Local Equational Assumptions}

As mentioned in the introduction, this work is largely inspired by, and is
intended as a continuation of, Altenkirch
et al.'s work on Smart Case \sidecite[*2]{altenkirch2011case}. This work
primarily
focussed on pattern matching on |Bool|eans (i.e. only introducing equations
from neutral\remarknote[][*2]{A "neutral" term is one comprising of a spine
of elimination forms blocked on a variable.} |Bool|-typed terms to closed 
boolean values). Even in this
limited form, the metatheory is non-trivial, with subtleties arising from 
how extending the set of equational assumptions (called 
"constraint sets") with new equations requires renormalising all equations
with respect to each other. For example:

\begin{example}[Coverage Checking in the Presense of Smart Case] \phantom{a}

Consider the program (in a dependent type theory with Smart Case).
\begin{spec}
foo : Bool → ...
foo b = case not b of
  true   → case b of
    true   → ?0
    false  → ...
  false  → ... 
\end{spec}

A proper implementation of Smart Case should rule that the case |?0| is
impossible as the constraint set as the impossible equation |false ≡ true|
is derivable from the constraints |not b ~ true| and |b ~ true| plus
β-conversion:

\begin{spec}
false
≡ -- by def |not| (|not true ≡ false|)
not true
≡ -- by constraint |b ~ true|
not b
≡ -- by constraint |not b ~ true|
true
\end{spec}

Note that the equation being added: |b ~ true| is, by itself, completely sound, 
and the term |b| cannot be reduced further even in the presense of the 
|not b ≡ false| constraint. Seemingly, any algorithm capable of detecting
impossibility here must iterate normalising all equations until
a fixpoint (or impossible equation) is reached.
\end{example}

Note that ruling out these impossible cases is not just a convenience to
avoid forcing the programmer to write code for situations that could never
occur. Avoiding these cases is \textit{necessary} to retain normalisation of
the type theory.

\begin{remark}[Equality Collapse and Consequences for Normalisation] \phantom{a}

In ITT, definitionally identifying non-neutral terms is dangerous as it can
lead to "equality collapse" \sidecite{conor2010wtypes}. For example,
assuming conversion is a congruence relation (which is highly
desirable for definitional equality to behave intuitively), and large
elimination (being able to eliminate from terms to types - a feature which gives 
dependent type theory much of its
expressivity and power) from booleans, one can derive definitional equality 
between arbitrary types
|A| and |B| in the presense of |true ≡ false|:
\begin{spec}
A
≡ -- \textit{by} def |if_then_else_| (|if true then t else u ≡ t|)
if true then A else B
≡ -- \textit{by} assumption |true ≡ false|
if false then A else B
≡ -- \textit{by} def |if_then_else_| (|if false then t else u ≡ u|)
B
\end{spec}
Once all types are definitionally equal, it is easy to
type self-application (e.g. |Bool ≡ (Bool → Bool)|) and so looping
terms like the classic |(λ x → x x) (λ x → x x)| are typeable, and
normalisation of open terms is lost.
\end{remark}

Despite these difficulties, some systems do implement similar features, to
varying levels of success. GHC Haskell, is based on a System F$_\text{C}$
core type theory, but layers on many surface features such as 
type-level equality constraints, automatically applied during the
"constraint solving" phase of typechecking \sidecite{sulzmann2007system}. 
Combined with type families, which enable real computation at the type
level, we can actually "prove"\remarknote{There are a couple caveats 
here:\newline
1. Haskell does not allow types to directly depend on values, so we have to
encode dependently-typed functions with so-called "singleton" encodings 
\sidecite[*2]{lindley2013hasochism,  eisenberg2020stitch}. \newline
2. Haskell is a partial language, so a "proof" of any type can be written
as |undefined|. Manual inspection is required to check totality/ termination.
\newline
3. Haskell does not yet support unsaturated type families
\sidecite[*4]{kiss2019higher}. We simulate such a feature here with a 
concrete type family with no cases, but of course this cannot be instantiated
with a "real" type function on booleans later.} 
the |bool-lemma| example from the introduction (\refexample{bool-lemma}).

\begin{example}[|f b ≡ f (f (f b))|, in Haskell] \phantom{a}
\begin{spec}
type data Bool = True | False
type SBool :: Bool -> Type
data SBool b where
  STrue  :: SBool True
  SFalse :: SBool False

type F :: Bool -> Bool
type family F b where 

boolLemma  :: (  forall b. SBool b -> SBool (F b)) 
           ->    forall b. SBool b -> F b :~: F (F (F b))
boolLemma  f STrue   = case f STrue of
  STrue   -> Refl
  SFalse  -> case f SFalse of
    STrue   -> Refl
    SFalse  -> Refl
boolLemma f SFalse  = case f SFalse of
  STrue  -> case f STrue of
    STrue   -> Refl
    SFalse  -> Refl
  SFalse  -> Refl
\end{spec}
\end{example}

Unfortunately, Haskell's constraint solving is undecidable and in practice many
desirable properties of conversion (such as congruence) do not hold.

\begin{example}[Conversion is not Congruent in GHC Haskell] \phantom{a}

In GHC 9.8.2, we can try to derive equations between arbitrary types
from the constraint |True ~ False|:
\begin{spec}
type IF :: Bool -> a -> a -> a
type family IF b t u where
  IF True  t u = t
  IF False t u = u

bad :: True ~ False => IF True () (() -> ()) :~: IF False () (() -> ())
bad = Refl
\end{spec}

But this produces the following type error:

\begin{spec}
• Couldn't match type ‘()’ with ‘() -> ()’
  Expected: IF True () (() -> ()) :~: IF False () (() -> ())
    Actual: () :~: ()
• In the expression: Refl
  In an equation for bad: bad = Refl
\end{spec}
\end{example}

Haskell is not the only language to support a "Smart Case"-like feature.
The dependently-typed language "Zombie" builds congruence closure right into the
definitional equality of 
the surface
language and implements Smart Case in full, while retaining decidable 
typechecking
and congruent conversion \sidecite{sjoberg2015programming}. 
The sacrifice is β-conversion: 
Zombie does not automatically apply computation rules, requiring manual
assistance to unfold definitions during typechecking.

This is certainly an interesting point in the design-space of dependently-typed
languages, coming with additional advantages such as accepting non-total
definitions without endangering decidability of typechecking. However, the focus
\sideremark{One could view traditional definitional equality as a hack, but it
is undeniably effective.}
of this project is justifying extending definitional equality of 
existing mainstream proof assistants, which unanimously build β-equality
into typechecking.

Sixty \sidecite{sixty} is a dependent typechecker which
also implements a form of Smart Case along with β-conversion, but there is 
no published work justifying it's implementation theoretically.

Andromeda 2 \sidecite{komel2021meta} is a proof assistant that supports
local equational assumptions via rewriting and indeed goes beyond ground 
equations,
with the goal of supporting user-specified type theories. They focus
primarily on provising soundness of the algorithm, and leave confluence/
termination checking and completeness results as future work.

\subsection{Type Theories with Global Equational Assumptions}

In the vein on Andromeda 2, there has been a significant body of work examining
type theories extended with more general global rewrite rules, plus 
implementations in Dedukti \sidecite{assaf2016dedukti}, 
Agda \sidecite{cockx2020type} and Rocq \sidecite{leray2024rewster} (though at
the time of writing, the Rocq implementation is still a work-in-progress). 
Work in the area has examined confluence
\sidecite{cockx2021taming} and termination
\sidecite{genestier2019sizechangetool} checking of rewrite rules. As we will
explore later in this report, Smart Case for infinitary and higher-order
types must necessarily be an approximation (as previously mentioned,
fully general Smart Case is equivalent to manual equality reflection, which is
undecidable), but we will aim for a more tailored criteria on accepted
equations than these works, taking advantage of the ground-ness of equations.

\subsection{Elaboration}

A principled and increasingly popular way to design and implement
programming languages
\sidecite{eisenberg2015system, brady2024yaflle, ullrich2023extensible}
is by "elaboration" into a minimal core syntax. A significant benefit of
this approach is modularity \sidecite{cockx2024core}: multiple extensions to
the surface language can be formalised and implemented without having to worry
about their interactions. Elaboration can also increase trust in the
resulting system, as it acts as evidence that all extensions are ultimately
conservative over the core, perhaps better-justfied, theory.

\sideremark{Note that automation around equality is still desirable even in
HoTT settings. Even implicit proof-relevant transports could be useful as a
principled route towards implicit coercions where there is an "obvious"
mapping between types.}
\sidecite{winterhalter2019eliminating, blot2024rewrite} have investigated
elaborating ETT and an ITT with rewrite rules respectively to an ITT
with explicit transports. However, both of these rely on Uniqueness of Identity
Proofs (UIP)/ axiom |K|, which is
undesirable in type theories with proof-relevant equality (e.g. Homotopy Type
Theory).

\subsection{Coproducts with Strict η-conversion Laws}

A strongly-related but subtly different type-system extension to Smart Case is
η-rules for positive types.

% Extensionality has a very concrete definition in dependent type theories


Note that even in ETT with equality reflection, conversion is not necessarily
complete with respect to semantic/observational equality from the point of view
of the meta. i.e. type theories which allow for
quantification over a sort of types, |Type|, but prevent case splitting
on this universe obey "for free" parametricity theorems, but building a type
theory where these parametericity results are internally provable is very 
involved \sidecite{altenkirch2024internal}.

When restricting ourselves to discussion of specific types (and functions taking
arguments of those types) though, we do find that many of these disparate
notions start to coincide.

% Formal proof that observational equality of functions on booleans is provable
% from η
We assume f true = f true, f false = g false
\begin{spec}

f
≡ λ b → f b
≡ λ b → f (if b then True else False)
≡ λ b → if b then f True else f False
≡ λ b → if b then g True else g False
≡ λ b → g (if b then True else False)
≡ λ b → g b
≡ g
\end{spec}



One could view much of the recent progress in type theory as taking bits and
pieces from ETT and carefully adding them to ITT in such a way as to avoid
breaking the core meta-theoretical properties. Of course, not everything
falls under this umbrella: in fact arguably the most famous modern type theory
result (univalence) explores a principle which is fundemantally incompatible
with erasing transports, but even this law can  be viewed as a kind of 
extensionality rule for types.


This work focusses less on the expressivity side (in fact, the ultimate aim is
to elaborate Smart Case into a small core without it)


\section{Decidability of Conversion}

% Formal definition of conversion
A conversion relation is a congruence relation on terms that aims to capture
a practical (i.e. decidable) subset of semantic equality. 
Applied to simple type systems, conversion
acts as a nice declarative specification of what reduction/normalisation
should achieve (normal forms should enable easy checking of conversion). In
the context of dependent types, conversion is central to the type system,
specifying exactly the definitional equality. For this reason, decidability
of typechecking in the context of dependent types hinges on decidability
of conversion. e.g. consider the typing rule for function application
|_·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B| in STLC. The repetition of |A| here
in STLC can simply refer to on-the-nose syntactic equality, given equality
(conversion) on types in STLC is trivial. In the setting of dependent types,
terms can appear within types, and so to typecheck application while respecting
conversion, we must decide whether said embedded terms are convertible.

Conversion typically includes syntactic equality extended with specific
computation (i.e. β/η) laws. However, this is not the only
design possibility: forgoing computation rules enables extending definitional
equality with arbitrary equational assumptions 
\sidecite{sjoberg2015programming}. Weak type theories forgo non-trivial 
conversion entirely \sidecite{winterhalter2020formalisation}.
On the other hand, extensional type theories admit arbitrary equality 
reflection.

% ---------------------------------------------------------------------------- %
% Formal definition of equality reflection
% ---------------------------------------------------------------------------- %
%if False
\begin{code}
module EqRefl where
  postulate
    Ctx : Set
    Ty  : Ctx → Set
    Tm  : ∀ Γ → Ty Γ → Set
  variable
    Γ Δ : Ctx
    A B : Ty Γ
    t u : Tm Γ A
  postulate
    _≡'_ : Tm Γ A → Tm Γ A → Ty Γ
    _~_  : Tm Γ A → Tm Γ A → Set
\end{code}
%endif

Equality reflection expresses that the object-theory judgement of a
propositional equality can be turned into a meta-theory judgement of
convertibility between the two terms.
\begin{code}
    reflect : Tm Γ (t ≡' u) → t ~ u
\end{code}
% ---------------------------------------------------------------------------- %

conversion checking in this setting is completely undecidable (it requires
arbitrary proof search to find possible |t ≡' u| terms).

This project focusses on type theories with decidable conversion, but one
could view the overarching mission statement here as investigating how close we 
can get to the convenience of on-paper ETT without losing decidability. 

\subsection{Reduction-based}

% ---------------------------------------------------------------------------- %
% Formal definition of strong normalisation
% ---------------------------------------------------------------------------- %
%if False
\begin{code}
module SNDef where
  postulate
    Tm : Set
    _→β_ : Tm → Tm → Set
    -- Acc : ∀ {A : Set} → (A → A → Set) → A → Set
  variable
    A : Set
    t : Tm
\end{code}
%endif
\begin{code}
  SN = ∀ t → Acc _→β_ t
\end{code}
Where |Acc| is the accessibility predicate and |_→β_| is the small-step 
reduction relation (congruence of all |β| rules)

Clasically: there exists no infinite chain of reductions
\begin{code}
  record ∞Chain (r : A → A → Set) (x : A) : Set where
    coinductive
    field
      {y}  : A
      head : r x y
      tail : ∞Chain r y
  
  SN-classical = ∀ t → ¬ ∞Chain _→β_ t
\end{code}
Under Markov's principle, these two concepts coincide
% Proof?
% ---------------------------------------------------------------------------- %

Some type theories lack obvious strongly normalising operational semantics but 
still have decidable conversion (e.g. type theories with eta-equality
or explicit substitutions \sidecite{altenkirch2009big}). 
One alternative strategy is to derive an
algorithm to decide conversion from weak-head normalisation 
\sidecite{abel2016decidability}. One extra nice advantage of such an approach is
that confluence of the reduction relation is usually much easier to show, with
often only one small-step possible from each syntactic construct. The downside
is that weak-head normalisation alone does not imply decidability of conversion 
e.g. in a system with η-equality of functions, arbitrary function-typed terms 
can be soundly expanded like `f → λ x. f x` to trivially end up in WHNF, but 
clearly a procedure which cycles between η-expanding and recursing on the bodies
to decide equality of functions will never terminate. Some care is required to
work out what laws should be dealt with by reduction and which can be checked
during conversion checking, as well as justifying this cyclic algorithm
does indeed terminate.


% Formal definition of weak-head reduction
\begin{code}
-- To characterise weak-head normal forms, we need to introduce the concept of
-- introduction and elimination forms. We consider types inductively defined
-- by their introduction forms, while elimination forms express 
-- recursion/induction over these structures.
-- I think this division is most cleanly expressed via β rules. All β rules
-- are of the form `e (i t₁ ... tₙ) u₁ ... uₙ → v`, where `e` is an elimination
-- constant and i is an introduction one.

-- Weak-head normal forms can then be defined as either headed by some
-- introduction rule, or a spine of elimination forms blocked on a variable
-- Whnf t = intro-headed t ⊎ neutral t
\end{code}


Big-step normalisation has also been demonstrated to extend to
dependent types \sidecite{altenkirch2020big}.


Much of the original work on "Smart Case" attacked the problem using big step
reduction (\sidecite{altenkirch2009smart}, private 
communication with Thorsten Altenkirch). Looking up a neutral expression
in a set of constraints is not too tricky, but problems seem to occur when
merging constraint sets (the main necessary case is adding one new constraint
to a set). For deciding equality of the neutrals when looking them, all neutral
LHSs must be kept normalised with respect to all other constraints. Adding a
single new constraint might unblock multiple neutral LHSs of other constraints,
which might unblock yet more etc... so the only applicable technique to arrive
at a fully normalised constraint set is to iterate reducing all constraints
with respect to others until a fixed point (i.e. very similar to ground 
completion). The only technique I am aware of to show such a fixed point exists
is to demonstrate that there exists some well-founded ordering on constraint
sets that continues to decrease during the repairing process: in other words
we end up needing a small step reduction relation anyway.


\subsection{Reduction-free Normalisation}

Normalisation-by-evaluation really comes into it's own when working with a
syntax quotiented by conversion.

Another 

