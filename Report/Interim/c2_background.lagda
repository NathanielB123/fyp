%if False
\begin{code}
{-# OPTIONS --prop --guardedness #-}

open import Utils
open import Common.Sort

module Report.Interim.chapters.background where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Background and Related Work}
\labch{background}

\section{Dependent Pattern Matching and LHS Unification}

Proof assistents like Agda that feature both metavariables and dependent pattern
matching benefit from using two different unification algorithms 
\sidecite[*6]{norell2007towards}: One often referred to as "RHS unification" 
designed to solve metavariables and the other "LHS unification" to deal with
pattern-matching.

The motivation for this distinction is that the desired properties of each
unification procedure are different. RHS unification is allowed to fill
metavariables whenever they are unique up to definitional equality, meaning
e.g. neutral equations like |f x = f ?0| can be solved with |?0 = x|.

LHS unification needs to be more careful.

In fact RHS unification can be even bolder: e.g. lossily solving 
|pred x = pred ?0| with |?0 = x|

Agda's approach the LHS unification then is to ...

\subsection{Green Slime}

....



\section{Equality in Type Theory}



% I think we need to move some of the conversion stuff to here because the
% immediately below sections really rely on it...


To further motivate

\section{Smart Case}

This work was primarily inspired by a presentation 
\sidecite{altenkirch2011case}. The hope is that 
recent advances in the meta-theory of type theory (i.e. a renewed interest in 
semantic approaches to normalisation)

This work focusses on a type theory with ground "equational assumptions".

\section{η and Extensionality}

Extensionality has a very concrete definition in dependent type theories


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
\begin{code}
-- We assume f true = f true, f false = g false

-- f
-- ≡ λ b → f b
-- ≡ λ b → f (if b then True else False)
-- ≡ λ b → if b then f True else f False
-- ≡ λ b → if b then g True else g False
-- ≡ λ b → g (if b then True else False)
-- ≡ λ b → g b
-- ≡ g
\end{code}



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

