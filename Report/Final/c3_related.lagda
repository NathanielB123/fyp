%if False
\begin{code}
{-# OPTIONS --prop --guardedness #-}

open import Utils renaming (_+ℕ_ to _+_)
import Relation.Binary.PropositionalEquality as EQ
open EQ.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎)
open import Common.Sort

module Report.Final.c2_background where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Related Work and Preliminaries}
\labch{related}

We begin this section looking at related type-system features and end with
a discussion on different approaches for proving decidability of conversion.

\section{Related Systems/Features}

\subsection{With-Abstraction}
\labsec{with}

Both Agda and Idris 2 support matching on non-variable expression to
a limited extent via |with|-abstractions (originally named "views")
\sidecite[*2]{mcbride2004view, agda2024with, idris2023with}. The key idea is to
apply a one-off rewrite to the context, replacing every occurence of the 
scrutinee expression with the pattern. In Agda, the implementation also
elaborates |with|-abstractions into separate top-level functions which
abstract over the scrutinee expression (so the final program only
contains definitions that match on individual variables).

Unfortunately, the one-off nature of |with|-abstraction rewrites limits
their applicability. If we re-attempt the |f b ≡ f (f (f b))| proof from
\refexample{bool-lemma}, taking advantage of this feature, the goal only gets
partially simplified:

\begin{spec}
bool-lemma : ∀ (f : Bool → Bool) b → f b ≡ f (f (f b)) 
bool-lemma f true with f true
bool-lemma f true | true = ?0
\end{spec}

At |?0|, Agda replaces every occurence of |f b| in the goal with |true|
and so expects a proof of |true ≡ f (f true)|, but it is not obvious
how to prove this (we could match on |f true| again, but Agda will force us
to cover both the |true| and |false| cases, with no memory of the prior
pattern-match).

For
\sideremark{This feature can also be simulated without special syntax
via the "inspect" idiom \sidecite[*2]{2024propositional}.}
scenarios like this, |with|-abstractions in Agda are extended with an
additional piece of syntax: following a |with|-abstraction with |in p| binds
evidence of the match (a proof of propositional equality) to the new variable
|p|.

\begin{example}[|f b ≡ f (f (f b))|, Using |with_in_| Syntax] \phantom{a}

\begin{code}
bool-lemma : ∀ (f : Bool → Bool) b → f b ≡ f (f (f b)) 
bool-lemma f true   with f true in p
bool-lemma f true   | true   = sym (cong f p ∙ p)
bool-lemma f true   | false  with f false in q
bool-lemma f true   | false  | true   = sym p
bool-lemma f true   | false  | false  = sym q
bool-lemma f false  with f false in p
bool-lemma f false  | true   with f true in q
bool-lemma f false  | true   | true   = sym q
bool-lemma f false  | true   | false  = sym p
bool-lemma f false  | false  = sym (cong f p ∙ p)
\end{code}
We can also avoid the manual equality reasoning by repeating earlier pattern
matches, but this gets very verbose, even when using Agda's |...| syntax for
repeating above matches. E.g. the first case turns into:
\begin{spec}
bool-lemma′ : ∀ (f : Bool → Bool) b → f b ≡ f (f (f b)) 
bool-lemma′ f true  with f true in p
... | true          with f true | p
... | true | refl   with f true | p
... | true | refl   = refl
\end{spec}
Agda contains yet another piece of syntactic sugar to help us here: |rewrite| 
takes a
propositional equality and applies a one-off 
rewrite to the
context (similarly to |with|-abstractions).
\begin{spec}
bool-lemma′′ : ∀ (f : Bool → Bool) b → f b ≡ f (f (f b)) 
bool-lemma′′ f true  with f true in p
... | true           rewrite p 
                     rewrite p = refl
\end{spec}
But by now we are up to four distinct syntactic constructs, and the full proof
still ends up more verbose than that with Smart Case.
\end{example}

|with|-abstractions also have a second critical issue that Smart Case solves:
the one-off nature of the rewrite can produce ill-typed contexts. Specifically,
it might be the case that for a context to typecheck, some neutral expression
(such as |n + m|) must definitionally be of that neutral form, and replacing it
with some pattern (like |su l|), without "remembering" their equality,
causes a type error.

In practice, this forces implementations to re-check validity of the context
after a |with|-abstraction and throw errors if anything goes
wrong.

\begin{example}[Ill-typed |with|-abstraction Involving |Fin|] \phantom{a}

\textit{|Fin| is the standard name for |Var| from \refdef{terms},
introduced with |ze : Fin (su n)| and |su : Fin n → Fin (su n)|.}
\begin{spec}
Pred : ∀ n m → Fin (n + m) → Set

foo : ∀ n m (i : Fin (n + m)) → Pred n m i → ⊤
foo n m i       p  with n + m
foo n m ze      p  | .(su _) = tt
foo n m (su i)  p  | .(su _) = tt
\end{spec}

Errors with:

\begin{spec}
[UnequalTerms]
w != n + m of type ℕ
when checking that the type
(n m w : ℕ) (i : Fin w) (p : Pred n m i) → ⊤ of the generated with
function is well-formed
\end{spec}
\end{example}

This type of error is especially prevalent when working with heavily indexed
types like those in \refsec{indexed-example}.

\subsection{Type Theories with Local Equational Assumptions}

As mentioned in the introduction, this work is largely inspired by, and is
intended as a continuation of, Altenkirch
et al.'s work on Smart Case \sidecite[*-1.5]{altenkirch2011case}. This work
primarily
focussed on pattern matching on booleans (i.e. only introducing equations
from neutral\remarknote{A "neutral" term is one comprising of a spine
of elimination forms blocked on a variable.} boolean-typed terms to closed 
boolean values). Even in this
limited form, the metatheory is non-trivial, with subtleties arising from 
how extending the set of equational assumptions (called 
"constraint sets") with new equations requires renormalising all equations
with respect to each other. For example:

\begin{example}[Coverage Checking in the Presense of Smart Case] \phantom{a}

\labexample{coverage}
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
impossible as the impossible equation |false ≡ true|
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
a fixed-point (or impossible equation) is reached.
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
type self-application (i.e. we have |Bool ≡ (Bool → Bool)|) and so looping
terms like the classic |(λ x → x x) (λ x → x x)| are typeable, and
normalisation of open terms is lost.
\end{remark}

Despite these difficulties, some systems do implement similar features, to
varying levels of success. GHC Haskell, is based on a System F$_\text{C}$
core theory, but layers on many surface features, including
automation of its 
type-level equality constraints \sidecite{sulzmann2007system}
(implemented in the
"constraint solving" typechecking phase). 
Combined with type families, which enable real computation at the type
level, we can actually "prove"\remarknote{There are a few caveats 
here:\newline
1. Haskell does not allow types to directly depend on values, so we have to
encode dependently-typed functions with so-called "singleton" encodings 
\sidecite[*14]{lindley2013hasochism,  eisenberg2020stitch}. \newline
2. Haskell is a partial language, so a "proof" of any type can be written
as |undefined|. Manual inspection is required to check totality/ termination.
\newline
3. Haskell does not yet support unsaturated type families
\sidecite[*12.5]{kiss2019higher}. We simulate such a feature here using a 
concrete type family with no cases, but of course this cannot be instantiated
with a "real" type-level function on booleans later.} 
the |f b ≡ f (f (f b))| example from the introduction (\refexample{bool-lemma}).

\begin{example}[|f b ≡ f (f (f b))|, in Haskell] \phantom{a}
\begin{spec}
type data Bool = True | False
type SBool :: Bool -> Type
data SBool b where
  STrue  :: SBool True
  SFalse :: SBool False

type F :: Bool -> Bool
type family F b where 

boolLemma  :: (forall b. SBool b -> SBool (F b)) 
           ->  forall b. SBool b -> F b :~: F (F (F b))
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

Unfortunately, Haskell's constraint solving is undecidable in theory and in 
practice many
desirable properties of conversion (such as congruence) do not hold.

\begin{example}[Conversion is not Congruent in GHC Haskell] \phantom{a}

In GHC 9.8.2, we can try to derive equations between arbitrary types
from the constraint |True ~ False|:
\begin{spec}
type IF :: Bool -> a -> a -> a
type family IF b t u where
  IF True  t u = t
  IF False t u = u

bad  :: True ~ False 
     => IF True () (() -> ()) :~: IF False () (() -> ())
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

\pagebreak
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
languages, coming with additional advantages such as the possibility of
accepting non-total
definitions without endangering decidability of typechecking. However, the focus
\sideremark{One could view traditional definitional equality as a hack, but
it is undeniably effective.}
of this project is justifying extending the definitional equality of 
existing mainstream proof assistants, which unanimously build in β-equality.

The Lean proof assistant features a tactic for automatically discharing
equality proofs following from congruence closure
\sidecite{selsam2016congruence}, but their algorithm is not
capable of interleaving congruence and reduction (which is required
in our setting to ensure transitivity of conversion).

Sixty \sidecite{sixty} is a dependent typechecker which
also implements a form of Smart Case along with full β-conversion, but there is 
no published work justifying its implementation theoretically.

Andromeda 2 \sidecite{komel2021meta} is a proof assistant that supports
local equational assumptions via rewriting and indeed goes beyond ground 
equations,
with the goal of supporting user-specified type theories. They focus
primarily on proving soundness of their equality checking algorithm, and leave 
confluence/termination checking and completeness results for future work.

\subsection{Type Theories with Global Equational Assumptions}
\labsec{rewrites}

In the vein on Andromeda 2, there has been a significant body of work examining
type theories extended with more general global rewrite rules, plus 
implementations in Dedukti \sidecite{assaf2016dedukti}, 
Agda \sidecite{cockx2020type} and Rocq
\sidecite{leray2024rewster} (though at
the time of writing, the Rocq implementation is still a work-in-progress). 
Work in the area has examined automatic (albeit necessarily conservative)
confluence
\sidecite{cockx2021taming} and termination
\sidecite{genestier2019sizechangetool} checking of these rewrites.
Agda's implementation of |REWRITE| rules specifically checks confluence, but
not termination.

Smart Case for infinitary and higher-order
types must necessarily be somewhat conservative and reject dangerous cases (as
previously mentioned,
fully general Smart Case is equivalent to manual equality reflection, which is
undecidable), but we will aim for a more tailored criteria for accepting
equations than these works, taking advantage of the ground-ness of equations.

\subsection{Elaboration}

A principled and increasingly popular way to design and implement
programming languages
\sidecite{eisenberg2015system, brady2024yaflle, ullrich2023extensible}
is by "elaboration" into a minimal core syntax. A significant benefit of
this approach is modularity \sidecite{cockx2024core}: multiple extensions to
the surface language can be formalised and implemented without having to worry
about their interactions. Elaboration can also increase trust in the
resulting system, ensuring that all extensions are ultimately
conservative over the, perhaps more-rigorously justfied, core theory.

\pagebreak
\sideremark{Note that implicit transporting along equivalences between
completely distinct types (such as ℕ and ℤ)
could be used to implement coercions/subtyping where there is an "obvious"
mapping, so restricting equations to those on datatypes
with trivial equality is limiting.\newline
Such use-cases in fact seem impossible to handle properly without an 
elaboration-like 
process inserting transports, given some sort of term-level computation is
ultimately required
to map between distinct types.}
\sidecite[*12]{winterhalter2019eliminating, blot2024rewrite} have investigated
elaborating ETT and ITT with global rewrites respectively to an ITT
with explicit transports. Both of these works rely on Uniqueness of Identity
Proofs (UIP)/axiom |K|, which is
incompatible with type theories that feature proof-relevant equality 
(e.g. Homotopy Type
Theory).

\subsection{Coproducts with Strict η}
\labsec{strict}

η-equations on type introduction/elimination forms express 
uniqueness principles and can be seen as
"dual" to β-laws (the connection can be made concrete with category theory). 
For example, η for the unit type |𝟙| can be written
as |∀ (t : Tm Γ 𝟙) → t ~ ⟨⟩|; that is, any |⊤|-typed term is
convertible to |⟨⟩|. η for non-dependent functions is written
|∀ (t : Tm Γ (A ⇒ B)) → t ~ ƛ (t [ wk ]) · (` vz)|\remarknote[][*2]{Note that
like
\refdef{terms}, we represent variables here as indices into the context. 
This convention is known
as "de-Bruijn indices" after \sidecite[*2.5]{de1972lambda}
and lets us avoid dealing with variable-freeness
conditions.}: any function-typed term can
be expanded into a lambda abstraction over the old term immediately
applied to the new variable.

Extending
conversion with η for unit, (dependent) pairs and
(dependent)
functions is relatively well-understood and mainstream proof assistants 
(such as Agda) commonly support definitional (or "strict") η for these types
(as long as conversion-checking is type-directed, these laws are easy to check
by η-expanding neutral terms immediately before comparing syntactically).
Such types are often collectively referred to as "negative" given they
are characterised primarily by their elimination rules.

η laws can also be given for "positive" types (types where the introduction
rules, or lack thereof, are primary, such as the empty type, coproducts,
booleans,  natural numbers etc...). It turns out that strict η for these types
is strongly-related to, and is actually more powerful than, Smart Case. 
In fact, presentations of coproduct
η \sidecite{dougherty2000equality, altenkirch2001normalization} often include 
analagous constructions to Smart Case constraint sets.

Focussing on the case of booleans, with the simply-typed recursor
|if : Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A|,
such an η-rule can be expressed as follows:

\begin{definition}[η For Booleans] \phantom{a}
%if False
\begin{code}
module BoolEta where
  variable
    A B : Set ℓ

  if_then_else_ : Bool → A → A → A
  if true   then t else u = t
  if false  then t else u = u
\end{code}
%endif

\begin{spec}
  Bool-η  : ∀ (t : Tm Γ 𝔹) (u : Tm (Γ , 𝔹) A)
          → u [ < t > ] ~ if t (u [ < TT > ]) (v [ < FF > ])
\end{spec}
In words: every term containing a boolean-typed sub-expression can be expanded
into
an |if| expression, with the sub-expression replaced by 
|TT| in the
|TT| branch and |FF| in the |FF| branch.

We can, of course, prove such a law internally (even if our theory, like Agda,
does not implement η for such types definitionally) by induction on booleans
(or pattern-matching), replacing explicit substitutions with function
application:

\begin{code}
  Bool-η-prop  : ∀ t (u : Bool → A)
               → u t ≡ if t then u true else u false
  Bool-η-prop true   u = refl
  Bool-η-prop false  u = refl
\end{code}
\end{definition}

Like the local equational assumptions of Smart Case, η for booleans enables
reducing repeated matches on the same neutral expression. We can show an
example of this using our internal |Bool-η-prop| law:

\begin{code}
  collapse-if  :  ∀ (f : Bool → Bool) b 
               →  if f b then (if f b then true else false) else false
               ≡  if f b then true else false
  collapse-if f b 
    = Bool-η-prop (f b) 
    λ fb → if fb then (if fb then true else false) else false
\end{code}

In fact, Boolean η can reduce this even further:

\begin{code}
  collapse-again  :  ∀ (f : Bool → Bool) b 
                  →  if f b then true else false ≡ f b
  collapse-again f b = sym (Bool-η-prop (f b) λ fb → fb)
\end{code}

Some further intuition for increase in power that η for booleans provides vs
Smart Case 
can be found in the way the η-rule admits so-called "commuting conversions".

\begin{example}[Commuting Conversions] \phantom{a}

Commuting conversions express the principle that case-splits on positive
types can be lifted upwards as long as the variables occuring in the scrutinee
remain in scope. i.e.
\begin{spec}
  comm  : ∀ (f : Tm (Γ , A) B) (t : Tm Γ 𝔹) (u v : Tm Γ A)
        → f [ < if t u v > ] 
        ~ if t (f [ < u > ]) (f [ < v > ])
\end{spec}
We can show an analagous rule follows internally from η as follows.
\begin{code}
  comm-internal  : ∀ (f : A → B) (t : Bool) (u v : A)
                 → f (if t then u else v) ≡ if t then f u else f v
  comm-internal f t u v = Bool-η-prop t λ b → f (if b then u else v)
\end{code}
\end{example}

In a system with strict η for functions and
another type |A|, definitional equality of functions on |A|
is observational\remarknote{Observational equality in type theory
refers to the idea that evidence of equality of terms at a particular type
can follow the structure of that type
\sidecite[*8]{altenkirch2007observational}.
For functions |f| and |g|, observational equality takes the form of a function
from evidence of
equal inputs |x ≡ y| to evidence of equal
outputs |f x ≡ f y| - i.e. pointwise equality (functions are equal precisely 
when they agree on all inputs).}.

\begin{theorem}[Strict η for Functions and Booleans Implies Definitional
Observational Equality of Boolean Functions] \phantom{a}
\labthm{obs-eta}

Assuming |f true == g true|, |f false == g false|:
\begin{spec}
f
== -- by η-equality of functions
λ b → f b
== -- by η-equality of booleans
λ b → f (if b then True else False)
== -- by commuting conversions
λ b → if b then f True else f False
== -- by assumption 
λ b → if b then g True else g False
== -- by commuting conversions
λ b → g (if b then True else False)
== -- by η-equality of booleans
λ b → g b
== -- by η-equality of functions
g
\end{spec}

Subtly, propositional, observational equality of boolean functions 
(|f true ≡ g true → f false ≡ g false → f ≡ g|) is not
provable internally
using the propositional |Bool-η-prop| principle given above (without
function extensionality). We do not have any boolean term |b| to pass to it!

This makes some sense, given propositional η-laws for inductive types can 
be proven merely by induction, but observational equality of functions (also
known as "function extensionality" in the general case) is not
provable in intensional MLTT \sidecite{streicher1993investigations}. 
\end{theorem}

It is perhaps also worth noting that in a dependently-typed setting, η for
general |A + B| binary coproducts can be obtained merely with η for
booleans, |Σ| types and large elimination, via the encoding
|A + B = Σ Bool (λ b → if b then A else B)| \sidecite{maillard2024splitting}.

There are a couple downsides to implementing η-conversion for finite
coproducts/booleans:
\begin{itemize}
  \item First, the meta-theory gets quite complicated. Previous proofs of
  normalisation for
  STLC with of strict η for binary coproducts have relied on
  somewhat sophisticated rewriting \sidecite{lindley2007extensional} or sheaf
  \sidecite{altenkirch2001normalization} theory.
  Normalisation for dependent type theory with boolean η remains open (though
  some progress on this front has been made recently
  \cite{maillard2024splitting}).
  \item Second, efficient implementation seems challenging. 
  Algorithms such as \cite{altenkirch2001normalization} aggressively
  introduce case-splits on all neutral subterms of coproduct-type and lift the
  splits
  as high as possible, in an effort to prevent the build-up of stuck
  terms. 
  \cite{maillard2024splitting} proposes an similar algorithm for
  typechecking dependent types with strict boolean η, using a monadic
  interpreter with an effectful splitting operation.
  \sidecite{altenkirch2004normalization}
  is even more extreme: when a variable |f| of type |Bool → Bool| is bound, for
  example, case
  splits are generated on |f true| and |f false| (regardless of whether such
  neutral terms actually occur anywhere in the body), in essence enumerating 
  over all possible implementations of |f|. One could imagine improving these
  algorithms, only case-splitting when a particular coproduct-typed
  sub-expression appears multiple times but I think |Smart Case|
  implementations are still likely to have overall more stable performance
  characteristics due to the lack of commuting conversions.
\end{itemize}

Smart Case is further distinguished from η-equality due to its potential
applications
beyond finitary, first-order types. Specifically, in this project, I am
aiming for a Smart Case
that at least supports equations between infinitary-typed (|ℕ|, |List A|,
|Tree A|, etc...)
\textit{neutrals}
(there are dangers here, but they only really arise when non-neutral
terms get involved). Decidable η-equality for such types is completely
infeasible
as it requires identifying functions on those types observationally (by
analagous argument to \refthm{obs-eta}): in other words, if we
could decide conversion modulo η for |ℕ|s, we would have a way to compute
whether arbitrary |ℕ → 𝔹| functions are equal on all inputs, which is enough
to solve the halting problem (consider the |ℕ → 𝔹| function that runs a
particular Turing machine for the input number of steps and returns whether
it halts).

\pagebreak
\section{Decidability of Conversion}

As mentioned in \refremark{defprop}, decidability of typechecking dependent
types hinges on decidability of conversion, so this property is quite
important for type theories intended to be used as programming languages.

The standard approach to proving decidability of conversion is to define
a normalisation function (reducing terms to "normal forms"), and then
prove this procedure sound and complete. There are multiple distinct
approaches to specifying normalisation, and so we will go over the main ones.

Note that all techniques listed below rely to some extent on
defining an intermediary term-predicate by recursion on types,
showing the predicate holds for all terms by induction on syntax, and
then proving the final result by simultaneous induction on types and the
predicate (a technique
that goes by the names
"logical relations", "computability predicates" and "reducibility candidates"
in the literature). 
There are alternative approaches to showing normalisation based
purely on rewriting theory, but these have not been shown to scale to
dependent types.

\subsection{Reduction-based}

Reduction-based techniques specify normalisation in terms of reduction rules,
and normal forms as terms that cannot be reduced further.

When using a congruent small-step reduction relation (the "operational
semantics"), one can justify
termination of naively reducing with respect to it by proving the
reduction relation is well-founded. This technique is called
"strong normalisation".

\begin{definition}[Strong Normalisation] \phantom{a}

For a given reduction relation on terms |_>>_ : Tm → Tm → Set|, we can define
\sideremark{Note the reduction relation defined on untyped terms |Tm| here.
The extension to typed terms |Tm Γ A| is easy as long as reduction is
type-preserving (obeys "subject reduction").}
strong normalisation constructively in terms of the accessibility predicate
|Acc|:
%if False
\begin{code}
module SNDef (Tm : Set) (_>>_ : Tm → Tm → Set) where
  variable
    A : Set
    t : Tm
    _<_ : A → A → Set
    x : A
\end{code}
%endif
\begin{code}
  SN = ∀ t → Acc (λ u v → v >> u) t
\end{code}

Intuitively, |Acc _<_ x| is the type of trees of finite height, where each
branch
represents a step along the |_<_| relation, with |x| at the top
and the smallest elements (with respect to |_<_|) at the bottom.
Induction on |Acc| allows us to step down the tree, one layer at a time.
It is defined inductively:
\begin{spec}
Acc  : (A → A → Set) → A → Set

acc  : (∀ {y} → y < x → Acc _<_ y) → Acc _<_ x
\end{spec}

Classically, strong normalisation can be equivalently encoded as the
non-existence of infinite chains of reductions:
%if False
\begin{code}
  record ∞Chain (_<_ : A → A → Set) (x : A) : Set where
    coinductive
    field
      {next}  : A
      step    : next < x
      steps   : ∞Chain _<_ next
  open ∞Chain public
\end{code}
%endif

\begin{code}
  SN-classical = ∀ t → ¬ ∞Chain (λ u v → v >> u) t
\end{code}

Where |∞Chain| is defined coinductively:
\begin{spec}
∞Chain  : (A → A → Set) → A → Set

next    : ∞Chain _<_ x → A
step    : ∀ (c : ∞Chain _<_ x) → next c < x
steps   : ∀ (c : ∞Chain _<_ x) → ∞Chain _<_ next
\end{spec}

We can easily prove |SN → SN-classical|:
\begin{code}
  acc-¬chain : Acc _<_ x → ¬ ∞Chain _<_ x
  acc-¬chain (acc a) c = acc-¬chain (a (step c)) (steps c)

  sn-acc-class : SN → SN-classical
  sn-acc-class p t = acc-¬chain (p t)
\end{code}
\end{definition}

A downside of working with a fully congruent small-step reduction relation
is that proving confluence is non-trivial.
Furthermore, some type theories lack obvious terminating
operational semantics but 
still have decidable conversion (e.g. type theories with η-rules
or explicit substitutions \sidecite{altenkirch2009big} and potentially
type theories with a sort of impredicative strict propositions 
\sidecite{abel2020failure}). 

To handle such theories,
one can instead define a \textit{deterministic} small-step reduction relation
without congruence rules (except those that reduce scrutinees
of elimination forms), and therefore
reduces terms only up until they are neutral or introduction-rule headed.
Such a relation is known as "weak-head reduction" and justifying its
termination goes by the name "weak-head normalisation". The downside is that
weak-head normalisation alone does not imply decidability of conversion
(e.g. consider how function-typed terms |t| can be soundly η-expanded to
|ƛ (t [ wk ]) · (` vz)|, putting them into intro-headed form, without making
any "real" progress reducing anything). Conversion checking and weak-head
normalisation must be interleaved, and termination of this interleaving
must itself be proved through a logical relations argument 
\sidecite{abel2016decidability}.

Finally, normalisation can also be defined with respect to a big-step
reduction relation \sidecite{altenkirch2020big}. In fact, much of the
original work on Smart Case attacked the problem using this approach
\sidecite{altenkirch2009smart}. Representing constraint sets as
mappings from neutral terms to normalised expressions enables extending
normalisation with a step that looks up stuck neutrals in the map.

Unfortunately, problems start to occur when
defining merging of constraint sets (i.e. to justify adding new constraints
in the branches of case splits). 
As explained in \refexample{coverage}, for looking up of neutrals to work
properly, LHSs must all be kept normalised
with respect to each other. However, adding a
single new constraint might unblock multiple neutral LHSs of other constraints,
which might unblock yet more etc... so seemingly the only feasible technique to
obtain fully normalised constraint mappings is to iterate reducing all
constraints
with respect to others until a fixed-point is reached (i.e. analagously to
ground completion). 
The only technique I am aware of to show a fixed-point
like this exists
is to demonstrate that there exists some well-founded ordering on constraint
sets that continues to decrease across iterations: in other words
we appear to end up needing a small-step reduction relation anyway.

\begin{remark}[Termination of Ground Completion and E-Graphs] \phantom{a}

Rewriting-to-completion also relies on having some total order
on terms, and ensuring rewrites consistently respect it (i.e. by
reversing them when necessary). I think any
ordering that 
places closed values like |true|/|false| at the bottom and acts like
a term encompassment ordering on neutrals should be sufficient to support
Smart Case on booleans and coproducts. Rewrites to non-neutral
infinitary-typed (e.g. ℕ) terms are trickier, and I think some sort of
"occurs check" will be necessary (the rewrite |t → su t| cannot be reversed,
as we can only justify rewriting neutral terms, but it also clearly
would lead to loops if left as-is).

Note that rewriting-to-completion is not the only algorithm for
deciding equivalence modulo a set of ground equations: bottom-up techniques
such as e-graphs \sidecite{nelson1980techniques, willsey2021egg} are also
applicable. These algorithms
can be seen as extending the union-find algorithm to terms, and termination
is justified merely by the number of e-classes decreasing during
congruence-repairing iterations. 

Unfortunately, while equations between neutral terms could likely be reasonably
handled by e-graphs, rewrites targetting introduction-headed terms are trickier
as these can unblock β-reductions, so we really do need to rewrite eagerly
(instead of delaying until conversion checking).
\end{remark}

\subsection{Reduction-free Normalisation}

Normalisation does not need to specified with respect to a reduction relation.
Reduction-free (also called "semantic" or "algebraic") arguments instead treat 
syntax as an algebraic structure (e.g. a "Category with Families" or "CwF"), 
where convertible terms are indistinguishable and theorems like 
normalisation are proved by showing a particular proof-relevant logical
predicate holds for every family of equal terms
\sidecite{altenkirch1995categorical, altenkirch2017normalisation,
sterling2021normalization}.

Such an approach was used to prove normalisation for STLC with coproducts
obeying strict η \sidecite{altenkirch2001normalization} (which, as mentioned
in \refsec{strict}, is more powerful than Smart Case for the same type), with 
the main
innovation being to evaluate into a sheaf model rather than 
the usual presheaf on the category of renamings.

\section{Preliminaries}

Before we get into the meat of the content in this report, we make a few more
general observations about \SC that motivate the coming chapters.

\subsection{Smart Case is Local Equality Reflection}

\subsubsection{Local Equality Reflection}

Recall the equality reflection rule from ETT

\begin{spec}
  reflectETT : Tm Γ (Id A t₁ t₂) → t₁ ≡ t₂
\end{spec}

If we turn this from a meta-level judgement to an object-level one, we arrive
at a syntactic construct we call ``local equality reflection''

\begin{spec}
  reflect  : Tm Γ (Id A t₁ t₂) → Tm (Γ ▷ t₁ ≡' t₂) (B [ wk ]Ty)
           → Tm Γ B
\end{spec}

This rule assumes some way of extending contexts with convertability 
assumptions (definitional equalities). Its utility comes from
the programmer not needing to manually transport over the propositional
equality |Id A t₁ t₂| manually inside |Tm (Γ ▷ t₁ ≡' t₂) (B [ wk ]Ty)|.

Typechecking dependent types with this local reflection rule is still
undecidable \sidecite{sjoberg2015programming}. The cited paper brings up
the example of reflecting the definition of the Collatz function
(in a context where |f : ℕ ⇒ 𝔹| is a variable).
\begin{spec}
Id (ℕ ⇒ 𝔹) f (ƛ n. if even? n then f (n /ℕ 2) else su (3 *ℕ n))
\end{spec}
If we accept the new definitional equality, |f| better halt on all
|ℕ|-typed inputs or |β|-reduction will run into a loop. At least for 
obviously definitionally inconsistent equations like |Id 𝔹 TT FF|, we can 
avoid reducing
terms in such contexts (if all terms are convertible, then normalisation
is unnecessary - we can just immediately return conversion evidence). 
For equations like the above though, we cannot assume inconsistency: 
without a counter-example to the Collatz conjecture, we have no way of
deriving a contradiction from its assumption.

As another example, imagine the programmer reflects a propositional
equation between two functions closed from |ℕ|s to |𝔹|s, |Id (ℕ ⇒ 𝔹) t u|.
If our type theory satisfies function extensionality, such proofs between
closed but distinct functions should still be provable, but deciding whether
two functions with infinitary domains are equal on all inputs (for any 
reasonably expressive theory\remarknote{E.g. is capable for formalising
Peano arithmetic.} is undecidable. If we reflect |t == u| for a |t| and |u|
for which there exists a closed natural number |n : ℕ| such that |t n == TT| 
and |u n == FF|, then by congruence we are in a definitionally inconsistent
context, and self-application is type-able.

\subsubsection{Indexed Pattern-matching and Forced Patterns}

\subsubsection{Recovering Decidability}

Before tackling dependently typed \SC, we will study the simpler problem of
deciding conversion for STLC terms modulo equations.

