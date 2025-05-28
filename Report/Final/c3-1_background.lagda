%if False
\begin{code}
{-# OPTIONS --prop --rewriting --termination-depth=10 #-}

open import Utils
module Report.Final.c13-1_background where

\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

% Background, but for real this time (not "Related Work")
\chapter{Background}
\labch{background}

\section{Agda-as-a-Metatheory}

In this report, the ambient metatheory that we will define languages and write
proofs will itself be a type theory (Agda 
\sidecite[*18]{norell2007towards, agda2024agda}, specifically).

This poses a bit of conundrum for the task of providing background: the only 
language with which we have to describe our type theories of study is itself a 
type theory. We shall take the compromise of first informally explaining the 
syntax/semantics of our metatheory (not too dissimilarly to how one might
work in an ``intuitive'' set theory without being given the ZFC
axioms), and then get more specific about how to model type theories
mathematically.

For readers already familiar with (dependent) type theory and Agda
syntax, this section is probably skippable\remarknote[][*12]{For the benefit of
readers who
\textit{are} Agda-proficient, we note that this entire report is
written in literate Agda, though we take some
liberties with the typesetting to appear closer to on-paper presentations,
writing $\forall$s as |∀|s and swapping 
the equality
symbols |_≡_| and |_=_| to align with their conventional meanings
in on-paper type theory}.

When working inside a particular type theory, we directly write both ``terms'' 
(typically denoted with the letters |t|, |u| and |v|)
and ``types'' (denoted with the letters |A|, |B|, |C|, etc.) 
Under the Curry-Howard correspondence, type theories can be semantically
understood as \curry{logics} or \howard{programming languages} with
terms as \howard{programs} or 
\curry{proofs}, and types as 
\howard{specifications} or
\curry{theorems}. Every term is unambiguously related to a single 
associated 
type\remarknote[][*16]{It is of course possible to write down a string of 
symbols 
that 
appears syntactically-similar to a term, but is not type-correct. We do not 
consider such strings to be valid terms.} (the type of that term). We denote
this relationship between terms and types with the ``|∶|'' operator, i.e.
|t ∶ A| denotes the external judgement the term |t| has type |A| (i.e.
|t ∶ A| is not an object inside the type theory).

\subsubsection{Variables and Binding}

Central to intuitive notation for type theory are the notions of ``variables'' 
and ``binding''. Intuitively, variables give us a way to name placeholders that
stand for possible terms (we call the name of a variable its ``identifier'').
Terms embed variables, but a particular variable
can only be used after it has been bound, which involves declaring its
type (syntactically, we reuse the ``|:|'' operator for denoting the types of
variables at their binding-sites, so e.g.
|x : A| denotes that the variable |x| is bound with type |A|).

Variables in type theory closely mirror their functionality in other 
\howard{programming languages}. 
From a \curry{logic} perspective, we can view variables as a way of labelling
\curry{assumptions}.

Implicitly, keeping track of which variables are ``in-scope'' (having 
been bound earlier) and their types is the ``context'', a list of variable
identifiers paired with their types. Contexts are extended via binding, but
can also be more generally mapped between using ``substitutions'': 
maps from the variables
of one context to terms inside another. 

When writing \howard{programs}/\curry{proofs} internally
to a type theory, we usually do not write contexts or substitutions directly
but, when giving examples, it will sometimes be useful to have some notation
for these concepts. We denote contexts with the letters |Γ|, |Δ|, |Θ| and
write them as (comma-separated) lists of bindings |x : A , y : B , z : C , ...|.
We denote substitutions with the letters |δ|, |σ|, |γ| and write them as lists
of ``|/|''-separated terms and variables, e.g. ``|t / x , u / y|'' denotes a
substitution where |x| is mapped to |t| and |y| is mapped to |u|.
Substitutions can applied to types or terms, replacing all embedded variables
with their repsective substitutes. We denote
the action of substitution postfix, with the substitution itself enclosed in 
``|[]|''s, i.e. |t [ u / x ]|
denotes the result of replacing all |x|s in |t| with |u|.

\subsubsection{Functions}

Aside from variables, terms and types can be constructed out of
so-called term and type ``formers''.
Arguably, the most important type former is the Π-type. |∀ (x : A) → B|, 
where |x : A| is bound inside |B|. Semantically, |∀ (x : A) → B|
represents \howard{functions} or \curry{implications} from |A| to |B|.

Term formers can be divided into introduction and elimination rules
which express how to construct and make use of (respectively) terms of that 
type.
Functions are introduced with λ-abstraction: 
|λ (x : A) → t ∶ ∀ (x : A) → B|
given |t ∶ B|, and eliminated with application, denoted by juxtaposition
|t u ∶ B [ u / x ]|\remarknote{Recall that |B [ u / x ]| denotes the result
of substituting |x| for |u| in |B|.} given
|t ∶ ∀ (x : A) → B| and |u ∶ A|. Intuitively, abstraction corresponds to
binding the ``parameters'' of a function, and application to applying a given
function to an ``argument''.

% Maybe worth saying this? Should reference some later discussion in
% the inductive types section?

% Being constructive, functions in type theory are always computable, ensured
% by construction. Non-computable functions can still be encoded as inductive
% relations.

For clarity and convenience, \howard{programs}/\curry{proofs} in our type 
theory ``Agda'' can be broken up into definitions: typed identifiers
which stand for specific terms (\howard{subprograms}/\curry{lemmas}), 
allowing them to be reused.
Syntactically, we
declare definitions to have particular types with ``|:|'' and ``implement'' them 
with ``|=|''. E.g. assuming the existence of a 
``base''\remarknote{That is, not ``parameterised'' by other types.} 
type former standing
for natural 
numbers ``|ℕ|'', we can write the identity function on |ℕ|, named |idℕ| as:

\sideremark{Note that while the |x|-variable in the type and body of |idℕ| do
semantically refer to the same |ℕ|-typed parameter, they can be given different 
identifiers.
The |∀| binds |x| in the codomain of the function type, and the |λ|
separately binds |x| in the body of the abstraction. We consider types/terms
modulo renaming of variables to be identical - ``α-equivalence''.}

\begin{code}
idℕ : ∀ (x : ℕ) → ℕ
idℕ = λ (x : ℕ) → x
\end{code}

Definitions are similar to variables, but they always stand for a single
concrete term (i.e. substitutions cannot substitute them for other terms).
When implementing definitions of function type, we can equivalently
bind variables on the LHS of the |=|, e.g.

\begin{code}
idℕ′ : ∀ (x : ℕ) → ℕ
idℕ′ x = x
\end{code}

Which evokes the usual syntax for defining functions in 
mathematics and programming (|f(x) ≡' x|), just with the parenthesis
optional and using a different equality symbol to convey directness.

\paragraph{Mixfix Notation} To break away from functions always appearing
on the left, we sometimes use Agda's support for ``mixfix'' and name 
definitions with |_|s to stand for locations of arguments. For example
additional on natural numbers can be declared |_+_ : ℕ → ℕ → ℕ|, and
afterwards used infix |x + y ∶ ℕ| when |x ∶ ℕ| and |y ∶ ℕ|.


% \subsubsection{Mixfix Notation}
% 
% One final important detail about Agda (this one entirely syntactic in nature)
% is its support for quite sophisticated user-defined syntax. When naming
% a variable or definition, Agda lets us place underscores anywhere in the
% identifier to mark places where arguments should go. For example, we can
% define the binary ``AND'' on Booleans like so:
% 
% \begin{code}
% _∧_ : 𝔹 → 𝔹 → 𝔹
% TT  ∧ _ = TT
% FF  ∧ b = b
% \end{code}
% 
% A nice example of the flexibility of this syntax is the Agda standard
% libraries equational reasoning combinators: |_≡⟨_⟩≡_|, |_≡⟨⟩_| and |∎|.
% 
% %if False
% \begin{code}
% infixr 2 step-≡′
% infixr 2 _≡⟨⟩′_
% step-≡′ = step-≡
% syntax step-≡′ x p q = x ≡⟨′ q ⟩ p
% _≡⟨⟩′_ = _≡⟨⟩_
% \end{code}
% %endif
% 
% \sideremark{To build the required proofs to advance each step here, we use
% a several identity-type combinators provided by the Agda standard library.
% Even if the details of how these work are slightly opaque, the general
% idea for how to advance each step should be clear.}
% 
% \begin{code}
% simple-proof : ∀ {x y z : 𝔹} → x ≡ y → x ≡ FF → not y ≡ TT
% simple-proof {x = x} {y = y} {z = z} p q =
%   not y
%   ≡⟨′ cong not (sym p) ⟩
%   not x 
%   ≡⟨′ cong not q ⟩
%   not FF
%   ≡⟨⟩′
%   TT ∎
% \end{code}
% 
% Because they come up so frequently, in this report, we will special-case the 
% typesetting of equational proofs to make them just a bit neater.
% 
% \begin{code}
% simple-proof′ : ∀ {x y z : 𝔹} → x ≡ y → x ≡ FF → not y ≡ TT
% simple-proof′ {x = x} {y = y} {z = z} p q =
%   not y
%   ≡⟨ cong not (sym p) ⟩≡
%   not x 
%   ≡⟨ cong not q ⟩≡
%   not FF
%   ≡⟨⟩
%   TT ∎
% \end{code}


Types can be quite descriptive, and so it is often the case that types and
terms alike are unambiguously specified by the surrounding context
(``inferable''). Taking advantage of this, we make use of a lot of ``syntactic 
sugar''.
We write |_| to stand for a term or type that is inferable. e.g. assuming 
existence of type formers |ℕ| and |Vec n| where |ℕ| denotes the type
of natural numbers, and |Vec n| the type of vectors of length |n| (where |n|
a term of type |ℕ|), we can write:

%if False
\begin{code}
postulate Vec : ℕ → Set
variable
  n : ℕ
\end{code}
%endif

\begin{code}
zeros : ∀ (n : ℕ) → Vec n

origin : Vec 3
origin = zeros _
\end{code}

Given the argument to |zeros| here clearly ought to be |3|.
Π-types and
λ-abstractions with inferable domains |∀ (x : _) → B|, |λ (x : _) → t| can
also be written without the annotation on the bound variable |∀ x → B|,
|λ x → t|. Functions where the codomain does not depend on the domain (like
e.g. |idℕ : ∀ (x : ℕ) → ℕ| above), can also be written more simply
by dropping the |∀|, |idℕ : ℕ → ℕ|.

Writing many |_|s can still get tiresome, so 
we also allow 
Π-types to implicitly bind parameters, denoted with ``|{}|''s, |∀ {x : A} → B|.
Implicit Π-types can still be introduced and eliminated explicitly with
|λ {x : A} → t| and |t {x = u}|\remarknote{Note we specify the name of the
parameter we instantiate here, (|x|). |t {u}| is also
a valid elimination-form, but only applies |u| to the very first 
implicitly-bound parameter, which is somewhat restrictive.}, but

\begin{code}
idVec : ∀ {n} → Vec n → Vec n
idVec xs = xs

origin′ : Vec 3
origin′ = idVec (zeros _)
\end{code}

Finally, writing |∀|s explicitly can also get unwieldy, so we
sometimes werite type signatures with seemingly unbound (``free'')
variables, which the assumption being that they should be implicitly
parameters.

\begin{code}
idVec′ : Vec n → Vec n
idVec′ xs = xs
\end{code}


\paragraph{Computation and Uniqueness} 

Critical to type theory is the notion of 
computation. Elimination
and introduction forms compute when adjacent in so-called β-rules. E.g.
function applications compute by replacing the bound variable with
the argument in the body. More formally, the β-rule for
Π-types is written |(λ (x : A) → t) u == t [ u / x ]|.
Dual to computation rules are ``uniqueness'' or ``extensionality'' laws
which we call η-rules. Agda features η for
Π-types, which tells us that all Π-typed terms, |t ∶ ∀ (x : A) → B|, 
are equivalent to  terms formed by λ-abstracting a fresh variable and 
applying it to |t|, i.e. |t == λ (x : A) → t x|.

\subsubsection{Universes}

In Agda, types are also ``first class'' (types are themselves
embedded in the syntax of terms).
Note that first-class types are not essential for a type theory to be 
``dependent'' (types can depend on terms via type formers that embed 
terms)\remarknote{In fact, the
type theories we shall study in this project will not
support first-class types, or even feature type variables, as the subtleties 
of such systems are generally orthogonal to the problems we shall consider}. 
This means 
that we have a ``type of types'', named |Set| and therefore can recover 
polymorphism (á la System F) by implicitly quantifying over |Set|-typed 
variables. E.g. the polymorphic identity function can be typed as
|id : ∀ {A : Set} → A → A|.

To avoid Russel-style paradoxes, type theories that embed types in terms in this
fashion also need a concept of a universe hierarchy (the term |Type| itself 
needs type, but |Type ∶ Type| is unsound \sidecite{hurkens1995simplification}). 
We refer to the Agda documentation \sidecite{agda2024universe} for details of 
how their implementation of universes works.

\subsubsection{Equality}

Equality in (intensional) type theory is quite subtle. The |_=_| above refers 
to  so-called ``definitional'' equality (or ``conversion'') which is decided 
automatically by the typechecker (types are always considered equal
up-to-conversion). We sometimes need to refer to equations that the
typechecker cannot automate, and for this we use a new type former |x ≡ y|,
called ``propositional'' equality. 
We discuss the intricacies of definitional and propositional equality in 
more depth in \refsec{equality}.

\begin{remark}[Curry Howard Breaks Down, Slightly] \phantom{a}

It is perhaps worth mentioning that while the Curry-Howard 
correspondence can be useful for intuition when learning type theory,
some types are much better understood as \curry{logical propositions} and 
others as \howard{classes of data}. E.g. the natural numbers are a very boring
\curry{proposition} given their inhabitation can be trivially proved with
|ze : ℕ|. Conversely, in most type theories |≡|-typed \howard{programs} 
always return |refl| eventually, and so cannot do much meaningful
computation\remarknote[][*-8]{Actually, computational 
interpretations of Homotopy Type Theory (HoTT) such
as Cubical Type Theory (□TT) propose an alternative perspective,
where transporting over the identity type (renamed the ``path'' type)
is a non-trivial operation. For example, paths between types
are generalised to isomorphisms (technically, ``equivalences'').}.
\end{remark} 

Propositional equality is introduced
with reflexivity, |refl ∶ x ≡ x| and can be eliminated using the principle
of identity-of-indiscernables 
|subst ∶ ∀ (P : A → Set) → x ≡ y → P x → P y|\remarknote{The full
elimination rule for identity types
(named axiom-J or ``path induction'') allows the ``motive'' |P| to also 
quantify over the identity proof itself: 
|≡-elim ∶ ∀ (P : ∀ y → x ≡ y → Set) (p : x ≡ y) → P x refl → P y p|, but
|subst| can be derived from this.
%
}.
Of course, |subst| itself must have a β-rule, |subst P refl x == x|.

Sometimes, we will take advantage of ``uniqueness of identity 
proofs'' (UIP). That is, we will consider all |≡|-typed terms to themselves
be propositionally equal. Assuming this globally is incompatible with some type 
theories (e.g. □TT), but is very convenient when working only with set-based
structures.

% TODO : Discuss |Prop| (maybe after inductive types?)

\subsubsection{Inductive Types}

Agda also contains a scheme for defining types inductively. We declare new
inductive type formers with the |data| keyword, and then inside a |where|
block, provide the introduction rules.

\begin{minipage}{0.5\textwidth}
\begin{code}
data 𝔹 : Set where
  TT  : 𝔹
  FF  : 𝔹
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{spec}
data ℕ : Set where
  ze  : ℕ
  su  : ℕ → ℕ
\end{spec}
\end{minipage}

As well as plain inductive datatypes like this, Agda also supports defining
parametric inductive types and inductive families, along with forward
declarations to enable mutual interleaving. We refer to the documentation
for the details on what is supported and the conditions that ensure inductive
types are well-founded (strictly-positive) \sidecite{agda2024data}.

Note we do not need to explicitly give an elimination rule. Inductive types
(being \textit{positive} type formers) are fully characterised by their
introduction rules (constructors). Eliminators can be derived 
mechanically by taking the displayed algebra \sidecite{kovacs2023type}
over the inductive 
type\remarknote{At least for simple inductive types. When one starts
defining inductive types mutually with each-other along with mutually recursive
functions, quotienting, mixing in coinduction etc... matters admittedly get more 
complicated \sidecite[*2]{kovacs2023complex}.
%
}. For example, the displayed
algebra over |𝔹| is a pairing of the \textit{motive} |P : 𝔹 → Set| along 
with \textit{methods} |P TT| and |P FF|, so the eliminator is written as

\begin{code}
𝔹-elim : ∀ (P : 𝔹 → Set) → P TT → P FF → ∀ b → P b
\end{code}

% TODO: Citations here?
Slightly unusually (e.g. compared to more Spartan type theories like MLTT or 
CIC, or even other type theories implemented by proof assistants like Lean or
Rocq), Agda does not actually build-in these elimination principles as
primitive. Instead, Agda's basic notion to eliminate inductive datatypes is
pattern-matching, which is syntactically restricted to the left-hand-side
of function definitions.

\begin{code}
not : 𝔹 → 𝔹
not TT  = FF
not FF  = TT
\end{code}

Note that traditional eliminators can be defined in terms of pattern-matching.

\begin{code}
𝔹-elim P Ptt Pff TT   = Ptt
𝔹-elim P Ptt Pff FF  = Pff 
\end{code}

\subsubsection{Equivalence Relations and Quotients}

Often in type theory, we will work with structures where there is some notion
of equivalence which is not merely syntactic. For example we might
define the integers as any number of applications of successor/predecessor
to zero.

\sideremark{Of course, we could pick a more ``canonical'' encoding of the 
integers, which does support syntactic equality. For example, a natural number 
magnitude paired with a Boolean sign
(being careful to avoid doubling-up on zero, e.g. by considering negative
integers to start at |-1|.).\\\\
Sticking only to structures where equality is syntactic is ultimately
untenable though. The canonical encoding of some type might be more
painful to work with in practice, or might not even exist.}

\begin{code}
data ℤ : Set where
  ze  : ℤ
  su  : ℤ → ℤ
  pr  : ℤ → ℤ
\end{code}

%if false
\begin{code}
variable 
  x y z x₁ x₂ x₃ y₁ y₂ y₃ : ℤ

infix 4 _~ℤ_
infixr 4 _∙~_
\end{code}
%endif

Syntactic equality on this datatype does not quite line up with how we might
want this type to behave. E.g. we have |¬ pr (su ze) ≡ ze|.

\begin{remark}[Proving Constructor Disjointness] \phantom{a}
\labremark{condisj}

Agda can automatically rule-out ``impossible'' pattern matches
(i.e. when no constructor is valid)
and allows us to write ``absurd'' patterns, ``|()|'', without
a RHS. This syntax effectively corresponds to using the principle of 
explosion, and relies on Agda's unification machinery
building-in a notion of constructor disjointness.

\begin{code}
pr-ze-disj : ¬ pr x ≡ ze
pr-ze-disj ()
\end{code}


This feature is merely for convenience though. In general, we can prove
\sideremark{Being able to pattern match on a term and return a |Type| relies
on a feature known as ``large elimination''. In type theories with universes,
this arises naturally from allowing the motive of an elimination 
rule/return type of a pattern matching definition to
lie in an arbitrary universe.}
disjointness of constructors by writing functions that distinguish
them, returning |⊤| or |⊥|. Then under the assumption of equality
between the two constructors, we can apply the distinguishing function
to both sides and then transport across the resulting proof of |⊥ ≡ ⊤|
to prove |⊥| from |tt|.

\begin{code}
is-pr : ℤ → Set
is-pr (pr _)  = ⊤
is-pr ze      = ⊥
is-pr (su _)  = ⊥

pr-ze-disj′ : ¬ pr x ≡ ze
pr-ze-disj′ p = subst is-pr p tt
\end{code}
\end{remark}

\begin{code}
prsu-ze : ¬ pr (su ze) ≡ ze
prsu-ze = pr-ze-disj
\end{code}

This situation can be rectified by ``quotienting''. 
Quotient inductive types allow us to define datatypes mutually with equations
we expect to hold, e.g.

\begin{spec}
data Qℤ : Set where
  ze    : Qℤ
  su    : Qℤ → Qℤ
  pr    : Qℤ → Qℤ
  prsu  : pr (su x) ≡ x
  supr  : su (pr x) ≡ x
\end{spec}

When pattern-matching on quotient types, we are forced to mutually show that our
definition is ``sound'' (i.e. it preserves congruence of propositional
equality). Syntactically, the pattern-matching definition |f| must include cases
for each equation |p : x ≡ y| 
(in the case of |Qℤ|, |prsu| and |supr|), returning a proof of |f x ≡ f y|.
 For example, we can define doubling on integers
|doubleQℤ : Qℤ → Qℤ|, accounting for |prsu| and |supr| like so:

\begin{spec}
doubleQℤ ze      = ze
doubleQℤ (su x)  = su (su (doubleℤ x))
doubleQℤ (pr x)  = pr (pr (doubleℤ x))
doubleQℤ prsu    =
  doubleQℤ (pr (su x))
  ≡⟨⟩
  pr (pr (su (su (doubleQℤ x))))
  ≡⟨ cong pr prsu ⟩≡
  pr (su (doubleQℤ x))
  ≡⟨ prsu ⟩≡
  doubleQℤ x ∎
doubleQℤ supr    = 
  doubleQℤ (su (pr x))
  ≡⟨⟩
  su (su (pr (pr (doubleQℤ x))))
  ≡⟨ cong su supr ⟩≡
  su (pr (doubleQℤ x))
  ≡⟨ supr ⟩≡
  doubleQℤ x ∎
\end{spec}

%TODO Move cubical discussion to the remark here
For technical reasons\remarknote{In short: Agda currently only supports
quotient types as a special cases of higher-inductive type (HIT)s
when using the |cubical| extension, which is incompatible with 
UIP and lacks some
useful pattern-matching automation.\\\\
Furthermore, sometimes it is actually useful to be able to reason about the
syntactic structure of objects which generally should be treated up to
equivalence. For example, which working with ``reduction'', \refsec{redconv}.
%
}, in the actual Agda mechanisation, we do not 
use quotients. We can simulate working with quotient types (at the cost of
significant boilerplate) by working explicitly with inductively-defined
equivalence relations. E.g. for |ℤ|

\begin{code}
data _~ℤ_ : ℤ → ℤ → Set where
  -- Equivalence
  rfl~ : x ~ℤ x
  sym~ : x₁ ~ℤ x₂ → x₂ ~ℤ x₁
  _∙~_ : x₁ ~ℤ x₂ → x₂ ~ℤ x₃ → x₁ ~ℤ x₃

  -- Congruence
  su : x₁ ~ℤ x₂ → su x₁ ~ℤ su x₂
  pr : x₁ ~ℤ x₂ → pr x₁ ~ℤ pr x₂

  -- Computation
  prsu : pr (su x) ~ℤ x
  supr : su (pr x) ~ℤ x
\end{code}

Using this relation, we can implement operations on |ℤ|, such as doubling,
as ordinary pattern-matching definitions, and
separately write proofs that they respect the equivalence.

\begin{code}
doubleℤ : ℤ → ℤ
doubleℤ ze      = ze
doubleℤ (su x)  = su (su (doubleℤ x))
doubleℤ (pr x)  = pr (pr (doubleℤ x))

doubleℤ~ : x₁ ~ℤ x₂ → doubleℤ x₁ ~ℤ doubleℤ x₂
doubleℤ~ rfl~          = rfl~
doubleℤ~ (sym~ x~)     = sym~ (doubleℤ~ x~)
doubleℤ~ (x~₁ ∙~ x~₂)  = doubleℤ~ x~₁ ∙~ doubleℤ~ x~₂
doubleℤ~ (su x~)       = su (su (doubleℤ~ x~))
doubleℤ~ (pr x~)       = pr (pr (doubleℤ~ x~))
doubleℤ~ prsu          = pr prsu ∙~ prsu
doubleℤ~ supr          = su supr ∙~ supr
\end{code}

Note that unlike matching on QITs, we have to explicitly account for
cases corresponding to equivalence and 
congruence\remarknote{It is not too difficult
to abstract over |rfl~|/|sym~|/|_∙~_| when mapping between equivalence 
relations, but this is not really achievable with 
congruence,
which is arguably the worse problem given
the number of congruence cases grows with the number of datatype constructors}.

Furthermore, when writing definitions/abstractions parameteric over types, 
when relevant, we must explicitly account for whether each type has an 
associated equivalence relation. A general ``design pattern'' arises here: to 
pair types with their equivalence relations in bundles called ``setoids''.
The result is sometimes described as ``setoid hell'' 
\sidecite{altenkirch2017hell} but for smaller mechanisations that stay
as concrete as possible, it can be managed.

Setoids can be turned into isomorphic QITs (in theories which support them)
by quotienting by the equivalence relation.

\begin{spec}
data _/_ (A : Set) (_~_ : A → A → Set) : Set where
  ⌜_⌝   : A → A / _~_
  quot  : ∀ {x y} → x ~ y → ⌜ x ⌝ ≡ ⌜ y ⌝
\end{spec}

Translating from QITs to setoids has been explored as part of
the work justifying Observational Type Theory (OTT), a type theory
that natively supports quotient types and UIP 
\sidecite{altenkirch1999extensional, altenkirch2019setoid, 
pujet2022observational}. We will detail the small additional complications
when translating types indexed by QITs into setoid ``fibrations'', applied to
the concrete example of a syntax for dependent type theory in 
\refsec{quotsetfibre}.
