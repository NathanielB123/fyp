%if False
\begin{code}
{-# OPTIONS --prop --rewriting --termination-depth=10 #-}

open import Utils
module Report.Final.c2-1_background where

\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

% Background, but for real this time (not "Related Work")
\chapter{Background}
\labch{background}

\section{Agda-as-a-Metatheory}
\labsec{agdameta}

In this report, the ambient metatheory in which we will define languages and 
write proofs will itself be a type theory (Agda 
\sidecite[*18]{norell2007towards, agda2024agda}, specifically).

This poses a bit of a
conundrum for the task of providing background: to formally introduce type
theory, we must first formally introduce type theory. 
We shall take the compromise of first informally explaining the 
syntax/semantics of our metatheory (not too dissimilarly to how one might
work in an ``intuitive'' set theory without being given the ZFC
% David Davies suggestion: "specify precisely how to model type theories..."
axioms), and then look at how to model type theories
mathematically.

Readers already familiar with (dependent) type theory and Agda
syntax\remarknote[][*12]{For the benefit of
readers who
\textit{are} Agda-proficient, we also note that this entire report is
written in literate Agda, though we take some
liberties with the typesetting to appear closer to on-paper presentations,
writing $\forall$s as |∀|s and swapping 
the equality
symbols |_≡_| and |_=_| to align with their conventional meanings
in on-paper type theory} may wish to skip ahead to \labsec{stlc}.

When working inside a particular type theory, we directly write both 
\emph{terms} 
(typically denoted with the letters |t|, |u| and |v|)
and \emph{types} (denoted with the letters |A|, |B|, |C|, etc.).
Under the Curry-Howard correspondence \sidecite{howard19080formulae}, 
type theories can be seen to semantically
represent \curry{logics} or \howard{programming languages} with
terms as \howard{programs} or 
\curry{proofs}, and types as 
\howard{specifications} or
\curry{theorems}.
Because of type theory's ability to act as a \curry{logic}, we must carefully
distinguish between \emph{internal} and \emph{external} judgements: internal 
judgements are objects of the type theory itself, arising from regarding
terms as \curry{proofs}, while external judgements
are those made in a metatheory (one level up) about objects of the type theory.
One example of an ``external'' judgement is typing:
every term, |t|, is associated with a single  
type, |A|\remarknote[][*16]{It is of course possible to write down a string of 
symbols 
that 
appears syntactically-similar to a term, but is not type-correct. We do not 
consider such strings to be valid terms.}, called the type of |t|.
We denote this relationship between types and terms with the ``|∶|'' operator,
so ``||t|| has type ||A||'' is written {|t ∶ A|}.

\subsubsection{Variables and Binding}

% David Davies suggests giving an example from maths, e.g. an integral
Central to intuitive notation for type theory are the notions of 
\emph{variables} 
and \emph{binding}. Effectively, variables provide a way to name 
``placeholders''  which stand for possible terms (we call the name of a variable its 
\emph{identifier}).
Terms embed variables, but a particular variable
can only be used after it has been bound, which involves declaring its
type (syntactically, we reuse the ``|:|'' operator for denoting the types of
variables at their binding-sites, so e.g.
{|x : A|} denotes that the variable |x| is bound with type |A|).

Variables in type theory closely mirror their functionality in other 
\howard{programming languages}. 
From a \curry{logic} perspective, we can view variables as a way of labelling
\curry{assumptions}.

Keeping track of which variables are \emph{in-scope} (having 
been bound earlier) and their types is the \emph{context}: a list of variable
identifiers paired with their types. Contexts are extended via binding, but
can also be more generally mapped between using \emph{substitutions}: 
maps from the variables
of one context to terms inside another. 
% David Davies suggests again motivating via maths examples 

When writing \howard{programs}/\curry{proofs} internally
to a type theory, we usually do not write contexts or substitutions directly
but, when giving examples, it will sometimes be useful to have some notation
for these concepts. We denote contexts with the letters |Γ|, |Δ|, |Θ| and
write them as (comma-separated) lists of bindings |x : A , y : B , z : C , ...|.
We denote substitutions with the letters |δ|, |σ|, |γ| and write them as lists
of ``|/|''-separated terms and variables, e.g. ``{|t / x , u / y|}'' denotes a
substitution where |x| is mapped to |t| and |y| is mapped to |u|.
Substitutions can applied to types or terms, replacing all embedded variables
with their respective substitutes. We denote
the action of substitution postfix, with the substitution itself enclosed in 
``|[]|''s, i.e. {|t [ u / x ]|}
denotes the result of replacing all |x|s in |t| with |u|.

\subsubsection{Functions}

% David Davies suggests introducing non-dependent functions first
Aside from variables, terms and types are made up of
so-called term and type \emph{formers}\sidecite{Sometimes, in other work, 
these are also collectively called
\emph{constructors}. We reserve the term \emph{constructor} only for a subset of 
term formers,
specifically, introduction rules associated with inductive datatypes.}.
Arguably, the most important type former is the Π-type. {|∀ (x : A) → B|}, 
where |x : A| is bound inside |B|. Semantically, {|∀ (x : A) → B|}
represents \howard{functions} or \curry{implications} from |A| to |B|.

Term formers can be divided into introduction and elimination rules
which express how to construct and use terms of that 
type, respectively.
Functions are introduced with λ-abstraction: 
{|λ (x : A) → t ∶ ∀ (x : A) → B|}
given {|t ∶ B|}, and eliminated with application, denoted by juxtaposition
{|t u ∶ B [ u / x ]|}\remarknote{Recall that |B [ u / x ]| denotes the result
of substituting |x| for |u| in |B|.} given
{|t ∶ ∀ (x : A) → B|} and |u ∶ A|. Intuitively, abstraction ({|λ (x : A) → t|}) 
corresponds to
binding the \emph{parameters} of a function (here, just |x|), and 
application (|t u|) to applying a given
function (|t|) to an \emph{argument} (|u|).

% Maybe worth saying this? Should reference some later discussion in
% the inductive types section?

% Being constructive, functions in type theory are always computable, ensured
% by construction. Non-computable functions can still be encoded as inductive
% relations.

For clarity and convenience, \howard{programs}/\curry{proofs} in our metatheory 
(Agda) can be broken up into definitions: typed identifiers
which stand for specific terms (\howard{subprograms}/\curry{lemmas}), 
allowing their reuse.
Syntactically, we
declare definitions to have particular types with ``|:|'' and 
``implement'' them 
with ``|=|''. For example, assuming the existence of a 
\emph{base}\remarknote{That is, not \emph{parameterised} by other types.} 
type former standing
for natural 
numbers ``|ℕ|'', we can write the identity function on |ℕ|, named |idℕ| as:

\sideremark{Note that while the |x|-variable in the type and body of |idℕ| do
semantically refer to the same |ℕ|-typed parameter, they can be given different 
identifiers.
The |∀| binds |x| in the codomain of the function type, and the |λ|
separately binds |x| in the body of the abstraction. We consider types/terms
modulo renaming of variables to be identical - \emph{α-equivalence}.}

\begin{code}
idℕ : ∀ (x : ℕ) → ℕ
idℕ = λ (x : ℕ) → x
\end{code}

Definitions are similar to variables, but they always stand for a single
concrete term (i.e. substitutions cannot substitute them for other terms).
When implementing definitions of function type, we can equivalently
bind variables on the LHS of the |=|, such as

\begin{code}
idℕ′ : ∀ (x : ℕ) → ℕ
idℕ′ x = x
\end{code}

which evokes the usual syntax for defining functions in 
mathematics and programming, |f(x) ≡' x| (just with the parenthesis
optional and using a different equality symbol to convey directness).

% David Davies suggests moving this
\paragraph{Mixfix Notation} Some functions, such as addition of natural
numbers ($+$) are more intuitively written \emph{infix} between the two
arguments (|+ x y| vs |x + y|). Agda supports using
such notational conventions by naming definitions 
with underscores (``|_|'') to stand for the locations of arguments. For example
we can declare addition of natural numbers with {|_+_ : ℕ → ℕ → ℕ|}, and
afterwards use it infix (|x + y ∶ ℕ| when |x ∶ ℕ| and |y ∶ ℕ|),
prefix (|_+_ x y|) or even partially apply it to just the LHS or RHS
(|(x +_) y| or |(_+ y) x|).


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
(\emph{inferable}). Taking advantage of this, we make use of a lot of 
\emph{syntactic sugar}.
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

\sideremark{Of course, overusing |_|s can get confusing. They are mostly
useful in situations where we are working with relations or predicates, 
and the details with how the underlying objects are manipulated are somewhat 
irrelevant.}

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
implicitly-bound parameter, which is somewhat restrictive.}.

\begin{code}
idVec : ∀ {n} → Vec n → Vec n
idVec xs = xs

origin′ : Vec 3
origin′ = idVec (zeros _)
\end{code}

Finally, writing |∀|s explicitly can also get unwieldy, so we
sometimes rewrite type signatures with seemingly unbound (\emph{free})
variables, which the assumption being that they should be implicit
parameters of appropriate type.

\begin{code}
idVec′ : Vec n → Vec n
idVec′ xs = xs
\end{code}

\subsubsection{Computation and Uniqueness}
\labsec{compuniq}

Critical to type theory is the notion of 
computation. Elimination
and introduction forms compute when adjacent in so-called β-rules. For example,
function applications compute by replacing the bound variable with
the argument in the body. More formally, the β-rule for
Π-types is written

\begin{spec}
(λ x → t) u == t [ u / x ]
\end{spec}

Dual to computation rules are \emph{uniqueness} or \emph{extensionality} laws
which we call η-rules. Agda features η for
Π-types, which tells us that all Π-typed terms, |t ∶ ∀ (x : A) → B|, 
are equivalent to  terms formed by λ-abstracting a fresh variable and 
applying it to |t|

\begin{spec}
t == λ x → t x
\end{spec}

Some η-rules are a lot trickier to decide than others. A general rule-of-thumb
is that η-laws for \emph{negative} type formers (e.g. functions (|Π|),
pairs (|Σ|), unit (|⊤|)) are easier to work with\remarknote{Specifically,
we can delay checking of these η laws until after β-reduction, or 
alternatively can deal with them directly via NbE (\refsec{nbe}) by specialising
unquoting appropriately.\\
Note that if term-equivalence is not type-directed
(e.g. in efficient implementations, or some formalisations), η-rules for 
negative type formers can still cause trouble 
\sidecite[*2]{lennon2022eta, kovacs2025eta})}.
η-laws for \emph{positive} type formers on the other
hand (e.g. Booleans (|𝔹|), coproducts (|_+_|), 
natural numbers (|ℕ|), propositional equality (|_≡_|)) are more subtle, either
requiring significantly more complicated normalisation algorithms
\sidecite{altenkirch2001normalization} or being outright undecidable.

\subsubsection{Universes}

In Agda, types are also \emph{first-class} (types are themselves
embedded in the syntax of terms)\remarknote{Note that first-class types are not 
essential for a type theory to be 
\emph{dependent} (types can depend on terms via type formers which embed 
terms).
In fact, the
type theories we shall study in this project will not
support first-class types, or even feature type variables, as the subtleties 
of such systems are generally orthogonal to the problems we shall consider}. 
This means 
that we have a ``type of types'', named |Set| and therefore can recover 
polymorphism (á la System F
\sidecite{girard1971extension, reynolds1974towards, girard1986system}) by 
implicitly quantifying over |Set|-typed 
variables. E.g. the polymorphic identity function can be typed as

\begin{spec}
id : ∀ {A : Set} → A → A
\end{spec}

To avoid Russell-style paradoxes, type theories that embed types in terms in 
this
% David Davies suggests explaining what a universe hierarchy is, which is
% reasonable but also, do I have time?
fashion also need a concept of a universe hierarchy (the term |Type| itself 
needs type, but |Type ∶ Type| is unsound \sidecite{hurkens1995simplification}). 
We refer to the Agda documentation \sidecite{agda2024universe} for details of 
how their implementation of universes works.

\subsubsection{Equality}

% TODO: Steffen wants me to explicitly indicate that conversion is
% bi-directional
Equality in (intensional) type theory is quite subtle. The |_=_| above refers 
to  so-called \emph{definitional} equality (or \emph{conversion}) which the 
typechecker automatically decides; types are always considered equal
up-to-conversion. We sometimes need to refer to equations that the
typechecker cannot automate, and for this we use a new type former |x ≡ y|,
called \emph{propositional} equality. 
We discuss the intricacies of definitional and propositional equality in 
more depth in \refsec{equality}.

As with Π-types, propositional equality has associated introduction
and elimination rules. Specifically, |_≡_| is introduced
with reflexivity, {|refl ∶ x ≡ x|} (|x| is equal to itself) 
and can be eliminated using the principle
of \emph{indiscernibility-of-identicals}
 \remarknote{The full
elimination rule for identity types
(named axiom-J or \emph{path induction}) allows the \emph{motive} |P| to also 
quantify over the identity proof itself: 
|≡-elim ∶ ∀ (P : ∀ y → x ≡ y → Set) (p : x ≡ y) → P x refl → P y p|, but
|subst| can be derived from this.
%
} (if |x ≡ y|, intuitively we should be 
able to use terms of type |P x| in all places where |P y| is expected, as long
as we specify an appropriate |P : A → Set| and proof of |x ≡ y|).

\begin{spec}
subst ∶ ∀ (P : A → Set) → x ≡ y → P x → P y|
\end{spec}

|subst| here stands for \emph{transport}, evoking the idea of ``transporting''
objects of type |P x| along equalities |x ≡ y|.
Of course, |_≡_| must also have a β-rule, |subst P refl x == x|.
However, we do not assume the corresponding definitional (or \emph{strict}) 
η-law  as this makes
conversion (and therefore typechecking) undecidable 
\sidecite{streicher1993investigations}.

We will, however, sometimes take advantage of propositional 
\emph{uniqueness of identity proofs} (UIP). That is, we will consider all 
|≡|-typed terms to themselves
be propositionally equal, e.g. witnessed with
%if False
\begin{code}
module _ {A : Set} {x : A} where
\end{code}
%endif
\begin{code}
  uip : ∀ (p : x ≡ x) → p ≡ refl
\end{code}
Assuming UIP globally is incompatible with some type 
theories (e.g. □TT), but is very convenient when working only with set-based
structures.

\begin{remark}[Curry Howard Breaks Down, Slightly] \phantom{a}

While the Curry-Howard 
correspondence can be useful for intuition when learning type theory,
some types are much better understood as \curry{logical propositions} and 
others as \howard{classes of data}. E.g. the natural numbers are a very boring
\curry{proposition} given their inhabitation can be trivially proved with
|ze : ℕ|. Conversely, in most type theories |≡|-typed \howard{programs} 
always return |refl| eventually, and so cannot do much meaningful
computation\remarknote[][*-8]{Actually, computational 
interpretations of Homotopy Type Theory (HoTT) \sidecite[*4]{hottbook}
such
as Cubical Type Theory (□TT) \sidecite[*6]{cohen2016cubical} 
propose an alternative perspective,
where transporting over the identity type (renamed the \emph{path} type)
is a non-trivial operation. For example, paths between types
are generalised to isomorphisms (technically, \emph{equivalences}).}.
\end{remark} 

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

As well as plain inductive datatypes like these, Agda also supports defining
parametric inductive types and inductive families, along with forward
declarations to enable mutual interleaving. We refer to the documentation
for the details on what is supported and the conditions that ensure inductive
types are well-founded (namely, strict-positivity) \sidecite{agda2024data}.

Note we do not need to explicitly give an elimination rule. Inductive types
(being \textit{positive} type formers) are fully characterised by their
introduction rules (constructors). Intuitively, eliminators correspond with
induction principles, and can be derived 
mechanically by taking the displayed algebra \sidecite{kovacs2023type}
over the inductive 
type\remarknote{At least for simple inductive types. When one starts
defining inductive types mutually with each-other along with recursive
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
Slightly unusually (e.g. compared to more Spartan type theories like MLTT
\sidecite{martin1975intuitionistic} or 
CIC \sidecite{pfenning1989cic}, or even other type theories implemented by 
proof assistants like Lean \sidecite{moura2021lean} or
Rocq \sidecite{rocq2024}), Agda does not actually build-in these elimination 
principles as
primitive. Instead, Agda's basic notion to eliminate inductive datatypes is
pattern matching, which is syntactically restricted to the left-hand-side
of function definitions.

\begin{code}
not : 𝔹 → 𝔹
not TT  = FF
not FF  = TT
\end{code}

Note that traditional eliminators can be defined in terms of pattern matching.

\begin{code}
𝔹-elim P Ptt Pff TT   = Ptt
𝔹-elim P Ptt Pff FF  = Pff 
\end{code}

\subsubsection{Equivalence Relations, Quotients and Setoids}
\labsec{equivquot}

Many types have some associated notions of equivalence
which are not merely syntactic. For example we might
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
and allows us to write \emph{absurd patterns}, ``|()|'', without
a RHS. This syntax effectively corresponds to using the principle of 
explosion, and relies on Agda's unification machinery
building-in a notion of constructor disjointness.

\begin{code}
pr-ze-disj : ¬ pr x ≡ ze
pr-ze-disj ()
\end{code}


This feature is merely for convenience though. In general, we can prove
\sideremark{Being able to pattern match on a term and return a |Type| relies
on a feature known as \emph{large elimination}. In type theories with universes,
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

This situation can be rectified by quotienting. 
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

When pattern matching on quotient types, we are forced to mutually show that our
definition is \emph{sound} (i.e. it preserves congruence of propositional
equality). Syntactically, each pattern matching definition |f| defined on
|Qℤ| must include cases
for each propositional equation |p : x ≡ y| 
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
% TODO reference https://github.com/agda/agda/issues/7905 as additional
% issues with using Cubical
For technical reasons\remarknote{In short: Agda currently only supports
quotient types as a special cases of higher-inductive type (HIT)s
when using the |cubical| extension, which is incompatible with 
UIP and lacks some
useful pattern matching automation.\\\\
Furthermore, sometimes it is actually useful to be able to temporarily 
reason about the
syntactic structure of objects, even if all operations we might define should
ultimately respect the equivalence. 
For example, when working with \emph{reduction}, \refsec{redconv}.
%
}, in the actual Agda mechanisation for this project, we do not 
use quotients. We can simulate working with quotient types (at the cost of
significant boilerplate) by working explicit inductively-defined
equivalence relations. E.g. for |ℤ|

\begin{code}
data _~ℤ_ : ℤ → ℤ → Set where
  -- Equivalence
  rfl~  : x ~ℤ x
  sym~  : x₁ ~ℤ x₂ → x₂ ~ℤ x₁
  _∙~_  : x₁ ~ℤ x₂ → x₂ ~ℤ x₃ → x₁ ~ℤ x₃

  -- Congruence
  su  : x₁ ~ℤ x₂ → su x₁ ~ℤ su x₂
  pr  : x₁ ~ℤ x₂ → pr x₁ ~ℤ pr x₂

  -- Computation
  prsu  : pr (su x) ~ℤ x
  supr  : su (pr x) ~ℤ x
\end{code}

Using this relation, we can implement operations on |ℤ|, such as doubling,
as ordinary pattern matching definitions, and
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

Furthermore, when writing definitions/abstractions parametric over types, 
when relevant, we must explicitly account for whether each type has an 
associated equivalence relation. A general \emph{design pattern} arises here: 
to pair types with their equivalence relations in bundles called 
\emph{setoids}.
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
when translating types indexed by QITs into setoid \emph{fibrations} (applied 
to the concrete example of a syntax for dependent type theory) in 
\refsec{quotsetfibre}.
