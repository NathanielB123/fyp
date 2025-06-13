%if False
\begin{code}
{-# OPTIONS --prop --rewriting --local-confluence #-}

open import Utils renaming (_+ℕ_ to _+_)
import Relation.Binary.PropositionalEquality as EQ
open EQ.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎)

import Agda.Builtin.Equality.Rewrite

module Report.Interim.c1_introduction where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Introduction and Motivation}
\labch{introduction}

Dependent pattern matching is the common extension of pattern matching to 
dependently-typed programming languages
\sidecite[*6]{coquand1992pattern, cockx2017dependent},
where, on top of acting as syntax sugar for eliminating inductively-defined
types, in the bodies of matches, each matched-on variable ("scrutinee") is 
substituted for the corresponding pattern everywhere in the typing context.

It is this substituting that enables taking advantage of information learned
over the course of a match. This allows, for example, defining equality testing
functions that return actual evidence for the result of the test.
\sideremark[*2]{
In this report, our code snippets will generally follow Agda 
\sidecite[*11]{norell2007towards} syntax (in fact,
this entire report is written in literate Agda, available at
\url{https://github.com/NathanielB123/fyp}), but we take some liberties
when typesetting. For example, writing $\forall$s as $\Pi$s and swapping 
the equality
symbols |_≡_| and |_=_| to align with their conventional meanings
in on-paper type theory.}
% \sideblankcite[*6]{norell2007towards} \phantom{a}

\begin{example}[Boolean Equality Testing] \phantom{a}
\begin{code}
test : ∀ (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
test true   = inl refl
test false  = inr refl
\end{code}
\end{example}

\textit{Where |_≡_| is the identity type introduced with reflexivity
|refl : x ≡ x|,
|A ⊎ B| is a sum type, introduced with injections |inl : A → A ⊎ B| and 
|inr : B → A ⊎ B| and |Bool| is the type of booleans introduced with
literals |true : Bool| and |false : Bool|.}

Note that in the |test true| branch, for example,
the substitutions |true / b| and |true / b| are applied to the context,
refining the goal type to |(true ≡ true) ⊎ (true ≡ false)|, at which |inl refl| 
typechecks successfully.

In mainstream functional programming languages, it is common to allow pattern
matching not just on the direct arguments of functions, but also on intermediary
expressions (e.g. via a |case_of_| construct). Extending dependent 
pattern-matching
accordingly would have direct utility: consider this concise proof that for
any boolean function |f : Bool → Bool|, |f b ≡ f (f (f b))|:
\sideremark{This example is originally from the Agda mailing list \sidecite[*2]
{altenkirch2009smart}.}.

\begin{example}[|f b ≡ f (f (f b))|, Concisely] \phantom{a}
\labexample{bool-lemma}
\begin{spec}
bool-lemma : ∀ (f : Bool → Bool) (b : Bool) → f b ≡ f (f (f b))
bool-lemma f true   = case f true of
  true   → refl
  false  → case f false of
    true   → refl
    false  → refl
bool-lemma f false  = case f false of
  true   → case f true
    true   → refl
    false  → refl
  false  → refl
\end{spec}
\end{example}

Unfortunately, mainstream proof assistants (such as Agda) generally do not
support such a
construct\remarknote[][*-6]{Some proof assistants do allow matching on 
expressions to
some
extent via "|with|-abstractions" \sidecite[*5]{mcbride2004view, agda2024with}. 
We will cover why this feature is not quite satisfactory (including for this 
example) in \refsec{with}.}, and we are instead forced to do the 
equational reasoning manually:
\sideremark[*12]{We can shorten these equational proofs by "code golfing"
and avoiding the more readable, but also more verbose equational reasoning 
syntax provided 
by the Agda standard library \sidecite[*5]{2024eqreasoning}, but for example,
the third case reduces down to |p ∙ sym (cong f (cong f p ∙ q) ∙ q)| - still
pretty complicated! }
\begin{example}[|f b ≡ f (f (f b))|, Manually] \phantom{a}
\begin{code}
bool-lemma′  : ∀ (f : Bool → Bool) b
             → f true   ≡ true ⊎ f true   ≡ false
             → f false  ≡ true ⊎ f false  ≡ false
             → f b ≡ f (f (f b))
bool-lemma′ f true   (inl p)  q        = 
  f true
  ≡⟨ sym (cong f p) ⟩
  f (f true)
  ≡⟨ sym (cong (f ∘ f) p) ⟩
  f (f (f true)) ∎
bool-lemma′ f true   (inr p)  (inl q)  =
  f true
  ≡⟨ sym (cong f q) ⟩
  f (f false)
  ≡⟨ sym (cong (f ∘ f) p) ⟩
  f (f (f true)) ∎
bool-lemma′ f true   (inr p)  (inr q)  =
   f true
   ≡⟨ p ⟩
   false
   ≡⟨ sym q ⟩
   f false
   ≡⟨ sym (cong f q) ⟩
   f (f false)
   ≡⟨ sym (cong (f ∘ f) p) ⟩
   f (f (f true)) ∎
-- etc... (the 'false' cases are very similar)
\end{code}
%if False
\begin{code}
bool-lemma′ f false  p        (inr q)  = sym (cong f (cong f q ∙ q))
bool-lemma′ f false  (inr p)  (inl q)  = sym (cong f (cong f q ∙ p))
bool-lemma′ f false  (inl p)  (inl q)  = q ∙ sym (cong f (cong f q ∙ p) ∙ p)
\end{code}
%endif
\begin{code}
bool-lemma : ∀ (f : Bool → Bool) b → f b ≡ f (f (f b))
bool-lemma f b = bool-lemma′ f b (test (f true)) (test (f false)) 
\end{code}
\end{example}

The trickyness with supporting matching on intermediary expressions is that
there
may not exist a unique unification solution between the scrutinee and pattern.
Dependent pattern matching must modify the typing context in the branch of a
match to make the scrutinee and pattern equal, but we cannot make |f b| equal 
|true| on-the-nose by substituting individual variables (without making any 
assumptions about the behaviour of |f| on closed booleans).

This project explores type theories with local, ground\remarknote{A "ground"
equation is one which is not quantified over any variables.}, equational
assumptions:
a setting designed to enable this extended version of pattern matching.
The idea is not novel, Altenkirch et al. first investigated such 
a theory during the development of ΠΣ \sidecite{altenkirch2008pisigma,
altenkirch2010pisigma}, naming this extended
pattern-matching construct "Smart Case" \sidecite{altenkirch2011case}. 
However, this work
was never published, ΠΣ eventually moved away from Smart Case,
and both completeness and decidability (among other
metatheoretical properties) remain open.

The full benefits of Smart Case are perhaps non-obvious. To motivate
this work further, we will next elaborate on the small jump from 
extending pattern-matching in this way to a manual version
of the equality reflection rule from Extensional Type Theory (ETT).
Such a feature has
potential to simplify a huge number of equational proofs written in modern
Intensional Type Theory (ITT) based proof assistants.

\section{Equality in Type Theory and Indexed Pattern Matching}

Before proceeding, it is important to clarify our understanding of 
equality in type theory.

\sideremark[*11]{Since Martin-Löf's first characterisation of intensional type
theory \sidecite[*9]{martin1975intuitionistic}, 
propositional equality has
been extended in numerous ways (the |K| rule 
\sidecite[*8]{streicher1993investigations}, 
OTT \sidecite[*10]{altenkirch2007observational}, 
CTT \sidecite[*12]{cohen2016cubical}), but all major 
presentations retain the ability to introduce with |refl| and eliminate with 
|J| (even if such operations are no longer primitive).}
\begin{remark}[Definitional vs Propositional Equality] \phantom{a}
\labremark{defprop}

In ITT, the foundation of modern proof assistants/dependently
typed programming languages Agda \sidecite{norell2007towards}, 
Rocq \sidecite[*2.5]{rocq2024}, Lean \sidecite[*4.5]{moura2021lean},
Idris2 \sidecite[*6.5]{brady2021idris}, 
equality judgements are
split into definitional (denoted with |_=_|) and propositional (denoted with
|_≡_|).

Definitional equality (also called "conversion") judgements are made the 
meta-level, and typing relations in ITT are given with types always equated up 
to convertibility. Conversion is usually comprised of syntactic equality 
plus computation rules (β and sometimes η) but there are other 
options, which we shall examine in \refch{background}.

Propositional equality judgements, on the other hand, are made at the level
of the (object) type theory itself. i.e. |_≡_ : A → A → Set| is an
object-theory type 
constructor (forming the "identity type") and terms of type |t ≡ u| can be 
introduced with |refl : t ≡ t|
and applied by "transporting" (|transp : (P : A → Set) → x ≡ y → P x → P y|,
representing the principle of "indiscernibility of identicals").
The full dependent elimination rule for identity
types
(named axiom |J| or "path induction") allows the motive |P| to also quantify
over the identity proof itself: 
|J : ∀ (P : ∀ y → x ≡ y → Set) (p : x ≡ y) → P x refl → P y p|.

The motivation for this division is that in dependently-typed systems, types can
contain terms that perform real computation, but typechecking requires
comparing types for equality (e.g. when checking function application is
valid). To retain decidability of typechecking, while enabling programmers
to write non-trivial
equational proofs, restricting the typechecker to a decidable approximation
of equality is required.

The equality reflection rule that defines ETT is simply an equating of
propositional and definitional equality. Specifically, adding the typing rule
|Tm Γ (t ≡ u) → t == u| (read as: the existence of a proof of propositional
equality between |t| and |u| implies |t| and |u| are convertible) is sufficient
to turn an intensional type theory into an extensional one.
\end{remark}

If we consider propositional equality |t ≡ u| to be an 
inductively defined type with one canonical element |refl : x ≡ x|, it
seems reasonable to allow pattern-matching on it like other inductive types. 
Eliminating equality proofs is only really \textit{useful}\remarknote{
Assuming the user is not interested in proving equality of equality
proofs. In fact, to prevent deriving the |K| rule, one must actively
prevent matching on |t ≡ u| when |t| and |u| are convertible \cite{cockx2017dependent}.} though if the LHS and 
RHS are not already definitionally equal 
(|J′ : ∀ (P : A → Set) → x ≡ x → P x → P x| is just a fancy identity function).

This observation motivates "indexed pattern-matching": the extension to
dependent pattern matching where arbitrary expressions are admitted as 
"forced patterns", and matching on elements of the identity type is allowed
exactly when variables occuring in LHS/RHS are simultaneously matched with
forced 
patterns such that in the substituted typing context, the propositional 
equation now holds definitionally \sidecite{cockx2017dependent}. 
With this feature, one can easily prove, 
for example |b ≡ true → not b ≡ false|:

\pagebreak
\begin{example}[|b ≡ true → not b ≡ false|] \phantom{a}
\begin{code}
not : Bool → Bool
not true   = false
not false  = true

not-true : ∀ b → b ≡ true → not b ≡ false
not-true .true refl = refl
\end{code} 
\end{example}

|.pat| is Agda's notation for forced patterns. Note that we do not need to
provide any case for |b == false|; conceptually, we are making use of 
|_≡_|'s  elimination rule here, not |Bool|'s. 
Type theory implementations can actually
go one step further and infer insertion of forced matches, including
on implicit arguments (denoted with |{}| in Agda), allowing the even more
concise:

\begin{code}
not-true′ : ∀ {b} → b ≡ true → not b ≡ false
not-true′ refl = refl
\end{code}

We have effectively turned a propositional equality into a definitional one,
simply by pattern matching! The downside of course, is that this can only
work unifying both sides of the equality provides a set of single-variable
substitutions which can be turned into forced matches. If we replace |b| with
an application |f b|:
\begin{spec}
not-true′′ : ∀ {f : Bool → Bool} {b} → f b ≡ true → not (f b) ≡ false
not-true′′ refl = refl
\end{spec}
We get an error:
\begin{spec}
[SplitError.UnificationStuck]
I'm not sure if there should be a case for the constructor refl,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
  f b ≟ true
when checking that the pattern refl has type f b ≡ true
\end{spec}
The conditions where indexed pattern-matching 
fails like this are often referred to by
dependently-typed programmers as  
"green slime" \sidecite{mcbride2012polynomial}. While there are various
work-arounds (helper functions that abstract over one side of the equation with
a fresh variable, manual coercing with |subst|, defining functions as inductive
relations and inducting on the "graph" of the function 
\sidecite{mcbride2025double} etc...), they all require the programmer to
write some form of boilerplate.

\textbf{This} is what makes a principled way of
matching on general expressions so exciting (and also hints at its
difficulty\remarknote{Indeed, the fully general version of this feature is
undecidable; we will aim to find a decidable fragment.}):
a proof assistant with this feature could start inferring forced matches on 
those expressions, providing a general way to turn propositional equalities
(which typically have to be manipulated and applied manually) into
definitional ones - i.e. manually invoked equality reflection.

As an example of how manual equality reflection can simplify many 
equational proofs, we consider the simple inductive proof that |0| is a 
right-identity |_+_| on |ℕ|s.
(i.e. |n + 0 ≡ n|, where |_+_| is addition of natural numbers defined by 
recursion on the left argument), first in an informal mathematical style:

\pagebreak
\begin{theorem}[|0| is a right identity of |_+_|] \phantom{a}

In the base case, it remains to prove |0 + 0 ≡ 0|, which is true by definition
of |_+_|. 

In the inductive case, it remains to prove |(n + 1) + 0 ≡ n + 1|,
which is true by definition of |_+_| and IH.

\begin{spec}
(n + 1) + 0
≡ -- \textit{by} def |_+_| (|(n + 1) + m == (n + m) + 1|)
(n + 0) + 1
≡ -- \textit{by} inductive hypothesis (|(n + 0) ≡ n|)
n + 1     
\end{spec}
\end{theorem}

In Agda, the same proof is expressed as follows:

\begin{example}[|0| is a right identity of |ℕ , _+_| , in Agda] \phantom{a}
\begin{code}
+0 : ∀ n → n + ze ≡ n
+0 ze      = refl
+0 (su n)  = cong su (+0 n)
\end{code}
\end{example}

As Agda's definitional equality automatically unfolds ($\beta$-reduces) 
pattern-matching definitions (justified by Agda only allowing
structurally recursive definitions, so reduction must terminate), we 
do not need to explicitly appeal to the definition of |_+_|.

On the other hand, though the syntax makes it concise, we have did have to
add more detail in one part of our Agda proof here than the informal 
one. |cong su| represents that in the inductive case, we cannot apply the 
inductive hypothesis directly: we have |(n + ze) ≡ n| but need 
|su (n + ze) ≡ su n|:
we must to apply |su| to both sides. In a type theory supporting
|case_of_| expressions with inferred forced matches, this manual appeal to 
congruence of propositional equality would be unnecessary.

\begin{spec}
+0′ : Π n → n + ze ≡ n
+0′ ze      = refl
+0′ (su n)  = case +0 n of
  refl → refl
\end{spec}

The difference might seem small: indeed |case_of_| is perhaps overly 
heavyweight syntax
and so the original |+0| definition could be argued more concise, 
but soon we will examine trickier examples where 
manual equational reasoning (in the form of |cong| and, later,
|subst|) starts causing immense pain. 

\section{A Larger Example: First-order Unification}

Inspired by \sidecite{sjoberg2015programming}, we present the use-case of
a verified first-order unification algorithm for an untyped syntax containing 
variables, 
application and constants. The example is a bit involved, but we repeat it in
detail now for a few reasons:
\begin{itemize}
  \item Since the publication of this work, Agda has had a significant extension
  to its automation of equational reasoning: global |REWRITE| rules
  \sidecite{cockx2020type}, so it will be
  interesting to examine where these can and cannot help.
  \item It is just a nice example: relatively self-contained while presenting a
  strong case for improved equational automation.
  \item The results of this project are all given in terms of a type-theoretic
  (approximately MLTT) metatheory. In fact, where possible, I aim to mechanise
  proofs in Agda. Implementing first-order unification for untyped terms should
  provide a nice introduction to how correct-by-construction programs/proofs are
  written, as well as the conventions used in this report.
\end{itemize}

Before we can implement anything however, we must define our syntax. 
We shall "index" terms by the number of variables in scope (the "context"). For 
example |Tm 3| will represent a term with three different free variables 
available.

For this example, we could easily restrict ourselves to a concrete (perhaps
infinite) collection of variables, but parameterising like this 
guides our later implementation of substitutions, and lines up better with the 
syntaxes (containing binders) that we will look at later.

% ---------------------------------------------------------------------------- %
% First-order terms
% ---------------------------------------------------------------------------- %
\begin{definition}[First-Order Terms And Variables] \phantom{a} 

\labdef{terms}
Variables and terms are defined inductively:
%if False
\begin{code}
data Var : ℕ → Set
data Tm  : ℕ → Set
\end{code}
%endif
\begin{spec}
Var  : ℕ → Set
Tm   : ℕ → Set
\end{spec}
%if False
\begin{code}
variable
  Γ Δ Θ : ℕ
\end{code}
%endif
Terms themselves are easy. We have no binding constructs, so the context
stays the same in all cases:
% This remark applies to the definition of variables below but needs to be
% higher to avoid overlapping with later stuff.
\sideremark{This |Var| datatype is common in dependently-typed programming, and
is often named |Fin| for "finite set". One way to understand it is that
the indexing of |vs| ensures the context is incremented at least as many
times as the |Var| itself and |vz| asks for one extra |su| call to make this 
inequality
strict. The flexibility enabling variables to exist in contexts
larger than themselves comes from the polymorphism of |vz| (|vz : Var Δ| 
typechecks for any context |Δ ≥ 1|).}
%if False
\begin{code}
data Tm where
\end{code}
%endif
\begin{code}
  `_   : Var Γ → Tm Γ        -- Variable
  _·_  : Tm Γ → Tm Γ → Tm Γ  -- Application
  ⟨⟩   : Tm Γ                -- Constant
\end{code}
Variables are determined uniquely by an index into the context, or in other 
words, can be represented by natural numbers strictly smaller than the number of 
variables in scope.
%if False
\begin{code}
data Var where
\end{code}
%endif
\begin{code}
  vz : Var (su Γ)
  vs : Var Γ → Var (su Γ)
\end{code}
Indexed typed like |Var|/|Fin| can be justified in dependent type theories
with a propositional identity type by "Fording"
\sidecite[*2]{mcbride2000dependently}. 
e.g. for |vz| we could have instead written isomorphic signature
|vz : Δ ≡ su Γ → Var Δ| - you can have any context, as long as it is |su Γ|! 
\end{definition}
% ---------------------------------------------------------------------------- %

Unification can be defined as the task of finding a substitution (the "unifier") 
that maps the terms being unified to equal terms\remarknote{A reasonable
follow-up question here might be: what does equality on terms mean? For now,
given these are first-order terms, we 
only consider on-the-nose syntactic equality.}. It seems reasonable then, to 
define substitutions next.

There are various different approaches to defining substitutions in proof
assistants. We shall use a first-order encoding of parallel substitutions; 
that is, a list of terms, equal in length to the
context, where operationally, the variable |vz| will be mapped to the first term
in the list  the list, |vs vz| to the second and so on... 

\pagebreak
\sideremark{This encoding of
substitutions is nice for two reasons:\newline
1. Substitutions can be composed while staying canonical. i.e. unlike sequences
of single substitutions.\newline
2. Higher-order encodings of substitutions (i.e. as functions) do not scale to 
dependently-typed syntax (without "very-dependent types" 
\sidecite[*2]{hickey1996formal, altenkirch2022munchhausen})}


% ---------------------------------------------------------------------------- %
% Parallel substitutions
% ---------------------------------------------------------------------------- %
\begin{definition}{Parallel Substitions} \phantom{a}

\labdef{par-subst}
We define substitutions in terms of lists of terms |Tms|, indexed first by the
context each of the terms in the list are in, and second by the length of the
list.
%if False
\begin{code}
data Tms (Δ : ℕ) : ℕ → Set where
\end{code}
%endif
\begin{spec}
Tms : ℕ → ℕ → Set
\end{spec}
\begin{code}
  ε    : Tms Δ ze
  _,_  : Tms Δ Γ → Tm Δ → Tms Δ (su Γ)
\end{code}

Interpreted as a substitution, |Tms Δ Γ| takes terms from context |Γ| to context
|Δ|.

\begin{code}
lookup  : Var Γ  → Tms Δ Γ → Tm Δ
_[_]    : Tm Γ   → Tms Δ Γ → Tm Δ
\end{code}

Operationally, substitution is defined by recursion on the target term.

\begin{code}
lookup vz      (δ , u) = u
lookup (vs i)  (δ , u) = lookup i δ

(` i)    [ δ ] = lookup i δ
(t · u)  [ δ ] = (t [ δ ]) · (u [ δ ])
⟨⟩       [ δ ] = ⟨⟩
\end{code}
\end{definition}
% ---------------------------------------------------------------------------- %

We can now define first-order unifiers (the goal of first-order
unification).

% ---------------------------------------------------------------------------- %
% First-order Unifiers
% ---------------------------------------------------------------------------- %
\begin{definition}[First-Order Unifiers] \phantom{a}
%if False
\begin{code}
data Unifier (t : Tm Γ) (u : Tm Γ) : Set where
\end{code}
%endif
\begin{spec}
Unifier : Tm Γ → Tm Γ → Set
\end{spec}
\begin{code}
  success : ∀ (δ : Tms Γ Γ) → t [ δ ] ≡ u [ δ ] → Unifier t u
\end{code}
\end{definition}
% ---------------------------------------------------------------------------- %

\sideremark{Note that this is only a partial specification of unification. In a
perfect world, we would require evidence in the failure case that there really
is no unifier, but requiring this would add significant clutter to the
example.\newline
In fact, one could go even further: in the successful cases, our specification
allows returning to any old unifier, of which there might be many. 
One could instead aim for the minimal/ most general unifier as in 
\sidecite[*6]{martelli1982efficient}, but, again, the machinery necessary to 
prove
a particular unifier is indeed the most general one is out of the scope of this 
example.}
Unification can now be specified as a function that takes two terms and attempts
to find a unifier (using the standard |Maybe| type to deal with possible
failure):
%if False
\begin{code}
interleaved mutual
  {-# TERMINATING #-}
\end{code}
%endif
\begin{code}
  unify : (t u : Tm Γ) → Maybe (Unifier t u)
\end{code}

We now attempy to define |unify| by cases:

\begin{spec}
  unify ⟨⟩ ⟨⟩ = just (success ?0 refl)
  -- ?0 : Tms Γ Γ
\end{spec}

... and immediately hit a slight snag: |⟨⟩| is trivially equal to |⟨⟩| but we 
still need to provide a substitution. The identity substitution |id : Tms Γ Γ| 
is probably most reasonable here, and can be constructed by recursion on context 
length (|id : Tms (su Γ) (su Γ)| equals |id : Tms Γ Γ| with all variables
incremented and |` vz| appended to the end).

%if False
\begin{code}
  id  : Tms Γ Γ
  _⁺  : Tms Δ Γ → Tms (su Δ) Γ
  inc : Tm Γ → Tm (su Γ)

  inc (` i)    = ` vs i
  inc (t · u)  = inc t · inc u
  inc ⟨⟩       = ⟨⟩

  ε        ⁺ = ε
  (δ , t)  ⁺ = (δ ⁺) , inc t

  wk : Tms (su Γ) Γ
  wk = id ⁺

  id {Γ = ze}   = ε
  id {Γ = su Γ} = wk , (` vz)

  variable
    t u v : Tm Γ
    i j k : Var Γ
    δ σ   : Tms Δ Γ

  data Occurs (i : Var Γ) : Tm Γ → Set where
    eq : Occurs i (` i)
    l· : Occurs i t → Occurs i (t · u)
    ·r : Occurs i u → Occurs i (t · u)
  
  ¬Occursπ₁ : ¬ Occurs i (t · u) → ¬ Occurs i t
  ¬Occursπ₁ p q = p (l· q)

  ¬Occursπ₂ : ¬ Occurs i (t · u) → ¬ Occurs i u
  ¬Occursπ₂ p q = p (·r q)

  _≡v?_ : (i j : Var Γ) → Dec (i ≡ j)
  vz   ≡v? vz   = yes refl
  vz   ≡v? vs j = no λ ()
  vs i ≡v? vz   = no λ ()
  vs i ≡v? vs j = map-Dec (cong vs) (λ where refl → refl) (i ≡v? j)

  occurs? : (i : Var Γ) (t : Tm Γ) → Dec (Occurs i t)
  occurs? i (` j) with i ≡v? j
  ... | yes refl = yes eq
  ... | no  ¬p   = no λ where eq → ¬p refl
  occurs? i (t · u) with occurs? i t
  ... | yes p = yes (l· p)
  ... | no ¬p with occurs? i u
  ... | yes q = yes (·r q)
  ... | no ¬q = no λ where (l· p) → ¬p p
                           (·r q) → ¬q q
  occurs? i ⟨⟩      = no λ ()

  _[_↦_] : Tms Δ Γ → Var Γ → Tm Δ → Tms Δ Γ
  (δ , u) [ vz   ↦ t ] = δ , t
  (δ , u) [ vs i ↦ t ] = (δ [ i ↦ t ]) , u

  _⨾_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  ε        ⨾ σ = ε
  (δ , t)  ⨾ σ = (δ ⨾ σ) , (t [ σ ])
  
  []lookup : lookup i δ [ σ ] ≡ lookup i (δ ⨾ σ)
  []lookup {i = vz}   {δ = δ , u} = refl
  []lookup {i = vs i} {δ = δ , u} = []lookup {i = i} {δ = δ}

  [][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
  [][] {t = ` i}   = []lookup {i = i}
  [][] {t = t · u} = cong₂ _·_ ([][] {t = t}) ([][] {t = u})
  [][] {t = ⟨⟩}    = refl

  i[i↦] : lookup i (δ [ i ↦ t ]) ≡ t
  i[i↦] {i = vz}   {δ = δ , _} = refl
  i[i↦] {i = vs i} {δ = δ , _} = i[i↦] {i = i} {δ = δ}

  i[j↦] : ¬ i ≡ j → lookup i (δ [ j ↦ u ]) ≡ lookup i δ
  i[j↦] {i = vz}   {j = vz}               p = ⊥-elim (p refl)
  i[j↦] {i = vs i} {j = vz}   {δ = δ , _} p = refl
  i[j↦] {i = vz}   {j = vs j} {δ = δ , _} p = refl
  i[j↦] {i = vs i} {j = vs j} {δ = δ , _} p 
    = i[j↦] {i = i} {j = j} {δ = δ} λ where refl → p refl

  i[⁺] : inc (lookup i δ) ≡ lookup i (δ ⁺)
  i[⁺] {i = vz}   {δ = δ , t} = refl
  i[⁺] {i = vs i} {δ = δ , t} = i[⁺] {i = i} {δ = δ}

  i[id] : lookup i id ≡ (` i)
  i[id] {i = vz}   = refl
  i[id] {i = vs i} = sym (i[⁺] {i = i}) ∙ cong inc (i[id] {i = i})

  t[i↦] : ¬ (Occurs i t) → t [ id [ i ↦ u ] ] ≡ t
  t[i↦]            {t = t · u}  p 
    = cong₂ _·_ (t[i↦] (¬Occursπ₁ p)) (t[i↦] (¬Occursπ₂ p))
  t[i↦]            {t = ⟨⟩}     p = refl
  t[i↦] {i = i}    {t = ` j}    p 
    = (i[j↦] {i = j} {j = i} {δ = id} λ where refl → p eq) ∙ i[id] {i = j}

  sym-unifier : Unifier t u → Unifier u t
  sym-unifier (success δ p) = success δ (sym p)
\end{code}
%endif

\begin{code}
  unify ⟨⟩ ⟨⟩ = just (success id refl)
\end{code}

We also have a couple easy failure cases:

\begin{code}
  unify (t₁ · t₂)  ⟨⟩         = nothing
  unify ⟨⟩         (u₁ · u₂)  = nothing
\end{code}

%if False
\begin{code}
  unify (t₁ · t₂)  (` j)  = map-maybe sym-unifier (unify (` j) (t₁ · t₂))
  unify ⟨⟩ (` i)          = map-maybe sym-unifier (unify (` i) ⟨⟩)
\end{code}
%endif

A more interesting case crops up when |t| is a variable:

\begin{spec} 
  unify (` i) u = ?0
\end{spec}

To implement this |?0|, we need to perform an "occurs check" to find whether
|i| occurs in |u|.

We define variables occuring free in first-order terms inductively as:
\begin{spec}
  Occurs : Var Γ → Tm Γ → Set

  eq  : Occurs i (` i)
  l·  : Occurs i t → Occurs i (t · u)
  ·r  : Occurs i u → Occurs i (t · u)
\end{spec}

And define occurs checking itself 
|occurs? : (i : Var Γ) (t : Tm Γ) → Dec (Occurs i t)| by recursion on
terms/variables. \textit{Where |Dec A| is the type of decisions over whether
the type |A| is inhabited, introduced with |yes : A → Dec A| and
|no : ¬ A → Dec A|. Negation of a type can be encoded as a function to
the empty type |⊥|.}

We also need a way to construct substitutions in which a single variable
is replaced with a particular term:

\begin{spec}
  _[_↦_] : Tms Δ Γ → Var Γ → Tm Δ → Tms Δ Γ
  (δ , u) [ vz   ↦ t ]  = δ , t
  (δ , u) [ vs i ↦ t ]  = (δ [ i ↦ t ]) , u
\end{spec}

Now, along with the |i[i↦] : lookup i (δ [ i ↦ t ]) ≡ t| and
|t[i↦] : ¬ (Occurs i t) → t [ id [ i ↦ u ] ] ≡ t| (provable by induction
on terms, variables and substitutions), and with the help of |with|-abstractions
to match on the result of the occurs check (the limitations of this
feature vs Smart Case are detailed in \refsec{with}), we can implement this
case (if |i| does not occur in |u|, the substition |id [ i ↦ u ]| is a valid
unifier, if |u| equals |` i|, |id| is a valid unifier, otherwise unification
fails).

\begin{code}
  unify (` i) u with occurs? i u 
  ... | no   p       = just (success (id [ i ↦ u ]) (
    lookup i (id [ i ↦ u ])
    ≡⟨ i[i↦] {i = i} ⟩
    u
    ≡⟨ sym (t[i↦] p) ⟩
    u [ id [ i ↦ u ] ] ∎)) 
  ... | yes  eq      = just (success id refl)
  ... | yes  (l· _)  = nothing
  ... | yes  (·r _)  = nothing
\end{code}

Note the manual equational reasoning required to prove |id [ i ↦ u ]| is valid.
Agda's user-defined |REWRITE| rules (\refsec{rewrites}) enable turning 
|i[i↦]| into a
definitional
equation, reducing the proof to just |sym (t[i↦] p)|, but |t[i↦]| has a
pre-condition 
(|¬ (Occurs i t)|) and so cannot be turned into a global |REWRITE|.
With Smart Case, we could merely match on |i[i↦] {i = i} {δ = δ} {t = u}| and 
|t[i↦] {u = t} p|, and write the proof as |refl|.

The remaining case (ignoring swapping of arguments) is where both sides
are applications.
Here, we attempt to unify the LHSs, and
if that succeeds, unify the RHSs with the LHS-unifying substitution applied.
If this unification also succeeds, we can compose the two unifiers, and again do
some equational reasoning to prove this is a valid unifier.

We define composition of substitutions by recursion on the first:
\begin{spec}
  _⨾_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  ε        ⨾ σ = ε
  (δ , t)  ⨾ σ = (δ ⨾ σ) , (t [ σ ])
\end{spec}

And prove the composition law |[][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]| by
induction on terms, variables and substitutions. This enables us to
finish the implementation of |unify|.

\sideremark{This implementation is unfortunately not structurally recursive 
(|t₂ [ δ ]| is not structurally smaller than |t₁ · t₂|). 
For the purposes of this example,
we just assert termination, though algorithms which Agda will accept more
directly do exist \sidecite[*2]{mcbride2003first}.}
\begin{code}
  unify (t₁ · t₂) (u₁ · u₂) with unify t₁ u₁
  ... | nothing             = nothing
  ... | just (success δ p)  with unify (t₂ [ δ ]) (u₂ [ δ ])
  ... | nothing             = nothing
  ... | just (success σ q)  = just (success (δ ⨾ σ) (
    (t₁ [ δ ⨾ σ ]) · (t₂ [ δ ⨾ σ ]) 
    ≡⟨ sym (cong₂ (_·_) ([][] {t = t₁}) ([][] {t = t₂})) ⟩
    (t₁ [ δ ] [ σ ]) · (t₂ [ δ ] [ σ ]) 
    ≡⟨ cong₂ _·_ (cong _[ σ ] p) q ⟩
    (u₁ [ δ ] [ σ ]) · (u₂ [ δ ] [ σ ])
    ≡⟨ cong₂ (_·_) ([][] {t = u₁}) ([][] {t = u₂}) ⟩
    (u₁ [ δ ⨾ σ ]) · (u₂ [ δ ⨾ σ ]) ∎))
\end{code}

Manually applying congruence rules has gotten quite tedious. Smart Case
would simplify this, by enabling matching on |p|, |q| and the four
instantiations of the composition law (Smart Case cannot take care of
inferring the necessary lemmas for an equational proof, but it can 
automatically chain them together).

Agda's |REWRITE| rules are also quite effective here: turning |[][]| into
a definitional equation reduces the proof to |cong₂ _·_ (cong _[ σ ] p) q|
(its support for non-ground equations making all possible instantiations
\sideremark{
Specifically, |t [ δ ] [ σ ] [ ξ ]| could reduce via |[][]| to
|t [ (δ ⨾ σ) ⨾ ξ ]| or to |t [ δ ⨾ (σ ⨾ ξ) ]|, which are not definitionally
equal .
}
hold definitionally).
However, |[][]| alone is not confluent (and indeed Agda with
|--local-confluence| checking enabled catches this). Non-confluent sets of
|REWRITE|
rules risk breaking subject reduction \sidecite{cockx2021taming}, so
avoiding them are important.

Turning associativity of |_⨾_| (|⨾⨾ : (δ ⨾ σ) ⨾ ξ ≡ δ ⨾ (σ ⨾ ξ)|)
into a |REWRITE| simultaneously with |[][]| repairs
confluence\remarknote{Technically, we also need 
|[]lookup : lookup i δ [ σ ] ≡ lookup i (δ ⨾ σ)| but this lemma is
required to prove |[][]| anyway.}, 
but of course requires proving this additional equation that isn't
directly necessary for our result. The situation is complicated even further
when we try to combine these rewrites with |i[i↦]| (which simplified the prior
|unify| case): |lookup i (δ [ i ↦ t ]) [ σ ]| can reduce to either 
|lookup i (δ [ i ↦ t ] ⨾ σ)| (by |[]lookup|) or |t [ σ ]| (by |i[i↦]|); we
need to prove additional laws about how |_[_↦_]| and |_⨾_| interact to
resolve this. 

In general, a particular algebraic structure one may wish to work with in a
\sideremark{One could, of course, imagine a proof assistant with support for
rewrite rules that can be locally enabled/disabled, but the state-of-the-art
in this area \sidecite[*3]{komel2021meta} leaves confluence/termination checking
for future work.}
proof assistant may not have a terminating and confluent presentation of its
equations (let alone such a presentation that a conservative, automatic
checker could identify as such). Global
|REWRITE| rules force the programmer to make careful decisions as to which
laws should be made definitional |REWRITE|s and which which should be kept 
propositional.

\pagebreak
\section{One More Example: Mechanising Type Theory}
\labsec{indexed-example}

The prior section gave an example where automating congruence
\sideremark{Indeed, Lean and Rocq feature tactics for exactly these sorts
of situations \sidecite[*2]{selsam2016congruence}.}
simplifies equational reasoning. 
Cases like this admittedly still might not be fully
convincing though: couldn't we just create a small proof-generating
script (a 
"tactic") to automatically generate such congruence proofs?

The full pain of not being able to reflect propositional equality proofs into
definitional assumptions rears its head when one works with
heavily-indexed types. A common pattern (commonly known amonst dependently typed
programmers "coherence" issues or "transport hell")
is as follows:
\begin{itemize}
  \item Some operations on an indexed
  type are forced to explicitly coerce (transport) along
  propositional equations relating different index expression.
  \item Equational proofs about these operations now need to deal with
  these transports, for example, explicitly using lemmas that push them 
  inside/outside of function applications.
\end{itemize}    

This situation is especially common when mechanising type theories with
some form of type dependency - e.g. System F
\sidecite{saffrich2024intrinsically} or dependent type theory. 

For example, using the technique of \sidecite{mcbride2010outrageous} to define
dependently-typed syntax (indexed by the interpretation of types), we can
attempt to define parallel substitutions analagous to \refdef{par-subst} and
prove the composition law. 
Even in the
raw recursive definition of the operation, heavy manual equational reasoning
is required to prove type preservation.

\sideremark{The details here are mostly irrelevant. The main important
thing to note is that the terms here are indexed by context and type
(so-called "intrinsically-typed" syntax) and |subst| is Agda's syntax for
transporting along equations (necessary to make the type of the substituted
term match up with the goal).}

\begin{spec}
_[_]tm : Tm Γ A → ∀ (δ : Objs s Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧os)
var x                  [ δ ]tm = obj→tm _ (x [ δ ]v)
app {B = B} M N        [ δ ]tm 
  = subst  (λ N[] → Tm _ (B ∘ (⟦ δ ⟧os ,sub N[]))) (N [ δ ]tm≡) 
           (app (M [ δ ]tm) (N [ δ ]tm))
lam {A = A} {B = B} M  [ δ ]tm 
  = subst (Tm _)  (dcong₂⁻¹ Πsem A≡ (cong (B ∘_) 
                  (to-coe≡⁻¹ _ (δ ↑os≡ A) 
  ∙ ↑[]-helper _ A≡ ∙ cong (_ ,sub_) (sym (semvz-helper A≡)))
  ∙ []-helper B ⟦ δ ⟧os A≡)) (lam (M [ δ ↑os _ ]tm))
  where A≡ = A [ δ ]≡
\end{spec}

When attempting to prove the composition law, things get completely
out-of-hand:

\begin{spec}
[]tm-comp  : ∀ (M : Tm Γ A) (δ : Objs s Δ Γ) (σ : Objs t θ Δ) 
           → M [ δ ]tm [ σ ]tm ≡ M [ δ ∘os σ ]tm
[]tm-comp {s = s} {t = t} (var x) δ σ 
  = cong (obj→tm (max s t)) ([]v-comp x δ σ)
[]tm-comp (app M N) δ σ = app≡ refl refl refl M≡ N≡
  where  M≡ = []tm-comp M δ σ
         N≡ = []tm-comp N δ σ
[]tm-comp {s = s} {t = t} (lam {A = A} {B = B} M) δ σ 
  = sym rm-subst ∙ coes-cancel2 ∙ sym coes-cancel 
  ∙ cong  (subst (Tm _) prf) 
          (to-coe≡ _ (lam≡ refl A[]≡ B[]≡ (_∙P_ {p = refl} M[]≡ ↑[]≡)))
  where  M[]≡   =  []tm-comp M (δ ↑os _) (σ ↑os _)
         A[]≡   =  []-comp A δ σ
         B[]≡   =  cong (B ∘_) (cong ((⟦ δ ⟧os ∘ ⟦ σ ⟧os ∘ semwk _) ,sub_)  
                   (cong₂  (λ v₁ v₂ → v₁ ∘ ((⟦ σ ⟧os ∘ semwk _) ,sub v₂)) 
                           (vzo≡ {A = A [ δ ]} s) (vzo≡ {A = A [ δ ] [ σ ]} t)
                ∙  sym (vzo≡ {A = A [ δ ∘os σ ]} (max s t))  ))
         ↑[]≡   =  []tm≡ refl (refl ,≡ A[]≡) refl (erefl M) (↑∘os≡ A δ σ)
         A≡     =  A [ δ ∘os σ ]≡
         M≡     =  M [ (δ ∘os σ) ↑os _ ]tm≡
         lamM≡  =  lamsem≡ refl refl refl M≡
         prf    =  dcong₂⁻¹ Πsem A≡ (cong (B ∘_) (((δ ∘os σ) ↑os≡ A) 
                ∙  ↑[]-helper _ A≡ ∙ cong (_ ,sub_) (sym (semvz-helper A≡)))
                ∙  []-helper B ⟦ δ ∘os σ ⟧os A≡)
         Aδ≡    =  A [ δ ]≡
         prfδ   =  dcong₂⁻¹ Πsem Aδ≡ (cong (B ∘_) ((δ ↑os≡ A) 
                ∙  ↑[]-helper _ Aδ≡ 
                ∙  cong (_ ,sub_) (sym (semvz-helper Aδ≡)))
                ∙  []-helper B ⟦ δ ⟧os Aδ≡)
         
         coes-cancel   =  coe-coe _ (cong (Tm _) prf) 
                          (cong (Tm _) (Πsem≡ refl (⟦⟧T≡ refl A[]≡) B[]≡))
         coes-cancel2  =  coe-coe (lam (M  [ wkos (A [ δ ]) δ , vzo s ]tm 
                                           [ wkos (A [ δ ] [ σ ]) σ , vzo t ]tm)) 
                          (cong (Tm _ ∘ (_∘ ⟦ σ ⟧os)) prfδ) _
         rm-subst      =  subst-application′ (Tm _) (λ _ → _[ σ ]tm) prfδ
\end{spec}

Along with the huge amount of congruence reasoning, a few of the steps here
(|coes-cancel|, |coes-cancel2|, |rm-subst|) do not even correspond to 
"meaningful"\remarknote{Defining "meaningful" here as equations which do not
trivially hold on untyped syntax/after erasing transports.} laws and only
exist to move around or cancel out transports.

Experiencing this pain when mechanising type theory was a significant
motivation in my selecting the topic of this project. The development
this final example originates from is available at
\url{https://github.com/NathanielB123/dep-ty-chk/tree/trunk}.
Hopefully, Smart Case will come to the rescue.
