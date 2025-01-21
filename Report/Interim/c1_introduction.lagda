%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils renaming (_+ℕ_ to _+_)
import Relation.Binary.PropositionalEquality as EQ
open EQ.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎)

module Report.Interim.c1_introduction where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Introduction and Motivation}
\labch{introduction}

Dependent pattern matching is the common extension of pattern matching to 
dependently-typed programming languages
\sidecite[*8]{coquand1992pattern}, \sidecite[*10]{cockx2017dependent},
where on top of acting as syntax sugar for eliminating inductively-defined
types, in the bodies of matches, each matched-on variable ("scrutinee") is 
substituted for the corresponding pattern everywhere in the typing context.

It is this substituting that enables taking advantage of information learned
over the course of a match. This allows, for example, defining equality testing
functions that return actual evidence of the result of the test.
\sideremark[*4]{
In this report, our code snippets will generally follow Agda 
\sidecite[*9]{norell2007towards} syntax (in fact,
this entire report is written in literate Agda!), but we take some liberties
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

Where |_≡_| is the identity type introduced with reflexivity |refl : x ≡ x|,
|A ⊎ B| is a sum type, introduced with injections |inl : A → A ⊎ B| and 
|inr : B → A ⊎ B| and |Bool| is the type of booleans introduced with
literals |true : Bool| and |false : Bool|. 

Note that in the |test true| branch, for example,
the substitutions |true / b| and |true / b| are applied to the context,
refining the goal type to |(true ≡ true) ⊎ (true ≡ false)|, at which |inl refl| 
typechecks successfully.

In mainstream functional programming languages, it is common to allow pattern
matching not just on the direct arguments of a function, but also on arbitrary
expressions (e.g. via |case_of_| expressions). Extending dependent 
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
\pagebreak
Unfortunately, mainstream proof assistants generally do not support such a
construct
\remarknote{Some proof assistants do allow matching on expressions to some
extent via "|with|-abstractions" \sidecite[*5]{mcbride2004view},
\sidecite[*7.5]{agda2024with}. 
We will cover why this feature is not quite satisfactory (including for this 
example) in \refch{background}.}, and we are instead forced to do the 
equational reasoning manually:
\sideremark[*12]{We can shorten these equational proofs by "code golfing"
and avoiding the more readable, but also more verbose equational reasoning 
syntax provided 
by the Agda standard library \sidecite[*5]{2024eqreasoning}, but for example,
the third case reduces down to |p ∙ sym (cong f (cong f p ∙ q) ∙ q)| - still
pretty complicated! }
\begin{example}[|f b ≡ f (f (f b))|, Manually] \phantom{a}
\begin{code}
bool-lemma′  : ∀ (f : Bool → Bool) (b : Bool) 
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

The trickyness with supporting matching on arbitrary expressions is that
there
may not exist a unique unification solution between the scrutinee and pattern.
Dependent pattern matching must modify the typing context in the branch of a
match to make the scrutinee and pattern equal, but we cannot make |f b| equal 
|true| on-the-nose by substituting individual variables, without making any 
assumptions about the behaviour of |f| on closed booleans.

This project explores type theories with local, ground\remarknote{A "ground"
equation is one which does not quantify over any variables.}
, equational assumptions:
a setting designed to enable this extended version of pattern matching.
The idea is not novel, Altenkirch et al. first investigated such 
a theory during the development of ΠΣ \sidecite{altenkirch2008pisigma}
\sidecite{altenkirch2010pisigma}, naming this extended
pattern-matching construct "Smart Case" \sidecite{altenkirch2011case}. 
However, this work
was never published, ΠΣ eventually moved away from Smart Case,
and both completeness and decidability (among other
metatheoretical properties) remain open.

The full benefits of Smart Case are perhaps non-obvious, so to motivate
this work further, we will next elaborate on the small jump from 
extending pattern-matching in this way to a local version
of the equality reflection rule from extensional type theory (ETT), which has
potential to simplify many equational proofs written in modern intensional
type theory (ITT) based proof assistants.

\section{Equality in Type Theory and Indexed Pattern Matching}

\begin{remark}[Definitional vs Propositional Equality] \phantom{a}

Before proceeding, it is probably important to clarify our understanding of 
equality
in type theory. In ITT (the foundation of modern proof assistants/dependently
typed programming languages Agda \sidecite{norell2007towards}, 
Rocq \sidecite[*2]{rocq2024}, Lean \sidecite[*4]{moura2021lean},
Idris2 \sidecite[*6]{brady2021idris}), 
equality judgements are
split into definitional (denoted with |_==_|) and propositional (denoted with
|_≡_|). 

Definitional equality (also called "conversion") judgements are made the 
meta-level, and typing relations in ITT are given with types always equated up 
to convertibility. Conversion is usually comprised of syntactic equality 
plus computation rules ($\beta$ and sometimes $\eta$) but there are other 
options, which we shall examine in \refch{background}.

Propositional equality judgements, on the other hand, are made at the level
of the (object) type theory itself. i.e. |_≡_ : A → A → Set| is a type 
constructor (forming the "identity type") and terms of type |t ≡ u| can be 
introduced with |refl : t ≡ t|
and eliminated with the |J| rule (|J : (P : A → Set) → x ≡ y → P x → P y|).
Since Martin-Löf's first characterisation of intensional type theory
\sidecite[*0]{martin1975intuitionistic}, 
propositional equality has
been extended in numerous ways (the |K| rule 
\sidecite[*1]{streicher1993investigations}, 
OTT \sidecite[*3]{altenkirch2007observational}, 
CTT \sidecite[*5]{cohen2016cubical}), but all major 
presentations retain the ability to introduce it with |refl| and eliminate with 
|J| (even if such operations are no longer primitive). Inspired by the homotopy 
interpretation of type theory, coercing with |J| 
is often called "transporting", and in Agda is written |subst|.

The equality reflection rule that defines ETT is simply an equating of
propositional and definitional equality. Specifically, adding the typing rule
|Tm Γ (t ≡ u) → t == u| (read as: the existence of a proof of propositional
equality between |t| and |u| implies |t| and |u| are convertible) is sufficient
to turn an intensional type theory into an extensional one.
\end{remark}

If we consider propositional equality |t ≡ u| to be an 
inductively defined type with one canonical element |refl : x ≡ x|, it
seems reasonable to allow pattern-matching on it like other inductive types. 
Eliminating equality proofs is only really \textit{useful} though 
\remarknote{Assuming the user is not interested in proving equality of equality
proofs. In fact, to prevent deriving the |K| rule (which is sometimes
desirable), one must actively
prevent matching on |t ≡ u| when |t| and |u| are convertible \cite{cockx2017dependent}.} if the LHS and 
RHS are not already definitionally equal 
(|J′ : ∀ (P : A → Set) → x ≡ x → P x → P x| is just a fancy identity function).

This observation motivates "indexed pattern-matching": the extension to
dependent pattern matching where arbitrary expressions are admitted as 
"forced patterns", and matching on elements of the identity type is allowed
exactly when variables on the LHS/RHS are simultaneously matched with forced 
patterns such that in the substituted typing context, the propositional 
equation now holds definitionally \sidecite{cockx2017dependent}. 
With this feature, one can easily prove, 
for example |b ≡ true → not b ≡ false|:

\begin{example}[b ≡ true → not b ≡ false] \phantom{a}
\begin{code}
not : Bool → Bool
not true   = false
not false  = true

not-true : ∀ b → b ≡ true → not b ≡ false
not-true .true refl = refl
\end{code} 
\end{example}

|.t| is Agda's notation for forced patterns. Note that we do not need to
provide any case for |b == false|; conceptually, we are making use of 
|_≡_|'s  elimination rule here, not |Bool|'s. 
Type theory implementations can actually
go one step further and infer insertion of forced matches, including
on implicit arguments (marked with |{}|), allowing the even more concise:

\begin{code}
not-true′ : ∀ {b} → b ≡ true → not b ≡ false
not-true′ refl = refl
\end{code}

We have effectively turned a propositional equality into a definitional one,
simply by pattern matching! The downside of course, is that this can only
work when one side of the |_≡_| is a variable. If it instead an application:
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

\textbf{This} is what makes a principled way of
matching on expressions so exciting (and also hints at it's difficulty
\remarknote{Indeed, the fully general version of this feature is
undecidable; we will aim to find a decidable fragment.}):
a proof assistant with this feature could start inferring forced matches on 
those expressions, providing a general way to turn propositional equalities
(which typically have to be manipulated and applied manually) into
definitional ones - i.e. manually invoked equality reflection.

As an example of how manual equality reflection can simplify many 
equational proofs, we consider the simple inductive proof that |0| is a 
right-identity  of |ℕ , _+_|
(i.e. |n + 0 ≡ n|), where |_+_| is addition of natural numbers defined by 
recursion on the left argument, first in a mathematical style:

\begin{theorem}[|0| is a right identity of |ℕ , _+_|] \phantom{a}

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

As Agda's definitional equality automatically unfolds/$\beta$-reduces 
pattern-matching definitions (justified by Agda only allowing
structurally recursive definitions, so unfolding must terminate), so we 
don't need to explicitly appeal to the definition of |_+_|.

On the other hand, though the syntax makes it concise, we have actually had to
add more detail in one place in our Agda proof here than in our mathematical 
one. |cong su| represents that in the inductive case, we cannot apply the 
inductive hypothesis directly: we have |(n + ze) ≡ n| but need 
|su (n + ze) ≡ su n|:
we need to apply |su| to both sides. In a type theory supporting
|case_of_| expressions with inferred forced matches, this appeal to 
congruence would be unnecessary.

\begin{spec}
+0′ : Π n → n + ze ≡ n
+0′ ze      = refl
+0′ (su n)  = case +0 n of
  refl → refl
\end{spec}

The difference might seem small: indeed |case_of_| is perhaps overly 
heavyweight syntax
and so the original |+0| definition could be argued more concise, 
but soon we will examine at trickier examples where 
manual equational reasoning (in the form of |cong| and, later,
|subst|) starts causing immense pain. 

\section{A Larger Example: First-order Unification}

Inspired by \sidecite{sjoberg2015programming}, we present the use-case of
a verified first-order unification algorithm for a syntax containing variables, 
application and constants. The example is a bit involved, but we repeat it in
detail now for a few reasons:
\begin{itemize}
  \item Since the publication of this work, Agda has had a significant extension
  to it's automation of equational reasoning: global |REWRITE| rules
  \sidecite{cockx2020type}, so it will be
  interesting to examine where these can and cannot help.
  \item It's just a nice example: relatively self-contained while presenting a
  reasonably strong case for improved equational automation.
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

For this example, we could easily restrict ourselves to a concrete (potentially
infinitate) collection of variables, but parameterising like this 
makes substitutions easier to define and lines up better with the syntaxes 
(containing binders) that we will look at later.

% ---------------------------------------------------------------------------- %
% First-order terms
% ---------------------------------------------------------------------------- %
\begin{definition}[First-Order Terms And Variables] \phantom{a} 

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
  Γ Δ : ℕ
\end{code}
%endif
Terms themselves are easy. We have no binding constructs, so the context
stays the same in all cases:
% This remark applies to the definition of variables below but needs to be
% higher to avoid overlapping with later stuff.
\sideremark{This datatype is common in dependently-typed programming, and
is often named |Fin| for "finite set". One way to understand it is that
the indexing of |vs| ensures the context is incremented at least as many
times as the |Var| and |vz| requires one extra |su| call to make this inequality
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
\end{definition}
% ---------------------------------------------------------------------------- %

Unification can be defined as the task of finding a substitution (the "unifier") 
that maps the terms being unified to equal terms\remarknote{A reasonable
follow-up question here might be: what does equality on terms mean? For now,
given these are first-order terms we 
only consider on-the-nose syntactic equality.}. It seems reasonable then, to 
define substitutions next.

There are various different approaches to defining substitutions in proof
assistants. We shall use a first-order encoding of parallel substitutions; 
that is, a list of terms, equal in length to the
context, where operationally, the variable |vz| will be mapped to the first term
in the list  the list, |vs vz| to the second and so on... 
\sideremark{This encoding of
substitutions is nice for two reasons:\newline
1. Substitutions can be composed while staying canonical. i.e. unlike sequences
of single substitutions.\newline
2. Higher-order encodings of substitutions (i.e. as functions) don't scale to 
dependently-typed syntax (without "very-dependent types" 
\sidecite[*2]{hickey1996formal, altenkirch2023munchhausen})}



% ---------------------------------------------------------------------------- %
% Parallel substitutions
% ---------------------------------------------------------------------------- %
\begin{definition}{Parallel Substitions} \phantom{a}

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
  ε   : Tms Δ ze
  _,_ : Tms Δ Γ → Tm Δ → Tms Δ (su Γ)
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
  success : (δ : Tms Γ Γ) → t [ δ ] ≡ u [ δ ] → Unifier t u
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
to find a unifier (using the standard |Maybe| type to deal possible failure):
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

  id {Γ = ze}   = ε
  id {Γ = su Γ} = (id ⁺) , (` vz)

  variable
    t u v : Tm Γ
    i j k : Var Γ

  data Occurs (i : Var Γ) : Tm Γ → Set where
    eq : Occurs i (` i)
    l· : Occurs i t → Occurs i (t · u)
    ·r : Occurs i u → Occurs i (t · u)
  
  occurs? : (i : Var Γ) (t : Tm Γ) → Dec (Occurs i t)
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
  unify (t₁ · t₂)     (` j) = {!   !}
  unify (t₁ · t₂) (u₁ · u₂) = {!   !}
  unify ⟨⟩ (` i) = {!   !}
\end{code}
%endif

A more interesting case crops up when |t| is a variable:

\begin{spec} 
  unify (` i) u = ?0
\end{spec}


Here, we need to perform an "occurs check" on |u|

\begin{code}
  unify (` i) u with occurs? i u 
  unify (` i) u  | no   p       = just (success {! !} (sym {! !}))
  unify (` i) u  | yes  eq      = just (success id refl)
  unify (` i) u  | yes  (l· _)  = nothing
  unify (` i) u  | yes  (·r _)  = nothing
\end{code}


\section{One More Example: Mechanising Type Theory}

The prior section gave an example where automating congruence simplifies
equational reasoning. Cases like this admittedly still might not be fully
convincing though: couldn't we just create a small automation script (a 
"tactic") to automatically generate such proofs?

The real pain of not being able to reflect propositional equality proofs into
definitional assumptions starts to rear it's head when one works with
heavily-indexed types. The general pattern is that as follows:
\begin{itemize}
  \item some operations on an indexed
  type |A : I → Set| are forced to explicitly coerce ("transport") along
  propositional equations relating different index expression.
  \item One now attempts to prove equations about these indexed types, and has
  to deal with explicitly shifting transports around.
\end{itemize} 