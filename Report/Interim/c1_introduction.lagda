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
\sidecite[*6]{coquand1992pattern}, \sidecite[*8]{cockx2017dependent},
where on top of acting as syntax sugar for eliminating inductively-defined
types, in the bodies of matches, each matched-on variable ("scrutinee") is 
substituted for the corresponding pattern everywhere in the typing context.

It is this substituting that enables taking advantage of information learned
over the course of a match. This allows, for example, defining equality testing
functions that return actual evidence of the result of the test.
\sideremark[*2]{
In this report, our code snippets will generally follow Agda 
\cite{norell2007towards} syntax (in fact,
this entire report is written in literate Agda!), but we take some liberties
when typesetting. For example, writing $\forall$s as $\Pi$s and swapping 
the equality
symbols |_≡_| and |_=_| to align with their conventional meanings
in on-paper type theory.}

\begin{example}[Boolean Equality Testing] \phantom{a}
\begin{code}
test : ∀ (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
test true   = inl refl
test false  = inr refl
\end{code}
\end{example}

Where |_≡_| is the identity type introduced with reflexivity |refl : x ≡ x| and
|A ⊎ B| is a sum type, introduced with injections |inl : A → A ⊎ B| and 
|inr : B → A ⊎ B|. 

Note that in the |test true| branch, for example,
the substitutions |true / b| and |true / b| are applied to the context,
refining the goal type to |(true ≡ true) ⊎ (true ≡ false)|, at which |inl refl| 
typechecks successfully.

In mainstream functional programming languages, it is common to allow pattern
matching not just on the direct arguments of a function, but also on arbitrary
expressions (e.g. via |case ... of ...| expressions). Extending dependent pattern-matching
accordingly would have direct utility: consider this concise proof that for
any boolean function |f : Bool → Bool|, |f b ≡ f (f (f b))|:
\sideremark{This example is originally from the Agda mailing list \cite
{altenkirch2009smart}.}.

\begin{example}[|f b ≡ f (f (f b))|, Concisely] \phantom{a}
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

Unfortunately, mainstream proof assistants generally do not support such a
construct
\remarknote{Some proof assistants do allow matching on expressions to some
extent via "|with|-abstractions" \cite{mcbride2004view}, \cite{agda2024with}. 
We will cover why this feature is not quite satisfactory (including for this 
example) in \refch{background}.}, and we are instead forced to do the 
equational reasoning manually:
\pagebreak
\phantom{a}
\sideremark{We can shorten these equational proofs via "code golfing"
instead of using the more readable equational-reasoning syntax provided 
by the Agda standard library \cite{2024eqreasoning}, but for example,
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
match so the result is kept track of, but we cannot make |f b| equal |true|
on-the-nose by substituting individual variables, without making any 
assumptions about the behaviour of |f| on closed booleans.

This project explores type theories with local ground equational assumptions,
a setting which should enable this extended version of pattern matching.
\sideremark{We will explain this connection in detail in
\refch{background}.}
The full benefits of such a theory are perhaps non-obvious, so to motivate
this work further, we note that it is a small jump from 
extending pattern-matching in this way to a local version
of the equality reflection rule from extensional type theory (ETT), which has
potential to simplify almost all equational proofs in modern intensional
type theory (ITT) based proof assistants.

Consider the simple inductive proof that |0| is a right-identity of |ℕ , _+_|
(i.e. |n + 0 ≡ n|), where |_+_| is addition of natural numbers defined by 
recursion on the left argument.

In the base case, it remains to prove |0 + 0 ≡ 0| which is true by definition
of |_+_|. In the inductive case, it remains to prove |(n + 1) + 0 ≡ n + 1|,
which can be proved via using the definition of |_+_| and the IH.

\begin{spec}
(n + 1) + 0
≡ -- \textit{by} def |_+_| (|(n + 1) + m == (n + m) + 1|)
(n + 0) + 1
≡ -- \textit{by} inductive hypothesis (|(n + 0) ≡ n|)
n + 1     
\end{spec}

Of course, in practice it is rare to articulate a proof in so much detail. In
a larger mathematical work, such a proof might be reduced to "trivial by 
induction on ℕ" or even skipped entirely.

In the Agda proof assistant, the same proof is expressed as follows:

\begin{code}
+0 : (n : ℕ) → n + ze ≡ n
+0 ze      = refl
+0 (su n)  = cong su (+0 n)
\end{code}

I think it is interesting to observe what Agda (and other ITT-based proof
assistants) are willing to automate, and what they are not. For example, we
never needed to explicitly appeal to the definition of |_+_| - these 
simplifications were entirely automatic, justified by how Agda only allows
structurally recursive definitions (so unfolding definitions until we get stuck
must terminate). In fact, this unfolding (or β-reducing) is exactly the basis
of so-called "definitional" equality.

On the other hand, though the syntax makes it concise, we have actually had to
more detailed in one place in our Agda proof here than in our mathematical one.
'cong su' represents that in the inductive case, we cannot apply the inductive
hypothesis directly: we have |(n + ze) ≡ n| but need |su (n + ze) ≡ su n| -
we need to apply |su| to both sides.

This might seem minor: the particular proof here still came out very
concisely, but soon we will move onto trickier examples where this sort of
manual equational reasoning starts causing immense pain. 




















% So one way we an phrase this introduction is that smart case is part of some
% grand effort to replicate on-paper ETT convenience in ITT proof assistants.
% I think this is a justifiable perspective, but I'm not convinced I am the
% one to justify this... I don't use ETT.

% Another way is to focus right in on the critical part of ITT: transports
% and why these are painful. I think I like this more.

- Division in type theories: extensional/intensional
Much of the recent work in type theory has examined questions about many
properties of ETT can be replicated in ITT without breaking it's core
metatheoretic properties.
% TODO: Cite OTT, CTT etc...
Such attempts at bringing ideas from ETT into the intensional world can be
crudely categorised into two camps:
- Those that focus on extending what is propositionally provable, providing
a more expressive propositional equality.
- Those that examine how to replicate the convenience of equational reasoning
  in ETT.
This work is placed sole-y in the second camp, but focusses on an aspect.




Much of the recent work in type theory has explored the question: how



% \begin{figure}[tb]
% \centering
% \includegraphics[width = 0.4\hsize]{./figures/imperial}
% \caption{Imperial College Logo. It's nice blue, and the font is quite stylish. But you can choose a different one if you don't like it.}
% \label{fig:logo}
% \end{figure}

% Figure~\ref{fig:logo} is an example of a figure. 



% TYPESETTING TODO: We need to decide on standard formatting for variables,
% constructors, reducing functions
% This can actually resolve confusion such as in "f x" is "f" a defined symbol
% or variable?

\section{Main Contributions/Aims}

This interim

This interim report begins with a few example use-cases as motivation and a
review of related work. 

After this, I give the essentially single (so far) 
technical result: strong normalisation for STLC + rewrites into closed values.
This isn't really a new result (it is a small extension over termination for 
STLC + rewrites into closed booleans, which is described as having been shown
in the canonical Smart Case reference and also more-or-less a corollary 
of SN for STLC + boolean eta rules), but I am unawhere of a similar 
presentation which focusses on the
core changes to ordinary SN proofs (specifically around retaining monotonicity
of substitution) in the literature.

I then spend a considerable amount of time looking at how to extend these ideas
towards the aim of this project: a dependently-typed theory with rewrites into 
arbitrary first-order (ground) terms. Essentially, I focus on examples, building
intuition for where I have found the theory to be tricky and discussing the
options (as I currently see them) for how to proceed.
The discussion here is obviously not yet polished, but I hope it will be
a similarly exciting journey to read along as it was directly finding these
edge-cases.

Finally, I will end with some details surrounding implementation that I have 
investigated, specifically relating to efficient ground completion (revealing
a potential exciting additional avenue on the theory-side in the process!).






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

For this example we could easily restrict ourselves to a concrete
number, or even infinite, number of variables, but parameterising like this 
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
dependently-typed syntax (without "very-dependent types" \cite{hickey1996formal} 
\cite{altenkirch2023munchhausen})}



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

We can now define the goal of first-order unifiers (the goal of first-order
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

Unification can now be specified as a function that takes two terms and attempts
to find a unifier (using the standard |Maybe| type to deal possible failure):
\sideremark{Note that this is only a partial specification of unification. In a
perfect world, we would require evidence in the failure case that there really
is no unifier, but attempting this would add significant clutter to the
example.\newline
In fact, one could go even further: in the successful cases our specification
allows returning to any old unifier, of which there might be many. 
One could instead aim for the minimal/ most general unifier as in 
\cite{martelli1982efficient}, but, again, the machinery necessary to prove
a particular unifier is indeed the most general one is out of the scope of this 
example.}
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








% So far (as of submitting this interim report) I have written a mechanised proof
% of strong normalisation of STLC + closed boolean rewrites. The main 
% contributions so far though comprise of the examples and edge-cases I have
% discovered in trying to extend these ideas towards dependent types.

% I have also started work on a proof-of-concept implementation of these ideas,
% currently comprising of a couple implementations of "ground completion" to deal
% with large sets of rewrites and an NbE evaluator for dependently-typed lambda 
% calculus, all written in Haskell.

% For next steps, my main priority is a normalisation/decidability of conversion
% proof for dependent types with some form of equational assumptions/
% local rewrites. The discussion in section ? attempts to summarise the 
% possibilities here.

% Decidability of conversion is important (critical for decidability of 
% typechecking) but it is not the be-all and end-all of the metatheoretical 
% results. I expect soundness to be relatively easy given the equational 
% pre-conditions on rewrites can exactly correspond to the relaxed conversion.
% Subject reduction is also free given our reduction rules are typed. Confluence
% is a bit more subtle but should follow easily from a proof that rewriting to 
% completion results in a confluent set of rewrites.

% On the implementation side, my main aim is a proof-of-concept typechecker with
% a few built-in type formers (...). I am interested in doing some small 
% explorations into performance: specifically comparing rewriting to completion
% and e-graphs (I have already implemented basic versions of both, but for
% proper performance testing, I should spend some time optimising and I need to
% find something to compare against). 

% Depending on how successful the metatheory work goes (i.e. if I finish early, or
% quickly hit major roadblocks) I might also look into implementation in a fork of
% the Agda proof assistent. Agda is a very large codebase, but my hope is that 
% many  existing features (such as its global REWRITE RULES) have already laid 
% much of the groundwork.


\section{One More Example: Instrinsically-typed System F}

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