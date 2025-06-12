%if False
\begin{code}
{-# OPTIONS --prop --rewriting --local-confluence #-}

open import Utils hiding (Bool-split)
import Relation.Binary.PropositionalEquality as EQ
open EQ.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎)

import Agda.Builtin.Equality.Rewrite

module Report.Final.c1-1_introduction where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Introduction}
\labch{introduction}

Dependent type theory provides a foundation for mechanised mathematics
and cutting-edge programming languages, in which the proof writer/programmer
can say what they mean with such precision that their claims
(``this theorem follows from these lemmas'', or ``this array access will
never be out of bounds'')
can be unambiguously checked by a computer implementation.

A significant boon of type-theory-based proof assistants
is their generality, being capable of scaling to
modern mathematics
\sidecite{escardo2025topology, buzzard2025flt}, and metamathematics,
including the study of new type theories
\sidecite{pujet2022observational, abel2023graded}. However, this 
generality
comes with a curse: using proof assistants often entails a significant
amount of tedium and boilerplate \sidecite{shi2025qed}.


% As proof assistants/dependently-typed programming languages increase
% in popularity, the consequences of this

% Dependently-typed languages have scaled to such challenges as
% mechanising recent (even novel) mathematics and even reasoning
% about themselves, in part due to how. As opposed to other techniques from formal
% methods such as model checking or fuzzing, automation in modern proof assistants
% is quite limited.

One significant pain-point in proof assistants is having to do
equational reasoning manually\remarknote{This gets especially egregious 
when proving properties of functions which themselves
rely on manual equational reasoning. In such situations (often referred to as
``transport hell''), we must employ
\emph{coherence} lemmas to deal with seemingly entirely bureaucratic details,
unrelated to the underlying function we actually care about e.g. 
showing that coercions (or \emph{transports}) 
can be pushed under function applications
\cite{saffrich2024intrinsically, kaposi2025type}.}
\sideblankcite{saffrich2024intrinsically, kaposi2025type}.
With a rich literature of techniques
designed to automatically decide equational theories (the \emph{word problem}),
including term rewriting \sidecite{baader1998term}, 
and E-Graphs \sidecite{nelson1980techniques, willsey2021egg}, it is 
perhaps
surprising that the capabilities of many proof assistants are
quite limited in
this area. For example, Agda and Rocq only have only recently gained global
rewrite rules \sidecite{cockx2020type, leray2024rewster}. One possible
underlying reason for this state of affairs 
is that modern proof assistants based specifically on
intensional type theory (ITT) rely on the built-in 
(\emph{definitional}) equality obeying some quite strong
properties, including decidability (so it can actually be
automated), transitivity and congruence. 
Extending definitional equality without losing any of these properties is
challenging.

%if False
\begin{code}
variable A : Set
\end{code}
%endif

For an example of where equational reasoning ``by hand'' gets tedious, 
consider the
below proof by cases that for any Boolean function, {|f ∶ Bool → Bool|},
\mbox{|f true ≡ f (f (f true))|} (we can of course also prove
{|f false ≡ f (f (f false))|, by an analagous argument).
\sideremark{This example is originally from the Agda mailing list 
\cite{altenkirch2009smart}.}\sideblankcite{altenkirch2009smart}
\begin{code}
Bool-split : ∀ b → (b ≡ true → A) → (b ≡ false → A) → A

bool-lemma : ∀ (f : Bool → Bool) → f true ≡ f (f (f true)) 
bool-lemma f 
  =  Bool-split (f true) 
     -- |f true ≡ true|
     (λ p →  f true
             ≡⟨ cong f (sym p) ⟩≡
             f (f true)
             ≡⟨ cong (λ □ → f (f □)) (sym p) ⟩≡
             f (f (f true)) ∎)
     -- |f true ≡ false|
     (λ p →  Bool-split (f false)
       -- |f false ≡ true|
       (λ q →  f true
               ≡⟨ cong f (sym q) ⟩≡
               f (f false)
               ≡⟨ cong (λ □ → f (f □)) (sym p) ⟩≡ 
               f (f (f true)) ∎)
\end{code}
\pagebreak
\sideremark{We could shorten the Agda proof here
by ``code golfing''. For example, we could swap the readable (but verbose)
equational reasoning combinators provided by the Agda standard library
\cite{2024eqreasoning}, for direct appeals to transitivity of equality
(|_∙_|). Specifically, this final case could be written as
|p ∙ sym (cong f (cong f p ∙ q) ∙ q)| - still pretty convoluted!
}\sideblankcite{2024eqreasoning}
\begin{code}
       -- |f false ≡ false|
       (λ q →  f true
               ≡⟨ p ⟩≡ 
               false
               ≡⟨ sym q ⟩≡ 
               f false
               ≡⟨ cong f (sym q) ⟩≡ 
               f (f false)
               ≡⟨ cong (λ □ → f (f □)) (sym p) ⟩≡ 
               f (f (f true)) ∎))
\end{code}

%if False
\begin{code}
Bool-split true  t f = t refl
Bool-split false t f = f refl
\end{code}
%endif

In the proof-of-concept dependent typechecker written during this project, 
the same theorem can be proved successfully with just the following proof term.

\begin{spec}
\f. sif (f TT) then Rfl else (sif (f FF) then Rfl else Rfl)
\end{spec}

Note that along with being much shorter, the proof is also conceptually
simpler. We merely split on the result of |f true| and |f false|,
and the rest is automated.

This example highlights a strong connection between local equational
assumptions and pattern matching\remarknote{Which we will analyse
in more detail in \refremark{scloceqref}}: every branch of a case split
gives rise to an equation between the ``scrutinee'' (the thing being split on)
and the ``pattern'', which the programmer might wish to take advantage of.
Connecting these two ideas is not novel -
Altenkirch et al. first investigated such 
a construct during the development of ΠΣ \sidecite{altenkirch2008pisigma,
altenkirch2010pisigma}, naming it \SC \sidecite{altenkirch2011case}. 
However, this work
was never published, ΠΣ eventually moved away from \SC,
and both completeness and decidability (among other
metatheoretical properties) remain open.

This project then, can be seen as an attempt at continuing this work. 
At risk of spoiling the conclusion early: our 
final type theory, \SCDef, will actually move away from truly local equations,
showing that we can recover most of the \emph{expressivity} of \SC while only
introducing new equations at the level of \emph{definitions}, and most of
the \emph{convenience} via \emph{elaboration}. We argue that \SCDef
has potential to serve as a basis for an implementation of \SC in 
e.g. Agda.

\begin{widepar}
On the path towards this conclusion though, we will first
investigate the problem of deciding equivalence
of simply-typed lambda calculus (STLC) 
terms modulo equations, and also spend time studying
a minimal dependent type theory featuring ``full'' \SC for Booleans,
named \SCBool.
Concretely, our contributions include:

% TODO section references everywhere!
\begin{itemize}
\item A proof of decidability of STLC modulo |β|-conversion, plus a set of
      Boolean equations (specifically, equations between |𝔹|-typed terms 
      and closed Booleans |TT|/|FF|).
\item A specification of a minimal dependently-typed language with \SC named
      \SCBool, including an appropriately-generalised notion of substitution
      to account for contexts containing equational assumptions.
\item Soundness of \SCBool, by constructing a model in Agda.
\item A typechecking algorithm for \SCBool, including a proof-of-concept
      implementation written in Haskell.
\item A specification of an alternative dependently-typed language supporting
      equational assumptions, but this time at the level of global 
      \emph{definitions}, \SCDef, along with another soundness proof.
\item Decidability of conversion for \SCDef, leveraging the technique of 
      normalisation by evaluation (NbE).
\item An elaboration algorithm from a surface language with \SC to \SCDef
      (compared to ``native'' \SC, we lose only congruence of conversion 
      over case splits). 
\end{itemize}

The formal results of this project are \emph{mostly} mechanised in Agda. 
Some holes
(corresponding to boring congruence cases)
remain in the soundness proofs, and the NbE proofs
skip over some bureaucratic details pertaining to e.g. naturality of
substitution.
\end{widepar}
