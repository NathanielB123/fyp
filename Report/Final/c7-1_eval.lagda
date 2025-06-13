\setchapterpreamble[u]{\margintoc}

\chapter{Evaluation and Future Work}

The goals of this project were to build a proof-of-concept typechecker
for \SC, and to make progress on the metatheory of type theories with local
equations. Both of these were achieved to some extent, though there is
still a significant amount of work remaining
before a full implementation in a mainstream
proof assistant can be justified.

\subsubsection{\SCBool}

As demonstrated at the very start of this report (\refch{introduction})
The poof-of-concept \SCBool typechecker was successful in
at least the sense that it admits
vastly simpler proofs of some theorems
(specifically those with a heavy reliance on 
Boolean case splitting, such as |f true ≡ f (f (f true))|)
than one can write in e.g. Agda. This demonstrates the practicality of \SC
and its potential benefits to some extent.
Unfortunately, the it is also very-much specialised to Boolean 
equations, and extending beyond this without
hitting issues with subject reduction or undecidability appears challenging
(\refsec{scboolnormfail}). On the other hand, I argue that the analysis and
counter-examples here
are still a valuable contribution, especially given the lack prior work
(recall that Altenkirch
et al.'s work on \SC \sidecite{altenkirch2011case} was never published).

\sideremark{Another interesting optimisation could be to leverage
non-destructive term rewriting techniques such as
E-Graphs \cite{nelson1980techniques, willsey2021egg}
for equations between neutrals. I think destructive rewriting
is ultimately required for equations where one side is of introduction form
(so later β-reductions get unblocked), but 
conversion checking modulo equations between neutrals
can be delayed.}\sideblankcite{nelson1980techniques, willsey2021egg}

The typechecker is also written in somewhat ``naive Haskell''. De Bruijn
variables are encoded in unary form, proofs using singletons will
perform computation at runtime despite their output ultimately being
irrelevant and the data structure choices are very sub-optimal
(most glaringly, local equations are stored as a list of pairs of neutrals
and values, rather than an efficient map data structure).
Future work on optimising and exploring the
overall performance impact of supporting \SC
(e.g. comparing against ordinary |with| abstraction) would be a good idea
before rushing to implement the feature in mainstream proof assistants.

\subsubsection{\SCDef}

At the end of this project, I feel positive about the potential for
ideas from \SCDef to form the basis for future proof assistant development. 
The fact that normalisation of \SCDef terms
does not need to interleaved with completion gives a huge amount of
flexibility. Another nice advantage of the theory
is that fits nicely with the design of existing proof assistants,
including Agda\remarknote{Agda already elaborates 
|with|-abstractions to top-level definitions.}.

This was ultimately just a side-benefit, but I think top-level definitions
being able to ask for definitional equations between their arguments
(approaching a form of first-class definitional equality) is also
a quite interesting feature which could be given direct surface syntax.

There is still a lot of work to do on the metatheory though.
Our normalisation result only accounts for
reflecting Boolean equations, and relies on the existence of a completed 
term-rewriting system (TRS) associated with the set of equations
in the context. \refsec{synrestrs} describes a possible
approach to generating these, but
it restricts the set of
acceptable equations in a quite significant 
way\remarknote{Specifically, LHSs of later
equations cannot occur as subterms in prior ones. In practice, this
means that users of \SC would sometimes have to carefully order their
case splits in order to avoid destabilising previous equations.}.
Leveraging completion to justify a wider set of equations could be
exciting future work (though this would almost certainly require
proving some sort of strong normalisation result).

Before integrating
\SCDef with the core type theories of existing proof assistant,
there also needs to be additional work on analysing 
the interactions between \SCDef and a myriad of
other modern proof assistant features (e.g. global rewrite rules 
\sidecite{cockx2020type}, cubical identity 
\sidecite{cohen2016cubical}, quotient types). 
\SCDef definitions are also quite limited 
in the sense that they can only depend on prior ones - that is,
(mutually) recursive definitions are not possible. Integrating \SCDef with
with work on justifying (structurally) recursive definitions
\sidecite{abel2002recursion}, type-based termination
\sidecite{barthe2006type, knisht2024termination}
or even going further and 
elaborating uses of induction into eliminators following
\sidecite{goguen2006eliminating, cockx2018elab} 
would be important future work. It could be interesting to also examine going
even further with elaboration, following work such as
\sidecite{hofmann1995conservativity, oury2005extensionality, 
winterhalter2019eliminating} to elaborate \SCDef into a traditional intensional
type theory (without equational assumptions).

Because I had the idea for \SCDef quite
late into the project,
I did not have time to write a typechecker implementation with which
to directly demonstrate its utility.
Beyond the elaboration of case splits (which I cover in detail in
\emph{scdefsplitelab}), I expect a similar implementation to 
\SCBool (tracking neutral to value mappings during NbE) should be possible.

\subsubsection{Mechanisation and Meta-Metatheory}

Taking a more general perspective, this project
can also be seen as an exploration in studying the metatheory of type
theory from a perspective grounded in mechanisation. We have used
the proof assistant Agda as our metatheory throughout.
A hugely exciting possibility that arises from committing to this 
approach is the potential to build
correct-by-construction, type theory
implementations (i.e. verified typecheckers) \sidecite{chapman2008eat}. 
The strictified syntaxes
defined in this project cut down massively on the transport boilerplate
usually associated with such efforts, but of course these syntaxes
also heavily relied on unsafe features of Agda (\refsec{strict}).
Future work could increase the level of trust in these
mechanised proofs by leveraging the construction of 
\sidecite{kaposi2025type} to strictify substitution laws safely.

Finally, I think it is also worth reflecting on whether the focus on
(categorically-inspired)
intrinsically-typed syntax (following e.g.
\sidecite{danielsson2006formalisation, altenkirch2016type}),
as opposed to the extrinsic approach
(where typing relations are defined on untyped terms,
used in e.g. \sidecite{abel2017decidability})
was ultimately the right decision. I think the benefits of
taking a more ``semantic'' (\cite{abel2017decidability})
definition of type theory are in part demonstrated by the soundness
proofs and the presentation of normalisation by evaluation for ordinary
dependent type theory (\refsec{depnbe}), in which semantic
equivalence of terms (conversion) is preserved throughout.

However, in the case of normalisation for \SCDef 
(\refsec{normscdef}), the story gets a little
messier, with the term rewriting aspects heavily relying on syntactic
analysis of pre-neutral terms. The overall normalisation algorithm is
still sound, but individual steps do not appear to preserve conversion.
Making this rigorous requires
some quite ugly and repetitive setoid reasoning.
Future work could aim to
rectify this messiness by somehow adjusting the NbE model/algorithm
such that conversion is fully preserved
(though I am not sure how one could actually achieve this) or
by translating the argument into a theory with direct support for working
at different levels of abstraction (i.e. 2LTT
\sidecite{annenkov2023two, kovacs2024elab}). 
