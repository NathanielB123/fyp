%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Common.Sort

module Report.Interim.chapters.introduction where
\end{code}
%endif

\chapter{Introduction}

Sidenote test \marginnote{this is a margine note}.


Reference test \sidecite{saffrich2024intrinsically}.


Yeow \sideremark{Test! }

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

\section{Main Contributions}

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






\section{A first example: first-order unification}

Following \sidecite{Z}

















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

\section{Dependent Pattern Matching and LHS Unification}

Proof assistents like Agda that feature both metavariables and dependent pattern
matching benefit from using two different unification algorithms 
[norell2007towards]: One often referred to as "RHS unification" 
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







