%if False
\begin{code}
module Report.Interim.c3_plan where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Current Progress, Aims, Plan}
\labch{plan}

\section{Current Progress}

As of submitting this interim report, I have collected a few examples of
situations
where Smart Case is useful (most of which have been given in
\refch{introduction}) and I have
mechanised a proof of strong normalisation for STLC plus rewrites
from neutrals into closed boolean values,
in Agda (\url{https://github.com/NathanielB123/fyp/blob/main/STLC/BoolRw/StrongNorm.agda}). The idea is that this setting is the simply-typed analogue to the 
dependent type theory required to justify Smart Case on booleans.

The proof is based on András Kovacs' 
Agda translation \sidecite{kovacs2020strong} of Jean-Yves Girard's 
strong-normalisation proof for STLC in "Proofs and Types" 
\sidecite{girard1989proofs}, and features
a "spontaneous" reduction relation where
boolean-typed terms of non intro-form are allowed to be immediately
rewritten to |true| or |false| at any time,
inspired by the extended, weak reduction relation of 
\sidecite{dougherty2000equality} (denoted with "⇒"). Such a relation
is of course not confluent, but it over-approximates the "true" set of
reductions that features a convertibility (modulo the constraint set) premise
on
rewrites, and so
strong normalisation of spontaneous reduction implies strong normalisation
of the reductions we actually care about. 

In my opinion, the most interesting part of the
proof ended-up being getting around the usual requirement for reduction
to respect substitution\remarknote{Spontaneous reduction fails here as it
enables |(` i) >> true|, but applying the substitution |true / i| to both
sides results in |true >> true| which cannot be allowed if we want
reduction to be well-founded.} (i.e. |t₁ >> t₂ → t₁ [ δ ] >> t₂ [ δ ]|).
This property usually required while proving the fundamental theorem in
the case of lambda abstractions
(to go from computability of |t₁ : Tm (Γ , A) B| and
|u : Tm Γ A| to computability of |t₂ [ < u > ] : Tm Γ B| using |t₁ >> t₂|),
and can be expressed with the following diagram:

\begin{tikzcd}[scaleedge cd=1.25, sep=huge]
|t₁| \arrow[r, "|_>>_|"] \arrow[d, swap, "|_[ δ ]|"]
& |t₂| \arrow[d, "|_[ δ ]|"] \\
|t₁ [ δ ]| \arrow[r, swap, dashrightarrow, "|_>>_|"]
& |t₂ [ δ ]|
\end{tikzcd}

I solved this by dividing single-variable substitutions into ones that 
substitute
for closed boolean values (|Sub-|) and ones that do not
(|Sub+|). 
It then becomes possible to prove:
\sideremark{In the Agda mechanisiation, I generalise these lemmas to
single-substitutions applying anywhere in the context rather than only on
the first variable, but the idea is the same.}
\begin{spec}
_[_]>>+ : t₁ >> t₂ → Sub+ Δ Γ < u > → (t₁ [ < u > ]) >> (t₂ [ < u > ])
\end{spec}
and
\begin{spec}
boolsub>> : Sub- Δ Γ < b > → t₁ >>* t₁ [ < b > ] [ wk ]
\end{spec}
\textit{Where |_>>*_| is the reflexive, transitive closure of spontaneous
reduction.}

\pagebreak
Or, as a diagram:

\begin{tikzcd}[scaleedge cd=1.25, sep=huge]
|t₁ [ < b >- ]| \arrow[r, "|_[ wk ]|"]
& |t₁ [ < b >- ] [ wk ]| \\
|t₁| \arrow[u, "|_[ < b >- ]|"] 
    \arrow[ur, dashrightarrow, "|_>>*_|"]
    \arrow[r, "|_>>_|"]
    \arrow[d, swap, "|_[ < u >+ ]|"]
& |t₂| \arrow[d, "|_[ < u >+ ]|"] \\
|t₁ [ < u >+ ]| \arrow[r, swap, dashrightarrow, "|_>>_|"]
& |t₂ [ < u >+ ]|
\end{tikzcd}

And it turns out this is
sufficient to repair the proof.

I have spent some time trying to identify a promising path
towards extending this result to dependent types, but so far I don't have
anything concrete (just examples of tricky edge-cases and ideas).

Finally, I have also done a bit of hacking on implementation: I have
implemented two equality saturation algorithms for first-order terms
(\url{https://github.com/NathanielB123/fyp/blob/main/Completion.hs}): 
one top-down (rewriting to completion) and one bottom-up (e-graphs), 
and begun working on an NbE (Normalisation
by Evaluation) typechecker.

\section{The Plan}

I think in the immediate future, focusing on implementation is a good
idea, and I hope that a simple proof-of-concept will not actually be too
difficult to get working. Dependent pattern matching is fiddly, but is also the
only 
real complicated component I need to add (I plan on skipping features like
user-defined datatypes,
termination checking of recursive functions,
universe hierarchies, etc... since the purpose is merely to demonstrate
Smart Case rather than build an actually usable dependently-typed
language). To extend NbE to deal with the equational assumptions, I plan on
maintaining a map from neutrals to values and looking up neutral terms
when reflecting/unquoting. 
The details with adding new equational assumptions might also get a bit tricky, 
but I think iterating normalisation of every LHS/RHS with respect to
all others until a fixed point is reached (i.e. analagous to 
rewriting-to-completion) should be reasonable.

After I have some primitive implementation, I plan on returning to the 
theory-side of the project.
I want to give extending my simply-typed proof to dependent types a shot,
though this will be non-trivial due to how reduction and conversion in
dependent type theories are so tightly linked. e.g. spontaneously replacing a 
neutral |Bool|-typed term |t| with |true| risks breaking typeability (if |t| and
|true| not already convertible). I am hoping a definition of (non-transitive)
"spontaneous conversion" will be enough to deal with this, but I think the
details will be tricky.

An alternative direction could be to focus on semantic approaches to
normalisation. I currently am unsure how to justify termination when adding
new equational assumptions in this setting, but I think Altenkirch et al.'s 
work on NbE for STLC + coproducts with strict η-laws
\sidecite{altenkirch2001normalization} must have run into similar
problems, so perhaps learning some basic sheaf theory (maybe with the help of
\sidecite{pedrot2021debunking}) will provide insight.

Outside of dependent types, I could also work more on the theory of the
simply-typed analogue. For example, building on the strong normalisation result
to mechanise a verified conversion-checker, and/or looking into 
confluence and completeness. I think this is likely to be easier, but perhaps
less exciting.

Beyond a simple implementation and progressing the core metatheory, I still 
believe that most of the potential extensions I listed
in the original project proposal would be exciting to look into. I think what
is actually feasible will depend heavily on what progress I can make on the
aforementioned main tasks though, so I don't think I
can make a concrete plan with respect to these yet.
