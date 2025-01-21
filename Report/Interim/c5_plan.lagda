\setchapterpreamble[u]{\margintoc}

\chapter{Current Progress, Aims, Plan}
\labch{plan}

% If we are going to have this note, why not just move this section to the end?
Note: I put this section in the introduction because I thought it fit, but
after writing it now I realise (especially past the first paragraph) it really
does assume a lot of background only covered in \refch{background}. Skipping
this section and returning to it later is encouraged.

As of the interim report, I have collected a few examples of situations
where "smart case" is useful (most of which have been given in the
introduction chapter) and I have
mechanised a proof of strong normalisation for STLC + closed boolean rewrites
in Agda. I also have spent considerable time trying to identify a promising path
towards extending this result to dependent types (both collecting/analysing 
tricky examples, and reading up on the literature with respect to normalisation 
proofs), but I don't have anything concrete here yet.
I also have done a bit of hacking on an implementation: I have
implemented two equality saturation algorithms for first-order terms: 
one top-down (rewriting to completion) and one bottom-up (e-graphs), 
and have begun working on an NbE (Normalisation
by Evaluation) typechecker.

I think in the immediate future, focussing on implementation is a good
idea, and I don't actually think implementation is likely to be all that
difficult. Dependent pattern matching is a bit fiddly, but is also the only 
real complicated component I need to add (I plan on skipping features like
termination checking, a universe hierarchy, etc... given this just needs
to be a proof-of-concept rather than an actually usable dependently-typed
language). To extend NbE to deal with the equational assumptions, I plan on
looking up neutrals in a map from them to values when reflecting/unquoting. 
The details with adding new equational assumptions might also get a bit tricky, 
but I think iterating normalisation of every LHS/RHS with respect to
all others until a fixpoint is reached (i.e. analgously to rewriting
to completion) is reasonable.

After I have some primitive implementation, I plan on returning to the 
theory-side of the project.
I want to give extending my simply-typed proof to dependent types a shot,
though this will be non-trivial, due to how reduction and conversion in
dependent type theories are so tightly linked. e.g. spontaneously replacing a 
neutral |Bool|-typed term |t| with |true| risks breaking typeability, if |t| and
|true| not already convertible. I am hoping a definition of (non-transitive)
spontaneous conversion will be enough to deal with this, but I think the
details will be tricky.

An alternative direction could be to focus on semantic approaches to
normalisation. I currently am unsure how to justify termination of adding
new equational assumptions in this setting, but I think Altenkirch et al.'s 
work on NbE for STLC + coproducts with strict η-laws
\sidecite{altenkirch2001normalization} must have run into similar
problems, so perhaps learning some basic sheaf theory (with the help of
\sidecite{pedrot2021debunking}) will provide insight.

Outside of dependent types, I could also work more on the theory of the
simply-typed analogue. For example, building on the strong normalisation result
to mechanise a verified conversion-checker, or looking at 
confluence and completeness. I think this is likely to be easier, but perhaps
less exciting.

Beyond a simple implementation and progressing the core metatheory, I still 
believe that most of the potential extensions I listed
in the original project proposal would be exciting to look into. I think what
is actually feasible will depend heavily on what progress I can make on the
aforementioned main tasks though, so I don't think I
can make a concrete plan with respect to these yet.


% Old:

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