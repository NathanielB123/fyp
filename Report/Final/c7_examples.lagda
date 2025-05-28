% Not a real chapter. Need to sprinkle these around as appropriate.

%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils

module Report.Final.c7_examples where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

% This almost certainly won't end up a dedicated chapter, but I'm not sure
% where to put this for now...
\chapter{Examples}
\labch{eg}

% Theorem
The number of iterations to normalise a set of rewrites to closed Booleans is
not bounded with respect to the number of equations.

To show this fact, we will consider the concrete case of a pair of rewrites, and
show that we can set up examples where an arbitrarily-high number of rewrites
is required to normalise them.

Let us start with a simple pair of rewrites

\begin{spec}
x >rw TT
if x then y else a >rw TT
\end{spec}

Clearly, the LHS of the second rewrite is not fully reduced. 
|if x then y else a >rw if TT then y else a >β y|, so our normalised rewrite
set is

\begin{spec}
x >rw TT
y >rw TT
\end{spec}

Now let us instead consider the pair of rewrites

\begin{spec}
if (if x then y else a) then x else b >rw TT
if x then y else a >rw TT
\end{spec}

Now it is the LHS of the first equation that is reducible. If we apply a
rewrite followed with a β-step, we are left with |x|, getting us back to our
first pair of rewrites.

In case the pattern is not yet clear, we repeat once more, constructing
the pair of rewrites

\begin{spec}
if (if x then y else a) then x else b >rw TT
if (if (if x then y else a) then x else b) then (if x then y else a) else c >rw TT
\end{spec}

A rewrite followed by a β-step on the second equation's LHS gets us back to
|if x then y else a|. The general construction here is to repeatedly replace the
LHS of the smaller equation with |if t then u else v| where |t| is the LHS of
the larger equation, |u| is the LHS of the smaller equation, and |v| is
arbitrary. We know the other equation is of the form |t >rw TT|, so this new LHS
clearly reduces back down to |u|.

A consequence of this is that existence terminating procedure to normalise
a particular term with respect to a set of rewrites is not sufficient to justify
decidability of type checking in the presense of \textbf{smart case}. i.e.
we might hope to implement introducing new equations by simply iterating through
the equation set and reducing every equation w.r.t. all others once; however,
this does not account for how one of the rewrite's LHSs reducing might
enable further reductions in rewrites which previously appeared fully-reduced.
Normalising rewrite sets must be repeated until a fixed-point is reached.

%Not sure what to call this sort of claim
%An ``active'' equation subset is a confluent subset of in-scope equations
%which we are allowed to reduce w.r.t.
When reducing terms w.r.t. ``active'' equation subsets during
\textbf{smart case} completion, dependencies must always be included in the
active subset.

\begin{spec}
x : Bool
z : if x then Bool else (Bool → Bool) 
y : Bool
x >rw y
(if x then +1 else x) (if y then x else 0) >rw True
x >rw True
y >rw False
\end{spec}

Note that active equation subsets {x >rw True} and {y >rw False} are confluent
independently.
However, reducing |(if x then +1 else x) (if y then x else 0)| with respect
to both of these equation sets, one after the other, will produce a 
self-application.

To fix this, we need to require |x >rw y| to always be in the active set when
reducing |(if x then +1 else x) (if y then x else 0)|. This can be justified by
how typing of |(if x then +1 else x) (if y then x else 0)| depends on
|x >rw y|.

𝔹b : Bool, b >rw true ⊢ if b then 0 else 1
ℕ≡η

\begin{spec}

\end{spec}


% Theorem
\textbf{Smart case} for higher-order types is undecidable.
% TODO
% I would like to consider both functions and QITs here...

% Theorem
\textbf{Smart case} for inductive types is undecidable. We specifically
focus on the case of natural numbers and show that deciding conversion
modulo ground |ℕ| equations is undecidable.

We specifically focus on equations of the form |x ~ su (f x)|. Note first of all
that unlike |x ~ su x|, this equation cannot immediately be rejected as
impossible. For example, |x ~ su (pred x)| holds for all |x == su y|.


% TODO 
% Actually maybe |x ~ su (if (f x) then pred x else x)| could work better.


% Theorem:
Subject reduction/type preservation is non-trivial.

Consider the equation
\begin{spec}
x >rw TT
\end{spec}
and the definition
\begin{spec}
y : if x then Bool else String
\end{spec}

Then we add an equation
\begin{spec}
y >rw TT
\end{spec}


% TODO - not sure if this example is good or makes sense

This has a severe consequence: it is seemingly impossible to give an
intrinsically-typed presentation of \textbf{smart case}.


% Theorem
Let an ordered equation set be linearly-dependent if typing of later
equations only depends on prior ones.
This linear-dependency property is not stable under reduction!

Lets assume the context
\begin{spec}
Γ = [ f : 𝔹 → 𝔹
    , g : ∀ x → if (f x) then Bool else ...
    , h : ∀ x → if (f x) then Bool else ... → Bool
    , y : 𝔹
    ]
\end{spec}

Then our set of rewrites is

\begin{spec}
h y (g y) >rw TT 
f y >rw TT
g y >rw TT
\end{spec}

We now reduce the first equation using the third to get |h y TT >rw TT|, but
|TT : if (f y) then Bool else ...| depends on |f y >rw TT|, which is equation
that occurs later in the rewrite set!

% Conjecture
Let an unordered equation set be linearly-orderable if there exists an order
such that the equation set is linearly dependent.
Linear-orderability is stable under reduction.
% Proving this seems like a massive pain (and I'm not 100% sure it is even
% true), but I have struggled to find a counter-example.

% Theorem
It is always possible to order an equation set such that it is linearly 
dependent.
% TODO - not sure this is true!

g 
f 
x  

\begin{spec}
f x >rw TT
g f x >rw TT
\end{spec}



% Theorem
Let an equation set be mutually-dependent if it is impossible to assign an
ordering such that it is linearly-dependent.
There exist mutually-dependent equation sets.
% I am not actually sure whether this is true or not...

\begin{spec}
g : ∀ x → if x then 𝔹 else ... → 𝔹
f : ∀ x y → if g x y then 𝔹 else ...

y' : 

g x' y' >rw TT | ???
f x' y' >rw TT | g x' y' = TT

?1 = ?3 : 𝔹
?2 = ?4 : if ?1 then 𝔹 else ...


f 


\end{spec}

\section{Restrictions}

Disallowing inductive and higher-order types is an easy decision to start with.
Of course in practice, single equations from neutrals to functions or QIT
values are completely fine, but as soon as multiple (possibly overlapping)
equations get involved, conversion quickly becomes undecidable. In practice, I
think a reasonable implementation strategy could be to allow some of these
equations when possible, and then only fail in the case of an overlap, but
this nuanced behaviour leads to quite a complicated specification. We instead
aim to focus on fully decidable \textbf{smart case} subsets, and leave 
generalisation to more implementation-appropriate behaviour for future work.


\subsection{Equations have to be of fully concrete type}

\subsection{No overlapping LHSs}

\subsection{No forced patterns}

\subsection{Neutral equations only}



