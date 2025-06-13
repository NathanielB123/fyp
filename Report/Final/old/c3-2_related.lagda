\pagebreak
\section{Decidability of Conversion}

As mentioned in \refremark{defprop}, decidability of typechecking dependent
types hinges on decidability of conversion, so this property is quite
important for type theories intended to be used as programming languages.

The standard approach to proving decidability of conversion is to define
a normalisation function (reducing terms to "normal forms"), and then
prove this procedure sound and complete. There are multiple distinct
approaches to specifying normalisation, and so we will go over the main ones.

Note that all techniques listed below rely to some extent on
defining an intermediary term-predicate by recursion on types,
showing the predicate holds for all terms by induction on syntax, and
then proving the final result by simultaneous induction on types and the
predicate (a technique
that goes by the names
"logical relations", "computability predicates" and "reducibility candidates"
in the literature). 
There are alternative approaches to showing normalisation based
purely on rewriting theory, but these have not been shown to scale to
dependent types.

\subsection{Reduction-based}

Reduction-based techniques specify normalisation in terms of reduction rules,
and normal forms as terms that cannot be reduced further.

When using a congruent small-step reduction relation (the "operational
semantics"), one can justify
termination of naively reducing with respect to it by proving the
reduction relation is well-founded. This technique is called
"strong normalisation".

\begin{definition}[Strong Normalisation] \phantom{a}

For a given reduction relation on terms |_>>_ : Tm → Tm → Set|, we can define
\sideremark{Note the reduction relation defined on untyped terms |Tm| here.
The extension to typed terms |Tm Γ A| is easy as long as reduction is
type-preserving (obeys "subject reduction").}
strong normalisation constructively in terms of the accessibility predicate
|Acc|:
%if False
\begin{code}
module SNDef (Tm : Set) (_>>_ : Tm → Tm → Set) where
  variable
    A : Set
    t : Tm
    _<_ : A → A → Set
    x : A
\end{code}
%endif
\begin{code}
  SN = ∀ t → Acc (λ u v → v >> u) t
\end{code}

Intuitively, |Acc _<_ x| is the type of trees of finite height, where each
branch
represents a step along the |_<_| relation, with |x| at the top
and the smallest elements (with respect to |_<_|) at the bottom.
Induction on |Acc| allows us to step down the tree, one layer at a time.
It is defined inductively:
\begin{spec}
Acc  : (A → A → Set) → A → Set

acc  : (∀ {y} → y < x → Acc _<_ y) → Acc _<_ x
\end{spec}

Classically, strong normalisation can be equivalently encoded as the
non-existence of infinite chains of reductions:
%if False
\begin{code}
  record ∞Chain (_<_ : A → A → Set) (x : A) : Set where
    coinductive
    field
      {next}  : A
      step    : next < x
      steps   : ∞Chain _<_ next
  open ∞Chain public
\end{code}
%endif

\begin{code}
  SN-classical = ∀ t → ¬ ∞Chain (λ u v → v >> u) t
\end{code}

Where |∞Chain| is defined coinductively:
\begin{spec}
∞Chain  : (A → A → Set) → A → Set

next    : ∞Chain _<_ x → A
step    : ∀ (c : ∞Chain _<_ x) → next c < x
steps   : ∀ (c : ∞Chain _<_ x) → ∞Chain _<_ next
\end{spec}

We can easily prove |SN → SN-classical|:
\begin{code}
  acc-¬chain : Acc _<_ x → ¬ ∞Chain _<_ x
  acc-¬chain (acc a) c = acc-¬chain (a (step c)) (steps c)

  sn-acc-class : SN → SN-classical
  sn-acc-class p t = acc-¬chain (p t)
\end{code}
\end{definition}

A downside of working with a fully congruent small-step reduction relation
is that proving confluence is non-trivial.
Furthermore, some type theories lack obvious terminating
operational semantics but 
still have decidable conversion (e.g. type theories with η-rules
or explicit substitutions \sidecite{altenkirch2009big} and potentially
type theories with a sort of impredicative strict propositions 
\sidecite{abel2020failure}). 

To handle such theories,
one can instead define a \textit{deterministic} small-step reduction relation
without congruence rules (except those that reduce scrutinees
of elimination forms), and therefore
reduces terms only up until they are neutral or introduction-rule headed.
Such a relation is known as "weak-head reduction" and justifying its
termination goes by the name "weak-head normalisation". The downside is that
weak-head normalisation alone does not imply decidability of conversion
(e.g. consider how function-typed terms |t| can be soundly η-expanded to
|ƛ (t [ wk ]) · (` vz)|, putting them into intro-headed form, without making
any "real" progress reducing anything). Conversion checking and weak-head
normalisation must be interleaved, and termination of this interleaving
must itself be proved through a logical relations argument 
\sidecite{abel2016decidability}.

Finally, normalisation can also be defined with respect to a big-step
reduction relation \sidecite{altenkirch2020big}. In fact, much of the
original work on Smart Case attacked the problem using this approach
\sidecite{altenkirch2009smart}. Representing constraint sets as
mappings from neutral terms to normalised expressions enables extending
normalisation with a step that looks up stuck neutrals in the map.

Unfortunately, problems start to occur when
defining merging of constraint sets (i.e. to justify adding new constraints
in the branches of case splits). 
As explained in \refexample{coverage}, for looking up of neutrals to work
properly, LHSs must all be kept normalised
with respect to each other. However, adding a
single new constraint might unblock multiple neutral LHSs of other constraints,
which might unblock yet more etc... so seemingly the only feasible technique to
obtain fully normalised constraint mappings is to iterate reducing all
constraints
with respect to others until a fixed-point is reached (i.e. analagously to
ground completion). 
The only technique I am aware of to show a fixed-point
like this exists
is to demonstrate that there exists some well-founded ordering on constraint
sets that continues to decrease across iterations: in other words
we appear to end up needing a small-step reduction relation anyway.

\begin{remark}[Termination of Ground Completion and E-Graphs] \phantom{a}

Rewriting-to-completion also relies on having some total order
on terms, and ensuring rewrites consistently respect it (i.e. by
reversing them when necessary). I think any
ordering that 
places closed values like |true|/|false| at the bottom and acts like
a term encompassment ordering on neutrals should be sufficient to support
Smart Case on booleans and coproducts. Rewrites to non-neutral
infinitary-typed (e.g. ℕ) terms are trickier, and I think some sort of
"occurs check" will be necessary (the rewrite |t → su t| cannot be reversed,
as we can only justify rewriting neutral terms, but it also clearly
would lead to loops if left as-is).

Note that rewriting-to-completion is not the only algorithm for
deciding equivalence modulo a set of ground equations: bottom-up techniques
such as e-graphs \sidecite{nelson1980techniques, willsey2021egg} are also
applicable. These algorithms
can be seen as extending the union-find algorithm to terms, and termination
is justified merely by the number of e-classes decreasing during
congruence-repairing iterations. 

Unfortunately, while equations between neutral terms could likely be reasonably
handled by e-graphs, rewrites targetting introduction-headed terms are trickier
as these can unblock β-reductions, so we really do need to rewrite eagerly
(instead of delaying until conversion checking).
\end{remark}

\subsection{Reduction-free Normalisation}

Normalisation does not need to specified with respect to a reduction relation.
Reduction-free (also called "semantic" or "algebraic") arguments instead treat 
syntax as an algebraic structure (e.g. a "Category with Families" or "CwF"), 
where convertible terms are indistinguishable and theorems like 
normalisation are proved by showing a particular proof-relevant logical
predicate holds for every family of equal terms
\sidecite{altenkirch1995categorical, altenkirch2017normalisation,
sterling2021normalization}.

Such an approach was used to prove normalisation for STLC with coproducts
obeying strict η \sidecite{altenkirch2001normalization} (which, as mentioned
in \refsec{coprodeta}, is more powerful than Smart Case for the same type), with 
the main
innovation being to evaluate into a sheaf model rather than 
the usual presheaf on the category of renamings.
