%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils hiding (Fin; _+ℕ_)
module Report.Final.c3-1_related where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Related Work}
\labch{related}

\section{Dependent Pattern Matching}
\labsec{deppatmatch}

Pattern matching in simply-typed languages (assuming a structural restriction
on recursive calls) can be viewed as syntax sugar for
using recursion principles. For example, addition of natural numbers
can be defined alternatively by pattern matching or |ℕ|'s recursor,
|ℕ-rec|:

%if False
\begin{code}
variable 
  n m : ℕ
  A B : Set
\end{code}
%endif

\begin{minipage}{0.425\textwidth}
\begin{code}
_+ℕ_ : ℕ → ℕ → ℕ
ze    +ℕ m = m
su n  +ℕ m = su (n +ℕ m)
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{code}
ℕ-rec : ℕ → A → (A → A) → A

_+ℕ′_ : ℕ → ℕ → ℕ
n +ℕ′ m = ℕ-rec n m su
\end{code}
\end{minipage}

In dependently-typed languages, we are not limited to only recursion principles
though. Dependently-typed eliminators can perform \emph{induction},
enabling, for example, the inductive proof that |ze| is a right identity of
|_+ℕ_|.

\begin{code}
ℕ-elim  : ∀ (P : ℕ → Set) (n : ℕ) 
        → P ze → (∀ {k} → P k → P (su k)) → P n

+ze : n +ℕ ze ≡ n
+ze {n = n} = ℕ-elim (λ n′ → n′ +ℕ ze ≡ n′) n refl (cong su)
\end{code}

\emph{Dependent} pattern matching is the extension of pattern matching to 
dependently-typed programming languages
\sidecite{coquand1992pattern, cockx2017dependent}, supporting such 
inductive definitions.
The key idea is, in the bodies of matches, to substitute each matched-on 
variable 
(``scrutinee'') for the corresponding pattern everywhere in the typing context.
For example, we can again prove |+ze|, this time by pattern matching:

\begin{code}
+ze′ : n +ℕ ze ≡ n
+ze′ {n = ze}    = refl
+ze′ {n = su n}  = cong su (+ze′ {n = n})
\end{code}

In the {|n = ze|} case, the substitution |ze / n| is applied everywhere, 
including in the goal type {|n +ℕ ze ≡ n|} to produce the \emph{refined} goal
|ze +ℕ ze ≡ ze|, at which |refl| typechecks successfully (|ze +ℕ ze| reduces
to |ze| definitionally). A similar process makes the {|n = su n|} 
case work out.


% For example, 
% in Agda, we can write equality testing
% functions that return actual evidence for the result of the test.
% 
% % \begin{example}[Boolean Equality Testing] \phantom{a}
% \begin{code}
% test : ∀ (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
% test true   = inl refl
% test false  = inr refl
% \end{code}
% % \end{example}
% 
% Note that in the {|test true|} branch, for example,
% the substitution {|true / b|} is applied to the context,
% refining the goal type to 
% {|(true ≡ true) ⊎ (true ≡ false)|}, at which {|inl refl|} 
% typechecks successfully.

A limitation of dependent pattern matching, defined in this way, is that
matching anything other than individual variables is hard to justify.
Substitutions can
only target variables. Many functional programming languages (e.g. Haskell 
\sidecite{marlow2010haskell}) support |case_of_|
\emph{expressions} on the RHS of definitions, where the scrutinee can be
any appropriately-typed term.

Some dependently-typed languages
feature |with|-abstractions, enabling similar matching on
intermediary expressions on the LHS. However, as we will explain in 
\refsec{withabstr}, this feature has some significant drawbacks.

\subsection{Indexed Pattern Matching}

Another important aspect of pattern matching in dependently-typed languages
is dealing with indexed types. For example, the type, |Fin n|, of natural
numbers bounded by |n ∶ ℕ|.

\begin{code}
data Fin : ℕ → Set where
  fz  : Fin (su n)
  fs  : Fin n → Fin (su n)
\end{code}

\sideremark{``Any natural number the programmer wants, as long as it's 
|su n|!''}

``Fording'' \sidecite{mcbride2000dependently} shows us how to reduce 
\emph{indexed} 
inductive types
to \emph{parameterised} inductive types, assuming the existence of a
propositional identity type

\begin{code}
data Finℱ (m : ℕ) : Set where
  fzℱ  : m ≡ su n → Finℱ m
  fsℱ  : m ≡ su n → Finℱ n → Finℱ m
\end{code}

but this does not immediately solve the puzzle of how to support
``convenient'' pattern matching. Without
a way to match on the inductive propositional equality type |x ≡ y|, we
are forced into heavily (ab)using manual transport. To give an example,
let us define the datatype of length-indexed vectors (again in ordinary
and ``Forded'' style)

\begin{widepar}
\begin{minipage}{0.65\textwidth}
\begin{code}
data Vec (A : Set) : ℕ → Set where
  []   : Vec A ze
  _∷_  : A → Vec A n → Vec A (su n)
\end{code}
\end{minipage}
\begin{minipage}{0.65\textwidth}
\begin{code}
data Vecℱ (A : Set) (m : ℕ) : Set where
  []ℱ  : m ≡ ze → Vecℱ A m
  ∷ℱ   : m ≡ su n → A → Vecℱ A n → Vecℱ A m
\end{code}
\end{minipage}
\end{widepar}

for which we will attempt to implement a total vector lookup operation.
Under the ``Forded'' approach (without being able to match on |_≡_|), 
we must use manual equational reasoning
(including relying on a proof of injectivity of |su|) to
get the indices to align in the recursive case, and we need to explicitly
appeal to constructor disjointness to demonstrate that out-of-bounds accesses
are impossible.

\begin{code}
su-inj      : su n ≡ su m → n ≡ m
ze/su-disj  : ¬ ze ≡ su n

vlookupℱ : Finℱ n → Vecℱ A n → A
vlookupℱ (fzℱ p)    ([]ℱ q)      = ⊥-elim (ze/su-disj (sym q ∙ p))
vlookupℱ (fsℱ p i)  ([]ℱ q)      = ⊥-elim (ze/su-disj (sym q ∙ p))
vlookupℱ (fzℱ p)    (∷ℱ q x xs)  = x
vlookupℱ (fsℱ p i)  (∷ℱ q x xs)  
  = vlookupℱ (subst Finℱ (su-inj (sym p ∙ q)) i) xs
\end{code}

With Agda's built-in support for indexed pattern-matching, we can instead
simply write:

\begin{code}
vlookup : Fin n → Vec A n → A 
vlookup fz      (x ∷ xs) = x
vlookup (fs i)  (x ∷ xs) = vlookup i xs
\end{code}

Behind the scenes, |vlookup| is elaborated to simultaneously match on
the |ℕ|-typed variable, |n|. We do not need to give cases for |n == ze|
because Agda builds-in constructor disjointness, and in the
recursive case, we get that the |n| in |i ∶ Fin n| and in |xs ∶ Vec A n|
are equal from built-in constructor injectivity.

A key idea here is \emph{forced patterns} (also called \emph{dot patterns})
\sidecite{cockx2017dependent}. Variables, |i|, can be matched with arbitrary
expressions, |t|, if the equation between the 
variable and expression (|i == t|) is forced by simultaneous 
matches on indexed types.

In Agda, we can explicitly write forced patterns by prefixing the expression
with a ``|.|''. Note that below, we match on the |n ∶ ℕ| argument to
|_∷_| with the existing variable |m| (bound from matching on 
the |Fin n| index),
rather than introducing a fresh variable. We are only able to do this because
Agda internalises the fact that |su| is injective (so there is 
ultimately no other option).

\begin{code}
vlookup′ : Fin n → Vec A n → A 
vlookup′ {n = .(su m)} (fz {n = m})    (_∷_ {n = .m} x xs) = x
vlookup′ {n = .(su m)} (fs {n = m} i)  (_∷_ {n = .m} x xs) = vlookup′ i xs
\end{code}

Indexed pattern matching makes it possible to reflect a subset of
propositional equations (specifically those where the LHS or RHS is
a single variable). For example, consider this (slightly intimidating)
law stating that transports can be pushed underneath (dependent)
function applications.

\begin{code}
subst-application′  : ∀  {A : Set} (B : A → Set) {C : A → Set}
                         {x₁ x₂ : A} {y : B x₁}
                         (g : ∀ x → B x → C x) (p : x₁ ≡ x₂) 
                    → subst C p (g x₁ y) ≡ g x₂ (subst B p y)
\end{code}

In Agda, we can prove this just by matching on |p ∶ x₁ ≡ x₂| with |refl|,
simultaneously forcing the match |x₂ = .x₁|. It remains to
prove {|subst C refl (g x₁ y) ≡ g x₁ (subst B refl y)|}, which reduces
to {|g x₁ y ≡ g x₁ y|}, at which point |refl| typechecks successfully.

\begin{code}
subst-application′ B {x₁ = x₁} {x₂ = .x₁} g refl = refl
\end{code}

\subsection{With Abstraction}
\labsec{withabstr}

Both Agda and Idris 2 support matching on intermediary expression to
a limited extent via |with|-abstractions (originally named "views")
\sidecite{mcbride2004view, agda2024with, idris2023with}. The key idea is to
apply a one-off rewrite to the context, replacing every occurrence of the 
scrutinee expression with the pattern. In Agda, the implementation also
elaborates |with|-abstractions into separate top-level functions which
abstract over the scrutinee expression (so the final ``core'' program only
contains definitions that match on individual variables).

Unfortunately, the one-off nature of |with|-abstraction rewrites limits
their applicability. If we re-attempt the |f true ≡ f (f (f true))| proof from
the introduction (\refch{introduction}), taking advantage of this feature, 
the goal only gets
partially simplified:

\begin{spec}
bool-lemma : ∀ (f : Bool → Bool) → f true ≡ f (f (f true)) 
bool-lemma f with f true
bool-lemma f | true = ?0
\end{spec}

At |?0|, Agda has replaced every occurrence of |f true| in the context with
|true| exactly once, and so now expects a proof of 
|true ≡ f (f true)|, but it is not obvious
how to prove this. 
We could match on |f true| again, but Agda will force us
to cover both the |true| and |false| cases, with no memory of the prior
match.

For
\sideremark{This feature can also be simulated without special syntax
via the "inspect" idiom 
\cite{2024propositional}.}\sideblankcite{2024propositional}
scenarios like this, |with|-abstractions in Agda are extended with an
additional piece of syntax: following a |with|-abstraction with ``|in p|'' 
binds evidence of the match (a proof of propositional equality between 
the scrutinee
and pattern) to the new variable
|p|.

\begin{code}
bool-lemma : ∀ (f : Bool → Bool) → f true ≡ f (f (f true)) 
bool-lemma f  with f true in p
bool-lemma f  | true   =  true
                          ≡⟨ sym p ⟩≡
                          f true
                          ≡⟨ cong f (sym p) ⟩≡
                          f (f true) ∎
bool-lemma f  | false  with f false in q
bool-lemma f  | false  | true   = sym p
bool-lemma f  | false  | false  = sym q
\end{code}

We could also avoid all manual equational reasoning by
repeating previous matches, forced, by simultaneously matching on the
propositional equality.

\begin{code}
bool-lemma′ : ∀ (f : Bool → Bool) → f true ≡ f (f (f true)) 
bool-lemma′ f  with f true in p
bool-lemma′ f  | true   with f true | p 
... | .true | refl      with f true | p 
... | .true | refl      = refl

bool-lemma′ f  | false  with f false in q
bool-lemma′ f  | false  | true   with f true | p
... | .false | refl     = refl

bool-lemma′ f  | false  | false  with f false | q
... | .false | refl     = refl
\end{code}

Agda contains yet another piece of syntactic sugar to make this
pattern neater: |rewrite| 
takes a
propositional equality, and applies a one-off rewrite to the context
by implicitly |with|-abstracting over the LHS.

\begin{code}
bool-lemma′′ : ∀ (f : Bool → Bool) → f true ≡ f (f (f true)) 
bool-lemma′′ f  with f true in p
bool-lemma′′ f  | true   rewrite p
                         rewrite p
  = refl
bool-lemma′′ f  | false  with f false in q
bool-lemma′′ f  | false  | true   rewrite p
  = refl

bool-lemma′′ f  | false  | false  rewrite q
  = refl
\end{code}

But by now we are up to four distinct syntactic constructs, and the proof
is still significantly more verbose than with \SIF:

\begin{spec}
\f. sif (f TT) then Rfl else (sif (f FF) then Rfl else Rfl)
\end{spec}

|with|-abstractions also have a critical issue that \SC intends to solve:
the one-off nature of the rewrite can produce ill-typed contexts. Specifically,
it might be the case that for a context to typecheck, some neutral expression
must definitionally be of that neutral form, and replacing it
with some pattern, without ``remembering'' their equality,
causes a type error.

In practice, this forces implementations to re-check validity of the context
after a |with|-abstraction and throw errors if anything goes
wrong.

\begin{example}[Ill-typed |with|-abstraction Involving |Fin|] \phantom{a}

In the following code snippet, we attempt a forced match on
|n +ℕ m|, as this expression occurs in the index of |i ∶ Fin (n +ℕ m)|.
Unfortunately, after rewriting |n +ℕ m| to |su k|, we are left with
|i ∶ Fin (su k)| and |Pred n m i| (which relies on |i| having type
|Fin n +ℕ m|) is no longer typeable.

\begin{spec}
Pred : ∀ n m → Fin (n +ℕ m) → Set

foo : ∀ n m (i : Fin (n +ℕ m)) → Pred n m i → ⊤
foo n m i       p  with n +ℕ m
foo n m fz      p  | .(su _) = tt
foo n m (fs i)  p  | .(su _) = tt
\end{spec}

Agda cannot do better here than just throwing an error:

\begin{spec}
[UnequalTerms]
w != n +ℕ m of type ℕ
when checking that the type
(n m w : ℕ) (i : Fin w) (p : Pred n m i) → ⊤ of the generated with
function is well-formed
\end{spec}
\end{example}

This type of error is especially prevalent when working with heavily indexed
types, and contributes to the well-known problem of ``green slime''
\sidecite{mcbride2012polynomial} (the general term for pain
arising from indexing types by
neutral expressions, like {|n +ℕ m|} as above). A common issue is that
a |with| abstraction works just fine when implementing some operation
on an indexed type, but when attempting to later prove properties about 
this operation, repeating the same |with| abstraction suddenly fails.

\section{Local Equational Assumptions}
\labsec{loceqs}

As mentioned in the introduction, this work is largely inspired by Altenkirch
et al.'s work on \SC \sidecite{altenkirch2011case}. 
% primarily
% focused on pattern matching on Booleans (i.e. only introducing equations
% from neutral |𝔹|-typed terms to closed 
% boolean values). 
Following the dependently-typed syntax introduced in
\refsec{dtlc}, we can add a \SC rule for Booleans
(we name this \SIF for short), assuming
a way to extend contexts with equational assumptions (|_▷_~_|) and
an associated weakening operator (|wk~|) as follows:

%if False
\begin{code}
module EqReflect where
  open import Report.Final.c2-4_background hiding (if)
    hiding (reflect; A; B)
  
  module _ {A : Ty Γ} where
\end{code}
%endif

\begin{code}
    _▷_~_  : ∀ Γ {A} → Tm Γ A → Tm Γ A → Ctx
    wk~    : Tms (Γ ▷ t₁ ~ t₂) Γ

    if  : ∀ (t : Tm Γ 𝔹) 
        → Tm (Γ ▷ t ~ TT)  (A [ wk~ ]Ty)
        → Tm (Γ ▷ t ~ FF)  (A [ wk~ ]Ty)
        → Tm Γ A
\end{code}

We explore a type theory using a similar typing rule for ``|if|'' in
\refch{scbool}. To give a small taste of what makes this theory tricky
metatheoretically, we introduce the notions of
\emph{definitional inconsistency} and \emph{equality collapse}.

\begin{definition}[Definitional Context Inconsistency] \phantom{a}

We define contexts to be definitionally inconsistent if |TT| and |FF| are
convertible under that context.

\begin{code}
  incon : Ctx → Set
  incon Γ = _≡_ {A = Tm Γ 𝔹} TT FF
\end{code}
\end{definition}

In ITT, definitionally identifying non-neutral terms is dangerous as it can
lead to equality collapse \sidecite{conor2010wtypes}.

\begin{definition}[Equality Collapse] \phantom{a}
We define equality collapse as the
state when all terms/types are convertible. Equality collapse
specifically at the level of types is very dangerous, as we shall see shortly.

\begin{code}
  collapse : Ctx → Set
  collapse Γ = ∀ (A B : Ty Γ) → A ≡ B
\end{code}
\end{definition}

\begin{remark}[Definitional Inconsistency Implies Equality Collapse] \phantom{a}
\labremark{eqcollapse}

Assuming congruence of conversion (which is highly
desirable for definitional equality to behave intuitively), and large
elimination of Booleans, we can derive equality collapse
(|A ≡ B| for arbitrary types |A| and |B|) from
definitional inconsistency (|TT ≡ FF|).

\begin{code}
  incon-collapse : incon Γ → collapse Γ
  incon-collapse Γ! A B = 
    A
    ≡⟨ sym IF-TT ⟩≡
    IF TT A B
    ≡⟨ cong (λ □ → IF □ A B) Γ! ⟩≡
    IF FF A B
    ≡⟨ IF-FF ⟩≡
    B ∎
\end{code}

Assuming β-rules for Booleans, we can also also derive that 
definitionally inconsistent contexts
collapse the term equality, using a similar argument.
\end{remark}

Convertibility of all types is dangerous, as we can perform self-application, 
and define terms
that loop w.r.t β-reduction.

\begin{example}[Equality Collapse Enables Self-Application] \phantom{a}
\labexample{definconselfapp}

Under definitional equality of all types, we have that, e.g.
|A ⇒ A == A|, which means we can type self-application.

\begin{code}
  _[_]! : incon Γ → Tms Δ Γ → incon Δ
\end{code}

%if False
\begin{code}
  Γ! [ δ ]! = 
    TT
    ≡⟨ sym[] TT[] ⟩≡ 
    subst (Tm _) 𝔹[] (TT [ δ ])
    ≡⟨ cong (subst (Tm _) 𝔹[]) (Γ! [ refl ]≡') ⟩≡ 
    subst (Tm _) 𝔹[] (FF [ δ ])
    ≡⟨ FF[] ⟩≡ 
    FF ∎
  module _ {A : Ty Γ} where
\end{code}
%endif

\begin{code}
    self-app : incon Γ → Tm Γ (Π A (A [ wk ]Ty))
    self-app Γ! 
      = ƛ subst  (Tm _) wk<>Ty 
                 (subst (Tm _) (incon-collapse (Γ! [ wk ]!) _ _) vz · vz)
\end{code}

To jump from here to truly looping terms such as 
\emph{Ω} (\mbox{|(ƛ x. x x) (ƛ x. x x)|}) we only need to
repeat the construction.
\end{example}

Of course, 
if a particular context is definitionally
inconsistent, conversion is trivially decidable (any two terms must be
convertible, assuming a β-law for Booleans). However, if definitional 
inconsistency is not decidable,
then the above example means we also lose normalisation/decidable conversion 
in open contexts, and therefore
in the setting of dependent types (specifically ITT) decidability
of typechecking is lost.

In \SCBool, collapsing the definitional equality is easy. We can just
case split on a closed Boolean (or some term that is convertible to a
closed Boolean). Then, one of the contexts, of one of the ``|if|'' branches,
most contain the definitionally-inconsistent assumption |TT ~ FF| (or reversed).

Normalising the scrutinee before checking the branches of ``|if|'' (to see if it
reduces to a closed Boolean) is not enough to detect definitional inconsistency.
For example, consider the program (in a context where |b ∶ 𝔹| and
|not = ƛ b. if b FF TT|)

\begin{spec}
if (not b) (if b ?0 ?1) ?2
\end{spec}

When checking the inner ``|if|'' expression (in the left branch
of the outer ``|if|''), the scrutinee, |b|, 
is is normal form
(the assumption |not b ~ TT| is not enough to derive |b == FF| by pure
equational reasoning). However, in |?0|, the context becomes definitionally
inconsistent (|b ~ TT| and the β-rule for Booleans 
implies |not b == not TT == FF|, so |not b ~ TT| enables deriving |FF == TT|). 

% TODO: Maybe reference completion once we add the section??
Possible solutions here include: applying completion to either transform the set 
of equations into a confluent TRS (where all LHSs are irreducible) or detect
definitional inconsistency; or placing syntactic restrictions on the
equations which can be introduced (i.e. the scrutinees of \SIF 
expressions) to try and stop this situation early.
We will consider both of these possibilities in \refch{scbool} and
\refch{scdef}.

A more direct use of local equational assumptions is 
\emph{local equality reflection}.

\subsection{Local Equality Reflection}
\labsec{locreflect}

Recall the equality reflection rule from ETT

%if False
\begin{code}
  module _ {A B : Ty Γ} where
\end{code}
%endif

\begin{code}
    reflectETT : Tm Γ (Id A t₁ t₂) → t₁ ≡ t₂
\end{code}

If we turn this from a meta-level judgement to an object-level one, we arrive
at a syntactic construct we call ``local equality reflection'' (assuming
some way of extending contexts with local equational assumptions)

\begin{code}
    reflect  : Tm Γ (Id A t₁ t₂) → Tm (Γ ▷ t₁ ~ t₂) (B [ wk~ ]Ty)
            → Tm Γ B
\end{code}

|reflect| is significantly less powerful than ``full'' ETT
equality reflection (|reflectETT|); the programmer must specify every equality
proof they want to reflect, rather than assuming the existence of an oracle 
which can do proof search during 
typechecking\remarknote{This is perhaps a slightly
unfair interpretation of |reflectETT| given the system is not expected to have
decidable typechecking.}. The utility over transport comes from not requiring 
the programmer to also specify where to apply each equation (we assume
definitional equality is congruent).

Perhaps surprisingly then, typechecking dependent types with this local 
reflection rule is still
undecidable, as shown in \sidecite{sjoberg2015programming}. 
They present
the example of reflecting the definition of the Collatz function
(in a context where |f : ℕ ⇒ 𝔹| is a variable).
\begin{spec}
Id (ℕ ⇒ 𝔹) f (ƛ n. if even? n then f (n /ℕ 2) else su (3 *ℕ n))
\end{spec}
If we accept the new definitional equality, |f| had better halt on all
|ℕ|-typed inputs or |β|-reduction might run into a loop
(e.g. deciding |f k == true| for |k ∶ ℕ|). At least in
the context of 
``obviously'' definitionally inconsistent \refremark{eqcollapse}
equations such as |Id 𝔹 TT FF|, we can skip conversion-checking (all terms must
be convertible). 
For equations like the above though, we cannot assume inconsistency: 
without a counter-example to the Collatz conjecture, we have no way of
deriving a contradiction from its assumption.

For another example, imagine the programmer reflects a propositional
equation between two arbitrary closed functions from |ℕ|s to |𝔹|s, 
|Id (ℕ ⇒ 𝔹) f g|.
Assuming our type theory is not anti-classical, assuming identity between 
pointwise-equal functions is reasonable (even if we do not build-in 
function extensionality).
However, if we reflect |f == g| for a |f| and |g|
for which there exists a closed natural number |n : ℕ| such that |f n == TT| 
and |g n == FF|, then by congruence we are in a definitionally inconsistent
context, and self-application is typeable. We have no hope of catching
this in a typechecker, as the problem of deciding whether
two functions with infinitary domains are equal on all inputs (for any 
reasonably expressive theory\remarknote{E.g. is capable for formalising
Peano arithmetic.}) is undecidable.

Local equality reflection and \SC are not ultimately so different.

\begin{remark}[Smart Case is Local Equality Reflection] \phantom{a}
\labremark{scloceqref}

Assuming indexed matching (via forced patterns) and ordinary eliminators, 
an unrestricted
\SC is exactly as powerful as |reflect|. To |reflect| a propositional
equality, {|p ∶ Id A u v|}, with \SC, we can simultaneously match on |p|
with |refl| and the term {|u ∶ A|} with the forced pattern |.v|. 
To go the other direction, 
we can apply the associated splitter for the type, and then in each branch,
reflect the provided propositional equality.

As a corollary, typechecking unrestricted \SC is undecidable! Therefore,
when justifying a language featuring \SC or local equality reflection, we must
pay specific attention to identifying restrictions on the class of equations
which can be reflected, so decidability can be maintained.

Generally in this project, we focus on using \SC-style syntax to
introduce local equations, as we argue it often makes examples cleaner.
Furthermore, in the absence of indexed pattern matching/forced patterns, 
\SC suggests some nice potential restrictions on equations
(e.g. \SIF can only introduce equations of the form 
|t ~ TT| and |t ~ FF|).
\end{remark}

\subsection{Existing Systems with Local Equations}

GHC Haskell may not be a full dependently-typed language
(it is instead based on a System F$_\text{C}$
core theory) but the surface language does include many quite sophisticated 
features, including
automation of its 
type-level equality constraints \sidecite{sulzmann2007system}
(implemented in the
\emph{constraint solving} typechecking phase). 
Combined with type families, which enable real computation at the type
level, we can actually ``prove''\remarknote{There are a few caveats 
here:\\
1. Haskell does not allow types to directly depend on values, so we have to
encode dependently-typed functions with \emph{singleton} encodings 
\sidecite[*12]{lindley2013hasochism,  eisenberg2020stitch}. \\
2. Haskell is a partial language, so a ``proof'' of any type can be written
as |undefined|. Manual inspection is required to check totality/termination.\\
3. Haskell does not yet support unsaturated type families
\sidecite[*11]{kiss2019higher}. We simulate such a feature here using a 
concrete type family with no cases, but of course this cannot be instantiated
with a ``real'' type-level function on booleans later.} 
our standard |f True ≡ f (f (f True))| example.

\begin{example}[|f b ≡ f (f (f b))|, in Haskell] \phantom{a}
\begin{spec}
type data TBool = True | False
type SBool :: TBool -> Type
data SBool b where
  STrue  :: SBool True
  SFalse :: SBool False

type F :: TBool -> TBool
type family F b where 

boolLemma  :: (forall b. SBool b -> SBool (F b)) 
           -> F True :~: F (F (F True))
boolLemma f = case f STrue of
  STrue   -> Refl
  SFalse  -> case f SFalse of
    STrue   -> Refl
    SFalse  -> Refl
\end{spec}
\end{example}

Unfortunately, Haskell's constraint solving is undecidable, and in 
practice many
desirable properties of conversion (such as congruence) do not hold.

\begin{example}[Conversion is not Congruent in GHC Haskell] \phantom{a}

In GHC 9.12.2, we can try to derive equations between arbitrary types
from the constraint |True ~ False|:
\begin{spec}
type IF :: Bool -> a -> a -> a
type family IF b t u where
  IF True  t u = t
  IF False t u = u

bad  :: True ~ False 
     => IF True () (() -> ()) :~: IF False () (() -> ())
bad = Refl
\end{spec}

But this produces the following type error:

\begin{spec}
  • Couldn't match type ‘()’ with ‘() -> ()’
    Expected: IF True () (() -> ()) :~: IF False () (() -> ())
      Actual: () :~: ()
  • In the expression: Refl
    In an equation for ‘bad’: bad = Refl
\end{spec}
\end{example}

Haskell is not the only language to support a \SC-like feature.
The dependently-typed language ``Zombie'' builds congruence closure
into the
definitional equality of 
the surface
language and implements \SC in full, while retaining decidable 
typechecking \sidecite{sjoberg2015programming}. 
The sacrifice is β-conversion: 
Zombie does not automatically apply computation rules, requiring manual
assistance to unfold definitions during typechecking.

This is certainly an interesting point in the design-space of dependently-typed
languages, coming with additional advantages such as the possibility of
accepting non-total
definitions without endangering decidability of typechecking. However, the focus
\sideremark{One could view traditional definitional equality as a hack,
carefully defining an equational theory that happens to be a decidable
subset of propositional equality,
and building it into the typechecker, but it is undeniably effective.}
of this project is justifying extending the definitional equality of 
existing mainstream proof assistants, which generally assume β-equality.

The Lean proof assistant features a tactic for automatically discharging
equality proofs following from congruence closure
\sidecite{selsam2016congruence}, but their algorithm is not
capable of interleaving congruence and reduction (which is required
in our setting to ensure transitivity of conversion).

Sixty \sidecite{sixty} is a dependent typechecker which
also implements a form of \SC along with full β-conversion, but there is 
no published work justifying its implementation theoretically.

Andromeda 2 \sidecite{komel2021meta} is a proof assistant that supports
local equational assumptions via rewriting with the goal of 
supporting user-specified type theories. The system goes beyond the 
class of equations we consider here, supporting also
rewrite rules that themselves quantify over variables (standing for all
appropriately-typed terms). In this report, we refer to such contextual 
equations
that only refer to prior-bound variables as \emph{ground}, and therefore
view this work as accounting also for \emph{non-ground} 
equations\remarknote{We justify this terminology by noting that, in a fixed
context, variables essentially act like constants. Of course, unlike
ordinary ground term rewriting, we do
need to worry about what happens when these bound variables are substituted
for other terms.}. They focus
primarily on proving soundness of their equality checking algorithm, and leave 
confluence/termination checking and completeness results for future work.

\sidecite{winterhalter2025controlling} also deals with non-ground
equations, following work on controlling unfolding in type theory
\sidecite{gratzer2022controlling}. In their setting, equations cannot
refer directly to local bound variables as \SC requires.

% Since I started working on this project, there has also been
% progress on \sidecite{winterhalter2025controlling} (CONTROLLING UNFOLDING
% IN TYPE THEORY REF AFTER DBLP COMES BACK ALIVE TODO)


% TODO: Put this somewhere, maybe
% Variables in our equations are always specifically 
% bound somewhere earlier in the context; they still stand for multiple terms
% in the sense that we can apply substitutions to the context, but e.g.
% in a context where |x ∶ 𝔹| and |y ∶ 𝔹|,
% the equation |x ~ TT| does not imply |y == TT|, because |x| and |y| are
% distinct bound variables. 
% In perhaps a slight abuse of 
% terminology, we call our restricted class of equations \emph{ground}.

\section{Global Equational Assumptions}
\labsec{rewrites}

There has been a significant body of work examining
type theories extended with global (non-ground) rewrite rules, plus 
implementations in Dedukti \sidecite{assaf2016dedukti}, 
Agda \sidecite{cockx2020type} and Rocq
\sidecite{leray2024rewster}. 
Work in the area has examined automatic (albeit necessarily conservative)
confluence
\sidecite{cockx2021taming} and termination
\sidecite{genestier2019sizechangetool} checking of these rewrites.
Agda's implementation of |REWRITE| rules specifically checks confluence, but
not termination.

A key difference between these works and \SC is that global equations
cannot refer to local variables bound inside terms/definitions. We also
cannot ever disable global rewrites which earlier definitions might
depend on without endangering subject reduction, which becomes
problematic when building larger developments. For example, two different
modules might rely on distinct sets of global rewrites that are individually
confluent and terminating, but together are not. It is now impossible
to safely import code from both of these modules.

\section{Elaboration}

A principled and increasingly popular way to design and implement
programming languages
\sidecite{eisenberg2015system, brady2024yaffle, ullrich2023extensible}
is by \emph{elaboration} into a minimal core syntax. A significant benefit of
this approach is modularity \sidecite{cockx2024core}: multiple extensions to
the surface language can be formalised and implemented without having to worry
about their interactions. Elaboration can also increase trust in the
resulting system, ensuring that all extensions are ultimately
conservative over the, perhaps more-rigorously justified, core theory.

\sidecite{winterhalter2019eliminating, blot2024rewrite} investigate
elaborating ETT and ITT plus global rewrite rules into an ITT
with explicit transports. Both of these works rely on Uniqueness of Identity
Proofs (UIP)/axiom |K|, which is
incompatible with type theories that feature proof-relevant equality 
(such as Homotopy Type
Theory)\remarknote{Note that implicit transporting along equivalences between
completely distinct types (such as ℕ and ℤ)
could be used to implement coercions/subtyping, so automating
equational reasoning on types with proof-relevant equality could still
be useful if there is a distinguished ``default'' mapping.\\
Such use-cases appear impossible to handle properly without an 
elaboration-like 
process inserting transports, given some sort of term-level computation is
ultimately required
to map between distinct types.}.

In this report, we do not consider the problem of similarly 
elaborating \SC to an 
ordinary intensional type theory, without contextual
equational assumptions (one could consider this mostly covered
by the above-cited prior work).
Instead, in \refch{scdef} we leverage a quite simple elaboration
algorithm based on lambda-lifting to give the appearance of \SC
while maintaining a more well-behaved core theory than \SCBool.

\section{Strict η for Coproducts}
\labsec{coprodeta}

Another use-case for tracking equational assumptions is to decide conversion
in the presence of strict η for Booleans or, more generally, coproducts.
For example, \sidecite{dougherty2000equality} and 
\sidecite{altenkirch2001normalization} introduce collections of equations
between
|(A + B)|-typed neutrals and terms of the form |in₁ i| or |in₂ i| (where |i|
is a variable), the latter naming these ``neutral constrained environments''.

We formally define the simply-typed η-law for Booleans, 
following the syntax introduced in
\refsec{stlc} (assuming fully strict substitution laws, and 
propositional quotienting by conversion).

\begin{definition}[η For Booleans] \phantom{a}
%if False
\begin{code}
module BoolEta where
  open import Report.Final.c4-3_booleq hiding (A; B)

  variable
    f : Tm Γ _
  
  postulate
    𝔹β₁ : if TT u v ≡ u
    𝔹β₂ : if FF u v ≡ v
    ⇒η : t ≡ ƛ ((t [ wk ]) · (` vz))
\end{code}
%endif

η-conversion for Booleans can be stated as

\begin{code}
    𝔹η  : u [ < t > ] ≡ if t (u [ < TT > ]) (u [ < FF > ])
\end{code}

In words: every term
containing a boolean-typed sub-expression, {|t ∶ Tm Γ 𝔹|}, can be expanded
into
an ``|if|'' expression, with |t| replaced by 
|TT| in the
|TT| branch and |FF| in the |FF| branch.

In dependent type theory, we can prove this law internally by induction
on Booleans (even if our theory, like Agda,
does not implement η for such types definitionally).

\begin{code}
  Bool-η  : ∀ (f : Bool → A) b 
           → f b ≡ Bool-rec b (f true) (f false)
  Bool-η f true   = refl
  Bool-η f false  = refl
\end{code}
\end{definition}

η for Booleans is quite powerful. For example, it enables deriving
\emph{commuting conversions}.

\begin{example}[Commuting Conversions] \phantom{a}

Commuting conversions express the principle that case-splits on inductive
types can be lifted upwards (towards the root of the term) as long as 
the variables occurring in the scrutinee
remain in scope. i.e.
\begin{code}
  𝔹-comm  : f [ < if t u v > ] ≡ if t (f [ < u > ]) (f [ < v > ])
\end{code}

This follows from |𝔹η| and |𝔹β₁|/|𝔹β₂| as follows

\begin{code} 
  𝔹-comm {f = f} {t = t} {u = u} {v = v} =
    (f [ < if t u v > ])
    ≡⟨ 𝔹η {u = f [ wk ^ _ ] [ < if (` vz) (u [ wk ]) (v [ wk ]) > ]} ⟩≡
    if t (f [ < if TT u v > ]) (f [ < if FF u v > ])
    ≡⟨ cong₂ (λ □₁ □₂ → if t (f [ < □₁ > ]) (f [ < □₂ > ])) 𝔹β₁ 𝔹β₂ ⟩≡
    if t (f [ < u > ]) (f [ < v > ]) ∎
\end{code}

Again, we can prove an analagous propositional law internally,
using |Bool-η|.

\begin{code}
  Bool-comm  : ∀ (f : A → B) (b : Bool) (x y : A)
             → f (Bool-rec b x y) ≡ Bool-rec b (f x) (f y)
  Bool-comm f b x y = Bool-η (λ b → f (Bool-rec b x y)) b
\end{code}
\end{example}

In a system with strict η for functions and
another type |A|, definitional equality of functions on |A|
is observational\remarknote{Observational equality in type theory
refers to the idea that evidence of equality of terms at a particular type
can follow the structure of that type
\cite{altenkirch2007observational}.\\
For functions |f| and |g|, observational equality takes the form of a function
from evidence of
equal inputs |x ≡ y| to evidence of equal
outputs |f x ≡ f y| - i.e. pointwise equality (functions are equal precisely 
when they agree on all inputs).}\sideblankcite{altenkirch2007observational}.

\begin{theorem}[Strict η for Functions and Booleans Implies Definitional
Observational Equality of Boolean Functions] \phantom{a}
\labthm{obs-eta}

Assuming |f · TT ≡ g · TT| and |f · FF ≡ g · FF|, we can derive
|f ≡ g| from |⇒η| and |𝔹η|.

\begin{code}
  𝔹⇒  : ∀ {f g : Tm Γ (𝔹 ⇒ 𝔹)}
      → f · TT ≡ g · TT → f · FF ≡ g · FF
      → f ≡ g
  𝔹⇒ {f = f} {g = g} tt≡ ff≡ = 
    f
    ≡⟨ ⇒η ⟩≡
    ƛ f′ · ` vz
    ≡⟨ cong (λ □ → ƛ f′ · □) (𝔹η {u = ` vz}) ⟩≡
    ƛ f′ · if (` vz) TT FF
    ≡⟨ cong (ƛ_) (𝔹-comm {f = f′ [ wk ] · ` vz}) ⟩≡
    ƛ (if (` vz) (f′ · TT) (f′ · FF))
    ≡⟨ cong₂ (λ □₁ □₂ → ƛ (if (` vz) □₁ □₂)) tt≡′ ff≡′ ⟩≡
    ƛ if (` vz) (g′ · TT) (g′ · FF)
    ≡⟨ cong (ƛ_) (sym (𝔹-comm {f = g′ [ wk ] · ` vz})) ⟩≡
    ƛ g′ · if (` vz) TT FF
    ≡⟨ cong (λ □ → ƛ g′ · □) (sym (𝔹η {u = ` vz})) ⟩≡
    ƛ g′ · ` vz
    ≡⟨ sym ⇒η ⟩≡
    g ∎
    where  f′    = f [ wk ]
           g′    = g [ wk ]
           tt≡′  = cong _[ wk ] tt≡
           ff≡′  = cong _[ wk ] ff≡
\end{code}



Subtly, propositional, observational equality of Boolean functions 
({|f true ≡ g true → f false ≡ g false → f ≡ g|}) is not
provable internally
using the with propositional |Bool-η| unless we also assume function
extensionality to get our hands on a |Bool|-typed term to pass as |b|.

This is to be expected, given we have seen that propositional η-laws 
for inductive types can 
be proven merely by induction, but observational equality of functions 
(called ``function extensionality'' in the general case) is not
provable in intensional MLTT \sidecite{streicher1993investigations}. 
% \begin{spec}
% f
% == -- by η-equality of functions
% λ b → f b
% == -- by η-equality of booleans
% λ b → f (if b then True else False)
% == -- by commuting conversions
% λ b → if b then f True else f False
% == -- by assumption 
% λ b → if b then g True else g False
% == -- by commuting conversions
% λ b → g (if b then True else False)
% == -- by η-equality of booleans
% λ b → g b
% == -- by η-equality of functions
% g
% \end{spec}
\end{theorem}

It is perhaps also worth noting that in a dependently-typed setting, η for 
|A ⊎ B| binary coproducts can be obtained merely with η for
booleans, |Σ| types and large elimination, via the encoding
{|A ⊎ B = Σ Bool (λ b → if b A B)|} \sidecite{kovacs2022strong}.

As mentioned in 
\hyperref[sec:compuniq]{Section 1.1 - Computation and Uniqueness}, while 
η rules for positive types
(such as Booleans or coproducts), can be
useful, 
they do have some downsides.
\begin{itemize}
  \item First, the meta-theory gets quite complicated. Previous proofs of
  normalisation for
  STLC with of strict η for binary coproducts have relied on
  somewhat sophisticated rewriting 
  \sidecite{ghani1995adjoint, lindley2007extensional} or sheaf
  \sidecite{altenkirch2001normalization} theory.
  Normalisation for dependent type theory with boolean η remains open (though
  some progress on this front has been made recently
  \sidecite{maillard2024splitting}).
  \item Second, efficient implementation appears challenging. 
  Algorithms such as \cite{altenkirch2001normalization} aggressively
  introduce case-splits on all neutral subterms of coproduct-type and lifts the
  splits
  as high as possible, in an effort to prevent the build-up of stuck
  terms. In the worst-case, this requires re-normalising 
  twice for every distinct coproduct-typed neutral subterm.
  \cite{maillard2024splitting} proposes a similar algorithm for
  typechecking dependent types with strict boolean η, using a monadic
  interpreter with an effectful splitting operation.
  \sidecite{altenkirch2004normalization}
  is even more extreme: when a variable |f| of type |Bool → Bool| is bound, for
  example, case
  splits are generated on |f true| and |f false| (regardless of whether such
  terms actually occur anywhere in the body), in essence enumerating 
  over all possible implementations of |f|. 
\end{itemize}

The (current) lack of normalisation result for dependent types with strict
Boolean η prevents justifying \SC merely by piggy-backing on existing work.
The problem we examine in this report is further distinguished from
η-equality due to its potential to target a wider variety of equations
than is allowed in the ``neutral constrained environments'' of
Dougherty \sidecite{dougherty2000equality}
or Altenkirch \cite{altenkirch2001normalization}. 
Specifically, we are also interested in equations 
where both sides are neutral, or equations between infinitary-typed
% TODO Reference section here?
terms (|ℕ|, |List A|, |Tree A|, etc..., for which η-equality is undecidable).
%  in other words, if we
% could decide conversion modulo η for |ℕ|s, we would have a way to compute
% whether arbitrary |ℕ → 𝔹| functions are equal on all inputs, which is enough
% to solve the halting problem (consider the |ℕ → 𝔹| function that runs a
% particular Turing machine for the input number of steps and returns whether
% it halts).

\section{Extension Types}

In retrospect, the machinery we introduce in \SCBool and \SCDef to
extend contexts with convertibility assumptions and generalise substitutions
appropriately can be seen as a subset of extension types 
\sidecite{riehl2017synthetic, zhang2023three}.

Extension types assume the existence of a sort of propositions |F|
that we can extend contexts with
%if False
\begin{code}
module _ where
  open import Report.Final.c2-4_background
\end{code}
%endif
\begin{code}
  F   : Ctx → Set
  _▷F_   : ∀ Γ → F Γ → Ctx
\end{code}

%if False
\begin{code}
  variable
    φ : F Γ
    t≡ : t ≡ u
  wkF    : Tms (Γ ▷F φ) Γ
\end{code}
%endif

Extension types, |A ∣ φ >eq u|,
encode terms that are convertible |u| under the assumption of |φ|.

\begin{code}
  _∣_>eq_  : (A : Ty Γ) (φ : F Γ) → Tm (Γ ▷F φ) (A [ wkF ]Ty) 
         → Ty Γ
\end{code}
%if False
\begin{code}
  module _ {A : Ty Γ} where 
\end{code}
%endif

\sideremark{
The introduction rule |inS| is often written as
\nocodeindent
\begin{code}
    inS′  : ∀ (t : Tm Γ A) → t [ wkF ] ≡ u 
          → Tm Γ (A ∣ φ >eq u)
\end{code}
making explicit |t| needs to be convertible to |u| under the assumption |φ|.
In a quotiented syntax, these two rules are equivalent (|inS′| is just
the ``Forded'' version of |inS|).
\resetcodeindent
}

\begin{code}
    inS   : ∀ (t : Tm Γ A) → Tm Γ (A ∣ φ >eq (t [ wkF ]))
    outS  : Tm Γ (A ∣ φ >eq u) → Tm Γ A
    out▷  : ∀ {t : Tm Γ (A ∣ φ >eq u)} → outS t [ wkF ] ≡ u
    extβ  : outS (inS {φ = φ} t) ≡ t   
\end{code}

\sideremark{In the context of Cubical type theory, extension types with
propositions |F Γ| corresponding to interval expressions that must
definitionally equal |i1| are are also called Cubical
subtypes (\cite{agda2024cubical}).}\sideblankcite{agda2024cubical}

Assuming a universe of types, |U|, and an 
|F Γ| which includes |𝔹|-typed convertibility assumptions,
we can give the following elimination rule for Booleans.

\begin{code}
  U      : Ty Γ
  El     : Tm Γ U → Ty Γ
  _~_    : Tm Γ 𝔹 → Tm Γ 𝔹 → F Γ

  ext-if  : ∀ {A : Tm Γ U} (t : Tm Γ 𝔹)
              (Att : Tm Γ (U ∣ (t ~ TT)  >eq (A [ wkF ])))
              (Aff : Tm Γ (U ∣ (t ~ FF)  >eq (A [ wkF ])))
          → Tm Γ (El (outS Att))
          → Tm Γ (El (outS Aff))
          → Tm Γ (El A)
\end{code}

This bears some resemblance with \SIF: the LHS and RHS branches of the
|if| expression can differ in type up to replacing the scrutinee with
|TT|/|FF|. Unlike the typing rule for \SC suggested in 
\sidecite{altenkirch2011case}, the LHS and RHS branch are still typed
in context |Γ|, which could make the metatheory much easier.

Unfortunately, this construct is more limited than we would like.
The concise proof of |f true ≡ f (f (f true))| from the
introduction (\refch{introduction}) cannot be replicated with |ext-if|.
If we make an attempt (working internally for convenience)

\remarknote{Type inference also appears to be more difficult for |ext-if|,
than full \SIF
hence the explicit annotations for the LHS and RHS types.
\SIF (as defined in
\refsec{loceqs}) can check the LHS and RHS 
branches at the same type as the entire 
|if| expression, |A ∶ Ty Γ|,
weakened to account for the new equation. |ext-if|, on the other hand,
requires coming up with types in |Γ|
for the LHS and RHS branches that just happen
to be convertible to |A| after weakening.}

\begin{spec}
bool-lemma : Id 𝔹 (f TT) (f (f (f TT)))
bool-lemma = ext-if  (f TT) (inS (Id 𝔹 TT TT)) (inS (Id 𝔹 FF (f (f FF))))
                     rfl
                     ext-if  (f FF) (inS (Id 𝔹 FF (f TT))) (inS (Id 𝔹 FF FF))
                             ?0 rfl
\end{spec}

we get stuck in the case labelled |?0|. The problem is that, as with
|with|-abstraction, |ext-if| does not have ``memory'' of the prior case splits.
|ext-if| still does manage a better job than |with|-abstraction, 
being able to apply the equation to the type multiple times
(e.g. simplifying |f (f (f TT))| all the way to |TT|
in the left branch of the split on |f TT|). However, in |?0|, we need to
reuse the fact that |f TT ≡ FF|, and no longer have access to it.

I therefore argue that \SC really does need to extend the context in which
the branches of the split are typed, with the appropriate equation. 
Therefore, it appears that the existing theory of extension types is not 
directly applicable
to this use-case.
