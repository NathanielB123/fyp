% Not a real chapter. Need to sprinkle these around as appropriate.

%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils

module Report.Final.c9-1_appendix where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}
\chapter{An Example Use-Case: First-Order Unification}
\labch{unifex}

% \setchapterstyle{lines}
% 
% \section{An Example Use-case: First-order Unification}

\sideremark{This section was originally written with the intention of
coming quite early in the report, and so re-explains notation and concepts
which are now covered also in \refch{background}. I thought it was
still, on balance, worth including.}

Inspired by \sidecite{sjoberg2015programming}, we present
in detail a potential use-case for type theory with local equality 
reflection. Concretely, we develop
a verified first-order unification algorithm.
The example is a bit involved, but I think it is
worth running through in part because,
since the publication of this work \cite{sjoberg2015programming}, 
Agda has had a significant extension
to its automation of equational reasoning
in the form of global |REWRITE| rules
\sidecite{cockx2020type}. It will be
interesting to examine where these can and cannot help.

We define the unification algorithm on an untyped syntax containing 
variables, 
application and constants. We index terms by the number
of variables in scope. For 
example, |Tm 3| will represent a term which can contain up to three
distinct variables.

% ---------------------------------------------------------------------------- %
% First-order terms
% ---------------------------------------------------------------------------- %
\begin{definition}[First-Order Terms And Variables] \phantom{a} 

\labdef{terms}
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
  Γ Δ Θ : ℕ
\end{code}
%endif
Terms themselves are easy. We have no binding constructs, so the context
stays the same in all cases:
% This remark applies to the definition of variables below but needs to be
% higher to avoid overlapping with later stuff.
\sideremark{This |Var| datatype is common in dependently-typed programming, and
is often named |Fin| for ``finite''. One way to understand it is that
the indexing of |vs| ensures the context is incremented at least as many
times as the |Var| itself and |vz| asks for one extra |su| call to make this 
inequality
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
Indexed typed like |Var|/|Fin| can be justified in dependent type theories
with a propositional identity type by ``Fording''
\sidecite[*2.5]{mcbride2000dependently}. 
e.g. for |vz| we could have instead written isomorphic signature
|vz : Δ ≡ su Γ → Var Δ| - you can have any context, as long as it is |su Γ|! 
\end{definition}
% ---------------------------------------------------------------------------- %

Unification can be defined as the task of finding a substitution 
(the \emph{unifier}) 
that maps the terms being unified to equal terms\remarknote{A reasonable
follow-up question here might be: what does equality on terms mean? For now,
given these are first-order terms, we 
only consider on-the-nose syntactic equality.}. It seems reasonable then, to 
define substitutions next.

There are various different approaches to defining substitutions in proof
assistants. We shall use a first-order encoding of parallel substitutions; 
that is, a list of terms, equal in length to the
context, where operationally, the variable |vz| will be mapped to the first term
in the list  the list, |vs vz| to the second and so on... 

\pagebreak
\sideremark{This encoding of
substitutions is nice for two reasons:\newline
1. Substitutions can be composed while staying canonical. i.e. unlike sequences
of single substitutions.\newline
2. Higher-order encodings of substitutions (i.e. as functions) do not scale to 
dependently-typed syntax (without \emph{very-dependent types}
\sidecite[*2]{hickey1996formal, altenkirch2022munchhausen})}


% ---------------------------------------------------------------------------- %
% Parallel substitutions
% ---------------------------------------------------------------------------- %
\begin{definition}{Parallel Substitutions} \phantom{a}
\labdef{par-subst}

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
  ε    : Tms Δ ze
  _,_  : Tms Δ Γ → Tm Δ → Tms Δ (su Γ)
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
  success : ∀ (δ : Tms Γ Γ) → t [ δ ] ≡ u [ δ ] → Unifier t u
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
to find a unifier (using the standard |Maybe| type to deal with possible
failure):
%if False
\begin{code}
interleaved mutual
  {-# TERMINATING #-}
\end{code}
%endif
\begin{code}
  unify : (t u : Tm Γ) → Maybe (Unifier t u)
\end{code}

We now attempt to define |unify| by cases:

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

  wk : Tms (su Γ) Γ
  wk = id ⁺

  id {Γ = ze}   = ε
  id {Γ = su Γ} = wk , (` vz)

  variable
    t u v : Tm Γ
    i j k : Var Γ
    δ σ   : Tms Δ Γ

  data Occurs (i : Var Γ) : Tm Γ → Set where
    eq : Occurs i (` i)
    l· : Occurs i t → Occurs i (t · u)
    ·r : Occurs i u → Occurs i (t · u)
  
  ¬Occursπ₁ : ¬ Occurs i (t · u) → ¬ Occurs i t
  ¬Occursπ₁ p q = p (l· q)

  ¬Occursπ₂ : ¬ Occurs i (t · u) → ¬ Occurs i u
  ¬Occursπ₂ p q = p (·r q)

  _≡v?_ : (i j : Var Γ) → Dec (i ≡ j)
  vz   ≡v? vz   = yes refl
  vz   ≡v? vs j = no λ ()
  vs i ≡v? vz   = no λ ()
  vs i ≡v? vs j = map-Dec (cong vs) (λ where refl → refl) (i ≡v? j)

  occurs? : (i : Var Γ) (t : Tm Γ) → Dec (Occurs i t)
  occurs? i (` j) with i ≡v? j
  ... | yes refl = yes eq
  ... | no  ¬p   = no λ where eq → ¬p refl
  occurs? i (t · u) with occurs? i t
  ... | yes p = yes (l· p)
  ... | no ¬p with occurs? i u
  ... | yes q = yes (·r q)
  ... | no ¬q = no λ where (l· p) → ¬p p
                           (·r q) → ¬q q
  occurs? i ⟨⟩      = no λ ()

  _[_↦_] : Tms Δ Γ → Var Γ → Tm Δ → Tms Δ Γ
  (δ , u) [ vz   ↦ t ] = δ , t
  (δ , u) [ vs i ↦ t ] = (δ [ i ↦ t ]) , u

  _⨾_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  ε        ⨾ σ = ε
  (δ , t)  ⨾ σ = (δ ⨾ σ) , (t [ σ ])
  
  []lookup : lookup i δ [ σ ] ≡ lookup i (δ ⨾ σ)
  []lookup {i = vz}   {δ = δ , u} = refl
  []lookup {i = vs i} {δ = δ , u} = []lookup {i = i} {δ = δ}

  [][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
  [][] {t = ` i}   = []lookup {i = i}
  [][] {t = t · u} = cong₂ _·_ ([][] {t = t}) ([][] {t = u})
  [][] {t = ⟨⟩}    = refl

  i[i↦] : lookup i (δ [ i ↦ t ]) ≡ t
  i[i↦] {i = vz}   {δ = δ , _} = refl
  i[i↦] {i = vs i} {δ = δ , _} = i[i↦] {i = i} {δ = δ}

  i[j↦] : ¬ i ≡ j → lookup i (δ [ j ↦ u ]) ≡ lookup i δ
  i[j↦] {i = vz}   {j = vz}               p = ⊥-elim (p refl)
  i[j↦] {i = vs i} {j = vz}   {δ = δ , _} p = refl
  i[j↦] {i = vz}   {j = vs j} {δ = δ , _} p = refl
  i[j↦] {i = vs i} {j = vs j} {δ = δ , _} p 
    = i[j↦] {i = i} {j = j} {δ = δ} λ where refl → p refl

  i[⁺] : inc (lookup i δ) ≡ lookup i (δ ⁺)
  i[⁺] {i = vz}   {δ = δ , t} = refl
  i[⁺] {i = vs i} {δ = δ , t} = i[⁺] {i = i} {δ = δ}

  i[id] : lookup i id ≡ (` i)
  i[id] {i = vz}   = refl
  i[id] {i = vs i} = sym (i[⁺] {i = i}) ∙ cong inc (i[id] {i = i})

  t[i↦] : ¬ (Occurs i t) → t [ id [ i ↦ u ] ] ≡ t
  t[i↦]            {t = t · u}  p 
    = cong₂ _·_ (t[i↦] (¬Occursπ₁ p)) (t[i↦] (¬Occursπ₂ p))
  t[i↦]            {t = ⟨⟩}     p = refl
  t[i↦] {i = i}    {t = ` j}    p 
    = (i[j↦] {i = j} {j = i} {δ = id} λ where refl → p eq) ∙ i[id] {i = j}

  sym-unifier : Unifier t u → Unifier u t
  sym-unifier (success δ p) = success δ (sym p)
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
  unify (t₁ · t₂)  (` j)  = map-maybe sym-unifier (unify (` j) (t₁ · t₂))
  unify ⟨⟩ (` i)          = map-maybe sym-unifier (unify (` i) ⟨⟩)
\end{code}
%endif

A more interesting case crops up when |t| is a variable:

\begin{spec} 
  unify (` i) u = ?0
\end{spec}

To implement this |?0|, we need to perform an \emph{occurs check} to find 
whether |i| occurs in |u|.

We define variables occurring free in first-order terms inductively as:
\begin{spec}
  Occurs : Var Γ → Tm Γ → Set

  eq  : Occurs i (` i)
  l·  : Occurs i t → Occurs i (t · u)
  ·r  : Occurs i u → Occurs i (t · u)
\end{spec}

And define occurs checking itself 
|occurs? : (i : Var Γ) (t : Tm Γ) → Dec (Occurs i t)| by recursion on
terms/variables. \textit{Where |Dec A| is the type of decisions over whether
the type |A| is inhabited, introduced with |yes : A → Dec A| and
|no : ¬ A → Dec A|. Negation of a type can be encoded as a function to
the empty type |⊥|.}

We also need a way to construct substitutions in which a single variable
is replaced with a particular term:

\begin{spec}
  _[_↦_] : Tms Δ Γ → Var Γ → Tm Δ → Tms Δ Γ
  (δ , u) [ vz   ↦ t ]  = δ , t
  (δ , u) [ vs i ↦ t ]  = (δ [ i ↦ t ]) , u
\end{spec}

Now, along with the |i[i↦] : lookup i (δ [ i ↦ t ]) ≡ t| and
|t[i↦] : ¬ (Occurs i t) → t [ id [ i ↦ u ] ] ≡ t| (provable by induction
on terms, variables and substitutions), and with the help of |with|-abstractions
to match on the result of the occurs check (the limitations of this
feature vs \SC are detailed in \refsec{withabstr}), we can implement this
case (if |i| does not occur in |u|, the substitution |id [ i ↦ u ]| is a valid
unifier, if |u| equals |` i|, |id| is a valid unifier, otherwise unification
fails).

\begin{code}
  unify (` i) u with occurs? i u 
  ... | no   p       = just (success (id [ i ↦ u ]) (
    lookup i (id [ i ↦ u ])
    ≡⟨ i[i↦] {i = i} ⟩≡
    u
    ≡⟨ sym (t[i↦] p) ⟩≡
    u [ id [ i ↦ u ] ] ∎)) 
  ... | yes  eq      = just (success id refl)
  ... | yes  (l· _)  = nothing
  ... | yes  (·r _)  = nothing
\end{code}

Note the manual equational reasoning required to prove |id [ i ↦ u ]| is valid.
Agda's user-defined |REWRITE| rules (\refsec{rewrites}) enable turning 
|i[i↦]| into a
definitional
equation, reducing the proof to just |sym (t[i↦] p)|, but |t[i↦]| has a
pre-condition 
(|¬ (Occurs i t)|) and so cannot be turned into a global |REWRITE|.
With \SC, we could merely match on |i[i↦] {i = i} {δ = δ} {t = u}| and 
|t[i↦] {u = t} p|, and write the proof as |refl|.

The remaining case (ignoring swapping of arguments) is where both sides
are applications.
Here, we attempt to unify the LHSs, and
if that succeeds, unify the RHSs with the LHS-unifying substitution applied.
If this unification also succeeds, we can compose the two unifiers, and again do
some equational reasoning to prove this is a valid unifier.

We define composition of substitutions by recursion on the first:
\begin{spec}
  _⨾_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  ε        ⨾ σ = ε
  (δ , t)  ⨾ σ = (δ ⨾ σ) , (t [ σ ])
\end{spec}

And prove the composition law |[][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]| by
induction on terms, variables and substitutions. This enables us to
finish the implementation of |unify|.

\sideremark{This implementation is unfortunately not structurally recursive 
(|t₂ [ δ ]| is not structurally smaller than |t₁ · t₂|). 
For the purposes of this example,
we just assert termination, though algorithms which Agda will accept more
directly do exist \sidecite[*2]{mcbride2003first}.}
\begin{code}
  unify (t₁ · t₂) (u₁ · u₂) with unify t₁ u₁
  ... | nothing             = nothing
  ... | just (success δ p)  with unify (t₂ [ δ ]) (u₂ [ δ ])
  ... | nothing             = nothing
  ... | just (success σ q)  = just (success (δ ⨾ σ) (
    (t₁ [ δ ⨾ σ ]) · (t₂ [ δ ⨾ σ ]) 
    ≡⟨ sym (cong₂ (_·_) ([][] {t = t₁}) ([][] {t = t₂})) ⟩≡
    (t₁ [ δ ] [ σ ]) · (t₂ [ δ ] [ σ ]) 
    ≡⟨ cong₂ _·_ (cong _[ σ ] p) q ⟩≡
    (u₁ [ δ ] [ σ ]) · (u₂ [ δ ] [ σ ])
    ≡⟨ cong₂ (_·_) ([][] {t = u₁}) ([][] {t = u₂}) ⟩≡
    (u₁ [ δ ⨾ σ ]) · (u₂ [ δ ⨾ σ ]) ∎))
\end{code}

Manually applying congruence rules has gotten quite tedious. \SC
would simplify this, by enabling matching on |p|, |q| and the four
instantiations of the composition law (\SC cannot take care of
inferring the necessary lemmas for an equational proof, but it can 
automatically chain them together).

Agda's |REWRITE| rules are also quite effective here: turning |[][]| into
a definitional equation reduces the proof to |cong₂ _·_ (cong _[ σ ] p) q|
(its support for non-ground equations making all possible instantiations
\sideremark{
Specifically, |t [ δ ] [ σ ] [ ξ ]| could reduce via |[][]| to
|t [ (δ ⨾ σ) ⨾ ξ ]| or to |t [ δ ⨾ (σ ⨾ ξ) ]|, which are not definitionally
equal .
}
hold definitionally).
However, |[][]| alone is not confluent (and indeed Agda with
|--local-confluence| checking enabled catches this). Non-confluent sets of
|REWRITE|
rules risk breaking subject reduction \sidecite{cockx2021taming}, so
avoiding them are important.

Turning associativity of |_⨾_| (|⨾⨾ : (δ ⨾ σ) ⨾ ξ ≡ δ ⨾ (σ ⨾ ξ)|)
into a |REWRITE| simultaneously with |[][]| repairs
confluence\remarknote{Technically, we also need 
|[]lookup : lookup i δ [ σ ] ≡ lookup i (δ ⨾ σ)| but this lemma is
required to prove |[][]| anyway.}, 
but of course requires proving this additional equation that isn't
directly necessary for our result. The situation is complicated even further
when we try to combine these rewrites with |i[i↦]| (which simplified the prior
|unify| case): |lookup i (δ [ i ↦ t ]) [ σ ]| can reduce to either 
|lookup i (δ [ i ↦ t ] ⨾ σ)| (by |[]lookup|) or |t [ σ ]| (by |i[i↦]|); we
need to prove additional laws about how |_[_↦_]| and |_⨾_| interact to
resolve this. 

In general, a particular algebraic structure one may wish to work with in a
\sideremark{One could, of course, imagine a proof assistant with support for
rewrite rules that can be locally enabled/disabled, but the state-of-the-art
in this area \sidecite[*3]{komel2021meta} leaves confluence/termination checking
for future work.}
proof assistant may not have a terminating and confluent presentation of its
equations (let alone such a presentation that a conservative, automatic
checker could identify as such). Global
|REWRITE| rules force the programmer to make careful decisions as to which
laws should be made definitional |REWRITE|s and which which should be kept 
propositional.
