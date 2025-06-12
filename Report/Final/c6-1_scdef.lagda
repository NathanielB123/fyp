%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils
open import Utils.IdExtras

module Report.Final.c6-1_scdef where

\end{code}
%endif

% https://discord.com/channels/427551550089723915/1378514733518553179/1378715303235682445

\setchapterpreamble[u]{\margintoc}

\chapter{Elaborating Smart Case}
\labch{scdef}

\section{A New Core Language}

To recap the findings of the previous chapter, 
locally-introduced equations caused two main issues
\begin{itemize}
\item Any restrictions on equations (enforced in order to retain decidability) 
      must
      be stable under substitution (to support introducing equations
      under λ-abstractions without losing subject reduction).
\item Any proofs by induction on the syntax must account for weakening
      the context with new equations. This is problematic for normalisation
      proofs, because neutral terms are not stable under introducing equations.
\end{itemize}

The latter of these issues is, in principle, solved if we give up
congruence of conversion over \SIF (or in general, whatever piece of syntax
happens to introduce equations). Specifically, if we give up

%if False
\begin{code}
module Cooked where
  open import Dependent.SCBool.Syntax hiding (if[]; 𝔹β₁; 𝔹β₂)

  wkeq : Tms (Γ ▷ t >eq b) Γ
  wkeq = π₁eq id

  wkeq~ :  ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
        →  Tms~ (Γ~ ▷ t~ >eq) Γ~ (wkeq {b = b}) wkeq
  wkeq~ t~ = π₁eq t~ id
\end{code}
%endif

\begin{code}
  if~  : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
       → Tm~ (Γ~ ▷ t~ >eq) (A~ [ wkeq~ t~ ]) u₁ u₂
       → Tm~ (Γ~ ▷ t~ >eq) (A~ [ wkeq~ t~ ]) v₁ v₂
       → Tm~ Γ~ A~ (if t₁ u₁ v₁) (if t₂ u₂ v₂)
\end{code}

then normalisation no longer needs to recurse into the LHS/RHS branches of
``|if|'' expressions until the scrutinee actually reduces to |TT| or |FF|.

The first issue can also be fixed by carefully relaxing the substitution law
for ``|if|'', |if[]|.

\begin{code}
  if[]  : Tm~ rfl~ rfl~  (if t u v [ δ ]) 
                         (if (coe~ rfl~ 𝔹[] (t [ δ ])) 
                         (coe~ rfl~ wk^eq (u [ δ ^eq t ])) 
                         (coe~ rfl~ wk^eq (v [ δ ^eq t ])))
\end{code}

Intuitively, we want substitutions to apply recursively to the scrutinee
(so we check if it reduces to |TT| or |FF|), but stack up on the LHS/RHS 
(so we do not invalidate the equation in each branch). One way we can achieve
this is by outright throwing away |if[]|, and generalising the
β-laws |𝔹β₁| and |𝔹β₂|

\begin{code}
  wk,Ty : Ty~ rfl~ (A [ δ ]) (A [ wkeq ] [ δ ,eq t~ ])

  𝔹β₁  : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) TT)
       → Tm~ rfl~ wk,Ty (if t u v [ δ ]) (u [ δ ,eq t~ ])
  𝔹β₂  : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) FF)
       → Tm~ rfl~ wk,Ty (if t u v [ δ ]) (v [ δ ,eq t~ ])
\end{code}

Using these new laws, the equational theory for ``|if|'' somewhat resembles
that of
a weak-head reduction strategy. That is, normalisation may halt as soon as
it hits a stuck ``|if|'' expression, instead of recursing into the branches.

This seems like an exciting route forwards. In practice, losing 
congruence of definitional equality
over case splits is not a huge deal, as the proof in question can always just
repeat the same case split, proving the desired equation in each 
branch separately. 
Unfortunately, from a metatheoretical standpoint,
non-congruent conversion is somewhat hard to justify. QIIT and GAT signatures,
for example,
bake-in congruence of the equational theory (we used an 
explicit conversion relation, |Tm~|, above for a reason).

The key insight in solving this comes in the form of
\emph{lambda lifting}.
For context, Agda's core language only supports pattern-matching at the
level of definitions, but it can still support
|with|-abstractions \sidecite{agda2024with} and 
pattern-matching lambdas \sidecite{agda2024lambda} via elaboration:
new top-level definitions are created for every ``local'' pattern-match.
Because definitions are \emph{generative}, from the perspective of the surface
language, Agda also loses congruence of conversion (actually, even
reflexivity of conversion) for pattern-matching
lambdas. For example, consider the equation between these two
seemingly-identical implementations of Boolean negation.

\begin{code}
not-eq : _≡_ {A = Bool → Bool}
             (λ where  true   → false 
                       false  → true) 
             (λ where  true   → false 
                       false  → true) 
\end{code}

Attempting to prove |not-eq| with reflexivity (|refl|) returns the error:

\begin{spec}
(λ { true → false ; false → true }) x !=
(λ { true → false ; false → true }) x of type Bool
Because they are distinct extended lambdas: one is defined at
   /home/nathaniel/agda/fyp/Report/Final/c6-1_scdef.lagda:110.15-111.37
and the other at
   /home/nathaniel/agda/fyp/Report/Final/c6-1_scdef.lagda:112.15-113.37,
so they have different internal representations.
\end{spec}

In \SCDef, we pull essentially the same trick. We can rigorously study
a core type theory which introduces equations via top-level definitions
(proving soundness and normalisation), and then describe an \emph{elaboration}
algorithm to take a surface language with an \SC-like construct, and
compile it into core \SCDef terms (by lifting \smart case-splits into
top-level definitions).

\subsection{Syntax}

To support global definitions, we introduce an additional 
sort: \emph{signatures} (|Sig|).
Signatures are similar to contexts in that they effectively store lists
of terms that we can reuse, but unlike contexts, signatures also store the
concrete implementation of every definition, and do not allow for
arbitrary substitution.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  Sig  : Set
  Ctx  : Sig → Set
\end{code}

We associate with |Sig| a set of morphisms, |Wk|, forming a
category of signature weakenings. |Ctx| is a presheaf on this category, and 
substitutions (|Tms|) are 
appropriately generalised to map between contexts paired with their signature
(we will embed signature weakenings into |Tms|).

%if False
\begin{code}
variable Ψ Φ Ξ : Sig
postulate
\end{code}
%endif

\begin{code}
  Ty   : Ctx Ξ → Set
  Tm   : ∀ (Γ : Ctx Ξ) → Ty Γ → Set
  Wk   : Sig → Sig → Set
  Tms  : Ctx Φ → Ctx Ψ → Set
\end{code}

%if False
\begin{code}
variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx Ψ
  A B C A₁ A₂ A₃ B₁ B₂ : Ty {Ξ = Ξ} Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  φ ψ ξ : Wk Φ Ψ
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  b b₁ b₂ : Bool

Ty≡ : Γ₁ ≡ Γ₂ → Ty {Ξ = Ξ} Γ₁ ≡ Ty Γ₂
Ty≡ = cong Ty

Tm≡ : ∀ Γ≡ → A₁ ≡[ Ty≡ {Ξ = Ξ} Γ≡ ]≡ A₂ → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂ 
Tm≡ = dcong₂ Tm

postulate
\end{code}
%endif

We consider all signature weakenings to be equal (i.e. every morphism
|Wk Φ Ψ| is unique; signature weakenings form a \emph{thin category}).

\begin{remark}[Specialised Substitutions] \phantom{a}
\labremark{scdefspecsub}

We could alternatively build a syntax taking non-generalised
(or ``specialised'')
substitutions as primitive 
(i.e. the signature contextualising the domain and range context
must be the same, {|Tms : Ctx Ξ → Ctx Ξ → Set|}). If we committed to this 
approach, we would have to add two distinct presheaf actions to |Ty| and |Tm| 
(one for |Wk| and one for |Tms|), and also ensure |Tms| itself is a 
displayed presheaf over signature weakenings.
Our category of generalised substitutions can then be derived by pairing
{|φ : Wk Φ Ψ|} and {|δ : Tms Δ Γ|} morphisms, with the overall effect
of on terms being to take them from context |Γ| to context |Δ [ γ ]|.

We will take exactly this approach in the strictified syntax, where it is
desirable for signature weakenings embedded in generalised substitutions to
compute automatically. For the explicit substitution presentation though,
defining generalised substitutions directly leads to a more concise
specification.
\end{remark}

We give the standard categorical combinators (substitution operations), 
and context extension (as in \refsec{dtlc}), 
eliding projections and equations for brevity.


\begin{code}
  id𝒲   : Wk Ψ Ψ
  _⨾𝒲_  : Wk Φ Ψ → Wk Ξ Φ → Wk Ξ Ψ

  id   : Tms Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  
  _[_]𝒲Ctx  : Ctx Ψ → Wk Φ Ψ → Ctx Φ
  _[_]Ty   : Ty Γ → Tms Δ Γ → Ty Δ
  _[_]     : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty)

  •       : Ctx Ξ
  _▷_     : ∀ (Γ : Ctx Ξ) → Ty Γ → Ctx Ξ

  ε      : Tms {Φ = Ξ} {Ψ = Ξ} Δ • 
  _,_    : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty) → Tms Δ (Γ ▷ A) 

\end{code}

%if False
\begin{code}
  π₁     : Tms Δ (Γ ▷ A) → Tms Δ Γ
\end{code}
%endif

Signatures are simply lists of definitions. Our first approximation for these 
definitions is a bundle containing a \emph{telescope} of
argument types |Γ : Ctx Ξ| (recall that contexts are just lists of types), 
a return  type |A : Ty Γ|, and a body |Tm Γ A|.

\sideremark{Note that |•𝒮| is the terminal object in the category of 
signature weakenings. After we define single-weakenings, we can derive the 
associated morphism |Wk Φ •𝒮| by composing them.}

\begin{code}
  •𝒮       : Sig
  _▷_⇒_≔_  : ∀ Ξ (Γ : Ctx Ξ) A → Tm Γ A → Sig
\end{code}

Intuitively, to call a definition with argument
telescope |Γ| while in a context |Δ|, we must provide an appropriate list of
arguments, specifically a list |Δ|-terms matching each type in |Γ|.
This is exactly a substitution (|Tms Δ Γ|).

Of course, we also want to be able to put 
equational assumptions in contexts, as in \SCBool.

%if False
\begin{code}
module ArbEq where
  postulate
\end{code}
%endif

\begin{code}
    _▷_~_   : ∀ (Γ : Ctx Ξ) {A} → Tm Γ A → Tm Γ A → Ctx Ξ
    _,eq′_  : ∀ (δ : Tms Δ Γ) → t₁ [ δ ] ≡ t₂ [ δ ]
            → Tms Δ (Γ ▷ t₁ ~ t₂)
\end{code}

%if False
\begin{code}
    π₁eq   : Tms Δ (Γ ▷ t₁ ~ t₂) → Tms Δ Γ

  wkeq : Tms (Γ ▷ t₁ ~ t₂) Γ
  wkeq = π₁eq id

  postulate
\end{code}
%endif

Rather than shying away from this generalisation,
and defining specific argument
telescope/argument list types, we commit fully to our extended notions of
context and substitution, and take advantage of the flexibility.

Specifically, placing equations in argument telescopes gives
us a way to preserve definitional equalities across definition-boundaries.
Intuitively, to call a definition that asks for a definitional equality
between |t₁| and |t₂| (its argument telescope contains |t₁ ~ t₂|),
the caller must provide evidence that {|t₁ [ δ ] == t₂ [ δ ]|}
(where |δ| is the list of arguments prior to the equation). In other words,
to call a function that asks for a definitional equality, that equation
must also hold definitionally at the call-site.

With that said, by only preserving equations (not reflecting new ones)
our definitions are still more limited than we need for \SCDef. Analogously
to let-bindings, we could inline the body of every definition
and retain a well-typed program (so their only possible application
as-currently-defined, like let-bindings, would be to factor out code reuse).
We support equality reflection local to each definition by allowing
them to each block on one propositional equality.

\begin{code}
    Id : ∀ A → Tm Γ A → Tm Γ A → Ty Γ
    
    _▷_⇒_reflects_≔_  : ∀ Ξ (Γ : Ctx Ξ) A {B t₁ t₂} → Tm Γ (Id B t₁ t₂)
                    → Tm (Γ ▷ t₁ ~ t₂) (A [ wkeq ]Ty)
\end{code}

Note that the return type of the definition, |A|, must still be valid without
the equational assumption, and therefore weakened while typing the body. 
If this were not the case, the result of calling definitions could
be ill-typed ({|t₁ [ δ ] == t₂ [ δ ]|} may not hold at the call-site).

Note that while each individual definition can only reflect one equation
at a time, definitions can depend on each other linearly, and 
preserve previous reflected equations (by asking for them in their
argument telescopes), so nesting multiple equality reflections.

\subsubsection{Returning to Booleans}

For closer comparison with \SCBool, and frankly, to simplify the coming
normalisation proof, we return to only supporting Boolean equations.

%if False
\begin{code}
postulate
  𝔹     : Ty Γ
  𝔹[]   : 𝔹 [ δ ]Ty ≡ 𝔹
  TT FF : Tm Γ 𝔹

⌜_⌝𝔹  : Bool → Tm Γ 𝔹
⌜ true  ⌝𝔹 = TT
⌜ false ⌝𝔹 = FF

postulate
\end{code}
%endif



\begin{code}
  _▷_>eq_  : ∀ (Γ : Ctx Ξ) → Tm Γ 𝔹 → Bool → Ctx Ξ
  _,eq_    : ∀ (δ : Tms Δ Γ) → t [ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ ⌜ b ⌝𝔹
           → Tms Δ (Γ ▷ t >eq b)
\end{code}

%if False
\begin{code}
  π₁>eq    : Tms Δ (Γ ▷ t >eq b) → Tms Δ Γ
wkeq : Tms (Γ ▷ t >eq b) Γ
wkeq = π₁>eq id
\end{code}
%endif

We could retain the existing |_▷_⇒_reflects_≔_|-style definition
by adding the appropriate restriction the RHS term (it needs to be
a closed Boolean). 
Together with the ordinary
% TODO : Ref splitters
dependent ``|if|'', we can recover \SIF by splitting on the 
scrutinee |t : Tm Γ 𝔹| and calling the appropriate definition with 
the propositional evidence {|Tm Γ (Id 𝔹 t TT|)|}/{|Tm Γ (Id 𝔹 t FF|)|}
in each branch.

For simplicity though, we instead fuse this notion of case-splitting
into the signature definitions. 
Instead of blocking on a propositional equation, definitions now block on a 
|𝔹|-typed scrutinee, and reduce to the LHS or RHS when the substituted
scrutinee becomes convertible to |TT| or |FF|.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  _▷_⇒_if_≔_∣_  : ∀ Ξ (Γ : Ctx Ξ) A (t : Tm Γ 𝔹) 
                → Tm (Γ ▷ t >eq true)   (A [ wkeq ]Ty) 
                → Tm (Γ ▷ t >eq false)  (A [ wkeq ]Ty)
                → Sig
\end{code}

As well as cutting down on the number of term formers, this removes
our dependence on having a propositional equality type.

We now define single signature weakenings, and the embedding of signature
weakenings into substitutions

\begin{code}
  wk𝒲   : Wk (Ψ ▷ Γ ⇒ A if t ≔ u ∣ v) Ψ
  wk𝒮   : Tms (Γ [ wk𝒲 {t = t} {u = u} {v = v} ]𝒲Ctx) Γ
\end{code}

\begin{spec}
⌜_⌝𝒲 : ∀ (φ : Wk Φ Ψ) → Tms (Γ [ φ ]𝒲Ctx) Γ
⌜ id     ⌝𝒲 = subst (λ □ → Tms □ _) (sym [id]) id
⌜ φ ⨾ ψ  ⌝𝒲 = subst (λ □ → Tms □ _) [][] (⌜ φ ⌝𝒲 ⨾ ⌜ ψ ⌝𝒲)
⌜ wk𝒮    ⌝𝒲 = wk𝒮
\end{spec}

%if False
\begin{code}
⌜_⌝𝒲 : ∀ (φ : Wk Φ Ψ) → Tms (Γ [ φ ]𝒲Ctx) Γ

postulate
  ▷>eq[] : (Γ ▷ t >eq b) [ φ ]𝒲Ctx 
         ≡ (Γ [ φ ]𝒲Ctx) ▷ (subst (Tm _) 𝔹[] (t [ ⌜ φ ⌝𝒲 ])) >eq b

postulate
\end{code}
%endif

Finally, we give the term former for function calls. Because terms are
a presheaf on signature weakenings, we only need to handle the case where
the called definition is the last one in the signature (in the strictified 
syntax, we instead use first-order de Bruijn variables).

\begin{code}
  call : Tm {Ξ = Ξ ▷ Γ ⇒ A if t ≔ u ∣ v} (Γ [ wk𝒲 ]𝒲Ctx) (A [ wk𝒮 ]Ty)

\end{code}

%if False
\begin{code}
wk𝒮⨾Tm  :  t [ wk𝒮 ⨾ δ ]
        ≡[ Tm≡ refl (𝔹[] ∙ sym 𝔹[]) ]≡
           subst (Tm (Γ [ wk𝒲 ]𝒲Ctx)) 𝔹[] (t [ ⌜ wk𝒲 ⌝𝒲 ]) [ δ ]

wkeq𝒮,Ty : ∀ {t≡ : t [ wk𝒮 ⨾ δ ] ≡[ Tm≡ {Ξ = Ξ} (refl {x = Γ}) 𝔹[] ]≡ ⌜ b ⌝𝔹}
         → A [ wkeq ]Ty 
             [  wk𝒮 ⨾ subst (Tms _) (sym ▷>eq[]) 
                (δ ,eq (sym[] {p = Tm≡ refl (sym 𝔹[])} wk𝒮⨾Tm ∙ t≡)) ]Ty 
         ≡ A [ wk𝒮 ]Ty [ δ ]Ty

postulate
\end{code}
%endif

Note that we also do not ask for a list of arguments here. Explicit 
substitutions handle this for us.

Of course, the β-laws for |call| must account for the list of arguments,
and so target substituted |call| expressions.

\begin{code}
  call-TT  :  ∀ (t≡ : t [ wk𝒮 ⨾ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ TT)
           →  call {t = t} {u = u} [ δ ]
           ≡[ Tm≡ refl (sym wkeq𝒮,Ty) ]≡
              u [  wk𝒮 ⨾ subst (Tms _) (sym ▷>eq[]) 
                   (δ ,eq (sym[] {p = Tm≡ refl (sym 𝔹[])} wk𝒮⨾Tm ∙ t≡)) ]
  call-FF  :  ∀ (t≡ : t [ wk𝒮 ⨾ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ FF)
           →  call {t = t} {v = v} [ δ ]
           ≡[ Tm≡ refl (sym wkeq𝒮,Ty) ]≡
              v [  wk𝒮 ⨾ subst (Tms _) (sym ▷>eq[]) 
                   (δ ,eq (sym[] {p = Tm≡ refl (sym 𝔹[])} wk𝒮⨾Tm ∙ t≡)) ]
\end{code}

Dealing with explicit substitutions here gets a little messy, but the key idea
is just that if the scrutinee is convertible to |TT| or |FF| after substituting
in the arguments, then the call should reduce to the appropriate branch. 
We have made use
of the following two commuting lemmas.

\begin{spec}
wk𝒮⨾Tm  :  t [ wk𝒮 ⨾ δ ]
        ≡[ Tm≡ refl (𝔹[] ∙ sym 𝔹[]) ]≡
           subst (Tm (Γ [ wk𝒲 ]𝒲Ctx)) 𝔹[] (t [ ⌜ wk𝒲 ⌝𝒲 ]) [ δ ]

wkeq𝒮,Ty  : ∀ {t≡ : t [ wk𝒮 ⨾ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ TT}
          → A  [  wkeq ]Ty 
               [  wk𝒮 ⨾ subst (Tms _) (sym ▷>eq[]) 
                  (δ ,eq (sym[] {p = Tm≡ refl (sym 𝔹[])} wk𝒮⨾Tm ∙ t≡)) ]Ty 
          ≡ A  [  wk𝒮 ]Ty [ δ ]Ty
\end{spec}

We do not need any other substitution laws for |call|. The composition functor
law is already enough for additional substitutions to recursively apply to
the argument list (by composing the substitutions).

\begin{spec}
call [ δ ] [ σ ] ≡ call [ δ ⨾ σ ]
\end{spec}

\subsection{Soundness}

We prove soundness of \SCDef by constructing a model. Our model contains two
notions of environments: one relating to signatures
(we denote signature environments with ``|χ|'') and 
one to local contexts (we denote context environments with ``|ρ|'' as usual).
Signature weakenings can be interpreted as functions between signature
environments,
while generalised substitutions become pairs of signature environment 
and context environment mappings.

\begin{code}
⟦Sig⟧ : Set₁
⟦Sig⟧ = Set
\end{code}
%if False
\begin{code}
variable
  ⟦Ψ⟧ ⟦Φ⟧ ⟦Ξ⟧ : ⟦Sig⟧ 
\end{code}
%endif
\begin{code}
⟦Ctx⟧ : ⟦Sig⟧ → Set₁
⟦Ctx⟧ ⟦Ψ⟧ = ⟦Ψ⟧ → Set

⟦Ty⟧ : ⟦Ctx⟧ ⟦Ψ⟧ → Set₁
⟦Ty⟧ ⟦Γ⟧ = ∀ χ → ⟦Γ⟧ χ → Set

⟦Tm⟧ : ∀ (⟦Γ⟧ : ⟦Ctx⟧ ⟦Ψ⟧) → ⟦Ty⟧ ⟦Γ⟧ → Set
⟦Tm⟧ ⟦Γ⟧ ⟦A⟧ = ∀ χ ρ → ⟦A⟧ χ ρ

⟦Wk⟧ : ⟦Sig⟧ → ⟦Sig⟧ → Set
⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ = ⟦Φ⟧ → ⟦Ψ⟧

⟦[]Ctx⟧ : ⟦Ctx⟧ ⟦Ψ⟧ → ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ → ⟦Ctx⟧ ⟦Φ⟧
⟦[]Ctx⟧ ⟦Γ⟧ ⟦δ⟧ = λ χ → ⟦Γ⟧ (⟦δ⟧ χ)

⟦Tms⟧ : ⟦Ctx⟧ ⟦Φ⟧ → ⟦Ctx⟧ ⟦Ψ⟧ → Set
⟦Tms⟧ {⟦Φ⟧ = ⟦Φ⟧} {⟦Ψ⟧ = ⟦Ψ⟧} ⟦Δ⟧ ⟦Γ⟧ 
  = Σ⟨ ⟦δ⟧ ∶ ⟦Wk⟧ ⟦Φ⟧ ⟦Ψ⟧ ⟩× (∀ {χ} → ⟦Δ⟧ χ → ⟦[]Ctx⟧ ⟦Γ⟧ ⟦δ⟧ χ)

⟦_⟧Sig  : Sig → ⟦Sig⟧
⟦_⟧Ctx  : Ctx Ψ → ⟦Ctx⟧ ⟦ Ψ ⟧Sig
⟦_⟧Ty   : Ty Γ → ⟦Ty⟧ ⟦ Γ ⟧Ctx
⟦_⟧Tm   : Tm Γ A → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
⟦_⟧Wk   : Wk Φ Ψ → ⟦Wk⟧ ⟦ Φ ⟧Sig ⟦ Ψ ⟧Sig 
⟦_⟧Tms  : Tms Δ Γ → ⟦Tms⟧ ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx
\end{code}

The interpretations of ordinary constructs from dependently-typed lambda
calculus are mostly unchanged 
in this new model, except for having to account for both environments.
E.g. |Π|-types are now interpreted as

\begin{spec}
⟦ Π A B ⟧Ty = λ χ ρ → ∀ tⱽ → ⟦ B ⟧Ty χ (ρ Σ, tⱽ)
\end{spec}

We therefore focus on the new cases. Local equations are
interpreted as propositional equations, as in \SCBool (\refsec{scboolsound})
and the new presheaf action on contexts is just function composition.

\begin{spec}
⟦ Γ ▷ t >eq b  ⟧Ctx = λ χ → Σ⟨ ρ ∶ ⟦ Γ ⟧Ctx χ ⟩× ⟦ t ⟧Tm χ ρ ≡ b
⟦ Γ [ δ ]Ctx   ⟧Ctx = λ χ → ⟦ Γ ⟧Ctx (⟦ δ ⟧Wk χ)
\end{spec}

As previously mentioned, we interpret signatures as environments.
Our Boolean-splitting definitions are interpreted with a single body,
plus equations it evaluates
evaluate to the appropriate branch depending on which closed Boolean the
scrutinee reduces to.

\begin{spec}
⟦ •𝒮                        ⟧Sig = ⊤
⟦ Ξ ▷  Γ ⇒ A if t ≔ u ∣ v   ⟧Sig
  =  Σ⟨  χ ∶ ⟦ Ξ ⟧Sig ⟩× 
     Σ⟨  f ∶ (∀ ρ → ⟦ A ⟧Ty χ ρ) ⟩×
         (∀ ρ (t≡ : ⟦ t ⟧Tm χ ρ ≡ true) 
         → f ρ ≡ ⟦ u ⟧Tm χ (ρ Σ, t≡)) ×   
         (∀ ρ (t≡ : ⟦ t ⟧Tm χ ρ ≡ false)
         → f ρ ≡ ⟦ v ⟧Tm χ (ρ Σ, t≡))
\end{spec}

Single signature weakenings are interpreted as projections:

\begin{spec}
⟦ wk𝒲  ⟧Wk   = fst
⟦ wk𝒮  ⟧Tms  = fst Σ, λ ρ → ρ
\end{spec}

and calls to definitions merely project out the body

\begin{spec}
⟦ call ⟧Tm (χ Σ, f Σ, f-tt Σ, f-ff) ρ 
  = f ρ
\end{spec}

The only non-trivial equations arise from |π₂eq| and |callTT|/|callFF|.
We can account for the former of these using the equation in the environment
and function extensionality, as in \SCBool. The computation laws for |call|
also require function extensionality; depending on whether the scrutinee
reduces to |TT| or |FF|, we apply the relevant equation in the signature
environment.
