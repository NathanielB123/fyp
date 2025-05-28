%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils hiding (ε)
open import Utils.IdExtras

module Report.Final.c11_scbool where

\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{A Minimal Language with Smart Case}
\labch{scbool}

\newcommand{\SCBool}{$\textsf{SC}^\textsc{Bool}$\xspace}

In this chapter, we introduce and study a minimal dependently-typed language
featuring a \SC-like elimination principle for Booleans. We name
this language \SCBool.

\section{Syntax}

Following on from our simply-typed examples, we will aim to stick with the 
intrinsically-typed discipline. For dependently-typed languages, however,
avoiding untyped syntax raises some new challenges. We resolve these by
switching to explicit substitutions and quotienting by conversion. 
% TODO add sentence about how we translated quotiented syntax into Agda

% TODO: Add note on weak type theory (Winterhalter is a nice reference)
Specifically, dependently-typed languages include computation at the type level,
in other words, type-equality (or \textit{convertibility}) is no longer purely 
syntactic. For example,
in ITT with large-elimination on booleans, we
would expect |x : Tm Γ (if TT then A else B)| to be usable in places where
terms of type |A| are expected (i.e. |if TT then A else B| and |A| are
convertible). Note how this relaxation of convertibility is seemingly in 
conflict with how we have previously defined the rules of our typed syntax - 
e.g. the repetition of |A| in |_·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B| implicitly
enforces that the domain of the function and the type of the argument are
equal on-the-nose (specifically, equal w.r.t. to the ambient notion of the
meta's propositional equality, which for ordinary inductive
types that we have used so far, corresponds to raw syntactic equality).

One could imagine trying to account for this by simultaneously defining the
syntax and normalisation (i.e. ensuring the types which index terms are always
normalised), but in practice this approach appears to be far too mutual to
be manageable (defining intrinsically-typed syntax mutually with recursive
substitutions alone remains out of reach in modern proof assistants).

As an alternative then, we shall define a syntax with explicit substitutions
and simultaneously \textit{quotient} by conversion,
producing a quotient-inductive-inductive, QII,
definition of our syntax. Specifically constructors and equations will be
interleaved, and propositional equality on terms will correspond
exactly with conversion.

Such syntaxes are often also referred to as 
``algebraic'' given there is a close correspondence between QII signatures
and generalised algebraic theories (GATs) \sidecite{kovacs2020large}. 
They can also be seen as ``categorical''
in the sense that our equations will ensure substitutions form a category,
with types and terms presheaves and dependent presheaves on substitutions
respectively - the syntax we will end up with is essentially a category with 
families (CwF) \sidecite{dybjer1995internal} with a few extensions to properly 
support \SC.

% TODO: We should create a format for "Agda boxes" which detail stuff about
% mechanisation!
As a quick side-note, it is perhaps worth mentioning that the syntax detailed 
below 
has been fully
mechanised in \textsf{-{}-safe} Agda, available at 
\url{https://github.com/NathanielB123/fyp/blob/main/Dependent/SCBool/Syntax.agda}. 
We detail the differences between the 
(somewhat cleaner) presentation here and the Agda encoding in \refsec{quotset}.

%TODO A note on examples (naming variables, ignoring weakenings)
% We should also mention, that while our syntax will, in the de Bruijn tradition,
% avoid named variables and include explicit weakenings (though not actually
% contain de Bruijn variables directly - we will explain why an explicit
% substitution calculus makes this unnecessary), when giving examples, named
% variables and eliding weakening results produces clearer 
% (more human-readable, or at least computer-scientist-readable) terms.
% Translation between de Bruijn variables and named representation is standard
% in the literature, so we will not cover this explicitly.


To start, our syntax will contain four sorts, representing contexts, types,
terms and substitutions (lists of terms):

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  Ctx  : Set
  Ty   : Ctx → Set
  Tm   : ∀ Γ → Ty Γ → Set
  Tms  : Ctx → Ctx → Set
\end{code}

%if False
\begin{code}
variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  b b₁ b₂ : Bool
\end{code}
%endif

\subsection{Types and Contexts}

We start by defining contexts and types. As usual, contexts can be 
constructed out of backwards lists of types:

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  •    : Ctx
  _▷_  : ∀ Γ → Ty Γ → Ctx 
\end{code}

For our minimal language, we will include only Booleans and Π as our canonical
type-formers.

\begin{code}
  𝔹  : Ty Γ   
  Π  : ∀ A → Ty (Γ ▷ A) → Ty Γ
\end{code}

We must also witness the action of substitutions (i.e. explicit
substitutions on types), and we also include large elimination on Booleans to 
ensure
the existence of ``real'' type-term dependencies (so compiling away
dependencies as in \sidecite{geuvers1994short, barras1997coq} is impossible).

\sideremark{Note that our large elimination principle for Booleans, |ifTy|, 
does not add
equations to the context as one might expect from a \smart-|if|. The constructor
corresponding to term-level \SC for Booleans will come later. Making type-level
|if| \smart in the same way should not pose many additional challenges, but 
we retain the more standard rule for simplicity.}

\begin{code}
  _[_]Ty  : Ty Γ → Tms Δ Γ → Ty Δ
  ifTy    : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ
\end{code}

To support \SC, we also need to be able to extend contexts with
rewrites. We will focus only on Boolean rewrites for now.

\begin{code}
  _▷_>rw_ : ∀ Γ → Tm Γ 𝔹 → Bool → Ctx
\end{code}

Note that the LHSs of these rewrites are entirely unconstrained. 
E.g. there is nothing
preventing us from adding clearly inconsistent (|TT >rw false|) or redundant
(|TT >rw true|) equations. We will elaborate on this aspect of our syntax in
\refsec{incon}.

We now state the computation rules for substitutions acting on types.
We rely on functoriality of context extension |_^_|, which we shall derive
later:

\begin{code}
_^_ :  ∀ (δ : Tms Δ Γ) A → Tms (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A)
\end{code}

As an operation on substitutions, we refer to |_^_| as ``lifting'' the 
substitution over the type we extend by.

%if False
\begin{code}
postulate
\end{code}
%endif

% TODO: if[]
\begin{code}
  𝔹[]   : 𝔹         [ δ ]Ty ≡ 𝔹
  Π[]   : Π A B     [ δ ]Ty ≡ Π (A [ δ ]Ty) (B [ δ ^ A ]Ty)
\end{code}

\subsection{Substitutions}

We are now ready to define substitutions. As usual, we find it useful to think
of substitutions as lists of terms (substitutes). 
We index by two contexts: the context
we are mapping into (i.e. that all the substitutes exist in) and the context
we are mapping from (i.e. the types of all substitutes, in sequence).

First of all, substitutions must form a category, so we include identity and 
composition.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  id   : Tms Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
\end{code}

We also add the action witnessing the functoriality of terms (i.e. explicit 
substitution).

\begin{code}
  _[_] : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty)
\end{code}

We now add constructors corresponding to lists of terms: the empty list,
cons-ing on a single term and the inverse operations projecting out the
term and the un-consed list.

\begin{code}
  ε    : Tms Δ •
  _,_  : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty) → Tms Δ (Γ ▷ A) 
  π₁   : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₂   : ∀ (δ : Tms Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]Ty)
\end{code}

These rules are sufficient for mapping between contexts of types alone, but
of course in our setting, contexts can also contain equations. To motivate our
approach towards accounting for this, we focus on |_,_|: to map from a context
extended with an additional type, we must provide a substitute for all variables
of that type. Analagously, to map from a context extended with a rewrite, we 
must provide an appropriate ``alternative'' to the rewrite.

The purpose of rewrites in terms is to be used inside conversion derivations.
Therefore, we take the appropriate notion of ``alternative'' to be
evidence of convertibility between the LHS of the rewrite with the substitution
applied.

%if False
\begin{code}
⌜_⌝𝔹 : Bool → Tm Γ 𝔹
postulate
\end{code}
%endif

\begin{code}
  _,rw_  :  ∀ (δ : Tms Δ Γ) → t [ δ ] ≡[ cong (Tm Δ) 𝔹[] ]≡ ⌜ b ⌝𝔹
         →  Tms Δ (Γ ▷ t >rw b)
  π₁rw   :  Tms Δ (Γ ▷ t >rw b) → Tms Δ Γ
  π₂rw   :  ∀ (δ : Tms Δ (Γ ▷ t >rw b)) 
         →  t [ π₁rw δ ] ≡[ cong (Tm Δ) 𝔹[] ]≡ ⌜ b ⌝𝔹
\end{code}

Note that requiring convertibility evidence (as opposed to e.g. evidence of the
substituted rewrite exactly occurs somewhere in |Δ|) enables removing rewrites
from contexts when they become redundant. 

Knowing substitutions are a category and having access to the |π₁|, |π₂|, 
|π₁rw| and |π₂rw| projections is quite powerful, from these facts alone we can 
derive single weakenings and the existence of the de Bruijn zero variable.

\begin{code}
wk    : Tms (Γ ▷ A) Γ
wkrw  : Tms (Γ ▷ t >rw b) Γ

wk    = π₁ id
wkrw  = π₁rw id

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ ▷ A) Γ
δ ⁺ A = δ ⨾ wk

_⁺_>rw_ : Tms Δ Γ → ∀ t b → Tms (Δ ▷ t >rw b) Γ
δ ⁺ t >rw b = δ ⨾ wkrw

vz  :  Tm (Γ ▷ A) (A [ wk ]Ty)
vz  =  π₂ id
\end{code}

We do not even need a direct rule for deriving convertibility from a rewrite
in the context: projecting from identity is sufficient!

\begin{code}
rw : t [ wkrw ] ≡[ cong (Tm (Γ ▷ t >rw b)) 𝔹[] ]≡ ⌜ b ⌝𝔹
rw = π₂rw id
\end{code}

For substitutions to form a category, identity and composition must satisfy
the expected laws.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  id⨾  : id  ⨾ δ   ≡ δ
  ⨾id  : δ   ⨾ id  ≡ δ
  ⨾⨾   : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
\end{code}

For types to be a presheaf (and terms a dependent presheaf) on substitutions, we
must have identity and composition laws.

\begin{code}
  [id]Ty  : A [ id ]Ty ≡ A
  [][]Ty  : A [ δ ]Ty [ σ ]Ty ≡ A [ δ ⨾ σ ]Ty
  [id]    : t [ id ] ≡[ cong (Tm Γ) [id]Ty ]≡ t
  [][]    : t [ δ ] [ σ ] ≡[ cong (Tm Θ) [][]Ty ]≡ t [ δ ⨾ σ ]
\end{code}

We can finally show functoriality of context extension by weakening 
all terms in the substitution and appending the zero variable.

\begin{code}
δ ^ A = (δ ⁺ (A [ δ ]Ty)) , subst (Tm _) [][]Ty vz
\end{code}

We can derive an analagous operation for lifting substitutions over rewrites, 
though the equational reasoning gets a little cluttered.

% TODO: Consider fancy formatting approaches to hide redundant lines in
% proofs like these. For example, could we have an identity like function
% which is interpreted as "\phantom{}", or at least changing colour?
\begin{code}
_^_>rw_  :  ∀ (δ : Tms Δ Γ) t b 
         →  Tms (Δ ▷ subst (Tm Δ) 𝔹[] (t [ δ ]) >rw b) (Γ ▷ t >rw b)
δ ^ t >rw b 
  =    (δ ⁺ (subst (Tm _) 𝔹[] (t [ δ ])) >rw b) 
  ,rw  (begin≅ 
    subst (Tm _) 𝔹[] (t [ δ ⁺ _ >rw b ]) 
    ≅⟨ subst-removable _ _ _ ⟩≅ 
    t [ δ ⁺ _ >rw b ]
    ≅⟨ sym [][] ⟩≡
    subst (Tm _) [][]Ty (t [ δ ] [ wkrw ]) 
    ≅⟨ subst-removable _ _ _ ⟩≅
    t [ δ ] [ wkrw ]
    ≅⟨ hsym rm-subst ⟩≅
    subst (Tm _) 𝔹[] (t [ δ ]) [ wkrw ]
    ≅⟨ hsym (subst-removable _ _ _) ⟩≅
    subst (Tm _) 𝔹[] (subst (Tm _) 𝔹[] (t [ δ ]) [ wkrw ]) 
    ≅⟨ rw ⟩≡
    ⌜ b ⌝𝔹 ≅∎)
  where 
    rm-subst =  cong-subst-removable (Tm _) 𝔹[] 
                (_[ (wkrw {t = subst (Tm _) 𝔹[] (t [ δ ])}) ]) 
                (t [ δ ])
\end{code}

Δ∅𝒞§Ωᶜ

We also take the time to prove a few useful substitution lemmas.
Specifically that substitutions on closed Booleans can be ignored, that 
following a single weakening with a single substitution
has no overall effect, and that single weakening commutes with |_^_|.

TODO: Actually write the proofs of these lemmas.
\begin{code}
⌜⌝𝔹[] : ⌜ b ⌝𝔹 [ δ ] ≡[ cong (Tm Δ) 𝔹[] ]≡ ⌜ b ⌝𝔹

wk<>Ty : A [ wk ]Ty [ id , u ]Ty ≡ A
wk<>   : t [ wk ] [ id , u ] ≡[ cong (Tm _) wk<>Ty ]≡ t

wk<>rwTy  : A [ wkrw ]Ty [ id ,rw ⌜⌝𝔹[] {b = b} ]Ty ≡ A
wk<>rw    : t [ wkrw ] [ id ,rw ⌜⌝𝔹[] {b = b} ] ≡[ cong (Tm Γ) wk<>rwTy ]≡ t

wk^rwTy : A [ wkrw ]Ty [ δ ^ t >rw b ]Ty ≡ A [ δ ]Ty [ wkrw ]Ty
\end{code}


\subsection{Terms}

Finally, we get onto defining our term syntax. Introduction rules for 𝔹 and
Π are as usual.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  ƛ_  : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  TT  : Tm Γ 𝔹
  FF  : Tm Γ 𝔹
\end{code}

Elimination rules are a little more interesting. We derive application
from the existence of an operation that inverts |ƛ_|:

\begin{code}
  ƛ⁻¹_ : Tm Γ (Π A B) → Tm (Γ ▷ A) B

_·_ :  Tm Γ (Π A B) → ∀ (u : Tm Γ A) 
    →  Tm Γ (B [ id , subst (Tm Γ) (sym [id]Ty) u ]Ty)
t · u = (ƛ⁻¹ t) [ id , subst (Tm _) (sym [id]Ty) u ]
\end{code}

|ƛ⁻¹_| is sometimes called ``categorical'' application and is common in 
CwF-style presentations \sidecite{altenkirch2016type}. Its action is effectively
to instantiate the 
variable bound by the LHS function with the first variable in the context.

When eliminating Booleans, the primary goal of \SCBool is to be \smart. Rather
than asking for a motive, we will add the appropriate rewrite to the context
in the LHS and RHS.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  if  :  ∀ (t : Tm Γ 𝔹) 
      →  Tm (Γ ▷ t >rw true)   (A [ wkrw ]Ty) 
      →  Tm (Γ ▷ t >rw false)  (A [ wkrw ]Ty)
      →  Tm Γ A
\end{code}

Note that the ultimate return type must be weakened in the left and right
branches - the validity of the type of the LHS/RHS itself cannot depend on the
rewrite, only the validity of the term.

As previously mentioned, there is no need to introduce variables and embed them 
into our term syntax and projections from identity substitutions and the 
presheaf action are sufficient to encode all de Bruijn variables. This
means we are actually already done with term constructors, and all that
remains are the various computation rules.

Substitution acts on various introduction rules as one would expect.

\begin{code}
  ƛ[]   : ((ƛ t) [ δ ]) ≡[ cong (Tm Δ) Π[] ]≡ (ƛ (t [ δ ^ A ]))
  TT[]  : (TT [ δ ]) ≡[ cong (Tm Δ) 𝔹[] ]≡ TT
  FF[]  : (FF [ δ ]) ≡[ cong (Tm Δ) 𝔹[] ]≡ FF
\end{code}

It turns out the action of substitution on |ƛ⁻¹_| is derivable from |β| and |η|
laws. Such is not the case for |if| unfortunately (we do not have an |η| law
for |𝔹|), so we define this interaction explicitly.

\begin{code}
  if[]  :  if t u v [ δ ] 
        ≡  if (subst (Tm _) 𝔹[] (t [ δ ]))
              (subst (Tm _) wk^rwTy (u [ δ ^ t >rw true ])) 
              (subst (Tm _) wk^rwTy (v [ δ ^ t >rw false ])) 
\end{code}

A while ago now, we assumed we had some way of embedding |Bool| into |Tm Γ 𝔹|,
we define this embedding explicitly now.

\begin{code}
⌜ true   ⌝𝔹 = TT
⌜ false  ⌝𝔹 = FF
\end{code}

TODO: Stuff

\begin{code}
⌜⌝𝔹[] {b = true}   = TT[]
⌜⌝𝔹[] {b = false}  = FF[]
\end{code}

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  ifTT : if TT u v ≡[ cong (Tm Γ) (sym wk<>rwTy) ]≡ u [ id ,rw TT[] ]
  ifFF : if FF u v ≡[ cong (Tm Γ) (sym wk<>rwTy) ]≡ v [ id ,rw FF[] ]

  β : ƛ⁻¹ (ƛ t) ≡ t
\end{code}

\subsection{Definitional Inconsistency}
\labsec{incon}

\begin{definition}[Definitional context inconsistency] \phantom{a}\\\\
An \SCBool context is considered def.-inconsistent iff under that
context, |TT| and |FF| are convertible.

\textnormal{\begin{code}
incon : Ctx → Set
incon Γ = _≡_ {A = Tm Γ 𝔹} TT FF
\end{code}}
\end{definition}

Importantly, note that |incon| is derivable even when all equations in the
context individually are not def.-inconsistent (i.e. are not
|TT >rw false| or |FF >rw true|). For example 
|Γ = (x : 𝔹) ▷ x >rw true ▷ (λ y. y) x >rw false|. Deciding definitional
(in)consistency of contexts relies on at least normalisation (really, 
completion) and so pre-conditions relating to such a principle in the syntax
are likely to cause issues. 

We can of course prove that in def.-inconsistent contexts, equality
``collapses'' (in the sense of \sidecite{conor2010wtypes}). The key idea is to 
set up the
chain of equations \\|t ≡ if TT then t else u 
≡ if FF then t else u ≡ u|.
As an introduction to working
with explicit substitutions, we will now show how to prove this fully 
explicitly.

\begin{definition}[Equality collapse]\phantom{a}\\\\
We define the condition for equality collapse as contexts in which all terms
are convertible.

\textnormal{\begin{code}
collapse : Ctx → Set
collapse Γ = ∀ A (t u : Tm Γ A) → t ≡ u
\end{code}}
\end{definition}

\begin{remark}[Equality collapses in inconsistent contexts]\phantom{a}\\
\textnormal{\begin{code}
incon-collapse : ∀ Γ → incon Γ → collapse Γ
\end{code}}

Given |_≡_ {A = Tm Γ 𝔹} TT ≡ FF|, we are tasked with proving 
|t ≡ u| for arbitrary terms |t u : Tm Γ A|. The key idea is to follow the chain
of equations |t ≡ if TT then t else u ≡ if FF then t else u ≡ u|, but we must
take care to account for explicit substitution and weakening. 

E.g. The |t| and |u| inside the |if| must be weakened to account for the new 
rewrite, and contracting the |if| requires explicitly instantiating this
rewrite with another substitution. Our |wk<>rw| lemma from earlier is exactly
what we need to show that these substitutions ultimately have no effect.

\begin{code}
incon-collapse Γ p A t u = 
  t
  ≡⟨ sym (subst-subst-sym wk<>rwTy) ⟩≡
  subst (Tm Γ) wk<>rwTy (subst (Tm Γ) (sym wk<>rwTy) t)
  ≡⟨ cong (subst (Tm Γ) wk<>rwTy) (sym[] wk<>rw) ⟩≡
  subst (Tm Γ) wk<>rwTy (t [ wkrw ] [ id ,rw TT[] ])
  ≡⟨ sym[] ifTT ⟩≡
  if TT  (t [ wkrw ]) (u [ wkrw ])
  ≡⟨ cong (λ □ → if □ (t [ wkrw ]) (u [ wkrw ])) p ⟩≡
  if FF  (t [ wkrw ]) (u [ wkrw ])
  ≡⟨ shift ifFF ⟩≡
  subst (Tm Γ) wk<>rwTy (u [ wkrw ] [ id ,rw FF[] ])
  ≡⟨ cong (subst (Tm Γ) wk<>rwTy) (shift wk<>rw) ⟩≡
  subst (Tm Γ) wk<>rwTy (subst (Tm Γ) (sym wk<>rwTy) u)
  ≡⟨ subst-subst-sym wk<>rwTy ⟩≡
  u ∎
\end{code}
\end{remark}

We define def.-consistent contexts as those which are not def.-inconsistent.
By definition, in def.-consistent contexts, equality does not collapse -
|TT ≡ FF| implies ⊥. We therefore argue that as long as def.-consistency is
decidable, decidability of conversion in arbitrary contexts is not a complete
lost cause (as we
can always first attempt to decide def.-consistency of the context and then
avoid reducing in def.-inconsistent contexts, where loops abound).
Of course, deciding def.-consistency require completing the set of rewrites,
which involved normalisation - I do not claim that deciding conversion is at
all easy! We shall discuss the problems in more detail in 
\refsec{scboolnormfail}.
%TODO If indeed I end up unable to prove decidability of conversion in SCBool
%it might be worth explicitly mentioning that...

\subsection{From Quotients to Setoids}
\labsec{quotset}

In practice, support for quotient types in modern proof assistants is somewhat
hit-or-miss.
In Agda, for example, there are at least two practical ways of defining
quotient-inductive types with different trade-offs: 
\begin{itemize}
  \item One can natively define QI types as 
  truncated higher-inductive (HI) defitions using
  the cubical extension \sidecite{vezzosi2019cubical}.

  \item One can assume the 
  existence of the particular quotient type 
  by postulating the constructors/induction principle/β-rules and then make them
  compute with |REWRITE| rules \sidecite{cockx2020type}.
\end{itemize}

Unfortunately, Cubical Agda's support for dependent pattern matching,
especially in the presense of inductive families, still leaves a lot to
be desired \sidecite{agda2024cubical, danielsson2019agda}.
Specifically, transports often get stuck on pattern-matching definitions which
rely on constructor injectivity/disjointness.

Postulating quotient types on the other hand, by the very nature of the 
technique, lacks 
guardrails against defining
possibly not-well-founded (e.g. non-strictly-positive) types and
requires a lot of boilerplate (e.g. explicitly writing out full type of the 
elimination principle, and always inducting on the type with that eliminator
rather than pattern-matching).

Furthermore, quotiented syntax, even when well-supported by the metatheory,
causes additional problem when studying the computational behaviour of terms.
Specifically, sound reduction relations (i.e. contained within conversion)
on quotiented syntax
are an entirely ill-defined concept, at the level of the meta.

For example, we might imagine defining a reduction relation 
|_>β_ : Tm Γ A → Tm Γ A → Set| with a case for contracting
β-redexes\remarknote{Of course, in our explicit substitution syntax,
|ƛ⁻¹ (ƛ t) >β t| is likely to be more natural formation of the β rule for 
Π-types, but we encounter the same problem either way.}:

%if False
\begin{code}
infix 4 _>β_

data _>β_ : Tm Γ A → Tm Γ A → Set where
\end{code}
%endif

\begin{code}
  β> : (ƛ t) · u >β t [ id , subst (Tm _) (sym [id]Ty) u ]
\end{code}

However, because we have quotiented terms by conversion (including β-conversion)
this case is (up to the propositional equality of the meta) equivalent to
reflexivity!

% \sideremark{We could actually go the other way |t₁ ≡ t₂ → t₁ >β t₂| by
% arbitrarily constructing a redex that reduces to |t₁|}

\begin{code}

β→≡ : t₁ >β t₂ → t₁ ≡ t₂
β→≡ (β> {t = t} {u = u}) = 
  (ƛ t) · u
  ≡⟨⟩
  (ƛ⁻¹ (ƛ t)) [ id , subst (Tm _) (sym [id]Ty) u ]
  ≡⟨ cong _[ _ ] β ⟩≡
  t [ id , subst (Tm _) (sym [id]Ty) u ] ∎
\end{code}

%if False
\begin{code}
-- coeβ> : t >β u → coe p t >β coe p u

variable
  Γ≡ : Γ₁ ≡ Γ₂
  A≡ : A₁ ≡[ cong Ty Γ≡ ]≡ A₂

>β≡ : ∀ {Γ≡ : Γ₁ ≡ Γ₂} {A≡ : A₁ ≡[ cong Ty Γ≡ ]≡ A₂} 
        (t≡ : t₁ ≡[ dcong₂ Tm Γ≡ A≡ ]≡ t₂) (u≡ : u₁ ≡[ dcong₂ Tm Γ≡ A≡ ]≡ u₂)
    → t₁ >β u₁ → t₂ >β u₂

β-refl : t >β t
β-refl = >β≡ ≡rdx ≡sub β> 
  where ≡rdx :   (ƛ (t [ wk ])) · TT ≡[ cong (Tm Γ) wk<>Ty ]≡ t
        ≡rdx = {!!}
        ≡sub :   t [ wk ] [ id , subst (Tm _) (sym [id]Ty) TT ] 
             ≡[  cong (Tm Γ) wk<>Ty ]≡ t
\end{code}
%endif

The key issue here is that some PL concepts (such as reduction) rely on
working with terms at a finer granularity that conversion. In principle,
this can be solved by working in a two-level metatheory 
\sidecite{annenkov2023two, kovacs2024elab}, where the inner (weak)
equality identifies terms up to conversion and the outer (strict) equality
regards the object theory as an ordinary inductive type.

Agda technically supports a form of 2LTT, but the extension is still very-much
experimental. For these reasons then, we follow 
\sidecite{altenkirch1999extensional, altenkirch2021constructing} in mechanically
translating our quotiented syntax to instead use setoids.

TODO: Explain the key ideas (coe/coh constructors)

\subsection{Strictification}

TODO!

\section{Soundness}

Conversion already gives our syntax an ``equational'' semantics (e.g. 
normalisation for \SCBool can be immediately defined as the task finding a
conversion-preserving mapping from terms to some other type with decidable 
equality) 
but that does not necessarily imply our semantics is ``reasonable'' in the sense
our theory can actually be used as a programming language or indeed a logic.

A useful sanity-check that we will attempt now is to define an interpretation
from our object theory into corresponding metatheory constructs (the ``standard
model'') and in-doing-so prove soundness\remarknote{Note that ``soundness'' can
be specified in numerous different ways. By soundness of a type theory in
isolation, we mean that in the empty context, there are no terms of the
empty type (i.e. viewed as a logic, the type theory contains no proofs of 
⊥).\\
Soundness of \textit{operations} on syntax (e.g. type-checking 
algorithms) are instead defined as those which respect conversion. This is 
exactly the sense in 
which ``soundness'' is used in the original \SC slides, specifically convertible
terms (defined declaratively) must be equivalent with respect to algorithmic
conversion (reduction followed by syntactic comparison).}. This task can also be
seen as defining denotational semantics for our theory.

In the standard model, contexts are interpreted as left-nested pairs
of (meta-)types (we refer to the inhabitants of these as ``environments''),
types as functions from environments to (meta-)types, terms as functions
from environments to the interpretation of the type at that environment and 
substitutions as functions between environments.

TODO: Describe the interesting cases here (|π₂rw| requires function 
extensionality!)

\section{Reduction}

\subsection{Challenges for Normalisation}
\labsec{scboolnormfail}

\begin{itemize}
  \item \textbf{Completion relies on strong normalisation.}
  \item \textbf{Neutrals are unstable under weakening.}
\end{itemize}

   
\section{Beyond Booleans}