%if False
\begin{code}
{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Utils hiding (Bool-split)
open import Utils.IdExtras

module Report.Final.c5-1_scbool where

open import Report.Final.c2-4_background 
  hiding (if; if[]; 𝔹β₁; 𝔹β₂; funext; sound)
  public

\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{A Minimal Language with Smart Case}
\labch{scbool}

In this chapter, we introduce and study a minimal dependently-typed language
featuring a \SC-like elimination principle for Booleans. We name
this language \SCBool. Our large chunk of the chapter is dedicated to
explaining why normalisation for this theory is so challenging,
with examples.
We will also detail the core ideas behind the Haskell
typechecker for an extended version of this language.

\section{Syntax}
\labsec{scboolsyntax}

When moving from STLC with local equations to dependent types, we note 
while equations of course must depend on the context (i.e. the LHS or RHS
terms can embed variables), it is also sometimes desirable for types
in the context to depend on local equations. For example, in a context
where we have |x ∶ 𝔹, y ∶ IF x 𝔹 A| and the (definitional) equation |x == TT| 
holds, we have |y ∶ 𝔹| (congruence of definitional equality), and so
ought to be able bind |z ∶ IF y B C|.

To support this, we fuse the ordinary and equational context: contexts
can now be extended either with types (introducing new variables) or
definitional equations (expanding conversion).

We build upon our quotiented, explicit-substitution syntax 
laid out in \refsec{dtlc}. Again, we have four sorts:

\begin{spec}
  Ctx  : Set
  Ty   : Ctx → Set
  Tm   : ∀ Γ → Ty Γ → Set
  Tms  : Ctx → Ctx → Set
\end{spec}

\sideremark{In principle, we could also make type-level, ``large'' |IF|
``smart'' in the same way, adding equations to the contexts the LHS and RHS
types are defined in. We avoid considering this here only for simplicity.}

We carry over all the substitution laws, the existence of context extension
and the term/type formers associated with |Π| and |𝔹| types, except term-level
(dependent) ``|if|''. In \SCBool, ``|if|'' will be ``smart'' in the sense that it will
add equations to the context in the left and right branches, as opposed
to requiring an explicit motive. 

We start by defining the obvious embedding of Booleans into \SCBool,
and prove the substitution law on embedded Booleans by cases.

\begin{code}
⌜_⌝𝔹 : Bool → Tm Γ 𝔹
⌜ true   ⌝𝔹 = TT
⌜ false  ⌝𝔹 = FF

⌜⌝𝔹[] : ⌜ b ⌝𝔹 [ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ ⌜ b ⌝𝔹
⌜⌝𝔹[] {b = true}   = TT[]
⌜⌝𝔹[] {b = false}  = FF[]
\end{code}

%if False
\begin{code}

variable
  D E : Ty Γ

-- Basically just appealing to UIP
coh[][]  : ∀  {p : C ≡ B} {q : A [ δ ]Ty [ σ ]Ty ≡ C} 
              {r : D [ σ ]Ty ≡ B} {s : A [ δ ]Ty ≡ D}
         → subst (Tm Θ) p (subst (Tm Θ) q (t [ δ ] [ σ ])) 
         ≡ subst (Tm Θ) r (subst (Tm Δ) s (t [ δ ]) [ σ ])
coh[][] {p = refl} {q = q} {r = refl} {s = refl} rewrite q = refl

coh⌜⌝𝔹 : ∀ {A≡ : 𝔹 ≡[ Ty≡ Γ≡ ]≡ 𝔹}
       → ⌜ b ⌝𝔹 ≡[ Tm≡ Γ≡ A≡ ]≡ ⌜ b ⌝𝔹
coh⌜⌝𝔹 {Γ≡ = refl} {A≡ = refl} = refl
postulate
\end{code}
%endif

The key idea behind \SCBool is to allow extending contexts with
Boolean equations which we expect to hold definitionally.

\begin{code}
  _▷_>eq_  : ∀ Γ → Tm Γ 𝔹 → Bool → Ctx
\end{code}

We need to define an analagous rule to |_,_| for context extension by
equations. Concretely, the question is this: given a substitution 
|δ : Tms Δ Γ|, what additional information do we need to map from
|Γ| extended by a new equation, |Γ ▷ t > eq b|? Recall that local equations
are used in terms/types to derive convertibility, so
I claim that the appropriate notion here is that
|t| and |b| are convertible in the new context |Δ| (i.e. with the substitution
applied).

\begin{code}
  _,eq_    : ∀ (δ : Tms Δ Γ) → t [ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ ⌜ b ⌝𝔹 
           → Tms Δ (Γ ▷ t >eq b)
\end{code}  

Note that requiring convertibility evidence (as opposed to e.g. evidence of the
substituted rewrite exactly occurs somewhere in |Δ|) enables removing rewrites
from contexts when they become redundant. 

We now give also the associated naturality laws and projections:

\begin{code}
  ,eq⨾  : ∀  {δ : Tms Δ Γ} {σ : Tms Θ Δ} {t≡} 
        →    (δ ,eq t≡) ⨾ σ 
        ≡    (δ ⨾ σ) ,eq  (subst (Tm Θ) 𝔹[] (t [ δ ⨾ σ ]) 
                          ≡⟨ cong (subst (Tm Θ) 𝔹[]) (sym [][]) ⟩≡ 
                          subst (Tm Θ) 𝔹[] (subst (Tm Θ) [][]Ty (t [ δ ] [ σ ]))
                          ≡⟨ coh[][] {p = 𝔹[]} ⟩≡
                          subst (Tm Θ) 𝔹[] (subst (Tm Δ) 𝔹[] (t [ δ ]) [ σ ])
                          ≡⟨ cong (subst (Tm Θ) 𝔹[]) (cong (_[ σ ]) t≡) ⟩≡ 
                          subst (Tm Θ) 𝔹[] (⌜ b ⌝𝔹 [ σ ])
                          ≡⟨ ⌜⌝𝔹[] ⟩≡ 
                          ⌜ b ⌝𝔹 ∎)
  π₁eq   : Tms Δ (Γ ▷ t >eq b) → Tms Δ Γ
  π₂eq   : ∀ (δ : Tms Δ (Γ ▷ t >eq b)) 
         → t [ π₁eq δ ] ≡[ Tm≡ refl 𝔹[] ]≡ ⌜ b ⌝𝔹
  ▷eqη   : δ ≡ π₁eq δ ,eq π₂eq δ
  π₁eq,  : ∀ {t≡ : t [ δ ] ≡[ Tm≡ (refl {x = Δ}) 𝔹[] ]≡ ⌜ b ⌝𝔹}
         → π₁eq (δ ,eq t≡) ≡ δ
  π₁eq⨾  : π₁eq (δ ⨾ σ) ≡ π₁eq δ ⨾ σ
\end{code}

Note that |π₂eq id| allows us to make use of the most recently bound
equation in the context as convertibility evidence. 

We define derived notions of weakening contexts by assuming new equations, 
|wkeq|, instantiating contextual equations with evidence of convertibility, 
|<_>>eq|,
and finally functoriality of context extension by equations, |_^_>eq_|

\begin{code}
wkeq : Tms (Γ ▷ t >eq b) Γ
wkeq = π₁eq id

<_>>eq : t ≡ ⌜ b ⌝𝔹 → Tms Γ (Γ ▷ t >eq b)
<_>>eq {t = t} {b = b} t≡ 
  =    id 
  ,eq  (subst (Tm _) 𝔹[] (t [ id ]) 
  ≡⟨ cong (subst (Tm _) 𝔹[]) (shift [id]) ⟩≡
  subst (Tm _) (sym [id]Ty ∙ 𝔹[]) t
  ≡⟨ cong (subst (Tm _) (sym [id]Ty ∙ 𝔹[])) t≡ ⟩≡ 
  subst (Tm _) (sym [id]Ty ∙ 𝔹[]) ⌜ b ⌝𝔹
  ≡⟨ coh⌜⌝𝔹 {A≡ = sym [id]Ty ∙ 𝔹[]} ⟩≡ 
  ⌜ b ⌝𝔹 ∎)

_^_>eq_  : ∀ (δ : Tms Δ Γ) t b
         → Tms (Δ ▷ subst (Tm Δ) 𝔹[] (t [ δ ]) >eq b) (Γ ▷ t >eq b)
δ ^ t >eq b 
  =    (δ ⨾ wkeq) 
  ,eq  (subst (Tm _) 𝔹[] (t [ δ ⨾ wkeq ])
       ≡⟨ cong (subst (Tm _) 𝔹[]) (sym [][]) ⟩≡
       subst (Tm _) 𝔹[] (subst (Tm _) [][]Ty ((t [ δ ]) [ wkeq ]))
       ≡⟨ coh[][] {p = 𝔹[]} ⟩≡
       subst (Tm _) 𝔹[] (subst (Tm _) 𝔹[] (t [ δ ]) [ π₁eq id ])
       ≡⟨ π₂eq id ⟩≡
       ⌜ b ⌝𝔹 ∎)
\end{code}

We also prove some equations about how these new substitution operations
commute. These are very similar to familiar laws pertaining to
context extension by types, rather than equations: weakening commutes
with lifting over the new equation, and weakening followed by instantiation
is identity.

\begin{code}
wkeq^    : wkeq ⨾ (δ ^ t >eq b) ≡ δ ⨾ wkeq

wk<>eq   : ∀ {t≡ : t ≡ ⌜ b ⌝𝔹} → wkeq ⨾ < t≡ >>eq ≡ id {Γ = Γ}
\end{code}

%if False
\begin{code}
wkeq^Ty  : A [ wkeq ]Ty [ δ ^ t >eq b ]Ty ≡ A [ δ ]Ty [ wkeq ]Ty
wk<>eqTy  : ∀ {t≡ : t ≡ ⌜ b ⌝𝔹} 
          → A [ wkeq {b = b} ]Ty [ < t≡ >>eq ]Ty ≡ A
wk<>eqTm  : ∀ {t≡ : t ≡ ⌜ b ⌝𝔹}
          → u [ wkeq {b = b} ] [ < t≡ >>eq ] 
          ≡[ Tm≡ refl (wk<>eqTy {t≡ = t≡}) ]≡ u
\end{code}
%endif

%if False
\begin{code}
-- I maybe added a few to many rewrites for identity types in "Utils.IdExtras"
-- unification is very unpredictable lol.
-- Making the proofs abstract helps a bit.
abstract
  wkeq^ {δ = δ} {t = t} {b = b} = 
    wkeq ⨾ (δ ^ t >eq b)
    ≡⟨ sym π₁eq⨾ ⟩≡
    π₁eq (id ⨾ (δ ^ t >eq b))
    ≡⟨ cong π₁eq id⨾ ⟩≡
    π₁eq (δ ^ t >eq b)
    ≡⟨ π₁eq, ⟩≡
    δ ⨾ wkeq ∎

  wkeq^Ty = [][]Ty ∙ refl [ wkeq^ ]Ty≡ ∙ sym [][]Ty

  wk<>eqTy {t≡ = t≡} = [][]Ty ∙ refl [ wk<>eq {t≡ = t≡} ]Ty≡ ∙ [id]Ty

  wk<>eq = {!!}
  wk<>eqTm = {!!}
postulate
\end{code}
%endif

\begin{code}
  if  : ∀ (t : Tm Γ 𝔹) 
      → Tm (Γ ▷ t >eq true)   (A [ wkeq ]Ty)
      → Tm (Γ ▷ t >eq false)  (A [ wkeq ]Ty)
      → Tm Γ A

  if[]  : if  t u v [ δ ] 
        ≡ if  (subst (Tm Δ) 𝔹[] (t [ δ ])) 
              (subst (Tm _) wkeq^Ty (u [ δ ^ t >eq true   ]))
              (subst (Tm _) wkeq^Ty (v [ δ ^ t >eq false  ]))
  𝔹β₁  : if TT u v 
       ≡[ Tm≡ refl (sym (wk<>eqTy {t≡ = refl})) ]≡ u [ < refl >>eq ]
  𝔹β₂  : if FF u v
       ≡[ Tm≡ refl (sym (wk<>eqTy {t≡ = refl})) ]≡ v [ < refl >>eq ]
\end{code}

As with our simply-typed equational contexts, \SCBool contexts can become
definitionally inconsistent, and collapse the definitional equality.

\begin{definition}[Definitional context inconsistency] \phantom{a}\\\\
An \SCBool context is considered def.-inconsistent iff under that
context, |TT| and |FF| are convertible.

\begin{code}
incon : Ctx → Set
incon Γ = _≡_ {A = Tm Γ 𝔹} TT FF
\end{code}
\end{definition}


Recall from \refremark{eqcollapse} that definitionally inconsistent contexts
lead to equality collapse: are types become convertible (assuming large
elimination of Booleans).

\begin{code}
collapse : Ctx → Set
collapse Γ = ∀ (A B : Ty Γ) → A ≡ B

incon-collapse : incon Γ → collapse Γ
\end{code}

%if False
\begin{code}
incon-collapse Γ! A B = 
  A
  ≡⟨ sym IF-TT ⟩≡
  IF TT A B
  ≡⟨ cong (λ □ → IF □ A B) Γ! ⟩≡
  IF FF A B
  ≡⟨ IF-FF ⟩≡
  B ∎
\end{code}
%endif

As an example of how the substitution calculus of \SCBool works,
we will prove also that definitional inconsistency implies the collapse
of the term equality.

\begin{code}
tm-collapse : Ctx → Set
tm-collapse Γ = ∀ A (u v : Tm Γ A) → u ≡ v

tm-incon-collapse : ∀ Γ → incon Γ → tm-collapse Γ
\end{code}

Note that, the |u| and |v| inside the ``|if|'' must be weakened to account for 
the new 
local equation, and contracting the ``|if|'' requires explicitly instantiating this
equation with a substitution. Our |wk<>eq| lemma from earlier is exactly
what we need to show that the composition of these two actions has
no ultimate effect.

\begin{code}
tm-incon-collapse Γ p A u v = 
  u
  ≡⟨ sym (subst-subst-sym wk<>eqTy) ⟩≡
  subst (Tm Γ) (sym (wk<>eqTy {t≡ = refl}) ∙ wk<>eqTy {t≡ = refl}) u
  ≡⟨ cong (subst (Tm Γ) wk<>eqTy) (sym[] (wk<>eqTm {t≡ = refl})) ⟩≡
  subst (Tm Γ) wk<>eqTy (u [ wkeq ] [ < refl >>eq ])
  ≡⟨ sym[] (𝔹β₁ {u = u [ wkeq ]} {v = v [ wkeq ]}) ⟩≡
  if TT  (u [ wkeq ]) (v [ wkeq ])
  ≡⟨ cong (λ □ → if □ (u [ wkeq ]) (v [ wkeq ])) p ⟩≡
  if FF  (u [ wkeq ]) (v [ wkeq ])
  ≡⟨ shift 𝔹β₂ ⟩≡
  subst (Tm Γ) wk<>eqTy (v [ wkeq ] [ < refl >>eq ])
  ≡⟨ cong (subst (Tm Γ) wk<>eqTy) (shift (wk<>eqTm {t≡ = refl})) ⟩≡
 subst (Tm Γ) (sym (wk<>eqTy {t≡ = refl}) ∙ wk<>eqTy {t≡ = refl}) v
  ≡⟨ subst-subst-sym wk<>eqTy ⟩≡
  v ∎
\end{code}

% Given |_≡_ {A = Tm Γ 𝔹} TT ≡ FF|, we are tasked with proving 
% |t ≡ u| for arbitrary terms |t u : Tm Γ A|. The key idea is to follow the chain
% of equations |t ≡ if TT then t else u ≡ if FF then t else u ≡ u|, but we must
% take care to account for explicit substitution and weakening. 
% 
% E.g. The |t| and |u| inside the ``|if|'' must be weakened to account for the new 
% rewrite, and contracting the ``|if|'' requires explicitly instantiating this
% rewrite with another substitution. Our |wk<>eq| lemma from earlier is exactly
% what we need to show that these substitutions ultimately have no effect.

\section{Soundness}
\labsec{scboolsound}

We prove soundness of \SCBool by updating the standard model construction 
given in \refsec{depsound}.

%if False
\begin{code}
variable 
  ⟦Γ⟧ : ⟦Ctx⟧
  ⟦A₁⟧ ⟦A₂⟧ : ⟦Ty⟧ ⟦Γ⟧
  ρ : ⟦Γ⟧
\end{code}

\begin{code}
Ty≡-inst : ⟦A₁⟧ ≡ ⟦A₂⟧ → ⟦A₁⟧ ρ ≡ ⟦A₂⟧ ρ
Ty≡-inst refl = refl
\end{code}
%endif



The model gets a little more interesting for \SCBool though. Our metatheory
does not feature a ``first-class'' definitional equality, so we instead
interpret definitional contextual equalities propositionally (i.e.
{⟦ Γ ▷ t >eq b ⟧Ctx == ⟦ Γ ▷ Id 𝔹 t ⌜ b ⌝𝔹 ⟧Ctx}).

\begin{spec}
⟦ Γ ▷ t >eq b ⟧Ctx = Σ⟨ ρ ∶ ⟦ Γ ⟧Ctx ⟩× ⟦ t ⟧Tm ρ ≡ b

⟦ π₁eq δ ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ .fst  
\end{spec}

When interpreting |_,eq_|, we split on the particular Boolean RHS
so the substitution
on it computes definitionally (slightly simplifying the equational reasoning,
at the cost of having to repeat it).

\begin{spec}
⟦ _,eq_ {t = t} {b = true} δ t≡  ⟧Tms 
  = λ ρ  → ⟦ δ ⟧Tms ρ
         Σ, cong-app 
         (⟦ t [ δ ] ⟧Tm
         ≡⟨ sym (coh⟦⟧Tm {t = t [ δ ]} {A≡ = 𝔹[]} {⟦A⟧≡ = refl}) ⟩≡
         ⟦ subst (Tm _) 𝔹[] (t [ δ ]) ⟧Tm
         ≡⟨ cong ⟦_⟧Tm t≡ ⟩≡
         ⟦ TT ⟧Tm ∎) ρ
⟦ _,eq_ {t = t} {b = false} δ t≡  ⟧Tms 
  = λ ρ  → ⟦ δ ⟧Tms ρ
         Σ, cong-app 
         (⟦ t [ δ ] ⟧Tm
         ≡⟨ sym (coh⟦⟧Tm {t = t [ δ ]} {A≡ = 𝔹[]} {⟦A⟧≡ = refl}) ⟩≡
         ⟦ subst (Tm _) 𝔹[] (t [ δ ]) ⟧Tm
         ≡⟨ cong ⟦_⟧Tm t≡ ⟩≡
         ⟦ FF ⟧Tm ∎) ρ
\end{spec}

\pagebreak
\sideremark{For all finite types |A|, the ``splitter'' and eliminator
are equally powerful.\\To derive the splitter, splitting on
a scrutinee {|x ∶ A|}, 
producing a type |B|, from the eliminator, we
instantiate the motive {|P ∶ A → Set|} with {|P y = x ≡ y → B|}.
The eliminator's methods then exactly correspond to the splitter's cases, 
and passing
{|refl ∶ x ≡ x|} to the result of eliminating gets back to type |B|.\\To
derive the eliminator from the splitter, we instead instantiate
{|B = P x|}, and transport the appropriate over the provided 
propositional equality in each case.\\Of course, splitters cannot induct,
so the splitter for infinitary types like |ℕ| is weaker than the 
associated eliminator.}
To interpret \smart ``|if|'', we define an analagous operation in our 
metatheory
that takes a propositional equality instead: the Boolean ``splitter''.

% TODO: This could maybe go in the preliminaries/related work...
% I.e. to explain why Smart Case cannot replace induction principles

%if False
\begin{code}
module _ {A : Set} where
\end{code}
%endif

\begin{code}
  Bool-split : (b : Bool) → (b ≡ true → A) → (b ≡ false → A) → A
  Bool-split true   t f = t refl
  Bool-split false  t f = f refl
\end{code}

\begin{spec}
⟦ if t u v ⟧Tm = λ ρ → Bool-split  (⟦ t ⟧Tm ρ) 
                                   (λ t≡ → ⟦ u ⟧Tm (ρ Σ, t≡)) 
                                   (λ t≡ → ⟦ v ⟧Tm (ρ Σ, t≡))
\end{spec}

Finally, to ensure soundness, we also need to show that conversion is preserved.
The updated computation rules for ``|if|'' still hold definitionally in 
the meta, but the new |π₂eq| law does not. We need to
manually project out the propositional equality from the substituted
environment, but to do this, we need to get our hands on an environment
to substitute (alternatively: evaluate the substitutes in). For this, we 
need function
extensionality (also, we again split on the Boolean to simplify the reasoning):

\begin{spec}
⟦ π₂eq {t = t} {b = true} δ   ⟧Tm =
  ⟦ subst (Tm _) 𝔹[] (t [ π₁eq δ ]) ⟧Tm
  ≡⟨ coh⟦⟧Tm {t = t [ π₁eq δ ]} {A≡ = 𝔹[]} {⟦A⟧≡ = refl} ⟩≡
  ⟦ t [ π₁eq δ ] ⟧Tm
  ≡⟨ funext (λ ρ → ⟦ δ ⟧Tms ρ .snd) ⟩≡
  ⟦ TT ⟧Tm ∎
⟦ π₂eq {t = t} {b = false} δ  ⟧Tm =
  ⟦ subst (Tm _) 𝔹[] (t [ π₁eq δ ]) ⟧Tm
  ≡⟨ coh⟦⟧Tm {t = t [ π₁eq δ ]} {A≡ = 𝔹[]} {⟦A⟧≡ = refl} ⟩≡
  ⟦ t [ π₁eq δ ] ⟧Tm
  ≡⟨ funext (λ ρ → ⟦ δ ⟧Tms ρ .snd) ⟩≡
  ⟦ FF ⟧Tm ∎
\end{spec}

%if False
\begin{code}
postulate ⟦▷>eq⟧ : ⟦ Γ ▷ t >eq b ⟧Ctx ≡ (Σ⟨ ρ ∶ ⟦ Γ ⟧Ctx ⟩× ⟦ t ⟧Tm ρ ≡ b)
{-# REWRITE ⟦▷>eq⟧ #-}

coh⟦⟧Tm  : ∀ {A≡ : A₁ ≡ A₂} {⟦A⟧≡ : ⟦ A₁ ⟧Ty ≡ ⟦ A₂ ⟧Ty}
         → ⟦ subst (Tm Γ) A≡ t ⟧Tm 
         ≡ subst (⟦Tm⟧ ⟦ Γ ⟧Ctx) ⟦A⟧≡ ⟦ t ⟧Tm
coh⟦⟧Tm {A≡ = refl} {⟦A⟧≡ = refl} = refl

postulate ⟦π₁eq⟧ : ⟦ π₁eq δ ⟧Tms ≡ λ ρ → ⟦ δ ⟧Tms ρ .fst
{-# REWRITE ⟦π₁eq⟧ #-}

postulate
  ⟦,eq⟧   :  ∀ {t≡ : t [ δ ] ≡[ Tm≡ refl  𝔹[] ]≡ TT}
          → ⟦ δ ,eq t≡ ⟧Tms 
          ≡  (λ ρ → ⟦ δ ⟧Tms ρ 
          Σ, cong-app 
          (⟦ t [ δ ] ⟧Tm
          ≡⟨ sym (coh⟦⟧Tm {t = t [ δ ]} {A≡ = 𝔹[]} {⟦A⟧≡ = refl}) ⟩≡
          ⟦ subst (Tm Δ) 𝔹[] (t [ δ ]) ⟧Tm
          ≡⟨ cong ⟦_⟧Tm t≡ ⟩≡
          ⟦ TT {Γ = Δ} ⟧Tm ∎) ρ)

  ⟦π₂eq⟧  : ∀ {δ : Tms Δ (Γ ▷ t >eq true)}
          → cong ⟦_⟧Tm (π₂eq δ) 
          ≡ (⟦ subst (Tm Δ) 𝔹[] (t [ π₁eq δ ]) ⟧Tm
          ≡⟨ coh⟦⟧Tm {t = t [ π₁eq δ ]} {A≡ = 𝔹[]} {⟦A⟧≡ = refl} ⟩≡
          ⟦ t [ π₁eq δ ] ⟧Tm
          ≡⟨ funext (λ ρ → ⟦ δ ⟧Tms ρ .snd) ⟩≡
          ⟦ TT {Γ = Δ} ⟧Tm ∎)

  ⟦if⟧ : (⟦ if t u v ⟧Tm) 
       ≡ λ ρ → Bool-split (⟦ t ⟧Tm ρ) (λ t≡ → ⟦ u ⟧Tm (ρ Σ, t≡)) 
                                      (λ t≡ → ⟦ v ⟧Tm (ρ Σ, t≡))

\end{code}
%endif

Soundness itself can be proved as usual: by passing the empty environment to
the interpreted proof of |Id 𝔹 TT FF|.

\begin{code}
sound : ¬ Tm • (Id 𝔹 TT FF)
sound t = tt/ff-disj (⟦ t ⟧Tm tt)
\end{code}

\section{Normalisation Challenges}
\labsec{scboolnormfail}

Normalisation of \SCBool is tricky. From our simply-typed
investigations in \refch{simply}, we already know that completing sets 
of equations 
(that is, turning them into confluent, terminating, rewriting systems) 
is essential
to decide equivalence under equational assumptions, and that when
such equations can be introduced locally, normalisation and
completion must be interleaved.

In \SCBool, 
checking whether the equational context can be completed before reducing
is even more important, given under definitionally inconsistent contexts,
terms that loop w.r.t. β-reduction can be defined 
(\refexample{definconselfapp}). 
We need to be careful to only
ever reduce terms after we have completed at least the set of equations that
their typing directly depends on.

\begin{example}[\SCBool Reduction W.R.T. a TRS Can Loop Even if the TRS Is Complete] \phantom{a}

Consider following the \SCBool context (assuming support for neutral
equations at |𝔹|-type\remarknote{We can avoid this assumption
by replacing |x| and |y| with slightly more complicated 
β-neutral terms |t| and |u| that are convertible 
modulo a particular Boolean equation. E.g. \mbox{|t = if x TT FF|} and 
\mbox{|u = if x TT TT|} are equal assuming |x >eq TT|.}).

\begin{spec}
Γ  = x ∶ 𝔹
   , y : 𝔹
   , z ∶ IF x 𝔹 (𝔹 ⇒ 𝔹)
   , x ~ y
   , (if x (ƛ _. TT) z) (if y z TT) >eq TT
   , x ~ FF
   , y ~ TT
\end{spec}

The TRS |x >rw FF, y >rw TT| is conservative over this equational context,
and is complete at least in the sense that all LHSs are
irreducible (with respect to the other TRS rewrite and β reduction).
However, if (during completion of the full context) 
we reduce \mbox{|(if x (ƛ _. TT) z) (if y z TT)|} w.r.t. this TRS, 
we get a self-application! 

\sideremark{Technically, self-application does not immediately imply the
existence of reduction loops, but we can easily repeat this 
construction to obtain Ω (\refexample{definconselfapp}).}

\begin{spec}
(if x (ƛ _. TT) z) (if y z TT) 
> (if FF (ƛ _. TT) z) (if TT z TT)
> z z
\end{spec}

The problem here is that \mbox{|(if x (ƛ _. TT) z) (if y z TT)|} relies on the
equation |x ~ y| to typecheck (specifically, so that in the left branch of 
the second ``|if|''
expression, |z ∶ 𝔹| as required). However, this equation is not
validated by the TRS. Essentially, the context is definitionally
inconsistent, but we failed to detect this.

If we instead required |x ~ y| to be in the TRS when reducing 
\mbox{|(if x (ƛ _. TT) z) (if y z TT)|}, then completing the TRS
with |x ~ FF| and |y ~ TT| also included will find the definitional 
inconsistency, so we can avoid blindly reducing.
\end{example}

% Still, in the presence of non-confluent rewrite lies trouble. |b >rw true|
% and |b >rw false| together enables self-application without either equation
% alone being obviously inconsistent. Of course, this can in principle 
% be obscured further by using LHSs which are still definitionally equal, but only
% via several reduction steps. To avoid problems, we at least need to ensure 
% that we only ever attempt to reduce terms
% (including rewrite LHSs) once all the equations they depend on
% to typecheck have been mutually completed. We leave the problem of
% how to formally encode such dependency tracking and define an appropriate
% reduction relation to future work. I conjecture that conversion in \SCBool
% is decidable, perhaps using such an approach, but do not have time in
% this project to investigate further. 

\subsection{Type Theory Modulo (Boolean) Equations}

\sideremark{Note that difficulties associated with completion can in principle
be avoided by requiring the set of equations to satisfy completion criteria
by construction. In this setting, our problem here is effectively a special
case of \cite{cockx2021taming}.\\
Unfortunately, when moving to locally-introduced equations, relying on
the LHSs all being mutually irreducible is not really feasible. As we
will discuss in \refsec{depbeyondbool}, any restrictions on equations 
must be stable under substitution, and irreducibility of LHSs does not
satisfy this criteria.}\sideblankcite{cockx2021taming}

A nice first-step towards normalisation for \SCBool would be
to attempt to prove decidability of conversion for for dependent types
modulo a fixed (global) set of Boolean equations. We can arrive at an explicit 
syntax for this problem by just replacing \SCBool's \SIF with the
ordinary dependent one\remarknote{Note that in such a setting, we can consider
a vastly restricted subset of \SCBool's substitutions, where the 
region of the context
up to the last equational assumption always remains constant, and no new
equations can be added.
% Specifically, we can define restricted weakenings which only
% append types (never equations) to the context, then replace the 
% terminal substitution |ε : Tms Δ •| with an embedding of these weakenings.
% \nocodeindent
% %if False
% \begin{code}
% postulate
% \end{code}
% %endif
% \begin{code}
%   Wk : Ctx → Ctx → Set
%   id𝒲   : Wk Γ Γ
%   _⁺𝒲_  : Wk Δ Γ → Wk (Δ ▷ A) Γ 
% 
%   Tms′  : Ctx → Ctx → Set
%   ε′    : Wk Δ Γ → Tms′ Δ Γ
% \end{code}
% \resetcodeindent
% We also should change |_,eq_|, |π₁eq| and |π₂eq|. General substitutions
% should not be able to extend the context with new equations, but we do still
% want equations defined earlier in the context to apply everywhere, so switching
% back to a de Bruijn variable-like |EqVar| rule for reflecting equational
% assumptions seems natural.
%TODO Code for this??
}.

A natural strategy here is to make an attempt at adapting our
simply-typed result from \refsec{simplenormcompl}. 
Unfortunately, it seems
impossible to reuse the same techniques. For starters,
non-deterministic reduction on dependent ``|if|'' does not preserve typing.
Recall that in the definition of ``|if|''

\begin{spec}
if  : ∀ (A : Ty (Γ ▷ 𝔹)) (t : Tm Γ 𝔹) 
      → Tm Γ (A [ < TT > ]Ty) → Tm Γ (A [ < FF > ]Ty)
      → Tm Γ (A [ < t > ]Ty)
\end{spec}

the LHS and RHS have type {|A [ < TT > ]Ty|} and {|A [ < FF > ]Ty|} respectively,
while the overall expression instead has type {|A [ < t > ]Ty|} (where |t|
is the scrutinee).

Actually, the problem is more
fundamental: we can construct terms in dependent type 
theory (with just with ordinary, dependent ``|if|'') that, after projecting out the 
untyped term, 
loop w.r.t. non-deterministic (or spontaneous) reduction. 
For example (working internally, in a context where |b ∶ 𝔹| and
|x ∶ A| for some type |A|), the following term is typeable with 
|IF b A (A ⇒ A) ⇒ A|.

\begin{spec}
ƛ  (y ∶ IF b A (A ⇒ A)). 
   (if [b′. IF b′ A (A ⇒ A) ⇒ A ⇒ A]  b (ƛ _. x)  y)
   (if [b′. IF b′ A (A ⇒ A) ⇒ A]      b y         x)
\end{spec}

The untyped projection of this term is just

\begin{spec}
ƛ y. (if b (ƛ _. x) y) (if b y x)
\end{spec}

Under non-deterministic reduction, we can collapse the first ``|if|'' to the 
right branch (|y|), and the second ``|if|'' to the left branch (also, |y|) 
resulting in |ƛ y. y y| (and under spontaneous
reduction, we can do the same thing in two steps, first collapsing the 
scrutinees the the appropriate closed Booleans). We then just need to repeat
the same construction, replacing |A| with |IF b A (A ⇒ A) ⇒ A|, and we are left
with (after erasing types)

\begin{spec}
(ƛ y. (if b (ƛ _. x) y) (if b y x)) (ƛ y. (if b (ƛ _. x) y) (if b y x))
\end{spec}

which (spontaneously or non-deterministically) reduces down to Ω

\begin{spec}
(ƛ y. y y) (ƛ y. y y)
\end{spec}

This puts us essentially back to square-one. We know to normalise 
\SCBool, we need to do completion, but completion can only be justified by
making progress w.r.t. to
some well-founded order, and our best candidate from STLC does not work. 
Perhaps one potential route forwards could be to define a TRS
for an \SCBool context as a list of Boolean rewrites, plus a small-step
relation covering the steps of completion (reducing a LHS, removing 
a redundant equation, concluding definitional inconsistency from an inconsistent
one).

Another difficulty with \SCBool is that we must account for weakening the
context by equations when recursing on the syntax (specifically, 
when recursing into the LHS and RHS branches of \SIF). Strong
normalisation defined as just accessibility w.r.t. the reduction relation
is clearly not stable under extending the context with new 
Boolean equations (the new equations can unlock new reductions)!
One route forwards here could be take inspiration from the
\emph{positively-characterised} neutral forms of
\sidecite{sterling2021normalization, gratzer2022controlling}. There, neutral
forms being unstable w.r.t. renamings was dealt with by pairing an
inductively defined neutral with a function from evidence that the neutral
becomes reducible (is \emph{destabilised}) in some renamed context
to a normal form. I think applying a similar idea to strong normalisation 
(parameterising accessibility over all renamed/thinned contexts) could
assist a strong normalisation proof for \SCBool similarly.

\subsection{Beyond Booleans}
\labsec{depbeyondbool}

On top of the prior-mentioned issues, \SCBool's scope is somewhat limited.
Specifically, generalising the \SC construct more general local equality
reflection, admitting a larger class of equations, appears impossible.

% A major motivating factor for my ``giving-up'' on \SCBool (on top of the
% challenges previously listed) is that going far beyond Boolean equations appears
% impossible.

As covered in \refremark{scloceqref}, when we start generalising \SC, it is
useful to view it through the lens of local equality reflection. 
A significant constraint with introducing equations locally,
as in \SCBool, is that the restrictions we enforce on reflected
equations must be stable under substitution. This
is a consequence of being able to introduce equations underneath λ-abstractions
and definitional β-reduction: if the equation restriction is not
stable under substitution, then β-reduction could take a well-typed term
that reflects a valid equation, and reduce it to a term where the 
reflected equation is no longer valid.

\subsubsection{Neutral Types}

This has significant consequences. One class of equations we may 
aim to
support are equations between arbitrary terms of neutral type. 
For example,
in a context with variables {|b ∶ 𝔹|} and {|x ∶ IF b A B|},
such that the term {|t ∶ Π b. IF b A B|} is typeable (and |t b| is neutral),
we might want to reflect the equation {|t b == x|}. However, if we then
applied the substitution {|TT / b|}, we get the new equation
{|t TT == x|}, where both sides now have type |A|. 
This was possible for any type |A| and term |t| that blocks on its argument,
so for example, we could make this example more concrete by setting
{|A = ℕ ⇒ 𝔹|} and {|t = ƛ b. if [b′. IF b′ (ℕ ⇒ 𝔹) B] b u v|}. Now,
|t TT| β-reduces to |u|, an arbitrary |ℕ ⇒ 𝔹|-typed term.
As mentioned in \refsec{locreflect}, reflecting equations higher-order-typed
equations like this quickly leads to undecidability. Therefore, we must prevent
|u == x|, and so to ensure stability under substitution, we must also
reject the original |t b == x| equation. In practice, I argue this example
is repeatable for pretty-much all equations of neutral 
type\remarknote{The main exception that I can think of is equations typed with
large |⊥-elim|. As |⊥-elim| has no computation rules, it cannot possibly
reduce down to a higher order type. Technically, I suppose one could also look
into the branches of |IF| to see if all branches return first-order types,
and design a restriction based on that.}.

\sideremark{A more skeptical reader might wonder whether our desire here -
i.e. reflecting neutral equations - is at all
realistic. I reply ``yes, because I have found a way to do it!'' and 
``skip ahead to the next chapter to see how!''}
In our minimal type theory, where the only neutral types can be constructed
out of large |IF|, perhaps this does not seem so important. One should consider
though, that in theories with type variables, equations of neutral 
type are extremely common. Consider, for example, code that is
generic over a functor, |F : Type → Type|. Note the functor laws such
as {|fmap-id : fmap id xs ≡ xs|} are all at neutral type. While our focus on
manual equality reflection of individual propositional equalities does not 
aim for quite the same convenience as building the functor equations into
the typechecker (i.e. we still need to manually instantiate the particular
functor law with our particular |F A|-typed term), we argue that this kind of
automation would still go a long way towards resolving the issues that
motivated work such as \sidecite{allais2013new}. Being restricted only to
Boolean equations is unnacceptable!

\subsubsection{Finitary Types}
\labsec{finitaryrw}

Going a little beyond our Boolean equations
appears to be achievable to some extent though. 
The first obvious equality-reflection-motivated 
generalisation is to allow |𝔹|-typed equations where the RHS is not
restricted to be a closed Boolean. Assuming an irreducible LHS and RHS,
the new equations here are all between neutral terms of |𝔹|-type,
and can be dealt with either directly via completion (using a term
ordering on neutrals to orient them appropriately) or (as 
exchanging neutral terms
cannot unblock β-reductions) conversion modulo these equations can be
delayed until after β-reduction (and then decided
using any approach we like - perhaps ground term rewriting,
perhaps E-Graphs). 

Note that the subject reduction issues we encountered with equations
of neutral type do not crop up here, because while substitutions
might unblock the LHS or RHS and allow it to reduce, this reduction
can only ever produce another |𝔹|-typed neutral term or a closed Boolean
(though we still would have to repeat completion after substitution).

% equations between |𝔹|-typed neutral terms. Assuming
% a normalisation proof of \SCBool based on completion, extending it to 
% account for neutral rewrites, oriented w.r.t. some term ordering should not be
% challenging (neutral equations are arguably better-behaved than 
% ones ending in closed Booleans, given they cannot unblock new |β|-reductions).

By extending our language with dependent pairs (|Σ|-types) with strict |η|, 
we also get sum/coproduct-typed equations ``for free'' via a similar argument to 
\sidecite{kovacs2022strong}. Specifically, we can define sums/coproducts
with Boolean large elimination like so
\begin{spec}
A + B = Σ (b ∶ 𝔹). IF b A B

in₁  t = TT  , t
in₂  t = FF  , t
\end{spec}
Equations of the form |t == in₁ u| at type |A + B| can now be decomposed into 
a Boolean equation |π₁ t == true| and an |A|-typed equation |π₂ t == u|. 
Of course, this approach only works if the |A|-typed equation is itself
valid. 

\begin{example}[Decomposing Coproduct Equations] \phantom{a}

I find it is interesting that taking this encoding can deal with rewrites
that otherwise appear like they should inevitably loop. For example,
consider the equations
\begin{spec}
t >eq in₁ (case t TT FF)
\end{spec}
where |t| is some neutral 
term of type |𝔹 + 𝔹|. Without decomposing using the above
encoding, we appear to be stuck. The rewrite must be oriented towards
|in₁ (case t TT FF)| or we risk missing β-reductions for case expressions
blocking on |t|, but because |t| is also a subterm of the RHS, this
rewriting process appears to have no end.

If we decompose this using the encoding above, and η-expand the RHS, we get 
\begin{spec}
(π₁ t , π₂ t) >eq (TT , π₂ (case t TT FF))
\end{spec}
This can be decomposed into the Boolean equation |π₁ t >eq TT| and
the neutral equation at |𝔹|-type |π₂ t ~ π₂ (case t TT FF)|.
Under a reasonable term ordering (that is, one which is a monotonic
simplification ordering), we would probably expect the latter equation
to be oriented |π₂ (case t TT FF) >eq π₂ t|, but given both sides are neutral,
this reorienting is fine!
\end{example}

Equations between neutrals |t == u|
of type |A + B| are unfortunately a bit more problematic:
the first |π₁ t == π₂ u| component
is fine, assuming validity of neutral Boolean equations, but |π₂ t == π₂ u|
has type |if b A B| - this is a neutral equation of neutral type, which as 
explained above, is hard to justify.

\subsubsection{Infinitary Types}

We can attempt to use a similar generic encoding to deal with infinitary
types such as natural numbers, |ℕ|. By considering the underlying functor,
we can decompose inductive types into a fixpoint operation.

\begin{spec}
fixℕ    : 𝟙 + ℕ → ℕ
unfixℕ  : ℕ → 𝟙 + ℕ
\end{spec}

Using this decomposition, and assuming a definitional η rule
|n == fixℕ (unfixℕ n)|, the equation |n ~ su m| is equivalent to

\begin{spec}
-- Original
n ~ su m
-- η-expanding |fix|
fixℕ (unfixℕ n) ~ fixℕ (in₂ m)
-- η-expanding |Σ|
fixℕ (π₁ (unfixℕ n) , π₂ (unfixℕ n)) ~ fixℕ (false , m)
\end{spec}

which can be decomposed into the two equations

\begin{spec}
π₁ (unfixℕ n) >eq  false

π₂ (unfixℕ n) ~    m
\end{spec}

However, with infinitary types, we do need to be a bit more careful, as
this decomposition process can end up producing infinitely-many equations.

\begin{spec}
n ~ su n
-- η-expanding |fix| and |+|
fixℕ (π₁ (unfixℕ n) , π₂ (unfixℕ n)) ~ fixℕ (false , n)
-- Decomposing
π₁ (unfixℕ n) >eq  false

π₂ (unfixℕ n) ~    n
-- But now if we η-expand |n| on the RHS...
π₂ (unfixℕ n) ~ fixℕ (π₁ (unfixℕ n) , π₂ (unfixℕ n))
-- ...the first decomposed rewrite applies!
π₂ (unfixℕ n) ~ fixℕ (false , π₂ (unfixℕ n))
-- And we are left with the same structure of equation as we got from initially
-- η-expanding
\end{spec}

Intuitively, the problematic cases here all arise when one side of the
equation occurs as a subterm of the other. We might hope to do a sort of
``occurs check'' to explicitly prevent this, but we again hit issues
with stability substitution. |n ~ su x| might pass the occurs check, but 
after applying the substitution |n / x| it certainly does not.

\pagebreak
\section{Typechecking Smart Case}
\labsec{typecheckingsc}

We end this section with a short description of the \SCBool 
typechecker implemented
in Haskell as a component of this project. As explained previously in 
\refsec{scboolnormfail}, I do not know how to prove normalisation of
\SCBool, and therefore do not claim that this typechecker is complete.
In practice though, it has handled the examples which I have
thrown at it correctly, without getting stuck in loops.

\sideremark{Idris2 also features |Type ∶ Type|, though there are plans
to add a universe hierarchy eventually.}
The language we check is a slight extension of \SCBool, including a single
impredicative universe (|Type ∶ Type|). This is technically unsound
(\sidecite{hurkens1995simplification}), but I argue that
programs/proofs which
might actually abuse this inconsistency are quite rare in practice (the
|Type ∶ Type| sledgehammer is also much simpler to implement than
an actual universe hierarchy, and concerns with universes are pretty 
orthogonal to the new features of \SCBool).

Other than the extensions to specifically support \SIF,
the implementation of \SCBool is pretty standard. Following
\sidecite{coquand1996algorithm}, it implements bidirectional typechecking
in terms of mutually recursive ``|infer|'' and ``|check|'' functions, and
decides convertibility of types using normalisation by evaluation (NbE).
\sideremark{We also use GADTs
to explicitly maintain a slightly more unusual invariant:
that terms do not contain ``obviously ill-typed'' β-redexes. That is, 
introduction rules in scrutinee position are always associated with
the appropriate
type former.\\\\Assuming a correct implementation, this is
completely reasonable (it is a subset of terms being well-typed in general),
but alone it is not necessarily preserved over operations
such as substitution or reduction. The compromise being struck here is
essentially that Haskell's type system is not powerful enough to model
full intrinsically-typed syntax, so I am encoding this 
weaker invariant and then coercing (technically unsafely) when necessary.
It is somewhat unclear whether this was a good idea, and for the
code snippets in the section, we prune away the details associated with this
aspect.}
To guard against mistakes in the implementation, it also makes extensive use
of GADTs (including singleton encodings \sidecite{lindley2013hasochism}) 
to maintain invariants, including that
terms are intrinsically well-scoped \sidecite{eisenberg2020stitch}
(after we complete a scope-checking pass, turning names into 
well-scoped de Bruijn variables) and normal/neutral forms do not contain
β-redexes. 



% A slightly experimental invariant, that terms do not
% contain ``obviously ill-typed''\remarknote{Specifically, scrutinees of
% elimination forms cannot take the form of introduction rules associated 
% with a different type former.} 
% β-redexes, is also ensured by the type
% indexing. Preserving this invariant safely during substitution and, 
% more generally,
% reduction, is not really possible without full dependent types, but Haskell,
% being a partial language, does allow us to |unsafeCoerce| between arbitrary
% types.

When implementing NbE in a partial language, we can take a couple 
shortcuts\remarknote{The optimisations I decided to make here were 
generally motivated
by simplicity rather than performance. There is certainly 
a lot of potential
to optimise further, e.g. by using a more efficient variable representation
than unary de Bruijn indices, using de Bruijn levels in values,
switching from metalanguage closures
to first-order ones, eliminating the overheads associated with singleton 
encodings by |unsafeCoerce|-ing more often, using more efficient data 
structures, unboxing etc.}:
\begin{itemize}
\item Rather than defining values as a type family on object-language types,
      and defining quoting and unquoting by recursion on types, we
      define values directly as a non-positive inductive datatype.       
\item Rather than always quoting before deciding conversion, we can decide
      conversion directly on values.
\end{itemize}

The novel part of the typechecker is dealing with the local equations.
We explain the implementation of this aspect in more detail, starting
with evaluation and then finishing with the actual typechecking.

To track equations, we store a map of rewrites, |EqMap g|, 
from neutrals to values, with the invariant that all neutral LHSs
are stuck w.r.t. all other rewrites. We pair this map with a list
of values associated with every variable in scope to form 
generalised environments, |Env d g|

% \sideremark{Technically, the actual Haskell code defines
% |EqMap g| as |[(Ne g, UnkVal g)]|. |UnkVal g| is
% just a small implementation detail with how
% we are maintaining the no-ill-typed-β-redexes invariant, unrelated
% to the core typechecking algorithm. In the below code snippets, we
% have hidden a lot of these sorts of encoding details.}

\begin{spec}
type EqMap g = [(Ne g, Val g)]
type Env d g = (Vals d g, EqMap d)
\end{spec}

Unquoting neutral terms during evaluation corresponds exactly to looking
up the neutral in the map. In the case the lookup fails (no rewrite
applies), we just embed the neutral into |Val| directly (for simplicity, 
we do not support η-conversion, though adding support for η of functions
by tweaking equality testing of neutral/normal forms should be 
possible \sidecite{lennon2022eta})

\begin{spec}
lookupNe :: EqMap g -> Ne g -> Val g
lookupNe es t = fromMaybe (Ne t) (lookup t es)

appVal :: EqMap g -> Val g -> Val g -> UnkVal g
appVal es (Ne t) u = lookupNe es (App t u)
\end{spec}

To support extending the context with
new equations, we must interleave evaluation and completion. For example, to
evaluate \SIF, we add the relevant equation (with |addEq|) 
between the scrutinee and |TT|/|FF| to the environment in which we evaluate 
each branch.

\begin{spec}
evalOrAbsrd  :: Maybe (Env d g) -> Model g -> PresVal d
eval         :: Env d g -> Tm g -> Val d
smrtIfVal    :: Env d g -> Maybe (Val d) -> Val d 
             -> Tm g -> Tm g 
             -> Val d

addEq  :: Env d g -> Val d -> Val d 
       -> Maybe (Env d g)

smrtIfVal r _ TT      u  _  = eval r u
smrtIfVal r _ FF      _  v  = eval r v
smrtIfVal r m (Ne t)  u  v
  |  rT  <- addEq r (Ne t) TT
  ,  rF  <- addEq r (Ne t) FF
  ,  u'  <- evalOrAbsrd rT u
  ,  v'  <- evalOrAbsrd rF v 
  = lookupNe (eqs r) (SmrtIf m t u' v')

eval r (SmrtIf m t u v)
  = smrtIfVal r m' t' u v
  where  m' = fmap (eval r) m
         t' = eval r t
\end{spec}

\sideremark{Dedicated absurd syntax is partially inspired by Agda's
impossible patterns.}

Note that |addEq| is partial in order to account for the context 
possibly becoming
definitionally inconsistent (|Nothing| means ``def. inconsistent''). 
To guard against the danger of evaluating 
under such
contexts, and make the behaviour of the typechecker more predictable, 
we introduce dedicated syntax for ``absurd'' terms in def. inconsistent
contests (``|!|'' or |Absrd|). We regard using any term other than
|!| in a def. inconsistent to be a type error\remarknote{We also
regard usage of |!| in def. consistent contexts to be a type
error.}. We always check
typeability of terms before evaluating them, so evaluation
should never encounter this case.

\begin{spec}
evalOrAbsrd (Just r)  t      = eval r t
evalOrAbsrd Nothing   Absrd  = Absrd
evalOrAbsrd Nothing   _      = __IMPOSSIBLE__
\end{spec}

Adding equations to the environment calls completion, which itself 
operates by repeatedly
iterating over the set of equations, evaluating LHSs w.r.t. all other equations,
until a fixed point is reached (as mentioned in \refsec{scboolnormfail},
we need to be careful here to not evaluate under sets of rewrites that
might be definitionally inconsistent).

\sideremark{|addRw| and |mkEq| together add the new equation |t ~ u| 
to the set
of rewrites, after ensuring it is not already ``obviously inconsistent''
(that is, literally of the form |TT ~ FF| or |FF ~ TT|. We also 
slightly optimise
the case of equations on variables, replacing the value in the
value environment rather than tracking an equation.
\\|evalVals r'' vs|
re-evaluates the value environment w.r.t. the new completed equations.}

\begin{spec}
complete :: Env g g -> Maybe (Env g g)
complete r = iterMaybeFix complStep r

addEq (vs, es) t u = do
  r'   <- addRw (mkEq t u) (idVals, es)
  r''  <- complete r'
  pure (evalVals r'' vs, eqs r'')
\end{spec}

Similarly to evaluation, inference for \SIF adds new equations to the
environment
before recursively typechecking the branches. We of course must check
that terms in def. inconsistent branches are absurd, though unlike
evaluation though, failing this check throws a human-readable type error
(as opposed to raising an internal exception).

\begin{spec}
checkMaybeAbsurd :: Ctx g -> Maybe (Env g g) -> Ty g -> Tm g -> TCM ()
checkMaybeAbsurd g  (Just r)  a  t      = check g r a t
checkMaybeAbsurd _  Nothing   _  Absrd  = pure ()
checkMaybeAbsurd _  Nothing   _  t      = throw 
  ("Body in inconsistent contexts must be absurd, but was instead " 
  <> show t)

infer g r (SmrtIf (Just m) t u v) = do
  check g r  U  m
  check g r  B  t
  let t'  = eval r t
  let rT  = addEq r t' TT
  let rF  = addEq r t' FF
  checkMaybeAbsurd g rT  m u
  checkMaybeAbsurd g rF  m v
  let m' = eval r m
  pure m'
\end{spec}

Note that while type inference for \SIF does not require a motive 
parameterised over
the scrutinee, it still does require an expected type to check at (|Just m|
above).
We support optionally annotating \SIF expressions with their return type,
but to take advantage of the type we are checking at if it is known,
|check| adds annotations before calling ``|infer|''

\begin{spec}
check g r a t = case t of
  SmrtIf Nothing t' u' v' -> do 
    _ <- infer g r (SmrtIf (Just a) t' u' v')
    pure ()
\end{spec}

In retrospect, having ``|infer|'' erase annotations and call into
``|check|'' for the actual typechecking logic would
have probably been a bit neater, but this approach also works.

% If the context ever becomes definitionally inconsistent, we


%  we replace the term
% with a dedicated piece of syntax |Absrd| (guaranteeing convertibility
% of all such terms, and guarding against the danger of evaluating
% under definitionally inconsistent contexts. 



% There is some infrastructure in place for supporting a wider class of
% equations that those of the form |t ~ b|, though keeping in mind
% the problems discovered in \refsec{depbeyondbool}, I am wary about how
% feasible it is to actually support this (e.g. without losing
% desirable properties such as subject reduction).

% \subsection{Bidirectional Typechecking}
% 
% The key motivation behind bidirectional typechecking is to reduce 
% annotation-burden on programs written in the surface language.
% Its inference capabilities our ultimate more limited than
% e.g. metavariables, but its behaviour is also much more predictable.
% 
% For example, Agda is capable of successfully elaborating 
% 
% \begin{code}
% foo = λ x → x +ℕ 1
% \end{code}
% 
% without any type annotations, while under the bi-directional discipline, 
% un-annotated |λ| abstraction cannot, in general, synthesise a type,
% so we must ask for an annotation here.
% 
% Note that Agda does not successfully elaborate the un-annotated identity 
% function (instead reporting the existence of unsolved metavariables).
% 
% \begin{spec}
% bar = λ x → x
% \end{spec}
% 
% \subsection{Hasochism and Well-scoped Syntax}
% 
% 
% 
% \subsection{Efficient Normalisation by Evaluation}
% 
% \subsection{``Inductively''-defined Values}
% 
% TODO! The general idea is defining values as a non-positive datatype
% with e.g. constructors like |VLam : (Ren → Val → Val) → Val| instead of by 
% recursion on object types (which isn't really possible in a 
% non-dependently-typed setting).
% 
% \subsection{Avoiding Quotation during Evaluation}
% 
% TODO! The general idea is to define ``neutral values'', which are also
% non-positive, but by examining the algorithm we can see that the operational 
% behaviour ends up the same.
% 
% Should probably also discuss how it is possible to decide conversion on
% values directly (i.e. fusing conversion-checking and quoting).
% 
% \subsection{De Bruijn Levels}
% 
% TODO! General idea is to represent variables in values with de Bruijn 
% \textit{levels} rather than \textit{indices}, such that variables count the
% number of binders between their binding site and the root of the term (rather
% than their binding site and their use). This makes inserting fresh variables
% (i.e. the presheaf stuff we needed for quoting to work) no longer require
% a full traversal of the value.
% 
% 
% \subsection{Meta vs First-Order Closures}
% 
% TODO! I don't currently plan on implementing this optimisation, but it
% is still probably worth mentioning.
% It turns out the operational behaviour of the NbE algorithm can be replicated
% without meta-language closures entirely! Closures can be represented in
% a first-order fashion by pairing un-evaluated terms and captured environments.
% This variation is no longer structurally recursive (we need to |eval| the
% closure bodies during applications, similarly to naive normalisation)
% but can be faster on than relying on meta-closures depending on implementation
% language/runtime.
% 
% \subsection{Supporting Local Equations}
% 
% Now we have sufficient background in NbE as implemented in the \SCBool
% typechecker. We explain the tweaks to the algorithm made to support
% local equations (arising from ``smart'' ``|if|'').
% 
% TODO! The general idea is just to track a map of neutrals to values and
% lookup neutrals in the map when necessary. Function values need to be
% parameterised by updated maps to reduce properly in contexts with new equations.
%  
% 