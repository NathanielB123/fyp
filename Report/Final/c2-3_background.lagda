%if False
\begin{code}
{-# OPTIONS --prop --rewriting --mutual-rewriting #-}

open import Utils hiding (_∘_)
open import Utils.IdExtras

module Report.Final.c2-3_background where

\end{code}
%endif

\subsection{Explicit Substitutions}

For STLC, we were able to get away with first defining terms inductively, and 
then substitutions later as a recursive operation (and conversion after that,
\sideremark{If one takes untyped terms as primitive and
then defines typing relations explicitly, recursive substitution for dependent
types is achievable directly \sidecite[*3.5]{abel2017decidability}, 
but this approach requires many tedious
proofs that e.g. substitution preserves typing.}
as an inductive relation). It is unclear how to do the same for dependent
type theory
(specifically, ITT) given types (with embedded terms) must be
considered equal up to at least β-conversion (and β-conversion at |Π|-types
inevitably refers to substitution.) One might hope to find a way to
define a dependently-typed syntax mutually with a recursive substitution
operation, but
unfortunately it is currently unclear how to make this work in practice
\sidecite[*3]{kaposi2025type}.

We therefore give an explicit substitution syntax for STLC, based on
categories with families 
(CwFs)\sidecite[*3]{dybjer1995internal, castellan2019cwf}, 
which can be more easily adapted to the setting
of dependent types.

Unlike our previous syntax, our explicit substitution calculus only contains
four main sorts: contexts, types, terms and substitutions but no variables.
Without variables, we no longer parameterise substitutions by whether
they are renamings or ``full'' substitutions.

%if False
\begin{code}
infixl 6 _▷_ _,_

postulate
\end{code}
%endif

\begin{code}
  Ctx  : Set
  Ty   : Set
  Tm   : Ctx → Ty → Set
  Tms  : Ctx → Ctx → Set
\end{code}

%if False
\begin{code}
variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx
  A B C A₁ A₂ A₃ B₁ B₂ : Ty
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
\end{code}
%endif

\pagebreak
\sidedef{Category}{A type of objects |Ob| and family of morphisms
|Hom : Ob → Ob → Set| forms a category if |Hom| includes identity and
composition.
\nocodeindent
%if False
\begin{code}
module _ {Ob : Set} (Hom : Ob → Ob → Set) where
  private variable 
    x y z : Ob
    f g h : Hom x y
\end{code}
%endif
\begin{code}
  record Category : Set where field
    idh  :  Hom x x
    _∘_  :  Hom x y → Hom y z 
         →  Hom x z
    id∘  :  idh ∘ f ≡ f
    ∘id  :  f ∘ idh ≡ f
    ∘∘   :  (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
\end{code}
\resetcodeindent
We denote flipped composition with |_⨾_|, 
which is convenient for substitutions as it aligns with their action
on terms being denoted postfix.
}

We start with some properties of substitutions. Substitutions should form a 
category with contexts as objects (i.e.
there is an identity substitution, and they can be composed).

We quotient by substitution laws here, but of course
we could work up to some equivalence relation instead.
By quotienting by
the substitution laws, but not |β|/|η|, we can obtain a syntax that is
isomorphic (w.r.t. propositional equality) to the recursive substitution 
approach (the proof of this is given in detail in 
\sidecite[*-9]{altenkirch2025copypaste}).

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  id   : Tms Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ

  id⨾  : id  ⨾ δ   ≡ δ
  ⨾id  : δ   ⨾ id  ≡ δ
  ⨾⨾   : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
\end{code}

\sidedef{Terminal Object}{An object |𝟙 : Ob| 
in a category |C| with a family of morphisms |Hom| is
terminal if there is a unique morphism 
from every other object in the category, |x : Ob|, to |𝟙|, |! : Hom x 𝟙|.
\nocodeindent
%if False
\begin{code}
module _ {Ob : Set} (Hom : Ob → Ob → Set) (𝟙 : Ob) where
  private variable 
    x y z : Ob
    f g h : Hom x y
\end{code}
%endif
\begin{code}
  record Terminal : Set where field
    !     : Hom x 𝟙
    uniq  : f ≡ !
\end{code}
\resetcodeindent
}
The category of substitutions features a terminal object (the empty context).
The unique morphism |ε| applied to terms will correspond to weakening
from the empty context.


%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  •    : Ctx
  ε    : Tms Δ •
  •η   : δ ≡ ε
\end{code}

Terms are a presheaf on substitutions. That is, there is a
(contravariantly) functorial action
that applies substitutions to terms.

\sidedef[*1]{Presheaf}{
\labdef{presheaf}
We call family of types |F : A → Set| a presheaf 
on a category |C| (with\\|Ob = A| and a family of morphisms |Hom|)
if it is a contravariant functor on |C|.
More concretely, there should exist a functorial action which ``lift''s 
morphisms in |C|, |Hom y x|, to functions, |F x → F y|.
\nocodeindent
%if False
\begin{code}
module _ {Ob : Set} (F : Ob → Set) {Hom : Ob → Ob → Set} 
         (C : Category Hom) where
  open Category C
  private variable 
    x y z : Ob
    f g h : Hom x y
    xs ys : F x
\end{code}
%endif
\begin{code}
  record Presheaf : Set where field
    map :  Hom y x → F x → F y
    map-id  :  map idh xs ≡ xs
    map-∘   :  map (f ∘ g) xs 
            ≡  map f (map g xs)
\end{code}
\resetcodeindent
}

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  _[_]  : Tm Γ A → Tms Δ Γ → Tm Δ A
  [id]  : t [ id ] ≡ t
  [][]  : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
\end{code}

To support binding, we must equip our CwF with 
\emph{context comprehension}, including a context extension 
operation |_▷_ : Ctx → Ty → Ctx|, 
and an associated way to
extend substitutions a fresh term to replace the new variable with.

\begin{code}
  _▷_  : Ctx → Ty → Ctx
  _,_  : Tms Δ Γ → Tm Δ A → Tms Δ (Γ ▷ A)
  
  ,⨾   : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , (t [ σ ])
\end{code}

We call laws like ``|,⨾|'' which cover how the various constructs of type theory
interact with 
the functor operations, \emph{naturality} laws. We can express these laws as
commutative diagrams, e.g.

\begin{tikzcd}[scaleedge cd=1.25, sep=huge]
|δ| \arrow[r, "|_⨾ σ|"] \arrow[d, swap, "|_, t|"]
&  |δ ⨾ σ| \arrow[d, "|_,  (t [ σ ])|"] 
\\ |δ , t| \arrow[r, swap, "|_⨾ σ|"]
&  |(δ , t) ⨾ σ ≡' (δ ⨾ σ) , (t [ σ ])|
\end{tikzcd}

Given our intuition of parallel substitutions as lists of terms, we 
should expect a (natural) isomorphism:
\begin{spec}
Tms Δ (Γ ▷ A) ≃ Tms Δ Γ × Tm Δ A
\end{spec}
This can be witnessed either directly with projection operations, or we
can take single-weakening and the zero de Bruijn variable as primitive
(|wk = π₁ id| and |vz = π₂ id|, or
|π₁ δ = wk ⨾ δ| and |π₂ δ = vz [ δ ]|) \sidecite[*-2]{castellan2019cwf}.

\begin{widepar}
\begin{minipage}{0.5\textwidth}
\begin{code}
  π₁   : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₂   : Tms Δ (Γ ▷ A) → Tm Δ A
  ▷η   : δ ≡ π₁ δ , π₂ δ
  π₁,  : π₁ (δ  ,  t) ≡ δ
  π₂,  : π₂ (δ  ,  t) ≡ t
  π₁⨾  : π₁ (δ  ⨾  σ) ≡ π₁ δ ⨾ σ
  π₂⨾  : π₂ (δ  ⨾  σ) ≡ π₂ δ [ σ ]
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{code}
  wk    : Tms (Γ ▷ A) Γ
  vz    : Tm (Γ ▷ A) A
  wk⨾   : wk ⨾ (δ , t) ≡ δ
  vz[]  : vz [ δ , t ] ≡ t
  id▷   : id {Γ = Γ ▷ A} ≡ wk , vz
\end{code}
\end{minipage}
\end{widepar}

From these primitives, we can derive single substitutions |<_>| and 
functoriality of context extension |_^_|. The former just substitutes
the zero de Bruijn variable for the given term, while acting as identity
everywhere else. The latter is obtained by first weakening all terms
in the substitution (to account for the new variable) and then mapping the
new zero variable to itself.

\begin{code}
<_> : Tm Γ A → Tms Γ (Γ ▷ A)
< t > = id , t

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ ▷ A) (Γ ▷ A)
δ ^ A = (δ ⨾ wk) , vz
\end{code}

We can extend this syntax with functions by adding the relevant type former
and
introduction/elimination rules. Rather than the usual rule
for application, it is convenient in explicit substitution syntaxes to 
take a more \emph{pointfree} combinator as primitive, which directly
inverts |ƛ_|.

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  _⇒_   : Ty → Ty → Ty
  ƛ_    : Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  ƛ⁻¹_  : Tm Γ (A ⇒ B) → Tm (Γ ▷ A) B

  ƛ[]    : (ƛ t) [ δ ] ≡ ƛ (t [ δ ^ A ])
  ƛ⁻¹[]  : (ƛ⁻¹ t) [ δ ^ A ] ≡ ƛ⁻¹ (t [ δ ])
\end{code}

Semantically, |ƛ⁻¹_| can be understood as the action of weakening the given
function, and then applying it to the fresh zero variable. We can derive
the more standard rule for application by following this up with a
single-substitution:

\begin{code}
_·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
t · u = (ƛ⁻¹ t) [ < u > ]
\end{code}

%if False
\begin{code}
infix 4 _~_

data _~_ : Tm Γ A → Tm Γ A → Set where
\end{code}
%endif

The advantages of |ƛ⁻¹_| should hopefully be evident from 
now super-concise statement of the |β|/|η| equations for |⇒|-types.

\begin{code}
  ⇒β  : ƛ⁻¹ ƛ t ~ t
  ⇒η  : t ~ ƛ ƛ⁻¹ t
\end{code}

For other type formers, using an explicit syntax does not change much, so
we will stop here.
