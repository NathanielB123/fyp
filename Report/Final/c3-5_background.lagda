%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils hiding (Bool; true; false)
module Report.Final.c13-4_background where

\end{code}
%endif

\section{Term Rewriting}

Perhaps unexpectedly, given the title of this project, we will not actually
rely on much rewriting theory in this report. The technical hurdles we will
run into will generally arise due to the combination of a type theory with
existing β-rules. Still some groundwork is important, both to cover the
bits of rewriting theory we will appeal to and to put this work in context.

\begin{definition}{Term Rewriting System (TRS)} \phantom{a}

A finite term rewriting system (TRS) is comprised of a set of function
symbols with fixed arities, a set of variables, and a set of rewrite rules
(pairs of terms).

%if False
\begin{code}
variable
  A : Set ℓ
  n : ℕ

open import Data.Vec using (Vec) 
  using (_[_]=_; _[_]≔_; tabulate)
  renaming (lookup to vLookup; map to vMap; _∷_ to _,_; [] to ε)
open import Data.List using (List) renaming (_∷_ to _,_; [] to ε)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any renaming (here to ∈z; there to ∈s)
open import Data.Vec.Membership.Propositional using () renaming (_∈_ to _v∈_)
open import Relation.Binary.Construct.Closure.Transitive as T using (Plus)
  renaming (_∼⁺⟨_⟩_ to _>⟨_⟩+_)
import Function.Bundles as B

finally = T.finally
syntax finally x y p = x >⟨ p ⟩+∎ y ∎

module _ {_>_ : A → A → Set} {x y} where
  infix 1 begin+_

  begin+_ : Plus _>_ x y → TransClosure _>_ x y
  begin+_ = B.Equivalence.to T.equivalent

pattern ∈0 = ∈z refl 
pattern ∈1 = ∈s ∈0
pattern ∈2 = ∈s ∈1
pattern ∈3 = ∈s ∈2
\end{code}
%endif

\begin{code}
record Symbols : Set where
  field
    nVars : ℕ
    nFuns : ℕ
    arity : Vec ℕ nFuns
\end{code}

%if False
\begin{code}
open Symbols public
\end{code}
%endif

\begin{code}
data Tm (Γ : Symbols) : Set where
  `_  : Fin (Γ .nVars) → Tm Γ
  _·_ : ∀ (f : Fin (Γ .nFuns)) → Vec (Tm Γ) (vLookup (Γ .arity) f) → Tm Γ

record Rule (Γ : Symbols) : Set where
  constructor _>_
  field
    lhs : Tm Γ
    rhs : Tm Γ

record TRS : Set where
  field
    syms  : Symbols
    rules : List (Rule syms)
\end{code}

%if False
\begin{code}
open TRS public
\end{code}
%endif
\end{definition}

%if False
\begin{code}
variable
  Γ Δ : Symbols
  t u : Tm Γ
  i   : Fin (Γ .nVars)
\end{code}
%endif


\begin{code}
Tms : Symbols → Set
Tms Γ = Vec (Tm Γ) (Γ .nVars)
\end{code}

%if False
\begin{code}
infix 6 _>_

variable
  f g : Fin (Γ .nFuns)
  ts us : Vec (Tm Γ) (vLookup (Γ .arity) f)

-- Agda would see this definition as structurally recursive if we fused
-- the map with the substitution operation, but that is ugly and not
-- really relevant.
{-# TERMINATING #-}
\end{code}
%endif

\sideremark{|vMap : (A → B) → Vec A n → Vec B n| applies the given function 
to every element of a vector.
Technically, a structurally-recursive implementation of |_[_]|
ought to use a specialised helper to map over |xs| in the |f · xs| case.
Type-based termination checking \sidecite[*4]{nisht2024}
(based on the theory of sized types \sidecite{*6]{abel2016sized}) can 
resolve this, but unfortunately an attempted implementation of this for Agda
was found to be unsound \sidecite[*7]{nisht2024agda}.}

\begin{code}
_[_] : Tm Γ → Tms Γ → Tm Γ
(` i)    [ δ ] = vLookup δ i
(f · ts) [ δ ] = f · vMap (_[ δ ]) ts

data _⊢_>_ (Ξ : TRS) : Tm (Ξ .syms) → Tm (Ξ .syms) → Set where
  -- Rewrite
  rw : (t > u) ∈ Ξ .rules → ∀ (δ : Tms (Ξ .syms)) 
     → Ξ ⊢ (t [ δ ]) > (u [ δ ])
  
  -- Congruence
  ·> : ts [ i ]= t → Ξ ⊢ t > u → Ξ ⊢ (f · ts) > (f · (ts [ i ]≔ u))

_⊢_>+_ : ∀ Ξ → Tm (Ξ .syms) → Tm (Ξ .syms) → Set
_⊢_>+_ Ξ = _[ Ξ ⊢_>_ ]+_
\end{code}



Note that variables in TRS rules always stand for any term

\begin{example}[SKI] \phantom{a}

We can encode the SKI calculus as a term rewriting system with four function
symbols and three variabes.

\begin{code}
pattern S  = f0
pattern K  = f1
pattern I  = f2
pattern ap = f3

pattern _⟨⟩ f = f · ε
pattern _⟨_,_⟩ f x y = f · (x , y , ε)

pattern x = f0
pattern y = f1
pattern z = f2

SKI : TRS
SKI .syms .nVars = 3
SKI .syms .nFuns = 4
SKI .syms .arity = tabulate λ where
  S  → 0
  K  → 0
  I  → 0
  ap → 2
SKI .rules 
  = ap ⟨ I ⟨⟩ , ` x ⟩              > ` x
  , ap ⟨ ap ⟨ K ⟨⟩ , ` x ⟩ , ` y ⟩ > ` x
  , ap ⟨ ap ⟨ ap ⟨ S ⟨⟩ , ` x ⟩ , ` y ⟩ , ` z ⟩ 
  > ap ⟨ ap ⟨ ` x , ` z ⟩ , ap ⟨ ` y , ` z ⟩ ⟩
  , ε
\end{code}

We can show that |I| can also be implemented in terms of |S| and |K|

\begin{code}
I′ : Tm (SKI .syms)
I′ = ap ⟨ ap ⟨ S ⟨⟩ , K ⟨⟩ ⟩ , K ⟨⟩ ⟩

-- TODO: Needing to substitute |z| even though it isn't used in the |∈1|
-- rewrite is a bit ugly.
I′> : SKI ⊢ ap ⟨ I′ , t ⟩ >+ t
I′> {t = t} = begin+ 
  (ap ⟨ I′ , t ⟩)
  >⟨ ⟪ rw ∈2 (tabulate λ where
      x → K ⟨⟩
      y → K ⟨⟩
      z → t) ⟫ ⟩+
  ap ⟨ ap ⟨ K ⟨⟩ , t ⟩ , ap ⟨ K ⟨⟩ , t ⟩ ⟩
  >⟨ ⟪ rw ∈1 (tabulate λ where
      x → t
      y → ap ⟨ K ⟨⟩ , t ⟩
      z → ` z) ⟫ ⟩+∎
  t ∎
\end{code}

\end{example}


\begin{definition}[Ground TRS] \phantom{a}

A finite ground term TRS is a finite TRS with no variables. We could encode
this merely as a pair of a TRS |Ξ| and a proof that |Ξ .syms .nVars ≡ 0|, but
this is not a very convenient representation. Substitutions are not
necessary for ground TRSs, so the definition of ground rewriting can be made
considerably simpler.

% TODO Agda

\end{definition}


\subsection{Completion}

Completion is an algorithm for turning a set of equations into a confluent
term rewriting system. On ground equations, the procedure is simpler
and decidable, so we focus on this special-case.

The key idea behind ground completion is to first define a total, decidable, 
monotonic, well-founded ordering on ground terms. We then repeatedly iterate 
through equations, orienting them to respect this order, and reducing LHSs/RHSs.
We may need to iterate through our set of equations multiple times,
reducing LHS/RHS terms further, taking advantage of new reduced equations.
We therefore justify iteration until a fixed point is reached by
the ordering on ground terms, lexicographically extended to the set of rewrites.

\subsubsection{E-Graphs}

An alternative algorithm to completion is E-Graphs.
