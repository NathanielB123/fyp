% OLD (unfinished from interim)

%if False
\begin{code}
{-# OPTIONS --prop #-}

open import Utils
open import Common.Sort

module Report.Final.c3_simplytyped where

infixr 5 _⇒_
infixl 4  _,_
infix  5  ƛ_
infixl 6  _·_
infix  7  `_
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Simply Typed Lambda Calculus with Closed Boolean Rewrites}
\labch{simply}

\section{Syntax}

Before we begin to prove anything, we must define our object theory.
Unlike many traditional approaches to meta-theory, inspired by so-called 
"semantic" \remarknote{also called "algebraic", "reduction-free"} 
approaches, we consider only well-typed terms. 
However we don't yet go so far as to quotient our syntax by conversion,
so e.g. |(λ x → x) y| and |y| will remain distinguishable.

Our base syntax looks like:

% ---------------------------------------------------------------------------- %
% Core STLC Definition
% ---------------------------------------------------------------------------- %
% We really should use multiple columns here
\begin{code}
-- Todo: Hide the 'data' keyword here
data Ctx : Set
data Ty  : Set
Var : Ctx → Ty → Set
Tm  : Ctx → Ty → Set
\end{code}
%if False
\begin{code}
data Tm[_] : Sort → Ctx → Ty → Set

variable
  Γ Δ Θ : Ctx
  A B C : Ty
  A₁ A₂ A₃ B₁ B₂ B₃ C₁ C₂ C₃ : Ty
  i j k : Var Γ A
  t u v : Tm Γ A
  t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  x y z : Tm[ q ] Γ A
  x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : Tm[ q ] Γ A
data Ctx where
\end{code}
%endif
\begin{code}
  ε   : Ctx
  _,_ : Ctx → Ty → Ctx
\end{code}
%if False
\begin{code}
data Ty where
\end{code}
%endif
\begin{code}
  _⇒_ : Ty → Ty → Ty
  𝔹' : Ty
\end{code}
%if False
\begin{code}
Tm  = Tm[ T ]
Var = Tm[ V ]

data Tm[_] where
\end{code}
%endif

\begin{code}
  vz     : Var (Γ , A) A
  vs     : Var Γ B → Var (Γ , A) B

  `_     : Var Γ A → Tm Γ A
  _·_    : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ƛ_     : Tm (Γ , A) B → Tm Γ (A ⇒ B)

  true   : Tm Γ 𝔹'
  false  : Tm Γ 𝔹'
  𝔹-rec  : Tm Γ 𝔹' → Tm Γ A → Tm Γ A → Tm Γ A 
\end{code}

% ---------------------------------------------------------------------------- %



% ---------------------------------------------------------------------------- %
% Note on the type signatures of non-⇒ constants
% ---------------------------------------------------------------------------- %
After lambda abstraction and application has been defined, we have quite 
a bit of flexibility when defining other constants.

For example, constants of arity >0 can have their premises/conclusions
separated by external (meta-level) or internal (object-level) function
types. E.g. natural number successor can be defined as
\begin{code}
ℕ' : Ty

suⁱ : Tm Γ (ℕ' ⇒ ℕ')
\end{code}
or
\begin{code}
suᵉ : Tm Γ ℕ' → Tm Γ ℕ'
\end{code}
Either can be defined in terms of the other
%if False
\begin{code}
{-# TERMINATING #-}
\end{code} 
%endif
\begin{code}
suⁱ = ƛ (suᵉ (` vz))
suᵉ n = suⁱ · n
\end{code}
A third option is to ask for the premises to exist in the appropriate place
in the context
\begin{code}
su, : Tm (Γ , ℕ') ℕ'
\end{code}
Which is equivalent to the suⁱ definition by |ƛ|/|ƛ⁻¹| 
% TODO: define ƛ⁻¹ somewhere
This last definition avoids any reference to meta or object-level functions
and so in a way places the least constraints on the surrounding type
theories. My impression is that this is why such a style is popular
in e.g. the nLab wiki \sidecite{nlab2024product}. However, this approach has 
dire consequences with respect to computation (specifically, stability of 
typing under substitution).
e.g. it is not possible to apply |su,| applied to |ze : Tm Γ ℕ| directly;
instead, forming a β-redex is actually required: |(ƛ su,) · ze|.

In this work, I stick to the convention of using meta-level functions
to distinguish premises due to the notational convenience of meta-level 
application.

The same flexibility arises again, one level deeper, when considering
constants that act like binders (typically elimination forms).
For example, the recursion principle for sum types can be seemingly
alternatively expressed as
%if False
\begin{code}
_+'_ : Ty → Ty → Ty
\end{code}
%endif

\begin{code}
+-recⁱ : Tm Γ (A ⇒ C) → Tm Γ (B ⇒ C) → Tm Γ (A +' B) → Tm Γ C
+-recᵉ : (Tm Γ A → Tm Γ C) → (Tm Γ B → Tm Γ C) → Tm Γ (A +' B) → Tm Γ C
+-rec, : Tm (Γ , A) C → Tm (Γ , B) C → Tm Γ (A +' B) → Tm Γ C 
\end{code}
Definitions like |+-recᵉ| are not allowed in our meta-theory so we can discard 
this option immediately.
\remarknote{Specifically, this fails the "strict positivity" condition of 
inductive definitions. This sort of definition effectively simulates HOAS 
\cite{pfenning1988higher}, but in traditional ITT meta-theory, the 
meta-function space is too powerful - e.g. functions can
go beyond binding and perform real computation, such as pattern matching, 
which allows so-called "exotic terms".}

A possible motivation for |+-recⁱ| is that following this convention ensures
that there is only one actual binding construct in the type theory (|ƛ|), which
can end up slightly simplifying the definition of substitution. On the other
hand, I find |+-rec,| more convenient (in practice, I find it is very common to
want to immediately bind the newly-available variables in each case), so I will
stick to this convention.
% ---------------------------------------------------------------------------- %

\section{Substitutions}

\begin{code}
data Tms[_] (q : Sort) : Ctx → Ctx → Set where
    ε   : Tms[ q ] Δ ε
    _,_ : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ , A)

variable
  δ σ ξ δ₁ δ₂ δ₃ σ₁ σ₂ σ₃ ξ₁ ξ₂ ξ₃ : Tms[ q ] Δ Γ

Vars = Tms[ V ]
Tms  = Tms[ T ]

vz[_] : ∀ q → Tm[ q ] (Γ , A) A
vz[ V ] = vz
vz[ T ] = ` vz

suc[_] : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ , A) B
_⁺_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) Γ
_^_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) (Γ , A)
_[_]   : Tm[ q ] Γ A → Tms[ s ] Δ Γ → Tm[ q ⊔ s ] Δ A 
id : Vars Γ Γ

<_> : Tm Γ A → Tms[ T ] Γ (Γ , A)
\end{code}

\subsection{Equations}

The following equations are easily proved by induction on terms/lists of 
terms/contexts (see \sidecite{altenkirch2025copypaste} for the details). 
We will generally use these equations where necessary implicitly, as if we are
in an extensional metatheory. In fact, in the mechanisation, these equations
are turned into Agda REWRITE rules to avoid cluttering proofs with transports.

\section{Conversion}

\section{Normalisation}

We consider a type theory with functions, booleans
% TODO: Maybe extend with more tycons
and coproducts and aim to prove normalisation

\subsection{Spontaneous Reductions}

Inspired by Dougherty and Subrahmanyam's approach to proving strong 
normalisation of STLC plus equational assumptions targeting coproduct values
\sidecite{dougherty2000equality}, we define a
reduction-relation that over-approximates reduction relation. Their work
targets coprodudcts, which makes their relation much more fiddly. e.g. there
reduction relation does not necessarily preserve types, and there is a
complex interplay between variables and constants. I believe the latter is
primarily motivated by a specific monotonicity (w.r.t. reduction) of
substitution condition required during the normalisation argument, which I will 
further elaborate on later, and becomes much easier to deal with when 
%TODO Link to where we end up covering this
restricting the targets of rewrites to closed terms.

% Formal definition of spontaneous reduction
% ---------------------------------------------------------------------------- %
Spontaneous Reduction


\begin{code}
t/f : Tm Γ A → Set

data _⟶!_ : Tm Γ A → Tm Γ A → Set where
\end{code}

Standard beta reductions
\begin{code}
  β         : ∀ {ƛt t[u]} → ƛt ≡ ƛ t → t[u] ≡ t [ < u > ] → (ƛt · u) ⟶! t[u]
  rec-true  : 𝔹-rec true u v ⟶! u
  rec-false : 𝔹-rec false u v ⟶! v
\end{code}

Spontaneous reduction
\begin{code}
  rw        : ¬ t/f {A = 𝔹'} t → t/f {A = 𝔹'} u → t ⟶! u
\end{code}

Congruence rules

\begin{code}
  l·     : t₁ ⟶! t₂ → (t₁ · u) ⟶! (t₂ · u) 
  ·r     : u₁ ⟶! u₂ → (t · u₁) ⟶! (t · u₂)
  ƛ_     : t₁ ⟶! t₂ → (ƛ t₁)   ⟶! (ƛ t₂)
  𝔹-rec₁ : t₁ ⟶! t₂ → 𝔹-rec t₁ u v ⟶! 𝔹-rec t₂ u v
  𝔹-rec₂ : u₁ ⟶! u₂ → 𝔹-rec t u₁ v ⟶! 𝔹-rec t u₂ v
  𝔹-rec₃ : v₁ ⟶! v₂ → 𝔹-rec t u v₁ ⟶! 𝔹-rec t u v₂
\end{code}
% ---------------------------------------------------------------------------- %

\subsection{Strong Normalisation}

We define strong normalisation in %TODO LINK TO SECTION HERE
but let us recap.

% ---------------------------------------------------------------------------- %
Strong normalisation of spontaneous reduction.
\begin{code}

\end{code}
% ---------------------------------------------------------------------------- %

We prove well-foundedness of this spontaneous reduction relation via 
computability predicates \remarknote{also known
as logical relations, reducibility predicates etc...}. The general 
structure of the proof is based on András Kovacs' 
Agda translation \sidecite{kovacs2020strong} of Jean-Yves Girard's 
strong-normalisation proof for STLC in "Proofs and Types" 
\sidecite{girard1989proofs}. Once we have that spontaneous reduction is
strongly normalising, SN of the conditional reduction relation will follow
immediately. Other properties of this reduction (such as soundness, 
completeness, confluence etc...) will be covered in the next section.

\section{Soundness, Completeness and Confluence}



