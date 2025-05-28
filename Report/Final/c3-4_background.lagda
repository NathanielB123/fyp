%if False
\begin{code}
{-# OPTIONS --prop --rewriting --mutual-rewriting #-}

open import Utils hiding (ε)
open import Utils.IdExtras

module Report.Final.c13-4_background where

\end{code}
%endif

\section{Dependently Typed Lambda Calculus}

We will define an intensional type theory. See \refsec{equality} for discussion
on alternatives.

\subsection{Syntax}

%if False
\begin{code}
infixl 6 _▷_ _,_

postulate
\end{code}
%endif

As with our explicit STLC syntax, we define all four sorts mutually.

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

Ty≡ = cong Ty
Tm≡ = dcong₂ Tm
Tms≡ = cong₂ Tms

variable
  Γ≡ Δ≡ Θ≡ : Γ₁ ≡ Γ₂
  A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂
\end{code}
%endif


%if False
\begin{code}
postulate
\end{code}
%endif

\sideremark{As we will detail in \refsec{quotsetfibre}, it is possible to 
split the
quotienting into
a separate equivalence relation, but in the setting of dependent types,
the details get a bit more complicated 
because the indexing of types, terms and substitutions then needs to
account for this equivalence
(note that substitutions and computation will now occur inside types, so 
type-equivalence is no longer syntactic).
}

We start with substitutions. As with STLC, these must form a category.
Again, we quotient our syntax, but this time, we will go a bit further
and even quotient by some |β|/|η| laws to account for ``definitional equality''
(in ITT, types should always be considered equivalent up to computation).

\begin{code}
  id   : Tms Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ

  id⨾  : id  ⨾ δ   ≡ δ
  ⨾id  : δ   ⨾ id  ≡ δ
  ⨾⨾   : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
\end{code}

The category of substitutions features a terminal object (the empty context).

\begin{code}
  •    : Ctx
  ε    : Tms Δ •
  •η   : δ ≡ ε
\end{code}

In dependent type theory, types are a presheaf on substitutions, and terms 
are a displayed presheaf.

\begin{code}
  _[_]Ty  : Ty Γ → Tms Δ Γ → Ty Δ
  [id]Ty  : A [ id ]Ty ≡ A
  [][]Ty  : A [ δ ]Ty [ σ ]Ty ≡ A [ δ ⨾ σ ]Ty
  
  _[_]  : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]Ty)
  [id]  : t [ id ] ≡[ cong (Tm Γ) [id]Ty ]≡ t
  [][]  : t [ δ ] [ σ ] ≡[ cong (Tm Θ) [][]Ty ]≡ t [ δ ⨾ σ ]
\end{code}

To support binding, we must support a (now dependent) context extension 
operation |_▷_  : ∀ Γ → Ty Γ → Ctx|.
 
\begin{code}
  _▷_  : ∀ Γ → Ty Γ → Ctx
  _,_  : Tms Δ Γ → Tm Δ (A [ δ ]Ty) → Tms Δ (Γ ▷ A)
  
  ,⨾ : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , subst (Tm Θ) [][]Ty (t [ σ ])
\end{code}

Like in STLC, we can witness the isomorphism
\begin{spec}
Tms Δ (Γ ▷ A) ≃ Σ⟨ δ ∶ Tms Δ Γ ⟩× Tm Δ (A [ δ ]Ty)
\end{spec}
either by adding projection operations or by taking
single-weakening and the zero de Bruijn variable as primitive.

\begin{widepar}
\begin{minipage}{0.75\textwidth}
\begin{code}
  π₁   : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₂   : ∀ (δ : Tms Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]Ty)
  ▷η   : δ ≡ π₁ δ , π₂ δ
  π₁,  : π₁ (δ , t) ≡ δ
  π₂,  : π₂ (δ , t) ≡[ Tm≡ refl (cong (A [_]Ty) π₁,) ]≡ t
\end{code}
\end{minipage}
\begin{minipage}{0.75\textwidth}
\begin{code}
  wk    : Tms (Γ ▷ A) Γ
  vz    : Tm (Γ ▷ A) (A [ wk ]Ty)  
  wk⨾   : wk ⨾ (δ , t) ≡ δ
  vz[]  : vz [ δ , t ] ≡[ Tm≡ refl ([][]Ty ∙ cong (A [_]Ty) wk⨾) ]≡ t
  id▷   : id {Γ = Γ ▷ A} ≡ wk , vz
\end{code}
\end{minipage}
\end{widepar}

We derive single substitutions |<_>| and functoriality of context extension
|_^_| as usual. Note we need to transport the term in both cases to account
for the functor laws holding only propositionally.

\begin{code}
<_> : Tm Γ A → Tms Γ (Γ ▷ A)
< t > = id , subst (Tm _) (sym [id]Ty) t

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A)
δ ^ A = (δ ⨾ wk) , subst (Tm _) [][]Ty vz
\end{code}

We can also prove some derived substitution lemmas, such as commutation of
single substitution.

% TODO: Maybe add the proof
\begin{code}
<>-comm : (δ ^ A) ⨾ < t [ δ ] > ≡ < t > ⨾ δ
\end{code}

%if False
\begin{code}
wkvzη : ∀ {δ : Tms Δ (Γ ▷ A)} → δ ≡ (wk ⨾ δ) , subst (Tm Δ) [][]Ty (vz [ δ ])
wkvzη = sym id⨾ ∙ cong₂ _⨾_ id▷ refl ∙ ,⨾

_▷≡_ = dcong₂ _▷_

_[_]Ty≡ : ∀ (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) (δ≡ : δ₁ ≡[ Tms≡ Δ≡ Γ≡ ]≡ δ₂)
        → A₁ [ δ₁ ]Ty ≡[ Ty≡ Δ≡ ]≡ A₂ [ δ₂ ]Ty
_[_]Ty≡ {Γ≡ = refl} {Δ≡ = refl} refl = cong (_ [_]Ty)

_,≡_ : ∀ {Γ≡ : Γ₁ ≡ Γ₂} {Δ≡ : Δ₁ ≡ Δ₂} {A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂} 
         (δ≡ : δ₁ ≡[ Tms≡ Δ≡ Γ≡ ]≡ δ₂) 
     → t₁ ≡[ Tm≡ Δ≡ (A≡ [ δ≡ ]Ty≡) ]≡ t₂
     → δ₁ , t₁ ≡[ Tms≡ Δ≡ (dcong₂ _▷_ Γ≡ A≡) ]≡ δ₂ , t₂
_,≡_ {Γ≡ = refl} {Δ≡ = refl} {A≡ = refl} refl refl = refl

_⨾≡_ : δ₁ ≡[ Tms≡ Δ≡ Γ≡ ]≡ δ₂ → σ₁ ≡[ Tms≡ Θ≡ Δ≡ ]≡ σ₂
     → δ₁ ⨾ σ₁ ≡[ Tms≡ Θ≡ Γ≡ ]≡ δ₂ ⨾ σ₂
_⨾≡_ {Δ≡ = refl} {Γ≡ = refl} {Θ≡ = refl} refl refl = refl

<_>≡ : ∀ {Γ≡ : Γ₁ ≡ Γ₂} {A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂} 
     → t₁ ≡[ Tm≡ Γ≡ A≡ ]≡ t₂ 
     → < t₁ > ≡[ Tms≡ Γ≡ (Γ≡ ▷≡ A≡) ]≡ < t₂ >
<_>≡ {Γ≡ = refl} {A≡ = refl} refl = refl

_[_]≡ : ∀ {Γ≡ : Γ₁ ≡ Γ₂} {Δ≡ : Δ₁ ≡ Δ₂} {A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂} 
          (t≡ : t₁ ≡[ Tm≡ Γ≡ A≡ ]≡ t₂) (δ≡ : δ₁ ≡[ Tms≡ Δ≡ Γ≡ ]≡ δ₂)
        → t₁ [ δ₁ ] ≡[ Tm≡ Δ≡ (A≡ [ δ≡ ]Ty≡) ]≡ t₂ [ δ₂ ]
_[_]≡ {Γ≡ = refl} {Δ≡ = refl} {A≡ = refl} refl refl = refl

-- TODO: Solve the transport hell
-- Ideal solution would probably be to carefully abstract over the equality
-- proofs so we can match with |refl| and have everything simplify down
-- Alternatively, could carefully applying |subst-removable| a bunch of
-- times
-- Easier would be to switch to heterogeneous equality and absorb all
-- the transports
coh-vz<> :  subst (Tm Δ) [][]Ty 
                  (subst (Tm (Δ ▷ (A [ δ ]Ty))) [][]Ty vz [ < t [ δ ] > ])
        ≡[ Tm≡ refl (refl [ ⨾⨾ ∙ cong (δ ⨾_) wk⨾ ∙ ⨾id ∙ sym id⨾ ]Ty≡) 
        ]≡ subst (Tm Δ) [][]Ty (subst (Tm Γ) (sym [id]Ty) t [ δ ])

wk⨾Ty : A [ wk ]Ty [ δ , t ]Ty ≡ A [ δ ]Ty
wk⨾Ty = [][]Ty ∙ cong (_ [_]Ty) wk⨾

wk⨾Tm : t [ wk ] [ δ , u ] ≡[ Tm≡ refl wk⨾Ty ]≡ t [ δ ]
wk⨾Tm {t = t} {δ = δ} {u = u} =
  subst (Tm _) wk⨾Ty (t [ wk ] [ δ , u ])
  ≡⟨ cong (subst (Tm _) (cong (_ [_]Ty) wk⨾)) [][] ⟩≡
  subst (Tm _) (cong (_ [_]Ty) wk⨾) (t [ wk ⨾ (δ , u) ])
  ≡⟨ refl [ wk⨾ ]≡ ⟩≡
  t [ δ ] ∎

wk<>Ty : A [ wk ]Ty [ < t > ]Ty ≡ A
wk<>Ty = wk⨾Ty ∙ [id]Ty

wk<>Tm : t [ wk ] [ < u > ] ≡[ Tm≡ refl wk<>Ty ]≡ t
wk<>Tm {t = t} {u = u} = 
  subst (Tm _) wk<>Ty (t [ wk ] [ < u > ])
  ≡⟨ cong (subst (Tm _) [id]Ty) wk⨾Tm ⟩≡
  subst (Tm _) [id]Ty (t [ id ])
  ≡⟨ [id] ⟩≡
  t ∎

wk-commTy : A [ wk ]Ty [ δ ^ A ]Ty ≡ A [ δ ]Ty [ wk ]Ty
wk-commTy = wk⨾Ty ∙ sym [][]Ty

wk-commTm : t [ wk ] [ δ ^ A ] 
          ≡[ Tm≡ refl wk-commTy 
          ]≡ t [ δ ] [ wk ]
wk-commTm {A = A} {t = t} {δ = δ} = 
  subst (Tm _) wk-commTy (t [ wk ] [ δ ^ A ])
  ≡⟨ cong (subst (Tm _) (sym [][]Ty)) wk⨾Tm ⟩≡
  subst (Tm _) (sym [][]Ty) (t [ δ ⨾ wk ])
  ≡⟨ sym[] [][] ⟩≡
  t [ δ ] [ wk ] ∎

vz<> : vz [ < t > ] ≡[ Tm≡ refl wk<>Ty ]≡ t

<>-comm 
  = ,⨾ ∙ (⨾⨾ ∙ cong (_ ⨾_) wk⨾ ∙ ⨾id ∙ sym id⨾) ,≡ coh-vz<> ∙ sym ,⨾

<>-commTy : B [ δ ^ A ]Ty [ < t [ δ ] > ]Ty ≡ B [ < t > ]Ty [ δ ]Ty
<>-commTy = [][]Ty ∙ cong (_ [_]Ty) <>-comm ∙ sym [][]Ty

[][]coh : ∀ {p : B [ δ ]Ty ≡ C} {q : subst (Tm Δ) p t ≡ u} 
        → A [ δ ^ B ]Ty  [ < t > ]Ty
        ≡ A [ subst (λ □ → Tms (Δ ▷ □) (Γ ▷ B)) p
                    (δ ^ B) ]Ty
            [ < u > ]Ty 
[][]coh {p = refl} {q = refl} = refl
\end{code}
%endif

%if False
\begin{code}
postulate
\end{code}
%endif

We extend our syntax with dependent function types by adding the relevant
type former, introduction and elimination rules. We take pointfree/categorical
application as primitive.

\begin{code}
  Π     : ∀ A → Ty (Γ ▷ A) → Ty Γ
  ƛ_    : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  ƛ⁻¹_  : Tm Γ (Π A B) → Tm (Γ ▷ A) B

  Π[]  : Π A B [ δ ]Ty ≡ Π (A [ δ ]Ty) (B [ δ ^ A ]Ty)
  ƛ[]  : (ƛ t) [ δ ] ≡[ Tm≡ refl Π[] ]≡ ƛ (t [ δ ^ A ])
  Πβ   : ƛ⁻¹ ƛ t ≡ t
  Πη   : t ≡ ƛ ƛ⁻¹ t
\end{code}

We can derive the more standard rule for application as usual. Interestingly,
we can also derive the substitution law for |ƛ⁻¹| from  |ƛ[]|, |Πβ| and 
|Πη|. For explicit STLC quotiented by |β|/|η| equations, we can write
essentially the same proof, but of course do not need to worry about
accounting for transporting of the term over |Π[]|.

\begin{code}
_·_ : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ < u > ]Ty)
t · u = (ƛ⁻¹ t) [ < u > ]

ƛ⁻¹[] : (ƛ⁻¹ t) [ δ ^ A ] ≡ ƛ⁻¹ (subst (Tm Δ) Π[] (t [ δ ]))
ƛ⁻¹[] {A = A} {t = t} {δ = δ} = 
  (ƛ⁻¹ t) [ δ ^ A ]
  ≡⟨ sym Πβ ⟩≡
  ƛ⁻¹ (ƛ ((ƛ⁻¹ t) [ δ ^ A ])) 
  ≡⟨ cong ƛ⁻¹_ (sym[] ƛ[]) ⟩≡
  ƛ⁻¹ subst (Tm _) Π[] ((ƛ (ƛ⁻¹ t)) [ δ ])
  ≡⟨ cong (λ □ → ƛ⁻¹ subst (Tm _) Π[] (□ [ δ ])) (sym Πη) ⟩≡
  ƛ⁻¹ subst (Tm _) Π[] (t [ δ ]) ∎
\end{code}

%if False
\begin{code}
postulate
\end{code}
%endif

We also show how to extend our syntax with Booleans and their dependent
elimination rule.

Given the term |if A t u v|, we call |A| the ``motive'' and |t| the 
``scrutinee''.

\begin{code}
  𝔹    : Ty Γ  
  𝔹[]  : 𝔹 [ δ ]Ty ≡ 𝔹

  TT  : Tm Γ 𝔹
  FF  : Tm Γ 𝔹
  if  : ∀ (A : Ty (Γ ▷ 𝔹)) (t : Tm Γ 𝔹) 
      → Tm Γ (A [ < TT > ]Ty) → Tm Γ (A [ < FF > ]Ty)
      → Tm Γ (A [ < t > ]Ty)
    
  TT[]  :  TT [ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ TT
  FF[]  :  FF [ δ ] ≡[ Tm≡ refl 𝔹[] ]≡ FF
  if[]  :  if A t u v [ δ ] 
        ≡[ Tm≡ refl (sym <>-commTy ∙ [][]coh {q = refl}) ]≡
           if  (A [ subst (λ □ → Tms (Δ ▷ □) (Γ ▷ 𝔹)) 𝔹[] (δ ^ 𝔹) ]Ty) 
               (subst (Tm Δ) 𝔹[] (t [ δ ])) 
               (subst (Tm Δ) (sym <>-commTy ∙ [][]coh {q = TT[]  }) (u [ δ ])) 
               (subst (Tm Δ) (sym <>-commTy ∙ [][]coh {q = FF[]  }) (v [ δ ])) 
  𝔹β₁   : if A TT u v ≡ u
  𝔹β₂   : if A FF u v ≡ v
\end{code}

So far, while types have been declared to depend on terms, we have no type 
formers which explicitly rely on this dependency. In my opinion, this
set-up makes it a little too easy to ``cheat'' when writing e.g. normalisation
proofs, as such theories can ultimately be compiled into weaker type systems
without type-term dependencies \sidecite{barras1997coq}.

A common way to account for this without adding much complexity
\sidecite{danielsson2006formalisation, altenkirch2016type} is to
add universes. Minimally, we can add one type former standing for 
a universe |U : Ty Γ| and embed |U|-typed terms in |Ty Γ| with
|El : Tm Γ U → Ty Γ|. However, because this universe cannot
contain |Π|-types (to ensure predicativity\remarknote{To prevent
Russel's paradox, it is important that |Π|-types always be placed in larger
universes than their domain or range.}), minised type theories like this 
are something of a special case. Specifically, in this setting, it is possible
to statically compute
the ``spine'' of |Π|s associated with each type, and use this to
(in proofs) justify
taking the inductive step from e.g. |Π A B| to |B [ < u > ]Ty|
(i.e. |B [ < u > ]Ty|'s spine is guaranteed 
to be smaller than |Π A B|s) \cite{danielsson2006formalisation}.

\sideremark{In a type theory with a hierarchy of universes, 
we could implement dependent and large elimination with the same
primitive by generalising the motive of |if| to a type of any universe level.}

For the type theories that form the basis of modern proof assistants
(e.g. Agda), this
technique does not work due to the presense of ``large elimination'' (recall 
from \refremark{condisj} that this is the
feature that allows us to generically prove constructor disjointness, 
among other things).
To ensure our proofs generalise to such theories, we therefore
add a primitive 
large elimination
rule for Booleans - i.e. type-level |if| expressions.

\begin{code}
  IF     :  Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ
  IF[]   :  IF t A B [ δ ]Ty 
         ≡  IF (subst (Tm Δ) 𝔹[] (t [ δ ])) (A [ δ ]Ty) (B [ δ ]Ty)
  IF-TT  :  IF TT A B ≡ A
  IF-FF  :  IF FF A B ≡ B
\end{code}

We could go further, and add a recursive large elimination rule 
e.g. for |ℕ|s, but I think |IF| provides a nice balance between forcing
us to demonstrate how to account for large elimination without adding too
much extra complexity.

We also show how extend the syntax with a propositional identity type 
|Id A t₁ t₂|. Elements of this type are introduced with reflexivity and 
eliminated with the
J rule (``path induction'').

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  Id   : ∀ A →  Tm Γ A → Tm Γ A → Ty Γ
  rfl  : Tm Γ (Id A t t)
\end{code}

%if False
\begin{code}
Id≡ : ∀ {Γ≡ : Γ₁ ≡ Γ₂} (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
        (t≡ : t₁ ≡[ Tm≡ Γ≡ A≡ ]≡ t₂) (u≡ : u₁ ≡[ Tm≡ Γ≡ A≡ ]≡ u₂)
    → Id A₁ t₁ u₁ ≡[ Ty≡ Γ≡ ]≡ Id A₂ t₂ u₂
Id≡ {Γ≡ = refl} refl refl refl = refl

variable
  p : Tm Γ (Id A t₁ t₂)

postulate
\end{code}
%endif

\begin{code}
  Id[]   : Id A t₁ t₂ [ δ ]Ty ≡ Id (A [ δ ]Ty) (t₁ [ δ ]) (t₂ [ δ ])
  rfl[]  : rfl {t = t} [ δ ] ≡[ Tm≡ refl Id[] ]≡ rfl
\end{code}

%if False
\begin{code}
wkvz<>Id : Id A t₁ t₂ ≡ (Id (A [ wk ]Ty) (t₁ [ wk ]) vz [ < t₂ > ]Ty)
wkvz<>Id = Id≡ (sym wk<>Ty) 
             (sym[] {p = Tm≡ refl wk<>Ty} wk<>Tm) 
             (sym[] {p = Tm≡ refl wk<>Ty} vz<>) 
       ∙ sym Id[]
postulate
\end{code}
%endif

\begin{code}
  J    : ∀  (B : Ty (Γ ▷ A ▷ Id (A [ wk ]Ty) (t₁ [ wk ]) vz)) 
            (p : Tm Γ (Id A t₁ t₂))
       → Tm Γ (B [ < t₁ > , subst (Tm Γ) wkvz<>Id rfl ]Ty) 
       → Tm Γ (B [ < t₂ > , subst (Tm Γ) wkvz<>Id p ]Ty)
  Idβ  : J B rfl t ≡ t
\end{code}

%if False
\begin{code}
vz^ : vz [ δ ^ A ] ≡[ Tm≡ refl wk-commTy ]≡ vz

wk-commId : (Id (A [ wk ]Ty) (t [ wk ]) vz [ δ ^ A ]Ty) 
          ≡ Id ((A [ δ ]Ty) [ wk ]Ty) (t [ δ ] [ wk ]) vz
wk-commId {t = t} {δ = δ} = Id[] ∙ Id≡ {Γ≡ = refl} wk-commTy wk-commTm vz^

<>,-comm : B [ < t₂ > , subst (Tm Γ) wkvz<>Id p ]Ty [ δ ]Ty
         ≡ B [ subst (λ □ → Tms (Δ ▷ (A [ δ ]Ty) ▷ □)
                     (Γ ▷ A ▷ Id (A [ wk ]Ty) (t₁ [ wk ]) vz))
                     wk-commId ((δ ^ A) ^ Id (A [ wk ]Ty) (t₁ [ wk ]) vz) ]Ty 
             [ < t₂ [ δ ] > 
             , subst (Tm Δ) wkvz<>Id (subst (Tm Δ) Id[] (p [ δ ])) ]Ty
-- <>,-comm {B = B} {t₁ = t₁} {p = p} {δ = δ} = 
--   B [ < t₁ > , subst (Tm _) wkvz<>Id p ]Ty [ δ ]Ty
--   ≡⟨ [][]Ty ⟩≡
--   B [ (< t₁ > , subst (Tm _) wkvz<>Id p) ⨾ δ ]Ty
--   ≡⟨ cong (B [_]Ty) ,⨾ ⟩≡
--   B [ (< t₁ > ⨾ δ) , subst (Tm _) [][]Ty (subst (Tm _) wkvz<>Id p [ δ ]) ]Ty
--   ≡⟨ cong (λ □ → B [ □ , _ ]Ty) (sym <>-comm) ⟩≡
--   B [ ((δ ^ _) ⨾ < t₁ [ δ ] >) , _ ]Ty 
--   -- ≡⟨ cong (B [_]Ty) (sym {!!}) ⟩≡
--   -- {!!}
--   ≡⟨ {!!} ⟩≡ -- TODO, more transport hell
--   {!!} ∎

<>,-comm′ : B [ < t > , subst (Tm Γ) wkvz<>Id rfl ]Ty [ δ ]Ty
         ≡ B [ subst (λ □ → Tms (Δ ▷ (A [ δ ]Ty) ▷ □)
                     (Γ ▷ A ▷ Id (A [ wk ]Ty) (t [ wk ]) vz))
                     wk-commId ((δ ^ A) ^ Id (A [ wk ]Ty) (t [ wk ]) vz) ]Ty 
             [ < t [ δ ] > 
             , subst (Tm Δ) wkvz<>Id rfl ]Ty
-- <>,-comm′ {t = t} {B = B} {δ = δ} = 
--   B [ < t > , subst (Tm _) wkvz<>Id rfl ]Ty [ δ ]Ty
--   ≡⟨ <>,-comm ⟩≡
--   B [ _ ]Ty 
--     [ < t [ δ ] > , subst (Tm _) wkvz<>Id (subst (Tm _) Id[] (rfl [ δ ])) ]Ty
--   ≡⟨ cong (λ □ → B [ subst (λ □ → Tms (_ ▷ _ ▷ □) _) wk-commId ((δ ^ _) ^ _) ]Ty 
--                    [ < t [ δ ] > , subst (Tm _) wkvz<>Id □ ]Ty) rfl[]  ⟩≡
--   B [ _ ]Ty [ < t [ δ ] > , subst (Tm _) wkvz<>Id rfl ]Ty ∎
postulate
\end{code}
%endif

\begin{code}
  J[]  : J {Γ = Γ} {A = A} {t₁ = u₁} {t₂ = u₂} B p t [ δ ] 
       ≡[ Tm≡ refl <>,-comm ]≡ 
         J (B [ subst (λ □ → Tms (Δ ▷ _ ▷ □) _) wk-commId 
                      ((δ ^ A) ^ Id (A [ wk ]Ty) (u₁ [ wk ]) vz) ]Ty) 
           (subst (Tm Δ) Id[] (p [ δ ])) 
           (subst (Tm Δ) <>,-comm′ (t [ δ ])) 
\end{code}

Given the term |J B p t|, we call |B| the ``motive'' and |p| the ``scrutinee''.

We can recover transporting (i.e. ``identity of indiscernables'') from |J|
by weakening the motive.

\begin{code}
transp  : ∀ (B : Ty (Γ ▷ A)) → Tm Γ (Id A t₁ t₂) 
        → Tm Γ (B [ < t₁ > ]Ty) → Tm Γ (B [ < t₂ > ]Ty)
transp B p t 
  = subst (Tm _) wk⨾Ty (J (B [ wk ]Ty) p (subst (Tm _) (sym wk⨾Ty) t))
\end{code}

\subsubsection{Equality in Type Theory}
\labsec{equality}

Both our metatheory (Agda) and the syntax-so-far are examples of 
``intensional'' type theory (ITT). Equality judgements are divided into
``definitional'' (in Agda, denoted with |_=_|) and ``propositional''
(in Agda, denoted by |_≡_|). As we have quotiented our syntax by conversion, 
definitional equality in our object theory corresponds to propositional equality
in the meta, |_≡_|, while propositional equality is represented with the
|Id| type former.

The key idea behind this division is that deciding propositional equality in 
general requires arbitrary proof search (and so is undecidable), so
definitional equality carves out a decidable subset of propositional equality
which the typechecker can feasibly automate.

While ITT is the foundation of many modern proof assistants/dependently
typed PLs, including Rocq \sidecite{rocq2024}, 
Lean \sidecite{moura2021lean} and Idris \sidecite{brady2021idris} as well
\sideremark{It is perhaps interesting to note that equality reflection
is exactly converse of the introduction rule for |Id| (up to |_≡_|):
\begin{code}
rfl′ : t₁ ≡ t₂ → Tm Γ (Id A t₁ t₂)
rfl′ refl = rfl
\end{code}
So, both of these rules together make propositional and definitional equality
equivalent.}
as Agda, it is not the only option. Our type theory can be turned into an
extensional type theory (ETT) by adding the ``equality reflection'' rule:

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  reflect : Tm Γ (Id A t₁ t₂) → t₁ ≡ t₂
\end{code}

ETT loses decidable typechecking, but practical proof
assistants can still in theory be built upon them by allowing the user
to explicitly write out typing/conversion derivations.

On the other end of the spectrum is weak type theory (WTT)
\sidecite[*6]{winterhalter2020formalisation}, where
definitional equality is left as pure syntactic equality and |β|/|η| laws
are instead built-in as propositional equalities.

%TODO citations
Even within ITT, there is still quite a large design-space in how to treat
equality. For example:
\begin{itemize}
  \item Whether definitional equality only encompasses
  |β| laws or if certain |η| laws are admitted also 
  \sidecite[*1]{maillard2024splitting, kovacs2025eta}.
  \item Whether propositional uniqueness-of-identity-proofs (UIP) holds
  \begin{code}
  uip : ∀ (p : Tm Γ (Id A t t)) → Tm Γ (Id (Id A t t) p rfl)
  \end{code}
  Or equivalently, as ``axiom K''
  \begin{code}
  K  : ∀ (B : Ty (Γ ▷ Id A t t)) (p : Tm Γ (Id A t t)) 
     → Tm Γ (B [ < rfl > ]Ty) → Tm Γ (B [ < p > ]Ty)
  \end{code}
  \item Whether (propositional) function extensionality is supported
  \begin{code}
  funext  : Tm (Γ ▷ A) (Id B (ƛ⁻¹ t₁) (ƛ⁻¹ t₂)) 
          → Tm Γ (Id (Π A B) t₁ t₂)
  \end{code}
  as in OTT and □TT.
  \item Whether equality at the level of types (i.e. in a type theory with 
        universes) is relaxed to that of ``equivalences'' (and is therefore
        computationally relevant, contradicting UIP) as in □TT.
\end{itemize}
etc...

      
% TODO - mention Cubical TT/proof relevant equality?



% Type theories of this flavour are the
% foundation of many modern modern proof assistants/dependently
% programming languages including Agda \sidecite{norell2007towards}, 
% Rocq \sidecite{rocq2024}, Lean \sidecite{moura2021lean},
% Idris2 \sidecite{brady2021idris}. The key idea here is to divide
% equality judgements into  ``definitional''
% and ``propositional''.
% 
% 
%  The important properties of these type
% theories is that equality judgements are divided into ``definitional''
% and ``propositional'' equality - 

% In ITT, the foundation of modern proof assistants/dependently
% typed programming languages Agda \sidecite{norell2007towards}, 
% Rocq \sidecite[*2.5]{rocq2024}, Lean \sidecite[*4.5]{moura2021lean},
% Idris2 \sidecite[*6.5]{brady2021idris}, 
% equality judgements are
% split into definitional (denoted with |_=_|) and propositional (denoted with
% |_≡_|).

% \sideremark[*11]{Since Martin-Löf's first characterisation of intensional type
% theory \sidecite[*9]{martin1975intuitionistic}, 
% propositional equality has
% been extended in numerous ways (the |K| rule 
% \sidecite[*8]{streicher1993investigations}, 
% OTT \sidecite[*10]{altenkirch2007observational}, 
% CTT \sidecite[*12]{cohen2016cubical}), but all major 
% presentations retain the ability to introduce with |refl| and eliminate with 
% |J| (even if such operations are no longer primitive).}
% \begin{remark}[Definitional vs Propositional Equality] \phantom{a}
% \labremark{defprop}
% 
% In ITT, the foundation of modern proof assistants/dependently
% typed programming languages Agda \sidecite{norell2007towards}, 
% Rocq \sidecite[*2.5]{rocq2024}, Lean \sidecite[*4.5]{moura2021lean},
% Idris2 \sidecite[*6.5]{brady2021idris}, 
% equality judgements are
% split into definitional (denoted with |_=_|) and propositional (denoted with
% |_≡_|).
% 
% Definitional equality (also called "conversion") judgements are made the 
% meta-level, and typing relations in ITT are given with types always equated up 
% to convertibility. Conversion is usually comprised of syntactic equality 
% plus computation rules (β and sometimes η) but there are other 
% options, which we shall examine in \refch{background}.
% 
% Propositional equality judgements, on the other hand, are made at the level
% of the (object) type theory itself. i.e. |_≡_ : A → A → Set| is an
% object-theory type 
% constructor (forming the "identity type") and terms of type |t ≡ u| can be 
% introduced with |refl : t ≡ t|
% and applied by "transporting" (|transp : (P : A → Set) → x ≡ y → P x → P y|,
% representing the principle of "indiscernibility of identicals").
% The full dependent elimination rule for identity
% types
% (named axiom |J| or "path induction") allows the motive |P| to also quantify
% over the identity proof itself: 
% |J : ∀ (P : ∀ y → x ≡ y → Set) (p : x ≡ y) → P x refl → P y p|.
% 
% The motivation for this division is that in dependently-typed systems, types can
% contain terms that perform real computation, but typechecking requires
% comparing types for equality (e.g. when checking function application is
% valid). To retain decidability of typechecking, while enabling programmers
% to write non-trivial
% equational proofs, restricting the typechecker to a decidable approximation
% of equality is required.

% The equality reflection rule that defines ETT is simply an equating of
% propositional and definitional equality. Specifically, adding the typing rule
% |Tm Γ (t ≡ u) → t == u| (read as: the existence of a proof of propositional
% equality between |t| and |u| implies |t| and |u| are convertible) is sufficient
% to turn an intensional type theory into an extensional one.

\subsection{Soundness}

Soundness of dependent type theory can be shown very similarly to STLC - we
construct the standard model. Rather than adding a dedicated empty type, we
show that |Tm • (Id 𝔹 TT FF)| is uninhabited.

\begin{code}
sound : ¬ Tm • (Id 𝔹 TT FF)
\end{code}

The main differences are:
\begin{itemize}
  \item Types are now interpreted as functions from environments to |Set| (so 
  terms become dependent functions)
  \item We need to mutually show soundness of interpretation w.r.t. 
  conversion. Conveniently, all conversion equations hold 
  definitionally in the model (|= refl|) so we skip over them in the below 
  presentation.
\end{itemize}

\begin{code}
⟦Ctx⟧ : Set₁
⟦Ctx⟧ = Set

⟦Ty⟧ : ⟦Ctx⟧ → Set₁
⟦Ty⟧ Γ = Γ → Set

⟦Tm⟧ : ∀ Γ → ⟦Ty⟧ Γ → Set
⟦Tm⟧ Γ A = ∀ ρ → A ρ

⟦Tms⟧ : ⟦Ctx⟧ → ⟦Ctx⟧ → Set
⟦Tms⟧ Δ Γ = Δ → Γ

⟦_⟧Ctx  : Ctx → ⟦Ctx⟧
⟦_⟧Ty   : Ty Γ → ⟦Ty⟧ ⟦ Γ ⟧Ctx
⟦_⟧Tm   : Tm Γ A → ⟦Tm⟧ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
⟦_⟧Tms  : Tms Δ Γ → ⟦Tms⟧ ⟦ Δ ⟧Ctx ⟦ Γ ⟧Ctx
\end{code}

Note that for type-level (large) |IF|, we can use |Bool|'s recursor, while
for term-level (dependent) |if|, we need to use the eliminator.

\begin{spec}
⟦ •      ⟧Ctx = ⊤
⟦ Γ ▷ A  ⟧Ctx = Σ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty

⟦ 𝔹          ⟧Ty = λ ρ → Bool
⟦ Id A t₁ t₂ ⟧Ty = λ ρ → ⟦ t₁ ⟧Tm ρ ≡ ⟦ t₂ ⟧Tm ρ
⟦ Π A B      ⟧Ty = λ ρ → ∀ uⱽ → ⟦ B ⟧Ty (ρ Σ, uⱽ)
⟦ A [ δ ]Ty  ⟧Ty = λ ρ → ⟦ A ⟧Ty (⟦ δ ⟧Tms ρ)
⟦ IF t A B   ⟧Ty = λ ρ → Bool-rec (⟦ t ⟧Tm ρ) (⟦ A ⟧Ty ρ) (⟦ B ⟧Ty ρ)

⟦ π₁ δ   ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ .fst
⟦ id     ⟧Tms = λ ρ → ρ                            
⟦ ε      ⟧Tms = λ ρ → tt
⟦ δ , t  ⟧Tms = λ ρ → ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ
⟦ δ ⨾ σ  ⟧Tms = λ ρ → ⟦ δ ⟧Tms (⟦ σ ⟧Tms ρ)

⟦ ƛ t         ⟧Tm = λ ρ      uⱽ   → ⟦ t ⟧Tm (ρ Σ, uⱽ)
⟦ ƛ⁻¹ t       ⟧Tm = λ (ρ Σ,  uⱽ)  → ⟦ t ⟧Tm ρ uⱽ
⟦ TT          ⟧Tm = λ ρ           → true
⟦ FF          ⟧Tm = λ ρ           → false
⟦ t [ δ ]     ⟧Tm = λ ρ           → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ)
⟦ π₂ δ        ⟧Tm = λ ρ           → ⟦ δ ⟧Tms ρ .snd
⟦ if A t u v  ⟧Tm 
  = λ ρ → Bool-elim (λ b → ⟦ A ⟧Ty (ρ Σ, b)) (⟦ t ⟧Tm ρ) (⟦ u ⟧Tm ρ) (⟦ v ⟧Tm ρ)
⟦ J B p t     ⟧Tm = 
  λ ρ → ≡-elim (λ ⟦u⟧ ⟦p⟧ → ⟦ B ⟧Ty ((ρ Σ, ⟦u⟧) Σ, ⟦p⟧)) (⟦ p ⟧Tm ρ) (⟦ t ⟧Tm ρ)
\end{spec}

%if False
\begin{code}

postulate ⟦•⟧ : ⟦ • ⟧Ctx ≡ ⊤
{-# REWRITE ⟦•⟧ #-}

postulate ⟦▷⟧ : ⟦ Γ ▷ A ⟧Ctx ≡ Σ ⟦ Γ ⟧Ctx ⟦ A ⟧Ty
{-# REWRITE ⟦▷⟧ #-}

postulate ⟦𝔹⟧ : ⟦ 𝔹 {Γ = Γ} ⟧Ty ≡ λ ρ → Bool
{-# REWRITE ⟦𝔹⟧ #-}

postulate ⟦[]Ty⟧ : ⟦ A [ δ ]Ty ⟧Ty ≡ λ ρ → ⟦ A ⟧Ty (⟦ δ ⟧Tms ρ)
{-# REWRITE ⟦[]Ty⟧ #-}

postulate ⟦,⟧ : ∀ {t : Tm Δ (A [ δ ]Ty)}
              → ⟦ δ , t ⟧Tms ≡ λ ρ → ⟦ δ ⟧Tms ρ Σ, ⟦ t ⟧Tm ρ
{-# REWRITE ⟦,⟧ #-}


postulate ⟦wk⟧ : ⟦ wk {A = A} ⟧Tms ≡ λ ρ → ρ .fst
{-# REWRITE ⟦wk⟧ #-}

postulate ⟦id⟧ : ⟦ id {Γ = Γ} ⟧Tms ≡ λ ρ → ρ
{-# REWRITE ⟦id⟧ #-}

postulate ⟦Id⟧ : ⟦ Id A t₁ t₂ ⟧Ty ≡ λ ρ → ⟦ t₁ ⟧Tm ρ ≡ ⟦ t₂ ⟧Tm ρ
{-# REWRITE ⟦Id⟧ #-}

postulate ⟦vz⟧ : ⟦ vz {A = A} ⟧Tm ≡ λ ρ → ρ .snd
{-# REWRITE ⟦vz⟧ #-}

postulate ⟦TT⟧ : ⟦ TT {Γ = Γ} ⟧Tm ≡ λ ρ → true
{-# REWRITE ⟦TT⟧ #-}

postulate ⟦FF⟧ : ⟦ FF {Γ = Γ} ⟧Tm ≡ λ ρ → false
{-# REWRITE ⟦FF⟧ #-}

postulate ⟦[]⟧ : ⟦ t [ δ ] ⟧Tm ≡ λ ρ → ⟦ t ⟧Tm (⟦ δ ⟧Tms ρ) 
{-# REWRITE ⟦[]⟧ #-}

-- To get ⟦J⟧ to typecheck, we need to deal with the |subst|s.
-- Maybe more REWRITE rules could help, but would probably be easier to just
-- switch to |Prop|.
\end{code}
%endif

\begin{code}
true/false-disj : ¬ true ≡ false 
true/false-disj ()

sound t = true/false-disj (⟦ t ⟧Tm tt)
\end{code}

\subsection{From Quotients to Setoids}
\labsec{quotsetfibre}

% Note it is currently looking like we might not get on to any proofs
% that rely on this finer granularity though... Still, we do want to talk about
% SN in at least our SCBool discussion, so I think this is still reasonable
% to mention.
Two reasons: ease of mechanisation in current proof assistants, and the
ability to work with terms at a finer granularity that up-to-conversion.

We follow the translation outlined in \sidecite{kovacs2022staged}
(also \sidecite{altenkirch1999extensional, altenkirch2019setoid, 
pujet2022observational}).
Contexts become a setoid, types become a setoid fibration on contexts,
substitutions become a setoid fibration on pairs of contexts and terms
become a setoid fibration on types paired with their contexts.
 
\subsection{Strictification}
\labsec{strict}

\sidecite{kaposi2023towards} illustrates a strategy for starting with a QIIT
presentation of a syntax and then ``strictifying'' the constructors
corresponding to the ``morally-recursive'' operations after-the-fact.
This is already a big improvement, but unfortunately cannot justify 
strictifying equations relating how the recursive operations interact
(e.g. the identity or composition laws).

\sidecite{kaposi2025type} presents a much more involved construction, in which
all laws corresponding to substitutions are eventually strictified.

% Something something justify my horrible Agda code...

Of course, it is not immediately apparent that these results translate from
QIITs to setoids, but with work like \sidecite{altenkirch2019setoid}
showing translation from OTT to pure type theory while preserving definitional 
equality, it is not too much of a stretch to assume such a construction is
possible.


% Also, unlike from pattern-matching, QIIRT eliminators require still
% writing out the cases for non-canonical elements (the advantage only comes
% from the equations being much easier to prove.

\section{Normalisation by Evaluation}

\subsection{Naive Normalisation}

...

\subsection{Extending to Dependent Types}

When applying NbE for dependent types, we need to deal with terms embedded
inside types. As a first approximation, we might try and keep a similar
type for |Val| and construct identity environments to evaluate
embedded terms in on demand:
\begin{spec}
Val : ∀ Γ → Ty Γ → Set
Val Γ (if t A B) with eval t idℰ
... | TT      = Val Γ A
... | FF      = Val Γ B
... | ne tᴺᵉ  = Ne Γ (if t A B)
\end{spec}

However, this definition poses difficulties for the case of |Π-types|, where
we need to recurse at types |A [ δ ]| and |B [ δ , u ]|.

\begin{spec}
Val Γ (Π A B)
  = ∀ {Δ δ} (δᵀʰ : Thin Δ Γ δ) (uⱽ : Val Δ (A [ δ ]))
  → Val Δ (B [ δ , u ])
\end{spec}

Unfortunately, multiple things go wrong here:
\begin{itemize}
  \item |A [ δ ]| and |B [ δ , u ]| are not structurally smaller than |Π A B|,
  so it is not obvious that |Val| as defined above is well-founded. 
  The case for |A| can be
  fixed by relying on how thinnings do not structurally alter
  (substitution-normal) types in a meaningful way. However, |B [ δ , u ]| is 
  harder In the presense of large elimination \refremark{condisj}, there is no
  easy structurally-derived order on types which is
  also stable w.r.t. substitution\remarknote{
  Consider e.g. recursing on a natural number to build an iterated |Π|-types,
  as is sometimes done in dependently-typed languages to achieve
  arity-polymorphism.}
  \item It turns out
  that some of the cases in |qval|/|uval| depend on completeness of the
  NbE algorithm. We could attempt to
  mutually prove correctness, but this does not appear to work 
  in practice, as explained in \sidecite{altenkirch2017normalisation}.
\end{itemize}

To solve the latter issue, we need to fuse NbE values with the correctness
proof, and therefore index values by the term which we are evaluating.
To solve the former, we can additionally parameterise types by a substitution,
and the corresponding environment in which to evaluate embedded terms.

\begin{code}
Env  : ∀ Δ Γ → Tms Δ Γ → Set
Val  : ∀ Γ A Δ δ → Env Δ Γ δ → Tm Δ (A [ δ ]Ty) → Set
\end{code}

% |B [ < u > ]| is not structurally smaller than |Π A B|. If the large elimination
% on types is suitably restricted, it is possible to justify |Val| by recursion
% on spines as suggested in \sidecite{danielsson2006formalisation}
% \begin{spec}
% data Sp : Set where
%   𝔹  : Sp
%   Π  : Sp → Sp → Sp
% 
% sp : Ty Γ → Sp
% sp 𝔹       = 𝔹
% sp (Π A B) = Π (sp A) (sp B)
% \end{spec}

% but adapting this approach to a theory with large elimination
% seems impossible. To recurse at |A| in |if t A B|, we require 
% |sp A| to be structurally smaller than |sp (if t A B)|, but we also need
% to ensure conversion is preserved, i.e. |sp (if TT A B) ≡ sp A|.
% These goals are incompatible\remarknote{Adding a new spine
% constructor for |if|, |if : Sp → Sp → Sp| and quotienting
% with |if sA sB ≡ sA|, |if sA sB ≡ sB| does not work, because after being
% quotiented in this way, |if| is not injective, so we cannot rule out
% the spine of |if t A B| being merely |sp A|.}.

Evaluating both terms and substitutions can then be specified like so:

\begin{code}
eval   : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ ρ (t [ δ ])
eval*  : ∀ δ (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)
\end{code}

TODO: COPY IN DETAILS FROM MY AGDA PROOF THAT ARE RELEVANT HERE

\section{Dependent Pattern Matching}
\labsec{matching}

We have also liberally used pattern-matching in our metatheory.

In general, pattern-matching acts as syntactic sugar for elimination
rules. It covers a number of convieniences, including generalising
induction patterns (e.g. recursing on on any subterm of a pattern,
lexicographic orders \sidecite{abel2002recursion}). 

In a non-dependent type theory, pattern-matching as syntax sugar for
recursors is sufficient. When terms can occur in types, we also want to
be able to take advantage of information learnt over the course of the
match. For example: (go to old background section for examples...)


For a full formal treatment, we refer to \sidecite{cockx2017dependent}
but 

%TODO
 