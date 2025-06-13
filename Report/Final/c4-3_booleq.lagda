%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

-- open import Report.Final.c4-1_booleq

module Report.Final.c4-3_booleq where

infixr 5 _⇒_
infixl 4  _,_
infix  5  ƛ_
infixl 6  _·_
infix  7  `_

infix 4 _>nd_
\end{code}
%endif

\subsection{Strong Normalisation of Non-Deterministic Reduction}

We now return to the world of simply typed terms in order to prove that
all such terms are strongly normalising w.r.t. non-deterministic reduction.
For this, we will use the technique of logical relations (also
known as computability \sidecite{tait1967computability} 
or reducibility candidates). The specific proof 
we attempt is based on Girard's proof of strong normalisation
for STLC in chapter 6 of \sidecite{girard1989proofs}, 
translated into Agda by András Kovács \sidecite{kovacs2020strong}.

%if False
\begin{code}
data Ty : Set where
  _⇒_  : Ty → Ty → Ty
  𝔹    : Ty
  
data Ctx : Set where
  •    : Ctx
  _▷_  : Ctx → Ty → Ctx

variable
  A B C : Ty
  Γ Δ Θ : Ctx

open import Common.Sort

data Tm[_] : Sort → Ctx → Ty → Set
Var = Tm[ V ]
Tm  = Tm[ T ]

data Tm[_] where
  vz  : Var (Γ ▷ A) A
  vs  : Var Γ B → Var (Γ ▷ A) B

  `_     : Var Γ A → Tm Γ A
  ƛ_     : Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  _·_    : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  TT FF  : Tm Γ 𝔹
  if     : Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A

data Tms[_] : Sort → Ctx → Ctx → Set where
  ε    : Tms[ q ] Δ •
  _,_  : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ ▷ A)

Ren = Tms[ V ]
Sub = Tms[ T ]  
 
_[_] : Tm[ q ] Γ A → Tms[ r ] Δ Γ → Tm[ q ⊔ r ] Δ A

tm⊑  : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
tms⊑  : q ⊑ r → Tms[ q ] Δ Γ → Tms[ r ] Δ Γ
_^_  : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ ▷ A) (Γ ▷ A)

vz          [ δ , t ]  = t
vs i        [ δ , t ]  = i [ δ ]
(` i)       [ δ ]      = tm⊑ ⊑T (i [ δ ])
(t · u)     [ δ ]      = (t [ δ ]) · (u [ δ ])
(ƛ t)       [ δ ]      = ƛ (t [ δ ^ _ ])
TT          [ δ ]      = TT
FF          [ δ ]      = FF
if t u v    [ δ ]      = if (t [ δ ]) (u [ δ ]) (v [ δ ])

id      : Tms[ q ] Γ Γ
_⁺_     : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ ▷ A) Γ
suc[_]  : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ ▷ A) B
_⨾_     : Tms[ q ] Δ Γ → Tms[ r ] Θ Δ → Tms[ q ⊔ r ] Θ Γ
wk      : Ren (Γ ▷ A) Γ
<_>     : Tm[ q ] Γ A → Tms[ q ] Γ (Γ ▷ A)

id {Γ = •}      = ε
id {Γ = Γ ▷ A}  = id ^ A

suc[ V  ] = vs
suc[ T  ] = _[ id {q = V} ⁺ _ ]
 
ε        ⁺ A = ε
(δ , t)  ⁺ A = (δ ⁺ A) , suc[ _ ] t

δ ^ A = (δ ⁺ A) , tm⊑ V⊑ vz

ε        ⨾ σ = ε
(δ , t)  ⨾ σ = (δ ⨾ σ) , (t [ σ ])

wk     = id ⁺ _
< t >  = tms⊑ V⊑ id , t

tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = V} {r = V} _ i = i
tm⊑ {q = T} {r = T} _ t = t

tms⊑ p ε       = ε
tms⊑ p (δ , t) = tms⊑ p δ , tm⊑ p t

variable
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ t[]′ : Tm Γ A
  δ σ : Tms[ q ] Δ Γ


⌜_⌝𝔹 : Bool → Tm Γ 𝔹
⌜ true   ⌝𝔹 = TT
⌜ false  ⌝𝔹 = FF

variable
  x y z : Tm[ q ] Γ A
  ξ : Tms[ q ] Δ Γ
  i j k : Var Γ A
  t[] t₂[] t′ : Tm Γ A

postulate 
  [][]  : x [ δ ] [ σ ] ≡ x [ δ ⨾ σ ]
  ⁺⨾    : (δ ⁺ A) ⨾ (σ , x) ≡ δ ⨾ σ
  ⨾⁺    : δ ⨾ (σ ⁺ A) ≡ (δ ⨾ σ) ⁺ A
  id⨾   : {δ : Tms[ q ] Δ Γ} → id {q = V} ⨾ δ ≡ δ
  ⨾id   : {δ : Tms[ q ] Δ Γ} → δ ⨾ id {q = V} ≡ δ
  suc[] : suc[ q ] x [ δ , y ] ≡  x [ δ ]
  [id]  : x [ id {q = V} ] ≡ x
  idT   : id {q = T} {Γ = Γ} ≡ tms⊑ V⊑T id
  
  [id,] : x [ (id {q = V} ⁺ A) , y ] ≡ x
  ⨾⨾    : (δ ⨾ σ) ⨾ ξ ≡ δ ⨾ (σ ⨾ ξ)
  
  ⊑⨾   : {q⊑r : q ⊑ r} {σ : Tms[ s ] Θ Δ} 
       → tms⊑ q⊑r δ ⨾ σ ≡ tms⊑ (⊑⊔s {s = s} q⊑r) (δ ⨾ σ)
  ⨾⊑   : {q⊑r : r ⊑ s} {δ : Tms[ q ] Δ Γ}
       → δ ⨾ tms⊑ q⊑r σ ≡ tms⊑ (s⊔⊑ {s = q} q⊑r) (δ ⨾ σ)
  
  ⊑⁺   : tms⊑ q⊑r δ ⁺ A ≡ tms⊑ q⊑r (δ ⁺ A) 

  [⊑]   : ∀ {q⊑r : q ⊑ r} {x : Tm[ s ] Γ A} 
        → x [ tms⊑ q⊑r δ ] ≡ tm⊑ (s⊔⊑ {s = s} q⊑r) (x [ δ ])
  [⊑,`] : x [ (tms⊑ ⊑T δ , (` j)) ] ≡ tm⊑ ⊑T (x [ δ , j ])

  ⊑[]   : ∀ {q⊑r : q ⊑ r} {x : Tm[ q ] Γ A} {δ : Tms[ s ] Δ Γ}
        → tm⊑ q⊑r x [ δ ] ≡ tm⊑ (⊑⊔s {s = s} q⊑r) (x [ δ ])

  id⁺vs : i [ id ⁺ A ] ≡ vs i

  tms⊑-id : tms⊑ q⊑r δ ≡ δ

-- Epic rewrite fail
-- https://github.com/agda/agda/issues/7602
T[][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
T[][] {t = t} = [][] {x = t}

V[][] : i [ δ ] [ σ ] ≡ i [ δ ⨾ σ ]
V[][] {i = i} = [][] {x = i}

{-# REWRITE [][] ⁺⨾ ⨾⁺ id⨾ ⨾id [id] ⨾⨾ ⊑⨾ ⨾⊑ ⊑⁺ [⊑] [⊑,`] id⁺vs tms⊑-id 
            T[][] V[][] [id,] ⊑[] idT #-}
\end{code}
%endif

To simplify the proof, we will assume all substitution equations hold
definitionally. For STLC, we can prove these equations by induction on
the syntax following \sidecite{altenkirch2025copypaste}, so to justify this
decision, we merely need to reflect these propositional equations as 
definitional ones (by conservativity of ETT over ITT 
\sidecite{hofmann1995conservativity, winterhalter2019eliminating} 
we, in principle, lose nothing by simplifying the presentation in this way).

We recall the definition of non-deterministic reduction.

\begin{code}
data _>nd_ : Tm Γ A → Tm Γ A → Set where
  -- Computation
  ⇒β   : (ƛ t) · u  >nd t [ < u > ]
  ndl  : if t u v   >nd u 
  ndr  : if t u v   >nd v
  
  -- Monotonicity
  ƛ_   : t₁  >nd t₂  → ƛ t₁       >nd ƛ t₂ 
  l·   : t₁  >nd t₂  → t₁ · u     >nd t₂ · u
  ·r   : u₁  >nd u₂  → t · u₁     >nd t · u₂
  if₁  : t₁  >nd t₂  → if t₁ u v  >nd if t₂ u v
  if₂  : u₁  >nd u₂  → if t u₁ v  >nd if t u₂ v
  if₃  : v₁  >nd v₂  → if t u v₁  >nd if t u v₂
\end{code}

We define computability (i.e. the logical relation) as follows

\begin{code}
P : ∀ Γ A → Tm Γ A → Set
P Γ 𝔹       t = SN _>nd_ t
P Γ (A ⇒ B) t 
  = ∀ {Δ} (δ : Ren Δ Γ) {u} → P Δ A u → P Δ B ((t [ δ ]) · u)
\end{code}

The resemblance to |Val| in NbE (\refsec{nbe}) should not be so surprising.
If we naively attempt to prove strong normalisation by direct structural 
induction on terms, we will again get stuck in the case of application, where
the LHS and RHS being strongly normalising does not imply that their application
is.

Like in NbE, we can parameterise function computability over renamings or
thinnings, corresponding to the presheaf exponential over the category of
renamings or the category of thinnings. 
We choose renamings here only for convenience.

Our analogue of NbE environments is evidence of computability of each of 
the terms we will substitute every variable for.

\begin{code}
data Ps (Δ : Ctx) : ∀ Γ → Sub Δ Γ → Set where
  ε   : Ps Δ • ε
  _,_ : Ps Δ Γ δ → P Δ A t → Ps Δ (Γ ▷ A) (δ , t)
\end{code}

We can prove that non-deterministic reduction is stable under substitutions and
inverting renamings.

\begin{code}
_[_]>    : t₁ >nd t₂ → (δ : Tms[ q ] Δ Γ) → t₁ [ δ ] >nd t₂ [ δ ]

[_]>⁻¹_  : ∀ (δ : Ren Δ Γ) → t [ δ ] >nd t[]′
         → Σ⟨ t′ ∶ Tm Γ A ⟩× (t >nd t′ × t′ [ δ ] ≡ t[]′)
\end{code}

These stability properties follow pretty directly from induction on the
definition of reduction (plus definitional substitution equations).
E.g. for the case of applying a substitution to |⇒β|, we need
|((ƛ t) · u) [ δ ] >nd t [ < u > ] [ δ ]|, which is satisfied immediately
with |⇒β| because
\begin{spec}
((ƛ t) · u) [ δ ] == (ƛ (t [ δ ^ A ])) · (u [ δ ])
\end{spec}
and
\begin{spec}
t [ < u > ] [ δ ] == t [ δ , (u [ δ ]) ] == t [ δ ^ A ] [ < u [ δ ] > ]
\end{spec}

%if False
\begin{code}
⇒β    [ δ ]> = ⇒β
ndl   [ δ ]> = ndl
ndr   [ δ ]> = ndr
(ƛ p) [ δ ]> = ƛ (p [ δ ^ _ ]>)
l· p  [ δ ]> = l· (p [ δ ]>)
·r p  [ δ ]> = ·r (p [ δ ]>)
if₁ p [ δ ]> = if₁ (p [ δ ]>)
if₂ p [ δ ]> = if₂ (p [ δ ]>)
if₃ p [ δ ]> = if₃ (p [ δ ]>)
\end{code}
%endif

%if False
\begin{code}
[_]>⁻¹_ {t = (ƛ t) · u}  δ ⇒β   = t [ < u > ]  Σ, ⇒β   Σ, refl
[_]>⁻¹_ {t = if t u v}   δ ndl  = u            Σ, ndl  Σ, refl
[_]>⁻¹_ {t = if t u v}   δ ndr  = v            Σ, ndr  Σ, refl
\end{code}
%endif

%if False
\begin{code}
[_]>⁻¹_ {t = ƛ t}       δ (ƛ p)  
  using t′ Σ, p′ Σ, q ← [_]>⁻¹_ {t = t} (δ ^ _) p
  = ƛ t′ Σ, ƛ p′ Σ, cong ƛ_ q
[_]>⁻¹_ {t = t · u}     δ (l· p)
  using t′ Σ, p′ Σ, q ← [_]>⁻¹_ {t = t} δ p
  = t′ · u Σ, l· p′ Σ, cong (_· _) q
[_]>⁻¹_ {t = t · u}     δ (·r p)
  using u′ Σ, p′ Σ, q ← [_]>⁻¹_ {t = u} δ p
  = t · u′ Σ, ·r p′ Σ, cong (_ ·_) q
[_]>⁻¹_ {t = if t u v}  δ (if₁ p) 
  using t′ Σ, p′ Σ, q ← [_]>⁻¹_ {t = t} δ p
  = if t′ u v Σ, if₁ p′ Σ, cong (λ □ → if □ _ _) q
[_]>⁻¹_ {t = if t u v}  δ (if₂ p) 
  using u′ Σ, p′ Σ, q ← [_]>⁻¹_ {t = u} δ p
  = if t u′ v Σ, if₂ p′ Σ, cong (λ □ → if _ □ _) q
[_]>⁻¹_ {t = if t u v}  δ (if₃ p) 
  using v′ Σ, p′ Σ, q ← [_]>⁻¹_ {t = v} δ p
  = if t u v′ Σ, if₃ p′ Σ, cong (λ □ → if _ _ □) q
\end{code}
%endif

From stability of reduction under inverted renamings, we can show that |SN| is
stable under (forwards) renaming, and therefore computability is also.
Note that we needed stability w.r.t. inverted renamings to show this because the 
reduction itself appears in contravariant position (i.e. left of arrow) in 
the type of |acc| (intuitively, we are transforming reduction chains
starting from |t [ δ ]| into reduction chains starting from |t|).

\begin{code}
_[_]SN   : SN _>nd_ t → ∀ (δ : Ren Δ Γ) → SN _>nd_ (t [ δ ])
acc tᴬ [ δ ]SN 
  = acc λ p →  let  t′ Σ, p′ Σ, q = [ δ ]>⁻¹ p
               in   subst (SN _>nd_) q (tᴬ p′ [ δ ]SN)
\end{code}

%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  _[_]P   : P Γ A t → ∀ (δ : Ren Δ Γ) → P Δ A (t [ δ ])
  _[_]Ps  : Ps Δ Γ δ → ∀ (σ : Ren Θ Δ) → Ps Θ Γ (δ ⨾ σ)
\end{code}

By analogous reasoning, strong normalisation is also stable under inverting
substitution.

\begin{code}
[_]SN⁻¹_ : ∀ (δ : Tms[ q ] Δ Γ) → SN _>nd_ (t [ δ ]) → SN _>nd_ t
[ δ ]SN⁻¹ (acc t[]ᴬ)
  = acc λ p → [ δ ]SN⁻¹ (t[]ᴬ (p [ δ ]>))
\end{code}

We are now ready to prove the fundamental theorem: |t [ δ ]| is computable
as long as all terms in |δ| are.

\begin{code}
fndThm : ∀ (t : Tm Γ A) → Ps Δ Γ δ → P Δ A (t [ δ ])
\end{code}

To prove the fundamental theorem, we need a couple of lemmas.
Specifically, that it is possible to derive strong
normalisation from computability (|P-SN|) and that if all immediate
reducts of a term (not headed by |ƛ|-abstraction) are computable, then the 
original term must be also (|P<|). These lemmas resemble quoting and
unquoting in NbE.

\begin{code}
ƛ? : Tm Γ A → Bool
ƛ? (ƛ _) = true
ƛ? _     = false

P-SN  : P Γ A t → SN _>nd_ t
P<    : ¬is ƛ? t → (∀ {t′} → t >nd t′ → P Γ A t′) → P Γ A t
\end{code}

The fundamental theorem is proved by induction on terms, similarly to
evaluation in NbE. We use the fact that |TT|, |FF| and fresh variables are
trivially computable (there are no reductions with these constructs
on the LHS). The cases for λ-abstraction and ``|if|'' are more
complicated, so we will cover these separately.

\begin{code}
lookupP : ∀ (i : Var Γ A) → Ps Δ Γ δ → P Δ A (i [ δ ])

tt-sn : SN _>nd_ (TT {Γ = Γ})
tt-sn = acc λ ()

ff-sn : SN _>nd_ (FF {Γ = Γ})
ff-sn = acc λ ()

`P : P Γ A (` i)
`P = P< tt λ ()

fndThm-ƛ    : (∀ {u} → P Γ A u → P Γ B (t [ < u > ]))
            → SN _>nd_ t → P Γ A u → SN _>nd_ u → P Γ B ((ƛ t) · u)
fndThm-if   : SN _>nd_ t → P Γ A u → SN _>nd_ u → P Γ A v → SN _>nd_ v 
            → P Γ A (if t u v)

fndThm (` i)       ρ = lookupP i ρ
fndThm (ƛ t)       ρ 
  = λ σ uᴾ → fndThm-ƛ  (λ uᴾ′ → fndThm t ((ρ [ σ ]Ps) , uᴾ′)) 
                       (P-SN (fndThm t ((ρ [ σ ⁺ _ ]Ps) , `P))) 
                       uᴾ (P-SN uᴾ)
fndThm (t · u)     ρ = fndThm t ρ id (fndThm u ρ)
fndThm TT          ρ = tt-sn
fndThm FF          ρ = ff-sn
fndThm (if t u v)  ρ 
  = fndThm-if (fndThm t ρ) uᴾ (P-SN uᴾ) vᴾ (P-SN vᴾ)
  where  uᴾ = fndThm u ρ
         vᴾ = fndThm v ρ
\end{code}

%if False
\begin{code}
lookupP vz     (ρ , uᴾ) = uᴾ
lookupP (vs i) (ρ , uᴾ) = lookupP i ρ

[_]ƛ⁻¹_ : ∀ (δ : Ren Δ Γ) → is ƛ? (t [ δ ]) → is ƛ? t
[_]ƛ⁻¹_ {t = ƛ _} δ tt = tt

-- TODO: Tidy this, use |[_]ƛ⁻¹_| as a helper
_[_]¬ƛ : ¬is ƛ? t → ∀ (δ : Ren Δ Γ) → ¬is ƛ? (t [ δ ]) 
_[_]¬ƛ {t = ` i}      p δ = tt
_[_]¬ƛ {t = t · u}    p δ = tt
_[_]¬ƛ {t = TT}       p δ = tt
_[_]¬ƛ {t = FF}       p δ = tt
_[_]¬ƛ {t = if t u v} p δ = tt
\end{code}
%endif

To prove the fundamental theorem in the case of |ƛ|-abstractions and ``|if|''
expressions, we repeatedly appeal to 
|P<| to step along the chain of reductions, and rely on |SN| of subterms to 
induct w.r.t. reduction order in the cases where a subterm
is reduced. When we finally hit |⇒β| or |ndl|/|ndr|, we return
computability of the reduct. To carry along computability evidence until
this point, we also need that computability is stable under reduction, |P>|.

\begin{code}
P> : t₁ >nd t₂ → P Γ A t₁ → P Γ A t₂

fndThm-ƛ> : (∀ {u} → P Γ A u → P Γ B (t [ < u > ]))
          → SN _>nd_ t → P Γ A u → SN _>nd_ u
          → (ƛ t) · u >nd t′ → P Γ B t′

fndThm-ƛ tᴾ tᴬ uᴾ uᴬ = P< tt (fndThm-ƛ> tᴾ tᴬ uᴾ uᴬ)

fndThm-ƛ> tᴾ tᴬ        uᴾ uᴬ        ⇒β  
  = tᴾ uᴾ
fndThm-ƛ> tᴾ tᴬ        uᴾ (acc uᴬ)  (·r u>)      
  = fndThm-ƛ tᴾ tᴬ (P> u> uᴾ) (uᴬ u>)
fndThm-ƛ> tᴾ (acc tᴬ)  uᴾ uᴬ        (l· (ƛ t>))  
  = fndThm-ƛ  (λ {u = u′} uᴾ′ → P> (t> [ < u′ > ]>) (tᴾ uᴾ′)) 
              (tᴬ t>) uᴾ uᴬ

fndThm-if>  : SN _>nd_ t → P Γ A u → SN _>nd_ u 
            → P Γ A v → SN _>nd_ v 
            → if t u v >nd t′ → P Γ A t′

fndThm-if tᴬ uᴾ uᴬ vᴾ vᴬ = P< tt (fndThm-if> tᴬ uᴾ uᴬ vᴾ vᴬ)

fndThm-if> tᴬ        uᴾ uᴬ        vᴾ vᴬ        ndl      = uᴾ
fndThm-if> tᴬ        uᴾ uᴬ        vᴾ vᴬ        ndr      = vᴾ
fndThm-if> (acc tᴬ)  uᴾ uᴬ        vᴾ vᴬ        (if₁ t>)  
  = fndThm-if (tᴬ t>) uᴾ uᴬ vᴾ vᴬ
fndThm-if> tᴬ        uᴾ (acc uᴬ)  vᴾ vᴬ        (if₂ u>)  
  = fndThm-if tᴬ (P> u> uᴾ) (uᴬ u>) vᴾ vᴬ
fndThm-if> tᴬ        uᴾ uᴬ        vᴾ (acc vᴬ)  (if₃ v>)  
  = fndThm-if tᴬ uᴾ uᴬ (P> v> vᴾ) (vᴬ v>) 
\end{code}

We now prove the remaining lemmas by recursion on types. 
\begin{itemize}
  \item Stability
        of computability under reduction is proved by considering larger and 
        larger
        spines (always applying the reduction to the LHS) until we reach 
        base |𝔹| type.
  \item Mapping from computability to strong normalisation is achieved by 
        repeatedly
        applying computability of |⇒|-typed terms to a fresh variable, and then
        taking advantage of how strong normalisability is stable under 
        taking subterms
        and renaming to get back to |SN| of the original |⇒|-typed term.
\end{itemize}


\begin{code}
P> {A = 𝔹}      t> (acc tᴬ) = tᴬ t>
P> {A = A ⇒ B}  t> tᴾ       = λ δ uᴾ → P> (l· (t> [ δ ]>)) (tᴾ δ uᴾ)

SN-l· : SN _>nd_ (t · u) → SN _>nd_ t
SN-l· (acc tuᴬ) = acc λ p → SN-l· (tuᴬ (l· p))

P-SN {A = 𝔹}      tᴬ  = tᴬ
P-SN {A = A ⇒ B}  tᴾ  
  = [ wk ]SN⁻¹ SN-l· (P-SN (tᴾ wk (`P {i = vz})))
\end{code}

|P<| (all reducts of a term being computable implies the term itself is)
is a bit more complicated. 

We mutually prove a more specialised version for the case of applications,
|P<·|, where
we have direct computability of the RHS and 
know every term the LHS reduces to is computable. We prove this by
appealing to |P<|: if the reduction occurs in the LHS, we can obtain
computability of the application immediately by combining computability info,
while if the reduction occurs in the RHS, we proceed by induction w.r.t.
reduction order (computability of the RHS implies it is strongly normalising).
We avoid needing to consider the case where the overall application contracts 
with |⇒β| by assuming the LHS is not |ƛ|-abstraction headed.

Then to prove |P<| itself at |⇒|-type, we take advantage of having access to 
computability of the argument
to apply |P<·|.

\begin{code}
P<·   : ¬is ƛ? t → (∀ {t′} → t >nd t′ → P Γ (A ⇒ B) t′) 
      → P Γ A u → SN _>nd_ u → P Γ B ((t · u))
P<·>  : ¬is ƛ? t → (∀ {t′} → t >nd t′ → P Γ (A ⇒ B) t′) 
      → P Γ A u → SN _>nd_ u → (t · u) >nd t′ → P Γ B t′


P<· ¬ƛ tᴾ uᴾ uᴬ = P< tt (P<·> ¬ƛ tᴾ uᴾ uᴬ)

P<·> ¬ƛ tᴾ uᴾ uᴬ        (l· t>)  = tᴾ t> id uᴾ
P<·> ¬ƛ tᴾ uᴾ (acc uᴬ)  (·r u>)  = P<· ¬ƛ tᴾ (P> u> uᴾ) (uᴬ u>)

P< {A = 𝔹}               ¬ƛ tᴾ = acc λ p → tᴾ p
P< {A = A ⇒ B} {t = t}   ¬ƛ tᴾ 
  = λ δ uᴾ → P<· (¬ƛ [ δ ]¬ƛ) 
                 (λ p σ uᴾ′ →  let  _ Σ, p′ Σ, q = [ δ ]>⁻¹ p 
                               in   subst (λ □ → P _ B ((□ [ σ ]) · _)) q 
                                          (tᴾ p′ (δ ⨾ σ) uᴾ′)) 
                 uᴾ (P-SN uᴾ)
\end{code}

Now to obtain strong normalisation, we merely need to derive computability
of all variables in the identity substitution, so we can apply the fundamental
theorem and follow it up with |P-SN|.

\begin{code}
idᴾ : Ps Γ Γ id
idᴾ {Γ = •}      = ε
idᴾ {Γ = Γ ▷ A}  = idᴾ [ wk ]Ps , `P

sn : SN _>nd_ t
sn {t = t} = P-SN (fndThm t idᴾ)
\end{code}
