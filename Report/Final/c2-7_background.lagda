%if False
\begin{code}
{-# OPTIONS --prop --rewriting --mutual-rewriting #-}

open import Utils hiding (ε)
open import Utils.IdExtras

open import Dependent.Standard.Strict

module Report.Final.c2-7_background where

\end{code}
%endif

\pagebreak
\subsection{NbE for Dependent Types}
\labsec{depnbe}

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
  harder In the presence of large elimination \refremark{condisj}, there is no
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

To solve the latter issue, we need to pair NbE values with the correctness
proofs (fusing the presheaf model with the logical relation), and therefore 
index values by the term which we are evaluating
(and environments by the list of terms they contain values of).
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
% constructor for ``|if|'', |if : Sp → Sp → Sp| and quotienting
% with |if sA sB ≡ sA|, |if sA sB ≡ sB| does not work, because after being
% quotiented in this way, ``|if|'' is not injective, so we cannot rule out
% the spine of |if t A B| being merely |sp A|.}.

Evaluating both terms and substitutions can then be specified like so:

\begin{code}
eval   : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ ρ (t [ δ ])
eval*  : ∀ δ (ρ : Env Θ Δ σ) → Env Θ Γ (δ ⨾ σ)
\end{code}

Given we are indexing values by the evaluated term, it is convenient to also
index normal forms by the normalised term (ultimately, working up to conversion,
any term which happens to be convertible to the normal form).

\begin{code}
data Ne : ∀ Γ A → Tm Γ A → Set
data Nf : ∀ Γ A → Tm Γ A → Set

data Ne where
  `_  : ∀ i → Ne Γ A (` i)
  _·_ : Ne Γ (Π A B) t → Nf Γ A u → Ne Γ (B [ < u > ]Ty) (t · u)
  if  : ∀ A {t u v} 
      → Ne Γ 𝔹 t → Nf Γ (A [ < TT > ]Ty) u → Nf Γ (A [ < FF > ]Ty) v
      → Ne Γ (A [ < t > ]Ty) (if A t u v)

data Nf where
  ne𝔹  : Ne Γ 𝔹 t → Nf Γ 𝔹 t
  neIF : Ne Γ 𝔹 u → Ne Γ (IF u A B) t → Nf Γ (IF u A B) t
  ƛ_   : Nf (Γ ▷ A) B t → Nf Γ (Π A B) (ƛ t)
  TT   : Nf Γ 𝔹 TT
  FF   : Nf Γ 𝔹 FF
\end{code}

Of course, if we are using a setoid-based model of syntax, we also
need coercion operations
%if False
\begin{code}
postulate
\end{code}
%endif

\begin{code}
  coeNe~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Ne Γ₁ A₁ t₁ → Ne Γ₂ A₂ t₂
  coeNf~ : ∀ Γ~ A~ → Tm~ Γ~ A~ t₁ t₂ → Nf Γ₁ A₁ t₁ → Nf Γ₂ A₂ t₂
\end{code}

We will elide these coercions (and cases pertaining to them) from now on
because dealing with coercions is ultimately very mechanical.

We also index thinnings by equivalent substitutions

\begin{code}
data Thin : ∀ Δ Γ → Tms Δ Γ → Set where
  ε      : Thin • • ε
  _^ᵀʰ_  : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ (A [ δ ]Ty)) (Γ ▷ A) (δ ^ A)
  _⁺ᵀʰ_  : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ A) Γ (δ ⨾ wk)

_[_]Nf   : Nf Γ A t → Thin Δ Γ δ → Nf Δ (A [ δ ]Ty) (t [ δ ])
_[_]Ne   : Ne Γ A t → Thin Δ Γ δ → Ne Δ (A [ δ ]Ty) (t [ δ ])
\end{code}

%if False
\begin{code}
idᵀʰ : Thin Γ Γ id
idᵀʰ {Γ = •}     = ε
idᵀʰ {Γ = Γ ▷ A} = idᵀʰ ^ᵀʰ A

wkᵀʰ : Thin (Γ ▷ A) Γ wk
wkᵀʰ = idᵀʰ ⁺ᵀʰ _

_⨾ᵀʰ_ : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)
\end{code}
%endif

We can now define environments by recursion on contexts. An
inductive definition like we had for STLC would still be well-founded,
but causes some subtle technical issues later on

%if False
data Env′ : ∀ Δ Γ → Tms Δ Γ → Set

data Env′ where
  ε    : Env′ Δ • ε
  _,_  : ∀ (ρ : Env Δ Γ δ) →  Val Γ A Δ δ ρ t → Env′ Δ (Γ ▷ A) (δ , t)
%endif

\begin{code}
Env Δ •        δ = ⊤
Env Δ (Γ ▷ A)  δ = Σ⟨ ρ ∶ Env Δ Γ (π₁ δ) ⟩× Val Γ A Δ (π₁ δ) ρ (π₂ δ)
\end{code}

Values are a bit more complicated. Again, the key idea is interpret types
into the category of presheaves, but dealing with large elimination
requires evaluating the embedded Boolean term.

%if False
\begin{code}
variable
  ρ ρ₁ ρ₂  : Env Δ Γ δ
  Ξ : Ctx

_[_]ℰ : Env Δ Γ δ → Thin Θ Δ σ → Env Θ Γ (δ ⨾ σ)
_∋_[_]𝒱 : ∀ A {t} → Val Γ A Δ δ ρ t → ∀ (σᵀʰ : Thin Θ Δ σ) 
        → Val Γ A Θ (δ ⨾ σ) (ρ [ σᵀʰ ]ℰ) (t [ σ ])
\end{code}
%endif

\sideremark{As in STLC (\refremark{funvalnat}), we technically should enforce 
naturality of |Π|-typed values here. To keep the presentation simpler, we again
skip this.}

\begin{code}
if-Val : ∀ Γ A B Δ δ (ρ : Env Δ Γ δ) {u[]} 
       → Tm Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) 
       → Nf Δ 𝔹 u[] → Set
if-Val Γ A B Δ δ ρ t TT
  = Val Γ A Δ δ ρ (coe~ rfl~ IF-TT t)
if-Val Γ A B Δ δ ρ t FF 
  = Val Γ B Δ δ ρ (coe~ rfl~ IF-FF t)
if-Val Γ A B Δ δ ρ {u[]} t (ne𝔹 _) 
  = Ne Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) t

Val Γ 𝔹           Δ δ ρ t = Nf Δ 𝔹 t
Val Γ (IF b A B)  Δ δ ρ t = if-Val Γ A B Δ δ ρ t (eval b ρ)
Val Γ (Π A B)     Δ δ ρ t 
  = ∀  {Θ γ} (γᵀʰ : Thin Θ Δ γ)
       {u} (uⱽ : Val Γ A Θ (δ ⨾ γ) (ρ [ γᵀʰ ]ℰ) u)
  → Val (Γ ▷ A) B Θ ((δ ⨾ γ) , u) ((ρ [ γᵀʰ ]ℰ) Σ, uⱽ) ((t [ γ ]) · u)
\end{code}

We also enforce |η|-equality of functions this time by embedding neutrals
only at |𝔹| and stuck |IF| types. This will slightly simplify the case
in the fundamental theorem for function application, at the cost of making
the embedding of neutrals into values more complicated. We call this
embedding operation \emph{unquoting}, and define it mutually with |qval|.

\begin{code}
uval : ∀ A {t} → Ne Δ (A [ δ ]Ty) t → Val Γ A Δ δ ρ t
qval : ∀ A {t} → Val Γ A Δ δ ρ t → Nf Δ (A [ δ ]Ty) t
\end{code}

%if False
\begin{code}
coe𝒱 : ∀ (A~ : Ty~ rfl~ A₁ A₂)
        → Tm~ Δ~ (A~ [ rfl~ ]Ty~) t₁ t₂
        → Val Γ A₁ Δ δ ρ t₁ → Val Γ A₂ Δ δ ρ t₂

postulate [id]ℰ : ∀ {ρ : Env Δ Γ δ} → ρ [ idᵀʰ ]ℰ ≡ ρ
{-# REWRITE [id]ℰ #-}
postulate [][]ℰ : ∀ {ρ : Env Δ Γ δ} {σᵀʰ : Thin Θ Δ σ} {γᵀʰ : Thin Ξ Θ γ}
                → ρ [ σᵀʰ ]ℰ [ γᵀʰ ]ℰ ≡ ρ [ σᵀʰ ⨾ᵀʰ γᵀʰ ]ℰ
{-# REWRITE [][]ℰ #-}
\end{code}
%endif

Evaluation of variables looks up the corresponding value in the environment
as usual. Evaluation of abstractions relies on coercing the value
at term |t [ (δ ⨾ γ) , u ]| to |(ƛ (t [ (δ ⨾ γ) ^ A ]) · u|

\begin{code}
lookupℰ : ∀ (i : Var Γ A) (ρ : Env Δ Γ δ) → Val Γ A Δ δ ρ (lookup i δ)
\end{code}
\begin{spec}
eval (` i)  ρ = lookupℰ i ρ
eval TT     ρ = TT
eval FF     ρ = FF
eval (ƛ t)  ρ {γ = γ} γᵀʰ {u = u} uⱽ 
  = coe𝒱  rfl~ (sym~ (Πβ {t = t [ (_ ⨾ _) ^ _ ]} {u = u})) 
          (eval {δ = (_ ⨾ _) , _} t ((ρ [ γᵀʰ ]ℰ) Σ, uⱽ))
\end{spec}

Dealing with the elimination rules (application and ``|if|''-expressions) 
is a bit trickier. We want evaluate |t · u| in |ρ|
by evaluating each term independently and directly applying them with the
identity thinning, |eval t ρ idᵀʰ (eval u ρ)| but hit two different 
type errors:
\begin{itemize}
  \item First of all, |eval t ρ idᵀʰ| expects a value in the environment
        |ρ [ idᵀʰ ]ℰ|, rather than |ρ|. We can separately prove the identity 
        law for thinning of
        values and environments to account for this discrepancy.
  \item The overall type of the application ends up as
        \begin{spec}
        Val (Γ ▷ A) B Δ (δ , (u [ δ ])) (ρ Σ, eval u ρ) ((t [ δ ]) · (u [ δ ]))
        \end{spec}
        but the inductive hypothesis requires
        \begin{spec}
        Val Γ (B [ < u > ]Ty) Δ δ ρ ((t [ δ ]) · (u [ δ ]))
        \end{spec}
        We seemingly need to ``shift'' substitutions onto and off of the type
        (|δ , (u [ δ ]) == < u > ⨾ δ|).
        \begin{code}
shiftVal[] : Val Δ (A [ δ ]Ty) Θ σ ρ t ≡ Val Γ A Θ (δ ⨾ σ) (eval* δ ρ) t
        \end{code}
\end{itemize}

We can get a better picture of the latter puzzle here by concretely writing
out the motives of the displayed (presheaf plus logical relation) model we are 
implicitly constructing via evaluation. The motives for
|Ctx|, |Ty|, |Var|, |Tm| and |Tms| are:

\begin{code}
record Motives : Set₂ where field
  PCtx  : Ctx → Set₁
  PTy   : PCtx Γ → Ty Γ → Set₁
  PVar  : ∀ (Γᴾ : PCtx Γ) → PTy Γᴾ A → Var Γ A → Set
  PTm   : ∀ (Γᴾ : PCtx Γ) → PTy Γᴾ A → Tm Γ A → Set
  PTms  : ∀ (Δᴾ : PCtx Δ) (Γᴾ : PCtx Γ) → Tms Δ Γ → Set
\end{code}

%if False
\begin{code}
module _ where
  open Motives
\end{code}
%endif

and in the case of evaluation, we instantiate these as follows

\begin{code}
  NbE : Motives 
  NbE .PCtx  Γ          = ∀ Δ → Tms Δ Γ → Set 
  NbE .PTy   Γᴾ  A      = ∀ Δ δ → Γᴾ Δ δ → Tm Δ (A [ δ ]Ty) → Set
  NbE .PVar  Γᴾ  Aᴾ  i  = ∀ Δ δ (ρ : Γᴾ Δ δ) → Aᴾ Δ δ ρ (lookup i δ)
  NbE .PTm   Γᴾ  Aᴾ  t  = ∀ Δ δ (ρ : Γᴾ Δ δ) → Aᴾ Δ δ ρ (t [ δ ]) 
  NbE .PTms  Δᴾ  Γᴾ  δ  = ∀ Θ σ (ρ : Δᴾ Θ σ) → Γᴾ Θ (δ ⨾ σ)
\end{code}

such that, modulo reordering of arguments, these match the types of
|Env|, |Val|, |eval| and |eval*|

%if False
\begin{code}
open Motives NbE
 
variable
  Γᴾ Δᴾ : PCtx Γ
  Aᴾ Bᴾ : PTy Γᴾ A
\end{code}
%endif

\begin{code}
elimCtx  : ∀ Γ  → PCtx Γ
elimTy   : ∀ A  → PTy (elimCtx Γ) A
elimVar  : ∀ i  → PVar (elimCtx Γ) (elimTy A) i
elimTm   : ∀ t  → PTm (elimCtx Γ) (elimTy A) t
elimTms  : ∀ δ  → PTms (elimCtx Δ) (elimCtx Γ) δ

elimCtx  Γ  Δ  δ       = Env Δ Γ δ
elimTy   A  Δ  δ  ρ t  = Val _ A Δ δ ρ t 
elimVar  i  Δ  δ  ρ    = lookupℰ i ρ
elimTm   t  Δ  δ  ρ    = eval t ρ
elimTms  δ  Θ  σ  ρ    = eval* δ ρ
\end{code}

From this perspective, we can see that the law we need corresponds exactly to 
preservation of type substitution in the model:

\begin{code}
_[_]Tyᴾ : PTy Γᴾ A → PTms Δᴾ Γᴾ δ → PTy Δᴾ (A [ δ ]Ty)
Aᴾ [ δᴾ ]Tyᴾ = λ Θ σ ρ t → Aᴾ Θ _ (δᴾ Θ σ ρ) t

elim-[]Ty  : ∀ {δ : Tms Δ Γ} 
           → elimTy (A [ δ ]Ty) ≡ elimTy A [ elimTms δ ]Tyᴾ

shiftVal[] {ρ = ρ} {t = t} = 
  cong-app (cong-app (cong-app (cong-app elim-[]Ty _) _) ρ) t
\end{code}

It turns out we will also rely on preservation of |id| and |wk|:

\sideremark{These laws are why we decided to implement |Env| recursively.
In an inductive definition of |Env|, we would only get isomorphisms here.}

\begin{code}
_,ᴾ_ : ∀ Γᴾ → PTy Γᴾ A → PCtx (Γ ▷ A)
Γᴾ ,ᴾ Aᴾ = λ Δ δ → Σ⟨ ρ ∶ Γᴾ Δ (wk ⨾ δ) ⟩× Aᴾ Δ (wk ⨾ δ) ρ ((` vz) [ δ ])

wkᴾ : ∀ {Aᴾ : PTy Γᴾ A} → PTms (Γᴾ ,ᴾ Aᴾ) Γᴾ (wk {A = A})
wkᴾ = λ θ σ ρ → ρ .fst

idᴾ : PTms Γᴾ Γᴾ id
idᴾ = λ θ σ ρ → ρ

elim-id  : elimTms (id {Γ = Γ}) ≡ idᴾ
elim-wk  : elimTms (wk {A = A}) ≡ wkᴾ {Aᴾ = elimTy A}
\end{code}

From now on, we assume both the functor laws for |_[_]ℰ| and 
the above preservation equations hold definitionally. Of
course, we will need to prove these properties
propositionally later.

%if False
\begin{code}
id-pres-rw  : ∀ {ρ : Env Δ Γ δ} → eval* id ρ ≡ ρ
id-pres-rw {ρ = ρ} = cong-app (cong-app (cong-app elim-id _) _) ρ
wk-pres-rw   : ∀ {ρ : Env Δ (Γ ▷ A) δ} → eval* wk ρ ≡ ρ .fst
wk-pres-rw {ρ = ρ} = cong-app (cong-app (cong-app elim-wk _) _) ρ
[]Ty-pres-rw  : Val Δ (A [ δ ]Ty) Θ σ ρ t ≡ Val Γ A Θ (δ ⨾ σ) (eval* δ ρ) t
[]Ty-pres-rw {ρ = ρ} {t = t}
  = cong-app (cong-app (cong-app (cong-app elim-[]Ty _) _) ρ) t
{-# REWRITE id-pres-rw wk-pres-rw []Ty-pres-rw #-}

-- We can avoid a termination pragma (see the original Agda mechanisation) but 
-- it requires a few tricks such as eagerly |with| abstracting which would just 
-- add clutter
--
-- NON_COVERING is of course required because we are ignoring |coe~| cases...
{-# NON_COVERING #-}
{-# TERMINATING #-}
\end{code}
%endif

With |elim-[]Ty| holding definitionally, evaluation of substitutions is merely
of fold of |eval| over the list of terms.

\begin{code}
eval* ε        ρ = tt
eval* (δ , t)  ρ = eval* δ ρ Σ, eval t ρ
\end{code}

Finally, we return to dealing with the eliminator cases of |eval|.
Evaluation of application just applies the left and right-hand-side values,
while evaluation of ``|if|''-expressions splits on the scrutinee. In the |TT| and
|FF| cases, we just select the appropriate value, while if the scrutinee
is a stuck neutral, we build a neutral ``|if|'' expression and embed it into
|Val| by unquoting.

\begin{code}
eval-if  : ∀ A {t u v} (tᴺᶠ : Nf Δ 𝔹 t)
         → Val (Γ ▷ 𝔹) A Δ (δ , TT) (ρ Σ, TT) u
         → Val (Γ ▷ 𝔹) A Δ (δ , FF) (ρ Σ, FF) v
         → Val (Γ ▷ 𝔹) A Δ (δ , t) (ρ Σ, tᴺᶠ) (if (A [ δ ^ 𝔹 ]Ty) t u v)
eval-if {δ = δ} A TT uⱽ vⱽ 
  = coe𝒱 (rfl~ {A = A}) (sym~ (𝔹β₁  (A [ δ ^ 𝔹 ]Ty))) uⱽ
eval-if {δ = δ} A FF uⱽ vⱽ 
  = coe𝒱 (rfl~ {A = A}) (sym~ (𝔹β₂  (A [ δ ^ 𝔹 ]Ty))) vⱽ
eval-if {δ = δ} A (ne𝔹 tᴺᵉ) uⱽ vⱽ 
  = uval A (if (A [ δ ^ 𝔹 ]Ty) tᴺᵉ (qval A uⱽ) (qval A vⱽ))
\end{code}

%if False
\begin{code}
lookupℰ (vz {A = A})    (ρ Σ, uⱽ) = uⱽ
lookupℰ (vs {B = B} i)  (ρ Σ, uⱽ) = lookupℰ i ρ

eval (` i)          ρ = lookupℰ i ρ
eval (ƛ t) ρ {γ = γ} γᵀʰ {u = u} uⱽ 
  = coe𝒱  rfl~ (sym~ (Πβ {t = t [ (_ ⨾ _) ^ _ ]} {u = u})) 
          (eval {δ = (_ ⨾ _) , _} t ((ρ [ γᵀʰ ]ℰ) Σ, uⱽ))
eval TT         ρ = TT
eval FF         ρ = FF
\end{code}
%endif

\begin{code}
eval (t · u)       ρ = eval t ρ idᵀʰ (eval u ρ)
eval (if A t u v)  ρ = eval-if A (eval t ρ) (eval u ρ) (eval v ρ)
\end{code}

We must also check in both |Val| and |eval| that |β| (and |η| in the case of
|Π|-typed terms) equations are preserved. |IF-TT| and |IF-FF| are preserved up
to coherence (|Val Γ (IF TT A B) Δ δ ρ t == Val Γ A Δ δ ρ (coe~ _ _ t)|.
|IFβ₁| and |IFβ₂| are conserved similarly
|eval (if A TT u v) ρ == coe𝒱 _ _ (eval u ρ)|.

|Πβ| and |Πη| are more subtle. We have
\begin{spec}
eval ((ƛ t) · u) ρ == coe𝒱 _ _ (eval t (ρ Σ, eval u ρ))
\end{spec}
and
\begin{spec}
eval (ƛ ((t [ wk ]) · (` vz))) ρ 
  == λ γᵀʰ {u} uⱽ → coe𝒱 _ _  (eval (t [ wk ]) 
                              ((ρ [ γᵀʰ ]ℰ) Σ, uⱽ) idᵀʰ uⱽ)
\end{spec}

But this does not get us quite far enough in either case. We need preservation
of term substitution.

\begin{code}
_[_]ᴾ  : ∀ {Γᴾ : PCtx Γ} {Δᴾ : PCtx Δ} {Aᴾ : PTy Γᴾ A}
       → PTm Γᴾ Aᴾ t → ∀ (δᴾ : PTms Δᴾ Γᴾ δ) 
       → PTm Δᴾ (Aᴾ [ δᴾ ]Tyᴾ) (t [ δ ])
tᴾ [ δᴾ ]ᴾ = λ Δ σ ρ → tᴾ Δ (_ ⨾ σ) (δᴾ Δ σ ρ)
\end{code}
\begin{spec}
elim-[] : elimTm (t [ δ ]) ≡ elimTm t [ elimTms δ ]ᴾ
\end{spec}

%if False
\begin{code}
elim-[]  : ∀ {t : Tm Γ A} {δ : Tms Δ Γ}
         →  elimTm (t [ δ ]) 
         ≡  _[_]ᴾ {t = t} {Aᴾ = elimTy A} (elimTm t) (elimTms δ)

elimIF-TT : Val Γ (IF TT A B) Δ δ ρ t ≡ Val Γ A Δ δ ρ (coe~ rfl~ IF-TT t)
elimIF-TT = {!!}

elimΠβ : ∀ {ρ : Env Δ Γ δ} → eval ((ƛ t) · u) ρ ≡[ {!!} ]≡ eval (t [ < u > ]) ρ
elimΠβ = {!!}

elimΠη : ∀ {ρ : Env Δ Γ δ} {t : Tm Γ (Π A B)} 
       → eval t ρ {γ = γ} ≡[ {!!} ]≡ eval (ƛ ((t [ wk ]) · (` vz))) ρ {γ = γ}
elimΠη = {!!}

elim𝔹β₁ : ∀ {ρ : Env Δ Γ δ} → eval (if A TT u v) ρ ≡[ {!!} ]≡ eval u ρ
elim𝔹β₁ = {!!}
\end{code}
%endif

Finally, we can proceed to the definitions of quoting and unquoting.
These functions are mutually recursive on types, with much of the
complexity coming from dealing with large |IF|.

\begin{code}
uval-if  : ∀ A B {u[] t} (uᴺᶠ : Nf Δ 𝔹 u[])
         → Ne Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) t
         → if-Val Γ A B Δ δ ρ t uᴺᶠ
qval-if  : ∀ A B {u[] t} (uᴺᶠ : Nf Δ 𝔹 u[])
         → if-Val Γ A B Δ δ ρ t uᴺᶠ
         → Nf Δ (IF u[] (A [ δ ]Ty) (B [ δ ]Ty)) t
\end{code}

\begin{code}
uval 𝔹           tᴺᵉ             = ne𝔹 tᴺᵉ
uval (Π A B)     tᴺᵉ γᵀʰ {u} uⱽ  = uval B ((tᴺᵉ [ γᵀʰ ]Ne) · qval A uⱽ)
uval (IF b A B)  tᴺᵉ             = uval-if A B (eval b _) tᴺᵉ

uval-if A B TT         tᴺᵉ = uval A (coeNe~ rfl~ IF-TT  coh tᴺᵉ)
uval-if A B FF         tᴺᵉ = uval B (coeNe~ rfl~ IF-FF  coh tᴺᵉ)
uval-if A B (ne𝔹 uᴺᵉ)  tᴺᵉ = tᴺᵉ

qval 𝔹           tⱽ = tⱽ
qval (IF b A B)  tⱽ = qval-if A B (eval b _) tⱽ
qval (Π A B)     tⱽ = coeNf~ rfl~ rfl~ (sym~ Πη) tᴺᶠ 
  where  vzⱽ  = uval {δ = _ ⨾ wk {A = (A [ _ ]Ty)}} A (` vz)
         tᴺᶠ  = ƛ qval B (tⱽ wkᵀʰ vzⱽ)

qval-if A B TT  tⱽ 
  = coeNf~ rfl~ (sym~ IF-TT)  (sym~ coh) (qval A tⱽ)
qval-if A B FF  tⱽ
  = coeNf~ rfl~ (sym~ IF-FF)  (sym~ coh) (qval B tⱽ)
qval-if A B (ne𝔹 uᴺᵉ) tⱽ = neIF uᴺᵉ tⱽ
\end{code}

Again, we need to ensure |IF-TT| and |IF-FF| are preserved by
|uval| and |qval|, and indeed they are
(up to coherence), so finally, we obtain normalisation:

%if False
\begin{code}
idℰ : Env Γ Γ id
\end{code}
%endif

\begin{code}
nbe : ∀ t → Nf Γ A t
nbe t = qval {δ = id} _ (eval t idℰ)
\end{code} 

We have checked soundness throughout the development of the algorithm.
Completeness instead follows from a simple inductive proof (on normal forms) 
that for |tᴺᶠ : Nf Γ A t|, we have |t ≡ ⌜ tᴺᶠ ⌝Nf|.

We should also technically check preservation of substitution operations
and the functor laws for thinning of values/environments. Functor laws for
thinnings follow by induction on types/contexts and eventually
(in the |𝔹| base case) on normal/neutral forms.

Preservation of substitution operations requires checking the associated 
naturality laws (which in-turn requires ensuring 
naturality of |Π|-typed values are natural). 
Staying well-founded is a little tricky: assuming 
substitution operations all respect some well-founded order,
we could in principle induct w.r.t. that, though in Agda (as we saw in
\refsec{naive}), well-founded induction
gets quite ugly. We could also pivot to explicit eliminators, via
which preservation laws would hold definitionally
(see e.g. the canonicity proof given in \sidecite{kaposi2025type}), 
but we would still have to
check all naturality equations, and we would lose the conciseness
of pattern matching. Ultimately I argue these technical
details are not fundamental to the algorithm/proof.

%TODO
% \section{Dependent Pattern Matching}
% \labsec{matching}
% 
% We have also liberally used pattern matching in our metatheory.
% 
% In general, pattern matching acts as syntactic sugar for elimination
% rules. It covers a number of conveniences, including generalising
% induction patterns (e.g. recursing on on any subterm of a pattern,
% lexicographic orders \sidecite{abel2002recursion}). 
% 
% In a non-dependent type theory, pattern matching as syntax sugar for
% recursors is sufficient. When terms can occur in types, we also want to
% be able to take advantage of information learnt over the course of the
% match. For example: (go to old background section for examples...)
% 
% 
% For a full formal treatment, we refer to \sidecite{cockx2017dependent}
% but 

%TODO
 