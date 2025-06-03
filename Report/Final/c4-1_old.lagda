

a normalisation algorithm which depends on
deciding |rw|'s convertability premise cannot work.

The trick is thus: we



 confluence and that whether term

 also need confluence. The new |_⊢_>_| relation definitely

The trick t


The obvious cause of our prior attempt at reduction relation failing was
that 

We clearly need a better reduction relation.






We might attempt to define a small-step reduction relation that corresponds to
this conversion relation.





\section{Normalisation}

We aim to show that this enhanced conversion relation is decidable via
the technique of strong normalisation. We define a small-step reduction
relation:

%if False
\begin{code}
infix 4 _⊢_>_ 
\end{code}
%endif

\begin{code}
-- data _⊢_>_ (Ξ : Eqs Γ) : Tm Γ A → Tm Γ A → Set where
--   -- Computation
--   ⇒β   : Ξ ⊢ (ƛ t) · u  > t [ < u > ]
--   𝔹β₁  : Ξ ⊢ if TT u v  > u 
--   𝔹β₂  : Ξ ⊢ if FF u v  > v
  
--   -- Rewriting
--   eq : EqVar Ξ t b → Ξ ⊢ t > ⌜ b ⌝𝔹

--   -- Monotonicity
--   ƛ_   : Ξ [ wk ]Eq  ⊢ t₁  > t₂  → Ξ ⊢ ƛ t₁       > ƛ t₂ 
--   l·   : Ξ           ⊢ t₁  > t₂  → Ξ ⊢ t₁ · u     > t₂ · u
--   ·r   : Ξ           ⊢ u₁  > u₂  → Ξ ⊢ t · u₁     > t · u₂
--   if₁  : Ξ           ⊢ t₁  > t₂  → Ξ ⊢ if t₁ u v  > if t₂ u v
--   if₂  : Ξ           ⊢ u₁  > u₂  → Ξ ⊢ if t u₁ v  > if t u₂ v
--   if₃  : Ξ           ⊢ v₁  > v₂  → Ξ ⊢ if t u v₁  > if t u v₂
\end{code}

% Oh I am very silly
% This reduction relation is nonsense
% The |eq| pre-condition should be |Ξ ⊢ t ~ ⌜ b ⌝𝔹|

% Maybe worth positing the idea of having a reduction which simplifies the
% equational context, and then using the old rule.

% What we can say is that for completes TRSs, the above reduction relation
% is equivalent.

% The completion algorithm can be justified by having |~|-pre is SN, and then 
% only ever
% actually rewriting by completed |TRS|s!

% |~|-pre is SN by existing work
% Normalisation then works by completing every time an equation is introduced,
% and inserting |!| if the equational context is inconsistent.

Note that this recuction relation is not confluent! To stay well-founded, we
do not support rewriting from |TT|/|FF|, but there is nothing stopping 
our equational context from containing ``bad'' equations like |TT ~ FF|.

To normalise terms in arbitrary equational contexts then, we need to first
complete the set of equations into a confluent (ground) TRS, and then proceed
reducing with small-step reduction. Strong normalisation is useful here, 
as taking the fixed point of repeatedly reducing equation LHSs can be
justified by extending reduction order over equational contexts 
lexicographically.

% Todo: we have some design decisions to make here
% We could define a restricted version of |_⊢_>_| which doesn't allow rewriting
% Booleans. Assuming this relation is well-founded (for any equational
% environment), justifying completion is not too hard.

% Alternatively, we could define a predicate on equation sets which guarantees
% they don't have any closed booleans on the LHS. Reduction as-is is SN
% for any such environment. We can then show how this property is decidable
% Normalisation still has to do completion so we can insert |!|s where-ever
% the equational environment is unsound (might be useful to define equality
% collapse early)

% I think I nice way to structure explanations could be: 
% This reduction relation is not SN in presense of Bool equations
% Redundant equations can obviously be removed
% Impossible equations imply equality collapse
% Therefore we can define normalisation as first completing the set of rewrites

\begin{code}
TRS : Eqs Γ → Set

sn : TRS Ξ → ∀ (t : Tm Γ A) → SN (Ξ ⊢_>_) t

-- TRS defined as:
-- All LHSs irreducible
-- All LHSs neutral
--
-- From this, we can pretty easily derive no overlap/confluence


-- data TRS where
--   •        : TRS (• {Γ = Γ})
--   _▷_>eq_  : TRS Ξ → {!!}
\end{code}

%if False
\begin{code}
infix 4 _⊢_>Eq_ _>Eq_ 
\end{code}
%endif

\begin{code}
data _⊢_>Eq_ (Ξ : Eqs Γ) : Eqs Γ → Eqs Γ → Set

_>Eq_ : Eqs Γ → Eqs Γ → Set
Ψ >Eq Φ = Ψ ⊢ Ψ >Eq Φ

data _⊢_>Eq_ Ξ where
  vz>  : Ξ ⊢ t₁ > t₂ → Ξ ⊢ Ψ ▷ t₁ >eq b >Eq Ψ ▷ t₂ >eq b
  vs>  : Ξ ⊢ Ψ₁ >Eq Ψ₂ → Ξ ⊢ t₁ ~ t₂ → Ξ ⊢ Ψ₁ ▷ t₁ >eq b >Eq Ψ₂ ▷ t₂ >eq b 

data SNEq (Ξ : Eqs Γ) : Eqs Γ → Set where
  •    : SNEq Ξ (• {Γ = Γ})
  _▷_  : SNEq Ξ Ψ → SN (Ξ ⊢_>_) t → SNEq Ξ (Ψ ▷ t >eq b)

snEq : TRS Ξ → ∀ Ψ → SN (Ξ ⊢_>Eq_) Ψ

sn▷   : TRS Ξ → SN (Ξ ⊢_>Eq_) Ψ → SN (Ξ ⊢_>_) t → SN (Ξ ⊢_>Eq_) (Ψ ▷ t >eq b)
sn▷>  : TRS Ξ → SN (Ξ ⊢_>Eq_) Ψ₁ → SN (Ξ ⊢_>_) t₁
      → Ξ ⊢ Ψ₁ ▷ t₁ >eq b >Eq Ψ₂ → SN (Ξ ⊢_>Eq_) Ψ₂

sn▷ Ξᶜ Ψᴬ tᴬ = acc (sn▷> Ξᶜ Ψᴬ tᴬ)

sn▷> Ξᶜ Ψᴬ        (acc tᴬ)  (vz> t>)     = sn▷ Ξᶜ Ψᴬ       (tᴬ t>)
sn▷> Ξᶜ (acc Ψᴬ)  tᴬ        (vs> Ψ> t~)  = sn▷ Ξᶜ (Ψᴬ Ψ>)  (sn Ξᶜ _)

snSNEq  : TRS Ξ → SNEq Ξ Ψ → SN (Ξ ⊢_>Eq_) Ψ
snSNEq> : TRS Ξ → SNEq Ξ Ψ₁ → Ξ ⊢ Ψ₁ >Eq Ψ₂ → SN (Ξ ⊢_>Eq_) Ψ₂

snSNEq Ξᶜ Ψ = acc (snSNEq> Ξᶜ Ψ)

-- This sucks - we need to combine structural and SN order here, and I'm not
-- quite sure how to justify it...
snSNEq> Ξᶜ (Ψ ▷ acc tᴬ)  (vz> t>)    = {! snSNEq Ξᶜ (Ψ ▷ tᴬ t>) !}
snSNEq> Ξᶜ (Ψ ▷ tᴬ)      (vs> Ψ> t~) = sn▷ Ξᶜ (snSNEq> Ξᶜ Ψ Ψ>) (sn Ξᶜ _)
\end{code}

We have a reduction relation and potential normalisation algorithm, but 
we of course still need to prove this reduction relation is well-founded.
We do this by picking a slightly larger reduction relation that is 
slightly better-behaved.

\subsection{Spontaneous and Non-Determinsitic Reduction}

\begin{code}
data _>!_ : Tm Γ A → Tm Γ A → Set where
  eqTT : t >! TT
  eqFF : t >! FF
\end{code}

Proving strong normalisation of spontaneous reduction directly is possible,
but is slightly awkward due to instability under substitutions.
E.g. we have |` i >! TT|, if we then apply the substitution |TT / i| to
both sides, we are left with |TT >! TT|, which is explicitly not allowed
to ensure |TT| stays in normal form.

We therefore consider yet another reduction relation: Non-Deterministic
Reduction. The idea is to allow any |if|-expression to immediately reduce
to the left or right branch (irrespective of the scrutinee).

\begin{code}
data _>ND_ : Tm Γ A → Tm Γ A → Set where
  ifND₁  : if t u v >ND u
  ifND₂  : if t u v >ND v
\end{code}

It turns out that we can prove that strong normalisation w.r.t.
non-determinsitic reduction implies strong normalisation w.r.t. spontaneous
reduction. In fact, we can prove this result inside untyped lambda calculus
(removing the |𝔹|-typed condition on spontaneous reduction. We will prove
this now.










With β-equality alone, we quickly get stuck if the scrutinee is a variable.
E.g. equations like |if t u u ~ u| or |if t t u ~ TT|. As mentioned in
(TODO REFERENCE RELATED WORK), strict η for Booleans can make such
such equations derivable.

\begin{code}
𝔹η : u [ < t > ] ~ if t (u [ < TT > ]) (v [ < FF > ])
\end{code}

However, I claim that |𝔹η| is too strong. Existing normalisation algorithms
all rely on effectively splitting on every Boolean neutral, requiring
re-normalising on the order of $2^n$ times, where $n$ is the number 
of distinct neutral Boolean subterms. 

%TODO Finish writing this
















But is not quite what we want: |_⊢_~_| should not only identify
terms modulo a fixed set of Boolean equations. We should be introducing
new equations in the branches of each |if| expression, i.e.

\begin{spec}
  if  : Ξ ⊢ t₁ ~ t₂ → Ξ ▷ t₁ >eq true ⊢ u₁ ~ u₂ → Ξ ▷ t₁ >eq false ⊢ v₁ ~ v₂
      → Ξ ⊢ if t₁ u₁ v₁ ~ if t₂ u₂ v₂
\end{spec}

We somewhat arbitrarily insert |t₁|, rather than |t₂|, into the equational
context. From stability of conversion over
weakening the
equational context
(i.e. adding new equations), we find the
choice here is ultimately irrelevant:


\begin{code}
data WkEqs {Γ} : Eqs Γ → Eqs Γ → Set where
  ε        : WkEqs • •
  _⁺_>eq_  : WkEqs Φ Ψ → Tm Γ 𝔹 → Bool → WkEqs (Φ ▷ t >eq b) (Ψ ▷ t >eq b)

wkeq : WkEqs (Ξ ▷ t >eq b) Ξ

_[_]Wk~ : Ψ ⊢ t₁ ~ t₂ → WkEqs Φ Ψ → Φ ⊢ t₁ ~ t₂

swapEqVar  : Ξ ⊢ t₁ ~ t₂ → EqVar (Ξ ▷ t₁ >eq true) u b 
           → Ξ ▷ t₂ >eq true ⊢ u ~ ⌜ b ⌝𝔹
swapEqVar t~ ez      = t~ [ wkeq ]Wk~ ∙~ eq ez
swapEqVar t~ (es e)  = eq (es e)
\end{code}

%if False
\begin{code}
_[_]~ : Ξ ⊢ t₁ ~ t₂ → ∀ (δ : Tms[ q ] Δ Γ) → Ξ [ δ ]Eq ⊢ t₁ [ δ ] ~ t₂ [ δ ]


-- I think we need an IH that equational contexts are equivalent...

swapEq : Ξ ⊢ t₁ ~ t₂ → (Ξ ▷ t₁ >eq true) ⊢ u₁ ~ u₂
       → (Ξ ▷ t₂ >eq true) ⊢ u₁ ~ u₂
swapEq t~ (eq e)            = swapEqVar t~ e
swapEq t~ (ƛ u~)            = ƛ swapEq (t~ [ wk ]~) u~

swapEq t~ (if u₁~ u₂~ u₃~)  = {!!}
  -- if (swapEq t~ u₁~) (swapEq {!   !} {!  u₂~ !}) {!!}

swapEq t~ ⇒β = {!   !}
swapEq t~ 𝔹β₁ = {!   !}
swapEq t~ 𝔹β₂ = {!   !}
swapEq t~ rfl~ = {!   !}
swapEq t~ (sym~ u~) = {!   !}
swapEq t~ (u~₁ ∙~ u~₂) = {!   !}
swapEq t~ (u~₁ · u~₂) = {!   !}
\end{code}
%endif

% TODO Find a place for these definitions

