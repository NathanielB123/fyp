{-# OPTIONS --prop --rewriting #-}
open import Utils
open import Common.Sort

-- Strong normalisation w.r.t. non-deterministic |if| reduction implies
-- strong normalisation w.r.t. β + boolean rewrites
module Untyped.BoolRw where

infix 4 _>β_ _>β≈_ _>rw_ _>rw≈_ _>rw*_ _>nd_ _[_]≈_ _>𝔹_ _>𝔹?_ _>𝔹≈_ _>𝔹*_

variable
  Γ Δ Θ : ℕ

data Tm[_] : Sort → ℕ → Set

Var = Tm[ V ]
Tm  = Tm[ T ]

data Tm[_] where
  vz  : Var (su Γ)
  vs  : Var Γ → Var (su Γ)
  `_  : Var Γ → Tm Γ 
  _·_ : Tm Γ → Tm Γ → Tm Γ
  ƛ_  : Tm (su Γ) → Tm Γ
  TT  : Tm Γ
  FF  : Tm Γ
  if  : Tm Γ → Tm Γ → Tm Γ → Tm Γ

data Tms[_] (q : Sort) (Δ : ℕ) : ℕ → Set where
  ε   : Tms[ q ] Δ ze
  _▷_ : Tms[ q ] Δ Γ → Tm[ q ] Δ → Tms[ q ] Δ (su Γ)

Tms = Tms[ T ]

variable
  i j k : Var Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ
  δ σ   : Tms[ q ] Δ Γ

tm⊑ : q ⊑ r → Tm[ q ] Γ → Tm[ r ] Γ
tm⊑ {q = T} {r = T} _ t = t
tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = V} {r = V} _ i = i

wk : Tm[ q ] Γ → Tm[ q ] (su Γ)
_⁺ : Tms[ q ] Δ Γ → Tms[ q ] (su Δ) Γ
_^ : Tms[ q ] Δ Γ → Tms[ q ] (su Δ) (su Γ)
id : Tms[ q ] Γ Γ 
_[_] : Tm[ q ] Γ → Tms[ r ] Δ Γ → Tm[ q ⊔ r ] Δ

ε       ⁺ = ε
(δ ▷ t) ⁺ = (δ ⁺) ▷ wk t

δ ^ = (δ ⁺) ▷ tm⊑ V⊑ vz

(` i)    [ δ ]     = tm⊑ ⊑T (i [ δ ])
TT       [ δ ]     = TT
FF       [ δ ]     = FF
(t · u)  [ δ ]     = (t [ δ ]) · (u [ δ ])
if t u v [ δ ]     = if (t [ δ ]) (u [ δ ]) (v [ δ ])
(ƛ t)    [ δ ]     = ƛ (t [ δ ^ ])
vz       [ δ ▷ u ] = u
(vs i)   [ δ ▷ u ] = i [ δ ]

wk {q = V} i = vs i
wk {q = T} t = t [ id {q = V} ⁺ ]

id {Γ = ze}   = ε
id {Γ = su Γ} = id {Γ = Γ} ^

<_> : Tm Γ → Tms[ T ] Γ (su Γ)
< t > = id ▷ t

data CongClosure (_>_ : ∀ {Γ} → Tm Γ → Tm Γ → Set) {Γ} : Tm Γ → Tm Γ → Set
_[_]≈_ : Tm Γ → (∀ {Γ} → Tm Γ → Tm Γ → Set) → Tm Γ → Set 
t [ r ]≈ u = CongClosure r t u


data CongClosure _>_ where
  ⟪_⟫ : t₁ > t₂ → t₁ [ _>_ ]≈ t₂
  l·  : t₁ [ _>_ ]≈ t₂ → t₁ · u [ _>_ ]≈ t₂ · u
  ·r  : u₁ [ _>_ ]≈ u₂ → t · u₁ [ _>_ ]≈ t · u₂
  ƛ_  : t₁ [ _>_ ]≈ t₂ → ƛ t₁ [ _>_ ]≈ ƛ t₂
  if₁ : t₁ [ _>_ ]≈ t₂ → if t₁ u v [ _>_ ]≈ if t₂ u v
  if₂ : u₁ [ _>_ ]≈ u₂ → if t u₁ v [ _>_ ]≈ if t u₂ v
  if₃ : v₁ [ _>_ ]≈ v₂ → if t u v₁ [ _>_ ]≈ if t u v₂

variable
  _>₁_ _>₂_ : ∀ {Γ} → Tm Γ → Tm Γ → Set

-- Note that |gmap| is quite challenging to define on congruence closures of
-- term relations. It needs to come with laws about how the operation applied
-- to the points commutes with the various term formers in a coherent way.
map≈ : (∀ {Γ} {t u : Tm Γ} → t >₁ u → t >₂ u) → t [ _>₁_ ]≈ u → t [ _>₂_ ]≈ u
map≈ f ⟪ p ⟫   = ⟪ f p ⟫
map≈ f (l· p)  = l· (map≈ f p)
map≈ f (·r p)  = ·r (map≈ f p)
map≈ f (ƛ p)   = ƛ (map≈ f p)
map≈ f (if₁ p) = if₁ (map≈ f p)
map≈ f (if₂ p) = if₂ (map≈ f p)
map≈ f (if₃ p) = if₃ (map≈ f p)

data _>β_ : Tm Γ → Tm Γ → Set where
  β    : (ƛ t) · u >β t [ < u > ]
  ifTT : if TT u v >β u
  ifFF : if FF u v >β v

_>β≈_ : Tm Γ → Tm Γ → Set
_>β≈_ = _[ _>β_ ]≈_

-- Like β reduction, but non-deterministically collapses if statements
-- (i.e. doesn't block on true/false)
data _>nd_ : Tm Γ → Tm Γ → Set where
  β    : (ƛ t) · u >nd t [ < u > ]
  ifTT : if t u v >nd u
  ifFF : if t u v >nd v

_>nd≈_ : Tm Γ → Tm Γ → Set 
_>nd≈_ = _[ _>nd_ ]≈_

emb𝔹 : Bool → Tm Γ
emb𝔹 true  = TT
emb𝔹 false = FF

variable
  b : Bool
  b₁ b₂ : Bool

𝔹? : Tm Γ → Bool
𝔹? TT = true
𝔹? FF = true
𝔹? _  = false

data _>rw_ : Tm Γ → Tm Γ → Set where
  rwTT : ¬is 𝔹? t → t >rw TT
  rwFF : ¬is 𝔹? t → t >rw FF

_>rw≈_ : Tm Γ → Tm Γ → Set
_>rw≈_ = _[ _>rw_ ]≈_

_>βrw_ : Tm Γ → Tm Γ → Set
_>βrw_ = _[ _>β≈_ ∣ _>rw≈_ ]_

SNβ : Tm Γ → Set
SNβ = SN _>β_

SNnd : Tm Γ → Set
SNnd = SN _>nd≈_

SNβrw : Tm Γ → Set
SNβrw = SN _>βrw_

_>rw*_ : Tm Γ → Tm Γ → Set
_>rw*_ = flip _[ flip _>rw≈_ ]*_

β⊆nd : t >β u → t >nd u
β⊆nd β    = β
β⊆nd ifTT = ifTT
β⊆nd ifFF = ifFF

data _>𝔹_ : Tm Γ → Tm Γ → Set where
  rwTT : t >𝔹 TT
  rwFF : t >𝔹 FF


_>𝔹≈_ : Tm Γ → Tm Γ → Set
_>𝔹≈_ = _[ _>𝔹_ ]≈_

_>𝔹?_ : Tm Γ → Tm Γ → Set
_>𝔹?_ = _[ _>𝔹≈_ ]?_

_>𝔹*_ : Tm Γ → Tm Γ → Set
_>𝔹*_ = flip _[ flip _>𝔹≈_ ]*_

_[]𝔹 : t >𝔹 u → t [ δ ] >𝔹 u [ σ ]
rwTT []𝔹 = rwTT
rwFF []𝔹 = rwFF

data _>𝔹*s_ : Tms Δ Γ → Tms Δ Γ → Set where
  refl : δ >𝔹*s δ
  _,_  : δ >𝔹*s σ → t >𝔹* u → (δ ▷ t) >𝔹*s (σ ▷ u)

_·*_ : t₁ >𝔹* t₂ → u₁ >𝔹* u₂ → t₁ · u₁ >𝔹* t₂ · u₂
p ·* q = map* _ l· p ∘* map* _ ·r q

ƛ* : t₁ >𝔹* t₂ → ƛ t₁ >𝔹* ƛ t₂
ƛ* = map* ƛ_ ƛ_

if* : t₁ >𝔹* t₂ → u₁ >𝔹* u₂ → v₁ >𝔹* v₂ → if t₁ u₁ v₁ >𝔹* if t₂ u₂ v₂
if* p q r = map* _ if₁ p ∘* map* _ if₂ q ∘* map* _ if₃ r

_^𝔹 : δ >𝔹*s σ → (δ ^) >𝔹*s (σ ^)
_⁺𝔹 : δ >𝔹*s σ → (δ ⁺) >𝔹*s (σ ⁺)

p ^𝔹 = (p ⁺𝔹) , ε

_[_]𝔹* : ∀ (t : Tm Γ) → δ >𝔹*s σ → t [ δ ] >𝔹* t [ σ ]
(` vz)     [ p , q ]𝔹* = q
(` vs i)   [ p , q ]𝔹* = (` i) [ p ]𝔹*
(t · u)    [ p ]𝔹*     = (t [ p ]𝔹*) ·* (u [ p ]𝔹*)
(ƛ t)      [ p ]𝔹*     = ƛ* (t [ p ^𝔹 ]𝔹*)
TT         [ p ]𝔹*     = ε
FF         [ p ]𝔹*     = ε
(if t u v) [ p ]𝔹*     = if* (t [ p ]𝔹*) (u [ p ]𝔹*) (v [ p ]𝔹*)
_          [ refl ]𝔹*  = ε

_[]𝔹≈ : t >𝔹≈ u → t [ δ ] >𝔹≈ u [ δ ]
⟪ p ⟫ []𝔹≈ = ⟪ p []𝔹 ⟫
l· p  []𝔹≈ = l· (p []𝔹≈)
·r p  []𝔹≈ = ·r (p []𝔹≈)
(ƛ p) []𝔹≈ = ƛ (p []𝔹≈)
if₁ p []𝔹≈ = if₁ (p []𝔹≈)
if₂ p []𝔹≈ = if₂ (p []𝔹≈)
if₃ p []𝔹≈ = if₃ (p []𝔹≈)

pattern ⟪_⟫* p = p ∷ ε

huh : t >𝔹* u → t [ δ ] >𝔹* u [ δ ]
huh ε        = ε
huh (p ∶> q) = (p []𝔹≈) ∶> huh q

refl    ⁺𝔹 = refl
(p , q) ⁺𝔹 = (p ⁺𝔹) , huh q

𝔹/nd-comm : t >𝔹≈ u → u >nd v → ∃[ w ] t >nd w × w >𝔹* v
𝔹/nd-comm (l· (ƛ p))       β    = _ Σ, β Σ, ⟪ p []𝔹≈ ⟫*
𝔹/nd-comm (·r {t = ƛ t} p) β    = _ Σ, β Σ, t [ refl {δ = id} , (p ∷ ε) ]𝔹*
𝔹/nd-comm (if₁ p)          ifTT = _ Σ, ifTT Σ, ε
𝔹/nd-comm (if₂ p)          ifTT = _ Σ, ifTT Σ, (p ∷ ε)
𝔹/nd-comm (if₃ p)          ifTT = _ Σ, ifTT Σ, ε
𝔹/nd-comm (if₁ p)          ifFF = _ Σ, ifFF Σ, ε
𝔹/nd-comm (if₂ p)          ifFF = _ Σ, ifFF Σ, ε 
𝔹/nd-comm (if₃ p)          ifFF = _ Σ, ifFF Σ, (p ∷ ε)

-- TODO - can we remove the duplication here?
𝔹/nd-comm≈ : t >𝔹≈ u → u >nd≈ v → ∃[ w ] t >nd≈ w × w >𝔹* v
𝔹/nd-comm≈ p ⟪ q ⟫ using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm p q = _ Σ, ⟪ q′ ⟫ Σ, p′
𝔹/nd-comm≈ (l· p) (l· q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm≈ p q 
  = _ Σ, l· q′ Σ, map* _ l· p′
𝔹/nd-comm≈ (·r p) (·r q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm≈ p q 
  = _ Σ, ·r q′ Σ, map* _ ·r p′
𝔹/nd-comm≈ (ƛ p) (ƛ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm≈ p q 
  = _ Σ, ƛ_ q′ Σ, map* _ ƛ_ p′
𝔹/nd-comm≈ (if₁ p) (if₁ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm≈ p q 
  = _ Σ, if₁ q′ Σ, map* _ if₁ p′
𝔹/nd-comm≈ (if₂ p) (if₂ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm≈ p q 
  = _ Σ, if₂ q′ Σ, map* _ if₂ p′
𝔹/nd-comm≈ (if₃ p) (if₃ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm≈ p q 
  = _ Σ, if₃ q′ Σ, map* _ if₃ p′
𝔹/nd-comm≈ (l· p)  (·r q)  = _ Σ, ·r q  Σ, (l· p  ∷ ε)
𝔹/nd-comm≈ (·r p)  (l· q)  = _ Σ, l· q  Σ, (·r p  ∷ ε)
𝔹/nd-comm≈ (if₁ p) (if₂ q) = _ Σ, if₂ q Σ, (if₁ p ∷ ε)
𝔹/nd-comm≈ (if₁ p) (if₃ q) = _ Σ, if₃ q Σ, (if₁ p ∷ ε)
𝔹/nd-comm≈ (if₂ p) (if₁ q) = _ Σ, if₁ q Σ, (if₂ p ∷ ε)
𝔹/nd-comm≈ (if₂ p) (if₃ q) = _ Σ, if₃ q Σ, (if₂ p ∷ ε)
𝔹/nd-comm≈ (if₃ p) (if₁ q) = _ Σ, if₁ q Σ, (if₃ p ∷ ε)
𝔹/nd-comm≈ (if₃ p) (if₂ q) = _ Σ, if₂ q Σ, (if₃ p ∷ ε)

𝔹*/nd-comm≈ : t >𝔹* u → u >nd≈ v → ∃[ w ] t >nd≈ w × w >𝔹* v
𝔹*/nd-comm≈ ε        r = _ Σ, r Σ, ε
𝔹*/nd-comm≈ (p <∶ q) r using _ Σ, r′  Σ, q′ ← 𝔹/nd-comm≈  q r  
                           | _ Σ, r′′ Σ, p′ ← 𝔹*/nd-comm≈ p r′
  = _ Σ, r′′ Σ, (q′ ∘* p′)

SNrw : Tm Γ → Set
SNrw = SN _>rw≈_

snrwTT : SNrw {Γ} TT
snrwTT = acc λ where ⟪ rwTT () ⟫
                     ⟪ rwFF () ⟫

snrwFF : SNrw {Γ} FF
snrwFF = acc λ where ⟪ rwTT () ⟫
                     ⟪ rwFF () ⟫

snrw> : t >rw u → SNrw u
snrw> (rwTT _) = snrwTT
snrw> (rwFF _) = snrwFF

snrw` : SNrw (` i)
snrw` = acc λ where ⟪ p ⟫ → snrw> p
                    
snrw· : SNrw t → SNrw u → SNrw (t · u)
snrw· (acc a₁) (acc a₂) = acc λ where ⟪ p ⟫  → snrw> p
                                      (l· p) → snrw· (a₁ p) (acc a₂)
                                      (·r p) → snrw· (acc a₁) (a₂ p)

snrwƛ : SNrw t → SNrw (ƛ t)
snrwƛ (acc a) = acc λ where ⟪ p ⟫ → snrw> p
                            (ƛ p) → snrwƛ (a p)

snrwif : SNrw t → SNrw u → SNrw v → SNrw (if t u v)
snrwif (acc a₁) (acc a₂) (acc a₃) 
  = acc λ where ⟪ p ⟫   → snrw> p
                (if₁ p) → snrwif (a₁ p) (acc a₂) (acc a₃)
                (if₂ p) → snrwif (acc a₁) (a₂ p) (acc a₃)
                (if₃ p) → snrwif (acc a₁) (acc a₂) (a₃ p)

snrw : ∀ (t : Tm Γ) → SNrw t
snrw (` i)      = snrw`
snrw (t · u)    = snrw· (snrw t) (snrw u)
snrw (ƛ t)      = snrwƛ (snrw t)
snrw TT         = snrwTT
snrw FF         = snrwFF
snrw (if t u v) = snrwif (snrw t) (snrw u) (snrw v)

rw⊆𝔹 : t >rw u → t >𝔹 u
rw⊆𝔹 (rwTT _) = rwTT
rw⊆𝔹 (rwFF _) = rwFF

_>ndrw_ : Tm Γ → Tm Γ → Set
_>ndrw_ = _[ _>nd≈_ ∣ _>rw≈_ ]_

SNndrw : Tm Γ → Set
SNndrw = SN _>ndrw_

snndrw  : t >𝔹* u → SNnd t → SNrw u → SNndrw u
snndrw> : t >𝔹* u → SNnd t → SNrw u → u >ndrw v → SNndrw v

snndrw p 𝒶nd 𝒶rw = acc (snndrw> p 𝒶nd 𝒶rw)

snndrw> p (acc 𝒶nd) (acc 𝒶rw) (inl q) using v Σ, q′ Σ, p′ ← 𝔹*/nd-comm≈ p q
  = snndrw p′ (𝒶nd q′) (snrw _)
snndrw> p (acc 𝒶nd) (acc 𝒶rw) (inr q) 
  = snndrw (p <∶ map≈ rw⊆𝔹 q) (acc 𝒶nd) (𝒶rw q)

snnd→snndrw : SNnd t → SNβrw t
snnd→snndrw a = accessible (map⊎ (map≈ β⊆nd) (λ p → p)) (snndrw ε a (snrw _))

-- Unfortunately, while simply-typed terms are SN w.r.t. |_>nd_| (the proof is
-- just a slight variation of the standard computability predicates argument for
-- |_>β_|), dependently typed terms are not. Here is a counter-example.
module MLTTNotSNnd where
  open import Function using (case_of_; case_return_of_)

  bool-elim : (P : Bool → Set ℓ) (b : Bool) → P true → P false → P b
  bool-elim P true  x y = x
  bool-elim P false x y = y

  base-or-func : Bool → Set
  base-or-func b = bool-elim _ b ℕ (ℕ → ℕ) 

  bad : ∀ (b : Bool) → base-or-func b → ℕ
  bad b x = ((bool-elim (λ b′ → base-or-func b′ → ℕ → ℕ) b
                        (λ _ → su) (λ x′ → x′)) x) 
            ((bool-elim (λ b′ → base-or-func b′ → ℕ) b
                        (λ x′ → x′) (λ _ → ze)) x)
   