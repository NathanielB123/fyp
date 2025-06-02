{-# OPTIONS --prop --rewriting #-}
open import Utils
open import Common.Sort

-- Strong normalisation w.r.t. non-deterministic |if| reduction implies
-- strong normalisation w.r.t. β + boolean rewrites
module Untyped.BoolRw where

infix 4 _>β_ _>!_ _>𝔹*_ _>nd_ _[_]>_ _>!?_ _>𝔹_

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

-- Monotonic closure
data MonoClosure (_>_ : ∀ {Γ} → Tm Γ → Tm Γ → Set) {Γ} : Tm Γ → Tm Γ → Set
_[_]>_ : Tm Γ → (∀ {Γ} → Tm Γ → Tm Γ → Set) → Tm Γ → Set 
t [ r ]> u = MonoClosure r t u

data MonoClosure _>_ where
  ⟪_⟫ : t₁ > t₂ → t₁ [ _>_ ]> t₂
  l·  : t₁ [ _>_ ]> t₂ → t₁ · u [ _>_ ]> t₂ · u
  ·r  : u₁ [ _>_ ]> u₂ → t · u₁ [ _>_ ]> t · u₂
  ƛ_  : t₁ [ _>_ ]> t₂ → ƛ t₁ [ _>_ ]> ƛ t₂
  if₁ : t₁ [ _>_ ]> t₂ → if t₁ u v [ _>_ ]> if t₂ u v
  if₂ : u₁ [ _>_ ]> u₂ → if t u₁ v [ _>_ ]> if t u₂ v
  if₃ : v₁ [ _>_ ]> v₂ → if t u v₁ [ _>_ ]> if t u v₂

variable
  _>₁_ _>₂_ : ∀ {Γ} → Tm Γ → Tm Γ → Set

-- Note that |gmap| is quite challenging to define on congruence closures of
-- term relations. It needs to come with laws about how the operation applied
-- to the points commutes with the various term formers in a coherent way.
map> : (∀ {Γ} {t u : Tm Γ} → t >₁ u → t >₂ u) → t [ _>₁_ ]> u → t [ _>₂_ ]> u
map> f ⟪ p ⟫   = ⟪ f p ⟫
map> f (l· p)  = l· (map> f p)
map> f (·r p)  = ·r (map> f p)
map> f (ƛ p)   = ƛ (map> f p)
map> f (if₁ p) = if₁ (map> f p)
map> f (if₂ p) = if₂ (map> f p)
map> f (if₃ p) = if₃ (map> f p)

data β-step : Tm Γ → Tm Γ → Set where
  ⇒β  : β-step ((ƛ t) · u) (t [ < u > ])
  𝔹β₁ : β-step (if TT u v) u
  𝔹β₂ : β-step (if FF u v) v

_>β_ : Tm Γ → Tm Γ → Set
_>β_ = _[ β-step ]>_

-- Like β reduction, but non-deterministically collapses if statements
-- (i.e. doesn't block on true/false)
data nd-step : Tm Γ → Tm Γ → Set where
  ⇒β  : nd-step ((ƛ t) · u) (t [ < u > ])
  ndl : nd-step (if t u v) u
  ndr : nd-step (if t u v) v

_>nd_ : Tm Γ → Tm Γ → Set 
_>nd_ = _[ nd-step ]>_

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

-- Spontaneous reduction
data !-step : Tm Γ → Tm Γ → Set where
  rwTT : ¬is 𝔹? t → !-step t TT
  rwFF : ¬is 𝔹? t → !-step t FF

_>!_ : Tm Γ → Tm Γ → Set
_>!_ = _[ !-step ]>_

_>β!_ : Tm Γ → Tm Γ → Set
_>β!_ = _[ _>β_ ∣ _>!_ ]_

SNnd : Tm Γ → Set
SNnd = SN _>nd_

SNβ! : Tm Γ → Set
SNβ! = SN _>β!_

_>!*_ : Tm Γ → Tm Γ → Set
_>!*_ = flip _[ flip _>!_ ]*_

β⊆nd : β-step t u → nd-step t u
β⊆nd ⇒β  = ⇒β
β⊆nd 𝔹β₁ = ndl
β⊆nd 𝔹β₂ = ndr

_>𝔹_ : Tm Γ → Tm Γ → Set
_>𝔹_ = _[ (λ _ u → is 𝔹? u) ]>_

_>!?_ : Tm Γ → Tm Γ → Set
_>!?_ = _[ _>𝔹_ ]?_

_>𝔹*_ : Tm Γ → Tm Γ → Set
_>𝔹*_ = flip _[ flip _>𝔹_ ]*_

data _>Tms𝔹*_ : Tms Δ Γ → Tms Δ Γ → Set where
  refl : δ >Tms𝔹* δ
  _,_  : δ >Tms𝔹* σ → t >𝔹* u → (δ ▷ t) >Tms𝔹* (σ ▷ u)

_·*_ : t₁ >𝔹* t₂ → u₁ >𝔹* u₂ → t₁ · u₁ >𝔹* t₂ · u₂
p ·* q = map* _ l· p ∘* map* _ ·r q

ƛ* : t₁ >𝔹* t₂ → ƛ t₁ >𝔹* ƛ t₂
ƛ* = map* ƛ_ ƛ_

if* : t₁ >𝔹* t₂ → u₁ >𝔹* u₂ → v₁ >𝔹* v₂ → if t₁ u₁ v₁ >𝔹* if t₂ u₂ v₂
if* p q r = map* _ if₁ p ∘* map* _ if₂ q ∘* map* _ if₃ r

_^𝔹 : δ >Tms𝔹* σ → (δ ^) >Tms𝔹* (σ ^)
_⁺𝔹 : δ >Tms𝔹* σ → (δ ⁺) >Tms𝔹* (σ ⁺)

p ^𝔹 = (p ⁺𝔹) , ε

_[_]𝔹* : ∀ (t : Tm Γ) → δ >Tms𝔹* σ → t [ δ ] >𝔹* t [ σ ]
(` vz)     [ p , q ]𝔹* = q
(` vs i)   [ p , q ]𝔹* = (` i) [ p ]𝔹*
(t · u)    [ p ]𝔹*     = (t [ p ]𝔹*) ·* (u [ p ]𝔹*)
(ƛ t)      [ p ]𝔹*     = ƛ* (t [ p ^𝔹 ]𝔹*)
TT         [ p ]𝔹*     = ε
FF         [ p ]𝔹*     = ε
(if t u v) [ p ]𝔹*     = if* (t [ p ]𝔹*) (u [ p ]𝔹*) (v [ p ]𝔹*)
_          [ refl ]𝔹*  = ε

_[]𝔹? : is 𝔹? t → is 𝔹? (t [ δ ])
_[]𝔹? {t = TT} tt = tt
_[]𝔹? {t = FF} tt = tt

_[]𝔹> : t >𝔹 u → t [ δ ] >𝔹 u [ δ ]
⟪ p ⟫ []𝔹> = ⟪ p []𝔹? ⟫
l· p  []𝔹> = l· (p []𝔹>)
·r p  []𝔹> = ·r (p []𝔹>)
(ƛ p) []𝔹> = ƛ (p []𝔹>)
if₁ p []𝔹> = if₁ (p []𝔹>)
if₂ p []𝔹> = if₂ (p []𝔹>)
if₃ p []𝔹> = if₃ (p []𝔹>)

pattern ⟪_⟫* p = p ∷ ε

_[]𝔹>* : t >𝔹* u → t [ δ ] >𝔹* u [ δ ]
ε        []𝔹>* = ε
(p ∶> q) []𝔹>* = (p []𝔹>) ∶> (q []𝔹>*)

refl    ⁺𝔹 = refl
(p , q) ⁺𝔹 = (p ⁺𝔹) , (q []𝔹>*)

_[_]𝔹>* : t >𝔹* u → δ >Tms𝔹* σ → t [ δ ] >𝔹* u [ σ ]
_[_]𝔹>* {u = u} p q = (u [ q ]𝔹*) ∘* (p []𝔹>*)

𝔹/nd-comm : t >𝔹 u → nd-step u v → ∃[ w ] nd-step t w × w >𝔹* v
𝔹/nd-comm (l· (ƛ p))       ⇒β  = _ Σ, ⇒β Σ, ⟪ p []𝔹> ⟫*
𝔹/nd-comm (·r {t = ƛ t} p) ⇒β  = _ Σ, ⇒β Σ, t [ refl {δ = id} , (p ∷ ε) ]𝔹*
𝔹/nd-comm (if₁ p)          ndl = _ Σ, ndl Σ, ε
𝔹/nd-comm (if₂ p)          ndl = _ Σ, ndl Σ, (p ∷ ε)
𝔹/nd-comm (if₃ p)          ndl = _ Σ, ndl Σ, ε
𝔹/nd-comm (if₁ p)          ndr = _ Σ, ndr Σ, ε
𝔹/nd-comm (if₂ p)          ndr = _ Σ, ndr Σ, ε 
𝔹/nd-comm (if₃ p)          ndr = _ Σ, ndr Σ, (p ∷ ε)

-- TODO - can we remove the duplication here?
𝔹/nd-comm> : t >𝔹 u → u >nd v → ∃[ w ] t >nd w × w >𝔹* v
𝔹/nd-comm> p ⟪ q ⟫ using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm p q = _ Σ, ⟪ q′ ⟫ Σ, p′
𝔹/nd-comm> (l· p) (l· q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm> p q 
  = _ Σ, l· q′ Σ, map* _ l· p′
𝔹/nd-comm> (·r p) (·r q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm> p q 
  = _ Σ, ·r q′ Σ, map* _ ·r p′
𝔹/nd-comm> (ƛ p) (ƛ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm> p q 
  = _ Σ, ƛ_ q′ Σ, map* _ ƛ_ p′
𝔹/nd-comm> (if₁ p) (if₁ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm> p q 
  = _ Σ, if₁ q′ Σ, map* _ if₁ p′
𝔹/nd-comm> (if₂ p) (if₂ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm> p q 
  = _ Σ, if₂ q′ Σ, map* _ if₂ p′
𝔹/nd-comm> (if₃ p) (if₃ q) using _ Σ, q′ Σ, p′ ← 𝔹/nd-comm> p q 
  = _ Σ, if₃ q′ Σ, map* _ if₃ p′
𝔹/nd-comm> (l· p)  (·r q)  = _ Σ, ·r q  Σ, (l· p  ∷ ε)
𝔹/nd-comm> (·r p)  (l· q)  = _ Σ, l· q  Σ, (·r p  ∷ ε)
𝔹/nd-comm> (if₁ p) (if₂ q) = _ Σ, if₂ q Σ, (if₁ p ∷ ε)
𝔹/nd-comm> (if₁ p) (if₃ q) = _ Σ, if₃ q Σ, (if₁ p ∷ ε)
𝔹/nd-comm> (if₂ p) (if₁ q) = _ Σ, if₁ q Σ, (if₂ p ∷ ε)
𝔹/nd-comm> (if₂ p) (if₃ q) = _ Σ, if₃ q Σ, (if₂ p ∷ ε)
𝔹/nd-comm> (if₃ p) (if₁ q) = _ Σ, if₁ q Σ, (if₃ p ∷ ε)
𝔹/nd-comm> (if₃ p) (if₂ q) = _ Σ, if₂ q Σ, (if₃ p ∷ ε)

𝔹*/nd-comm> : t >𝔹* u → u >nd v → ∃[ w ] t >nd w × w >𝔹* v
𝔹*/nd-comm> ε        r = _ Σ, r Σ, ε
𝔹*/nd-comm> (p <∶ q) r using _ Σ, r′  Σ, q′ ← 𝔹/nd-comm>  q r  
                           | _ Σ, r′′ Σ, p′ ← 𝔹*/nd-comm> p r′
  = _ Σ, r′′ Σ, (q′ ∘* p′)

SN! : Tm Γ → Set
SN! = SN _>!_

sn!TT : SN! {Γ} TT
sn!TT = acc λ where ⟪ rwTT () ⟫
                    ⟪ rwFF () ⟫

sn!FF : SN! {Γ} FF
sn!FF = acc λ where ⟪ rwTT () ⟫
                    ⟪ rwFF () ⟫

sn!> : !-step t u → SN! u
sn!> (rwTT _) = sn!TT
sn!> (rwFF _) = sn!FF

sn!` : SN! (` i)
sn!` = acc λ where ⟪ p ⟫ → sn!> p
                    
sn!· : SN! t → SN! u → SN! (t · u)
sn!· (acc a₁) (acc a₂) = acc λ where ⟪ p ⟫  → sn!> p
                                     (l· p) → sn!· (a₁ p) (acc a₂)
                                     (·r p) → sn!· (acc a₁) (a₂ p)

sn!ƛ : SN! t → SN! (ƛ t)
sn!ƛ (acc a) = acc λ where ⟪ p ⟫ → sn!> p
                           (ƛ p) → sn!ƛ (a p)

sn!if : SN! t → SN! u → SN! v → SN! (if t u v)
sn!if (acc a₁) (acc a₂) (acc a₃) 
  = acc λ where ⟪ p ⟫   → sn!> p
                (if₁ p) → sn!if (a₁ p) (acc a₂) (acc a₃)
                (if₂ p) → sn!if (acc a₁) (a₂ p) (acc a₃)
                (if₃ p) → sn!if (acc a₁) (acc a₂) (a₃ p)

sn! : ∀ (t : Tm Γ) → SN! t
sn! (` i)      = sn!`
sn! (t · u)    = sn!· (sn! t) (sn! u)
sn! (ƛ t)      = sn!ƛ (sn! t)
sn! TT         = sn!TT
sn! FF         = sn!FF
sn! (if t u v) = sn!if (sn! t) (sn! u) (sn! v)

!-step𝔹 : !-step t u → is 𝔹? u
!-step𝔹 (rwTT _) = _
!-step𝔹 (rwFF _) = _

_>nd!_ : Tm Γ → Tm Γ → Set
_>nd!_ = _[ _>nd_ ∣ _>!_ ]_

SNnd! : Tm Γ → Set
SNnd! = SN _>nd!_

snnd!  : t >𝔹* u → SNnd t → SN! u → SNnd! u
snnd!> : t >𝔹* u → SNnd t → SN! u → u >nd! v → SNnd! v

snnd! p ndᴬ !ᴬ = acc (snnd!> p ndᴬ !ᴬ)

snnd!> p (acc ndᴬ) !ᴬ (inl q) using v Σ, q′ Σ, p′ ← 𝔹*/nd-comm> p q
  = snnd! p′ (ndᴬ q′) (sn! _)
snnd!> p ndᴬ (acc 𝒶rw) (inr q) 
  = snnd! (p <∶ map> !-step𝔹 q) ndᴬ (𝒶rw q)

snnd→snβ! : SNnd t → SNβ! t
snnd→snβ! a = accessible (map⊎ (map> β⊆nd) (λ p → p)) (snnd! ε a (sn! _))

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
   