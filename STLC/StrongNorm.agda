{-# OPTIONS --injective-type-constructors --rewriting --prop --show-irrelevant #-}

import Agda.Builtin.Equality.Rewrite

open import Utils
open import STLC.Syntax

-- Strong normalisation of STLC + Boolean rewrites
-- Based on https://github.com/AndrasKovacs/misc-stuff/blob/master/agda/STLCStrongNorm/StrongNorm.agda
module STLC.StrongNorm where

⊑⊔s : q ⊑ r → (q ⊔ s) ⊑ (r ⊔ s)
⊑⊔s V⊑T = ⊑T
⊑⊔s rfl = rfl

s⊔⊑ : q ⊑ r → (s ⊔ q) ⊑ (s ⊔ r)
s⊔⊑ {s = V} q⊑r = q⊑r
s⊔⊑ {s = T} _   = rfl

⊔V : q ⊔ V ≡ q
⊔V {q = V} = refl
⊔V {q = T} = refl

⊔T : q ⊔ T ≡ T
⊔T {q = V} = refl
⊔T {q = T} = refl

⊔⊔ : (q ⊔ r) ⊔ s ≡ q ⊔ (r ⊔ s)
⊔⊔ {q = V} = refl
⊔⊔ {q = T} = refl

{-# REWRITE ⊔V ⊔T ⊔⊔ #-}

variable
  t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ ξ : Tms[ q ] Δ Γ
  q⊑r : q ⊑ r
  Ξ : Ctx

module Justβ where
  -- β-reduction
  data _→β_ : Tm Γ A → Tm Γ A → Set where
    β  : ((ƛ t) · u) →β (t [ < u > ])

-- Closure of a relation over terms
data TmClo (R : ∀ {Γ A} → Tm Γ A → Tm Γ A → Set) : Tm Γ A → Tm Γ A → Set

data TmClo R where
  ap : R t₁ t₂ → TmClo R t₁ t₂
  
  l· : TmClo R t₁ t₂ → TmClo R (t₁ · u) (t₂ · u) 
  ·r : TmClo R u₁ u₂ → TmClo R (t · u₁) (t · u₂)
  ƛ_ : TmClo R t₁ t₂ → TmClo R (ƛ t₁) (ƛ t₂)

IsBool : Tm Γ A → Set
IsBool true  = ⊤
IsBool false = ⊤
IsBool _     = ⊥

¬IsBool : Tm Γ A → Set
¬IsBool true  = ⊥
¬IsBool false = ⊥
¬IsBool _     = ⊤

bool? : (t : Tm Γ A) → IsBool t ⊎ ¬IsBool t
bool? true          = inl tt
bool? false         = inl tt
bool? (` i)         = inr tt
bool? (t · u)       = inr tt
bool? (ƛ t)         = inr tt
bool? (𝔹-rec c t u) = inr tt

-- Substitution laws
-- Postulated because I can't be bothered rn
postulate 
  [][]  : x [ δ ] [ σ ] ≡ x [ δ ⨾ σ ]
  ⁺⨾    : (δ ⁺ A) ⨾ (σ , x) ≡ δ ⨾ σ
  ⨾⁺    : δ ⨾ (σ ⁺ A) ≡ (δ ⨾ σ) ⁺ A
  id⨾   : {δ : Tms[ q ] Δ Γ} → id ⨾ δ ≡ δ
  ⨾id   : {δ : Tms[ q ] Δ Γ} → δ ⨾ id ≡ δ
  vz[]  : ∀ {δ : Tms[ r ] Δ Γ} → vz[ q ] [ δ , x ] ≡ tm⊑ ⊑⊔₂ x
  suc[] : suc[ q ] x [ δ , y ] ≡  x [ δ ]
  [id]  : x [ id ] ≡ x
  ⨾⨾    : (δ ⨾ σ) ⨾ ξ ≡ δ ⨾ (σ ⨾ ξ)
  
  ⊑⨾   : {q⊑r : q ⊑ r} {σ : Tms[ s ] Θ Δ} 
       → tms⊑ q⊑r δ ⨾ σ ≡ tms⊑ (⊑⊔s {s = s} q⊑r) (δ ⨾ σ)
  ⨾⊑   : {q⊑r : r ⊑ s} {δ : Tms[ q ] Δ Γ}
       → δ ⨾ tms⊑ q⊑r σ ≡ tms⊑ (s⊔⊑ {s = q} q⊑r) (δ ⨾ σ)
  
  ⊑⁺   : tms⊑ q⊑r δ ⁺ A ≡ tms⊑ q⊑r (δ ⁺ A) 

  [⊑]   : {q⊑r : q ⊑ r} {x : Tm[ s ] Γ A} 
        → x [ tms⊑ q⊑r δ ] ≡ tm⊑ (s⊔⊑ {s = s} q⊑r) (x [ δ ])
  [⊑,`] : x [ (tms⊑ ⊑T δ , (` vz)) ] ≡ tm⊑ ⊑T (x [ δ , vz ])

  tms⊑-id : tms⊑ q⊑r δ ≡ δ

-- Epic rewrite fail
T[][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
T[][] {t = t} = [][] {x = t}

V⨾⨾ : ∀ {σ : Tms[ q ] Θ Δ} → (δ ⨾ σ) ⨾ ξ ≡ δ ⨾ (σ ⨾ ξ)
V⨾⨾ = ⨾⨾

{-# REWRITE [][] ⁺⨾ ⨾⁺ id⨾ ⨾id vz[] [id] ⨾⨾ ⊑⨾ ⨾⊑ ⊑⁺ [⊑] [⊑,`] tms⊑-id 
            T[][] V⨾⨾ #-}


data Sort→ : Set where
  β rw : Sort→ 

variable
  q→ r→ s→ : Sort→

data _[_]→_ : Tm Γ A → Sort→ → Tm Γ A → Set where
  -- TODO: Add the '𝔹-rec' β-laws
  β  : ((ƛ t) · u)   [ β ]→ (t [ < u > ])
  rw : ¬IsBool {A = 𝔹'} t → IsBool {A = 𝔹'} u → t [ rw ]→ u

  l· : t₁ [ q→ ]→ t₂ → (t₁ · u) [ q→ ]→ (t₂ · u) 
  ·r : u₁ [ q→ ]→ u₂ → (t · u₁) [ q→ ]→ (t · u₂)
  ƛ_ : t₁ [ q→ ]→ t₂ → (ƛ t₁)   [ q→ ]→ (ƛ t₂)

_→β_ : Tm Γ A → Tm Γ A → Set
_→β_ = _[ β ]→_

_→rw_ : Tm Γ A → Tm Γ A → Set
_→rw_ = _[ rw ]→_

data SN : ∀ Γ A → Tm Γ A → Set where
  acc : (∀ {q→ u} → t [ q→ ]→ u → SN Γ A u) → SN Γ A t

true-sn : SN Γ 𝔹' true
true-sn = acc (λ where (rw () _))

false-sn : SN Γ 𝔹' false
false-sn = acc (λ where (rw () _))

bool-sn : IsBool t → SN Γ A t
bool-sn {t = true}  tt = true-sn
bool-sn {t = false} tt = false-sn

Val : ∀ Γ A → Tm Γ A → Set
Val Γ 𝔹' t      = SN Γ 𝔹' t
Val Γ (A ⇒ B) t 
  = ∀ {Δ} (δ : Vars Δ Γ) {u} → Val Δ A u → Val Δ B ((t [ δ ]) · u)

data Env (Δ : Ctx) : ∀ Γ → Tms[ T ] Δ Γ → Set where
  ε   : Env Δ ε ε
  _,_ : Env Δ Γ δ → Val Δ A t → Env Δ (Γ , A) (δ , t)

_[_]b : IsBool t → (δ : Tms[ q ] Δ Γ) → IsBool (t [ δ ])
_[_]b {t = true}  tt _ = tt
_[_]b {t = false} tt _ = tt

[_]b⁻¹_ : (δ : Vars Δ Γ) → IsBool (t [ δ ]) → IsBool t
[_]b⁻¹_ {t = true}  _ tt = tt
[_]b⁻¹_ {t = false} _ tt = tt

¬bool→ : ¬ IsBool t → ¬IsBool t
¬bool→ {t = ` _}         _  = tt
¬bool→ {t = _ · _}       _  = tt
¬bool→ {t = ƛ _}         _  = tt
¬bool→ {t = 𝔹-rec _ _ _} _  = tt
¬bool→ {t = true}        ¬b = ¬b tt
¬bool→ {t = false}       ¬b = ¬b tt

¬bool← : ¬IsBool t → ¬ IsBool t
¬bool← {t = ` _} _ ()

_[_]¬b : ¬IsBool t → (δ : Vars Δ Γ) → ¬IsBool (t [ δ ])
¬b [ δ ]¬b = ¬bool→ (λ b → ¬bool← ¬b ([ δ ]b⁻¹ b))

[_]¬b⁻¹_ : (δ : Vars Δ Γ) → ¬IsBool (t [ δ ]) → ¬IsBool t
[ δ ]¬b⁻¹ ¬b = ¬bool→ (λ b → ¬bool← ¬b (b [ δ ]b))

_[_]→ : t [ q→ ]→ u → (δ : Vars Δ Γ) 
      → (t [ δ ]) [ q→ ]→ (u [ δ ])
β       [ δ ]→ = β
rw ¬b b [ δ ]→ = rw (¬b [ δ ]¬b) (b [ δ ]b) 
l· p    [ δ ]→ = l· (p [ δ ]→)
·r p    [ δ ]→ = ·r (p [ δ ]→)
(ƛ p)   [ δ ]→ = ƛ (p [ δ ^ _ ]→)

_[_]→β : t →β u → (δ : Tms[ q ] Δ Γ) 
        → (t [ δ ]) →β (u [ δ ])
β     [ δ ]→β = β
l· p  [ δ ]→β = l· (p [ δ ]→β)
·r p  [ δ ]→β = ·r (p [ δ ]→β)
(ƛ p) [ δ ]→β = ƛ (p [ δ ^ _ ]→β)

[_]→β⁻¹_ : ∀ (δ : Vars Δ Γ) → (t [ δ ]) →β u
          → ∃ λ u⁻¹ → (t →β u⁻¹) × (u⁻¹ [ δ ] ≡ u)

[_]→β⁻¹_ {t = ƛ t} δ (ƛ p) 
  = let u⁻¹   Σ, p   Σ, q = [_]→β⁻¹_ {t = t} (δ ^ _) p 
      in ƛ u⁻¹ Σ, ƛ p Σ, cong ƛ_ q

[_]→β⁻¹_ {t = t · u · v} δ (l· p) 
  = let tu⁻¹     Σ, p    Σ, q = [_]→β⁻¹_ {t = t · u} δ p
      in tu⁻¹ · v Σ, l· p Σ, cong (_· (v [ δ ])) q
[_]→β⁻¹_ {t = (ƛ t) · u} δ (l· (ƛ p)) 
  = let t⁻¹         Σ, p        Σ, q = [_]→β⁻¹_ {t = t} (δ ^ _) p
      in (ƛ t⁻¹) · u Σ, l· (ƛ p) Σ, cong (λ t → (ƛ t) · (u [ δ ])) q

[_]→β⁻¹_ {t = ` i · u} δ (·r p) 
  = let u⁻¹       Σ, p    Σ, q = [_]→β⁻¹_ {t = u} δ p 
      in ` i · u⁻¹ Σ, ·r p Σ, cong (` (i [ δ ]) ·_) q
[_]→β⁻¹_ {t = t · u · v} δ (·r p)
  = let v⁻¹         Σ, p    Σ, q = [_]→β⁻¹_ {t = v} δ p 
      in t · u · v⁻¹ Σ, ·r p Σ, cong ((t [ δ ]) · (u [ δ ]) ·_) q
[_]→β⁻¹_ {t = (ƛ t) · u} δ (·r p) 
  = let u⁻¹       Σ, p    Σ, q = [_]→β⁻¹_ {t = u} δ p 
      in (ƛ t) · u⁻¹ Σ, ·r p Σ, cong ((ƛ t [ δ ^ _ ]) ·_) q
[_]→β⁻¹_ {t = 𝔹-rec c t u · v} δ (·r p)
  = let v⁻¹         Σ, p    Σ, q = [_]→β⁻¹_ {t = v} δ p 
      in 𝔹-rec c t u · v⁻¹ Σ, ·r p 
      Σ, cong (𝔹-rec (c [ δ ]) (t [ δ ]) (u [ δ ]) ·_) q

[_]→β⁻¹_ {t = (ƛ t) · u} δ β = t [ < u > ] Σ, β Σ, refl

[_]→rw⁻¹_ : ∀ (δ : Vars Δ Γ) → (t [ δ ]) →rw u
          → ∃ λ u⁻¹ → (t →rw u⁻¹) × (u⁻¹ [ δ ] ≡ u)

[_]→rw⁻¹_ {t = t₁ · t₂} δ (l· p) 
  = let t₁⁻¹ Σ, p Σ, q = [ δ ]→rw⁻¹ p 
      in t₁⁻¹ · t₂ Σ, l· p Σ, cong (_· t₂ [ δ ]) q
[_]→rw⁻¹_ {t = t₁ · t₂} δ (·r p)
  = let t₂⁻¹ Σ, p Σ, q = [ δ ]→rw⁻¹ p 
      in t₁ · t₂⁻¹ Σ, ·r p Σ, cong (t₁ [ δ ] ·_) q
[_]→rw⁻¹_ {t = ƛ t}     δ (ƛ p)  
  = let t⁻¹ Σ, p Σ, q = [ δ ^ _ ]→rw⁻¹ p
      in ƛ t⁻¹ Σ, ƛ p Σ, cong ƛ_ q

[_]→rw⁻¹_ {u = true}  δ (rw ¬b tt) = true  Σ, rw ([ δ ]¬b⁻¹ ¬b) tt Σ, refl
[_]→rw⁻¹_ {u = false} δ (rw ¬b tt) = false Σ, rw ([ δ ]¬b⁻¹ ¬b) tt Σ, refl

[_]→⁻¹_ : ∀ (δ : Vars Δ Γ) → (t [ δ ]) [ q→ ]→ u
        → ∃ λ u⁻¹ → (t [ q→ ]→ u⁻¹) × (u⁻¹ [ δ ] ≡ u)
[_]→⁻¹_ {q→ = β}  = [_]→β⁻¹_
[_]→⁻¹_ {q→ = rw} = [_]→rw⁻¹_

Val→ : t [ q→ ]→ u → Val Γ A t → Val Γ A u
Val→ {A = 𝔹'}    p (acc a)      = a p
Val→ {A = A ⇒ B} p tⱽ      δ uⱽ = Val→ (l· (p [ δ ]→)) (tⱽ δ uⱽ)

_[_]sn : SN Γ A t → ∀ (δ : Vars Δ Γ) → SN Δ A (t [ δ ])
acc a [ δ ]sn = acc (λ p → let u⁻¹ Σ, q Σ, r = [ δ ]→⁻¹ p 
                            in subst (SN _ _) r (a q [ δ ]sn))

[_]sn⁻¹_ : (δ : Vars Δ Γ) → SN Δ A (t [ δ ]) → SN Γ A t
[ δ ]sn⁻¹ acc a = acc (λ p → [ δ ]sn⁻¹ a (p [ δ ]→))

_∋_[_]V : ∀ A {t} → Val Γ A t → ∀ (δ : Vars Δ Γ) → Val Δ A (t [ δ ])
𝔹'       ∋ tⱽ [ δ ]V       = tⱽ [ δ ]sn
((A ⇒ B) ∋ tⱽ [ δ ]V) σ uⱽ = tⱽ (δ ⨾ σ) uⱽ

_[_]E : Env Δ Γ δ → ∀ (σ : Vars Θ Δ) → Env Θ Γ (δ ⨾ σ)
ε        [ σ ]E = ε
(ρ , tⱽ) [ σ ]E = (ρ [ σ ]E) , (_ ∋ tⱽ [ σ ]V)

ValAcc : ∀ Γ A → Tm Γ A → Set
ValAcc Γ A t = ∀ {q→ u} → t [ q→ ]→ u → Val Γ A u

neu : Tm Γ A → Set
neu (ƛ _) = ⊥
neu _     = ⊤

_[_]neu : neu t → (δ : Vars Δ Γ) → neu (t [ δ ])
_[_]neu {t = _ · _}       tt δ = tt
_[_]neu {t = true}        tt δ = tt
_[_]neu {t = false}       tt δ = tt
_[_]neu {t = 𝔹-rec _ _ _} tt δ = tt
_[_]neu {t = ` _}         tt δ = tt

-- Syntactic equality modulo flipping booleans
data _~/𝔹_ : Tm Γ A → Tm Γ A → Set where
  bool  : IsBool t → IsBool u → t ~/𝔹 u 
  `rfl  : (` i) ~/𝔹 (` i)
  _·_   : t₁ ~/𝔹 t₂ → u₁ ~/𝔹 u₂ → (t₁ · u₁) ~/𝔹 (t₂ · u₂)
  ƛ_    : t₁ ~/𝔹 t₂ → (ƛ t₁) ~/𝔹 (ƛ t₂)  
  𝔹-rec : t₁ ~/𝔹 t₂ → u₁ ~/𝔹 u₂ → v₁ ~/𝔹 v₂ → 𝔹-rec t₁ u₁ v₁ ~/𝔹 𝔹-rec t₂ u₂ v₂

rfl/𝔹 : t ~/𝔹 t
rfl/𝔹 {t = true}        = bool tt tt
rfl/𝔹 {t = false}       = bool tt tt
rfl/𝔹 {t = ` i}        = `rfl
rfl/𝔹 {t = t · u}       = rfl/𝔹 · rfl/𝔹
rfl/𝔹 {t = ƛ t}        = ƛ rfl/𝔹
rfl/𝔹 {t = 𝔹-rec c t u} = 𝔹-rec rfl/𝔹 rfl/𝔹 rfl/𝔹

_[_]~/𝔹 : t ~/𝔹 u → (δ : Tms[ q ] Δ Γ) → (t [ δ ]) ~/𝔹 (u [ δ ])
bool b₁ b₂  [ δ ]~/𝔹 = bool (b₁ [ δ ]b) (b₂ [ δ ]b)
`rfl        [ δ ]~/𝔹 = rfl/𝔹
(t · u)     [ δ ]~/𝔹 = (t [ δ ]~/𝔹) · (u [ δ ]~/𝔹)
(ƛ t)       [ δ ]~/𝔹 = ƛ (t [ δ ^ _ ]~/𝔹)
𝔹-rec c t u [ δ ]~/𝔹 = 𝔹-rec (c [ δ ]~/𝔹) (t [ δ ]~/𝔹) (u [ δ ]~/𝔹)

_[_]→rw : t →rw u → (δ : Tms[ q ] Δ Γ) 
        → ((t [ δ ]) →rw (u [ δ ])) ⊎ ((t [ δ ]) ~/𝔹 (u [ δ ]))
rw {t = t} ¬b b [ δ ]→rw with bool? (t [ δ ])
... | inl b[]  = inr (bool b[] (b [ δ ]b))
... | inr ¬b[] = inl (rw ¬b[] (b [ δ ]b))
l· p [ δ ]→rw with p [ δ ]→rw
... | inl p[] = inl (l· p[])
... | inr p[] = inr (p[] · rfl/𝔹)
·r p [ δ ]→rw with p [ δ ]→rw 
... | inl p[] = inl (·r p[])
... | inr p[] = inr (rfl/𝔹 · p[])
(ƛ p) [ δ ]→rw with p [ δ ^ _ ]→rw
... | inl p[] = inl (ƛ p[])
... | inr p[] = inr (ƛ p[])

_[_]→/𝔹 : t [ q→ ]→ u → (δ : Tms[ q ] Δ Γ)
        → (t [ δ ]) [ q→ ]→ (u [ δ ]) ⊎ ((t [ δ ]) ~/𝔹 (u [ δ ]))
_[_]→/𝔹 {q→ = β}  p δ = inl (p [ δ ]→β)
_[_]→/𝔹 {q→ = rw}     = _[_]→rw

SN-l· : SN Γ B (t · u) → SN Γ (A ⇒ B) t
SN-l· (acc f) = acc (λ p → SN-l· (f (l· p)))

SN-·r : SN Γ B (t · u) → SN Γ A u
SN-·r (acc f) = acc (λ p → SN-·r (f (·r p)))

IsBool/𝔹 : t ~/𝔹 u → IsBool t → IsBool u
IsBool/𝔹 {t = true}  (bool tt b) tt = b
IsBool/𝔹 {t = false} (bool tt b) tt = b

¬IsBool/𝔹 : t ~/𝔹 u → ¬IsBool t → ¬IsBool u
¬IsBool/𝔹 {t = ` _}         `rfl          tt = tt
¬IsBool/𝔹 {t = _ · _}       (_ · _)       tt = tt
¬IsBool/𝔹 {t = ƛ _}         (ƛ _)         tt = tt
¬IsBool/𝔹 {t = 𝔹-rec _ _ _} (𝔹-rec _ _ _) tt = tt

sym/𝔹 : t₁ ~/𝔹 t₂ → t₂ ~/𝔹 t₁
sym/𝔹 (bool b₁ b₂)  = bool b₂ b₁
sym/𝔹 `rfl          = `rfl
sym/𝔹 (t · u)       = sym/𝔹 t · sym/𝔹 u
sym/𝔹 (ƛ t)         = ƛ sym/𝔹 t
sym/𝔹 (𝔹-rec c t u) = 𝔹-rec (sym/𝔹 c) (sym/𝔹 t) (sym/𝔹 u)

-- TODO: Fill in this boring setoid stuff
_~/𝔹*_ : Tms Δ Γ → Tms Δ Γ → Set
_[_]/𝔹 : t ~/𝔹 u → δ ~/𝔹* σ → (t [ δ ]) ~/𝔹 (u [ σ ])
<_>/𝔹 : t ~/𝔹 u → < t > ~/𝔹* < u > 

l→/𝔹 : t₁ ~/𝔹 t₂ → t₁ [ q→ ]→ u₁ → ∃ λ u₂ → u₁ ~/𝔹 u₂ × t₂ [ q→ ]→ u₂
l→/𝔹 (bool b₁ b₂)   (rw ¬b b) = ⊥-elim (¬bool← ¬b b₁)
l→/𝔹 `rfl           (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
l→/𝔹 (_ · _)        (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
l→/𝔹 (𝔹-rec _ _ _)  (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
l→/𝔹 ((ƛ t) · u) β            = _ Σ, (t [ < u >/𝔹 ]/𝔹) Σ, β
l→/𝔹 (t · u)     (l· p)       = let t⁻¹ Σ, t~ Σ, q = l→/𝔹 t p
                                  in _ Σ, (t~ · u) Σ, (l· q)
l→/𝔹 (t · u)     (·r p)       = let u⁻¹ Σ, u~ Σ, q = l→/𝔹 u p
                                  in _ Σ, (t · u~) Σ, (·r q)
l→/𝔹 (ƛ t)       (ƛ p)        = let t⁻¹ Σ, t~ Σ, q = l→/𝔹 t p
                                  in _ Σ, (ƛ t~) Σ, (ƛ q)

SN~ : t ~/𝔹 u → SN Γ A t → SN Γ A u
SN~ p (acc a) = acc (λ q → let u⁻¹ Σ, p′ Σ, q′ = l→/𝔹 (sym/𝔹 p) q 
                            in SN~ (sym/𝔹 p′) (a q′))

Val~ : t ~/𝔹 u → Val Γ A t → Val Γ A u
Val~ {A = 𝔹'}              = SN~
Val~ {A = A ⇒ B} p tⱽ δ uⱽ = Val~ (p [ δ ]~/𝔹 · rfl/𝔹) (tⱽ δ uⱽ)

Val[]→ : (δ : Tms[ q ] Δ Γ) → t [ q→ ]→ u → Val Δ A (t [ δ ]) 
        → Val Δ A (u [ δ ])
Val[]→ δ p t[]ⱽ with p [ δ ]→/𝔹
... | inl p[] = Val→ p[] t[]ⱽ
... | inr p[] = Val~ p[] t[]ⱽ

reify   : Val Γ A t → SN Γ A t
reflect : neu t → ValAcc Γ A t → Val Γ A t
eval    : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Δ A (t [ δ ])


-- The 'SN's are only necessary here to show termination
eval-lam : SN (Γ , A) B t → (∀ {u} → Val Γ A u → Val Γ B (t [ < u > ])) 
          → SN Γ A u → Val Γ A u → Val Γ B ((ƛ t) · u)
          
eval-lam-acc : SN (Γ , A) B t → (∀ {u} → Val Γ A u → Val Γ B (t [ < u > ])) 
                → SN Γ A u → Val Γ A u → ValAcc Γ B ((ƛ t) · u)

eval-lam tₛₙ tⱽ uₛₙ uⱽ = reflect tt (eval-lam-acc tₛₙ tⱽ uₛₙ uⱽ) 

eval-lam-acc (acc f) tⱽ (acc g) uⱽ β         = tⱽ uⱽ
eval-lam-acc (acc f) tⱽ (acc g) uⱽ (rw ¬b b) = bool-sn b
eval-lam-acc (acc f) tⱽ (acc g) uⱽ (l· (ƛ p))
  = eval-lam (f p) (λ uⱽ′ → Val[]→ (< _ >) p (tⱽ uⱽ′)) (acc g) uⱽ
eval-lam-acc (acc f) tⱽ (acc g) uⱽ (·r p) 
  = eval-lam (acc f) tⱽ (g p) (Val→ p uⱽ)

  
reflect {A = 𝔹'}    n tⱽ      = acc tⱽ                                      
reflect {A = A ⇒ B} {t = t} n tⱽ δ uⱽ 
  = reflect tt (λ where p → go p (n [ δ ]neu) t[]ⱽ (reify uⱽ) uⱽ) 
  where t[]ⱽ : ValAcc _ _ (t [ δ ])
        t[]ⱽ p σ uⱽ with _ Σ, p Σ, refl ← [ δ ]→⁻¹ p = tⱽ p (δ ⨾ σ) uⱽ
  
        go : (u₁ · u₂) [ q→ ]→ v → neu u₁ → ValAcc _ (A ⇒ B) u₁ 
            → SN Γ A u₂ → Val _ _ u₂ → Val _ B v
        go (rw ¬b b) n tⱽ uₛₙ uⱽ = bool-sn b
        go (l· p)    n tⱽ uₛₙ uⱽ = tⱽ p id uⱽ
        go (·r p)    n tⱽ (acc a) uⱽ 
          = reflect tt (λ q → go q n tⱽ (a p) (Val→ p uⱽ))

vz-val : Val (Γ , A) A (` vz)
vz-val = reflect tt λ where (rw ¬b b) → bool-sn b

reify {A = 𝔹'}    tⱽ = tⱽ
reify {A = A ⇒ B} tⱽ = [ id ⁺ A ]sn⁻¹ (SN-l· (reify (tⱽ (id ⁺ A) vz-val)))

lookup : ∀ (i : Var Γ A) (ρ : Env Δ Γ δ) → Val Δ A (i [ δ ])
lookup vz     (ρ , u) = u
lookup (vs i) (ρ , u) = lookup i ρ

eval (` i)   ρ    = lookup i ρ
eval (t · u) ρ    = eval t ρ id (eval u ρ)
eval (ƛ t) ρ σ uⱽ 
  = eval-lam (reify (eval t (ρ [ σ ⁺ _ ]E , vz-val))) 
              (λ uⱽ′ → eval t ((ρ [ σ ]E) , uⱽ′)) 
              (reify uⱽ) uⱽ

eval true  ρ = true-sn
eval false ρ = false-sn
eval (𝔹-rec c t u) ρ = {!   !}
