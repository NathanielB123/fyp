{-# OPTIONS --prop --show-irrelevant #-}

open import Utils
open import STLC.Syntax

-- Equivalence relation on terms corresponding to syntactic equality modulo 
-- flipping booleans
module STLC.BoolRw.BoolFlip where

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

data _~/𝔹_ : Tm[ q ] Γ A → Tm[ q ] Γ A → Set where
  bool  : IsBool t → IsBool u → t ~/𝔹 u 
  Vrfl  : _~/𝔹_ {q = V} i i
  `rfl  : (` i) ~/𝔹 (` i)
  _·_   : t₁ ~/𝔹 t₂ → u₁ ~/𝔹 u₂ → (t₁ · u₁) ~/𝔹 (t₂ · u₂)
  ƛ_    : t₁ ~/𝔹 t₂ → (ƛ t₁) ~/𝔹 (ƛ t₂)  
  𝔹-rec : t₁ ~/𝔹 t₂ → u₁ ~/𝔹 u₂ → v₁ ~/𝔹 v₂ → 𝔹-rec t₁ u₁ v₁ ~/𝔹 𝔹-rec t₂ u₂ v₂

data _~/𝔹*_ {q} {Δ} : Tms[ q ] Δ Γ → Tms[ q ] Δ Γ → Set where
  ε   : ε ~/𝔹* ε
  _,_ : δ₁ ~/𝔹* δ₂ → x₁ ~/𝔹 x₂ → (δ₁ , x₁) ~/𝔹* (δ₂ , x₂)

rfl/𝔹 : _~/𝔹_ {q = q} x x
rfl/𝔹 {q = V}           = Vrfl
rfl/𝔹 {x = true}        = bool tt tt
rfl/𝔹 {x = false}       = bool tt tt
rfl/𝔹 {x = ` i}         = `rfl
rfl/𝔹 {x = t · u}       = rfl/𝔹 · rfl/𝔹
rfl/𝔹 {x = ƛ t}         = ƛ rfl/𝔹
rfl/𝔹 {x = 𝔹-rec c t u} = 𝔹-rec rfl/𝔹 rfl/𝔹 rfl/𝔹

rfl/𝔹* : δ ~/𝔹* δ 
rfl/𝔹* {δ = ε}     = ε
rfl/𝔹* {δ = δ , x} = rfl/𝔹* , rfl/𝔹

_[_]~/𝔹 : t ~/𝔹 u → (δ : Tms[ q ] Δ Γ) → (t [ δ ]) ~/𝔹 (u [ δ ])
bool b₁ b₂  [ δ ]~/𝔹 = bool (b₁ [ δ ]b) (b₂ [ δ ]b)
`rfl        [ δ ]~/𝔹 = rfl/𝔹
(t · u)     [ δ ]~/𝔹 = (t [ δ ]~/𝔹) · (u [ δ ]~/𝔹)
(ƛ t)       [ δ ]~/𝔹 = ƛ (t [ δ ^ _ ]~/𝔹)
𝔹-rec c t u [ δ ]~/𝔹 = 𝔹-rec (c [ δ ]~/𝔹) (t [ δ ]~/𝔹) (u [ δ ]~/𝔹)

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

tm⊑/𝔹 : (p : q ⊑ r) → x₁ ~/𝔹 x₂ → tm⊑ p x₁ ~/𝔹 tm⊑ p x₂
tm⊑/𝔹 {q = V}         p Vrfl = rfl/𝔹
tm⊑/𝔹 {q = T} {r = T} p x    = x

_[_]/𝔹   : x₁ ~/𝔹 x₂ → δ₁ ~/𝔹* δ₂ → (x₁ [ δ₁ ]) ~/𝔹 (x₂ [ δ₂ ])
_⁺/𝔹_    : δ₁ ~/𝔹* δ₂ → ∀ A → (δ₁ ⁺ A) ~/𝔹* (δ₂ ⁺ A)
_^/𝔹_    : δ₁ ~/𝔹* δ₂ → ∀ A → (δ₁ ^ A) ~/𝔹* (δ₂ ^ A)
suc[_]/𝔹 : ∀ q {x₁ : Tm[ q ] Γ A} {x₂ : Tm[ q ] Γ A} 
         → x₁ ~/𝔹 x₂ → suc[_] {A = B} q x₁ ~/𝔹 suc[ q ] x₂

suc[ V ]/𝔹 Vrfl = Vrfl
suc[ T ]/𝔹 t    = t [ rfl/𝔹* ]/𝔹

ε       ⁺/𝔹 A = ε
(δ , t) ⁺/𝔹 A = (δ ⁺/𝔹 A) , (suc[ _ ]/𝔹 t)

δ ^/𝔹 A = (δ ⁺/𝔹 A) , rfl/𝔹

Vrfl {i = vz}                      [ δ , u ]/𝔹 = u
Vrfl {i = vs i}                    [ δ , u ]/𝔹 = Vrfl {i = i} [ δ ]/𝔹
`rfl {i = i}                       [ δ ]/𝔹     = tm⊑/𝔹 ⊑T (Vrfl {i = i} [ δ ]/𝔹)
bool {t = true}  {u = true}  tt tt [ δ ]/𝔹     = bool tt tt
bool {t = true}  {u = false} tt tt [ δ ]/𝔹     = bool tt tt
bool {t = false} {u = true}  tt tt [ δ ]/𝔹     = bool tt tt
bool {t = false} {u = false} tt tt [ δ ]/𝔹     = bool tt tt
(t · u)                            [ δ ]/𝔹     = (t [ δ ]/𝔹) · (u [ δ ]/𝔹)
(ƛ t)                              [ δ ]/𝔹     = ƛ (t [ δ ^/𝔹 _ ]/𝔹)
𝔹-rec c t u                        [ δ ]/𝔹 
  = 𝔹-rec (c [ δ ]/𝔹) (t [ δ ]/𝔹) (u [ δ ]/𝔹)

<_>/𝔹 : t₁ ~/𝔹 t₂ → < t₁ > ~/𝔹* < t₂ > 
< t >/𝔹 = rfl/𝔹* , t
