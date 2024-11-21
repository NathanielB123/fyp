{-# OPTIONS --injective-type-constructors --rewriting --prop --show-irrelevant #-}

open import Utils

open import STLC.Syntax
open import STLC.SubstEq
open import STLC.BoolRw.BoolFlip
open import STLC.BoolRw.Reduction

-- Strong normalisation of STLC + Boolean rewrites
-- Based on https://github.com/AndrasKovacs/misc-stuff/blob/master/agda/STLCStrongNorm/StrongNorm.agda
module STLC.BoolRw.StrongNorm where

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

_[_]→ : t [ q→ ]→ u → (δ : Vars Δ Γ) 
      → (t [ δ ]) [ q→ ]→ (u [ δ ])
β refl refl [ δ ]→ = β refl refl
𝔹-rec-β₁ b  [ δ ]→ = 𝔹-rec-β₁ (b [ δ ]b)
𝔹-rec-β₂ b  [ δ ]→ = 𝔹-rec-β₂ (b [ δ ]b)
rw ¬b b     [ δ ]→ = rw (¬b [ δ ]¬b) (b [ δ ]b) 
l· p        [ δ ]→ = l· (p [ δ ]→)
·r p        [ δ ]→ = ·r (p [ δ ]→)
𝔹-rec₁ p    [ δ ]→ = 𝔹-rec₁ (p [ δ ]→)
𝔹-rec₂ p    [ δ ]→ = 𝔹-rec₂ (p [ δ ]→)
𝔹-rec₃ p    [ δ ]→ = 𝔹-rec₃ (p [ δ ]→)
(ƛ p)       [ δ ]→ = ƛ (p [ δ ^ _ ]→)

_[_]→β : t →β u → (δ : Tms[ q ] Δ Γ) 
        → (t [ δ ]) →β (u [ δ ])
β refl refl [ δ ]→β = β refl refl
𝔹-rec-β₁ b  [ δ ]→β = 𝔹-rec-β₁ (b [ δ ]b)
𝔹-rec-β₂ b  [ δ ]→β = 𝔹-rec-β₂ (b [ δ ]b)
l· p        [ δ ]→β = l· (p [ δ ]→β)
·r p        [ δ ]→β = ·r (p [ δ ]→β)
𝔹-rec₁ p    [ δ ]→β = 𝔹-rec₁ (p [ δ ]→β)
𝔹-rec₂ p    [ δ ]→β = 𝔹-rec₂ (p [ δ ]→β)
𝔹-rec₃ p    [ δ ]→β = 𝔹-rec₃ (p [ δ ]→β)
(ƛ p)       [ δ ]→β = ƛ (p [ δ ^ _ ]→β)

ƛ[_]⁻¹_ : (δ : Vars Δ Γ) → t [ δ ] ≡ ƛ u → ∃ λ u⁻¹ → t ≡ ƛ u⁻¹
ƛ[_]⁻¹_ {t = ƛ t} δ refl = _ Σ, refl 

[_]→β⁻¹_ : ∀ (δ : Vars Δ Γ) → (t [ δ ]) →β u
          → ∃ λ u⁻¹ → (t →β u⁻¹) × (u⁻¹ [ δ ] ≡ u)

[_]→β⁻¹_ {t = t · u} δ (β p q) with t′ Σ, refl ← ƛ[_]⁻¹_ {t = t} δ p
                               with refl       ← p
                               with refl       ← q
  = _ Σ, β refl refl Σ, refl
[_]→β⁻¹_ {t = 𝔹-rec t u v}  δ (𝔹-rec-β₁ p) = u Σ, 𝔹-rec-β₁ ([ δ ]b⁻¹ p) Σ, refl
[_]→β⁻¹_ {t = 𝔹-rec t u v} δ (𝔹-rec-β₂ p) = v Σ, 𝔹-rec-β₂ ([ δ ]b⁻¹ p) Σ, refl

[_]→β⁻¹_ {t = ƛ t} δ (ƛ p) 
  = let u⁻¹   Σ, p⁻¹   Σ, q = [_]→β⁻¹_ {t = t} (δ ^ _) p 
     in ƛ u⁻¹ Σ, ƛ p⁻¹ Σ, cong ƛ_ q

[_]→β⁻¹_ {t = t · u} δ (l· p)
  = let t⁻¹     Σ, p′    Σ, q = [_]→β⁻¹_ {t = t} δ p
     in t⁻¹ · u Σ, l· p′ Σ, cong (_· (u [ δ ])) q
[_]→β⁻¹_ {t = t · u} δ (·r p)
  = let u⁻¹     Σ, p′    Σ, q = [_]→β⁻¹_ {t = u} δ p
     in t · u⁻¹ Σ, ·r p′ Σ, cong (t [ δ ] ·_) q

[_]→β⁻¹_ {t = 𝔹-rec t u v} δ (𝔹-rec₁ p) 
  = let t⁻¹           Σ, p′        Σ, q = [_]→β⁻¹_ {t = t} δ p
     in 𝔹-rec t⁻¹ u v Σ, 𝔹-rec₁ p′ Σ, cong (λ □ → 𝔹-rec □ (u [ δ ]) (v [ δ ])) q
[_]→β⁻¹_ {t = 𝔹-rec t u v} δ (𝔹-rec₂ p) 
  = let u⁻¹           Σ, p′        Σ, q = [_]→β⁻¹_ {t = u} δ p
     in 𝔹-rec t u⁻¹ v Σ, 𝔹-rec₂ p′ Σ, cong (λ □ → 𝔹-rec (t [ δ ]) □ (v [ δ ])) q
[_]→β⁻¹_ {t = 𝔹-rec t u v} δ (𝔹-rec₃ p) 
  = let v⁻¹           Σ, p′        Σ, q = [_]→β⁻¹_ {t = v} δ p
     in 𝔹-rec t u v⁻¹ Σ, 𝔹-rec₃ p′ Σ, cong (λ □ → 𝔹-rec (t [ δ ]) (u [ δ ]) □) q

[_]→rw⁻¹_ : ∀ (δ : Vars Δ Γ) → (t [ δ ]) →rw u
          → ∃ λ u⁻¹ → (t →rw u⁻¹) × (u⁻¹ [ δ ] ≡ u)

[_]→rw⁻¹_ {t = t₁ · t₂}     δ (l· p) 
  = let t₁⁻¹      Σ, p    Σ, q = [ δ ]→rw⁻¹ p 
     in t₁⁻¹ · t₂ Σ, l· p Σ, cong (_· t₂ [ δ ]) q
[_]→rw⁻¹_ {t = t₁ · t₂}     δ (·r p)
  = let t₂⁻¹      Σ, p    Σ, q = [ δ ]→rw⁻¹ p 
     in t₁ · t₂⁻¹ Σ, ·r p Σ, cong (t₁ [ δ ] ·_) q
[_]→rw⁻¹_ {t = 𝔹-rec c t u} δ (𝔹-rec₁ p) 
  = let c⁻¹           Σ, p        Σ, q = [ δ ]→rw⁻¹ p
     in 𝔹-rec c⁻¹ t u Σ, 𝔹-rec₁ p Σ, cong (λ □ → 𝔹-rec □ (t [ δ ]) (u [ δ ])) q
[_]→rw⁻¹_ {t = 𝔹-rec c t u} δ (𝔹-rec₂ p)
  = let t⁻¹           Σ, p        Σ, q = [ δ ]→rw⁻¹ p
     in 𝔹-rec c t⁻¹ u Σ, 𝔹-rec₂ p Σ, cong (λ □ → 𝔹-rec (c [ δ ]) □ (u [ δ ])) q
[_]→rw⁻¹_ {t = 𝔹-rec c t u} δ (𝔹-rec₃ p)
  = let u⁻¹           Σ, p        Σ, q = [ δ ]→rw⁻¹ p
     in 𝔹-rec c t u⁻¹ Σ, 𝔹-rec₃ p Σ, cong (λ □ → 𝔹-rec (c [ δ ]) (t [ δ ]) □) q
[_]→rw⁻¹_ {t = ƛ t}         δ (ƛ p)  
  = let t⁻¹   Σ, p   Σ, q = [ δ ^ _ ]→rw⁻¹ p
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

¬lam : Tm Γ A → Set
¬lam (ƛ _) = ⊥
¬lam _     = ⊤

_[_]¬lam : ¬lam t → (δ : Vars Δ Γ) → ¬lam (t [ δ ])
_[_]¬lam {t = _ · _}       tt δ = tt
_[_]¬lam {t = true}        tt δ = tt
_[_]¬lam {t = false}       tt δ = tt
_[_]¬lam {t = 𝔹-rec _ _ _} tt δ = tt
_[_]¬lam {t = ` _}         tt δ = tt

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
𝔹-rec₁ p [ δ ]→rw with p [ δ ]→rw
... | inl p[] = inl (𝔹-rec₁ p[])
... | inr p[] = inr (𝔹-rec p[] rfl/𝔹 rfl/𝔹)
𝔹-rec₂ p [ δ ]→rw with p [ δ ]→rw
... | inl p[] = inl (𝔹-rec₂ p[])
... | inr p[] = inr (𝔹-rec rfl/𝔹 p[] rfl/𝔹)
𝔹-rec₃ p [ δ ]→rw with p [ δ ]→rw
... | inl p[] = inl (𝔹-rec₃ p[])
... | inr p[] = inr (𝔹-rec rfl/𝔹 rfl/𝔹 p[])

_[_]→/𝔹 : t [ q→ ]→ u → (δ : Tms[ q ] Δ Γ)
        → (t [ δ ]) [ q→ ]→ (u [ δ ]) ⊎ ((t [ δ ]) ~/𝔹 (u [ δ ]))
_[_]→/𝔹 {q→ = β}  p δ = inl (p [ δ ]→β)
_[_]→/𝔹 {q→ = rw}     = _[_]→rw

l→/𝔹 : t₁ ~/𝔹 t₂ → t₁ [ q→ ]→ u₁ → ∃ λ u₂ → u₁ ~/𝔹 u₂ × t₂ [ q→ ]→ u₂
l→/𝔹 (bool b₁ b₂)   (rw ¬b b) = ⊥-elim (¬bool← ¬b b₁)
l→/𝔹 `rfl           (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
l→/𝔹 (_ · _)        (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
l→/𝔹 (𝔹-rec _ _ _)  (rw ¬b b) = _ Σ, bool b b Σ, rw tt b

l→/𝔹 ((ƛ t) · u)              (β refl refl) = _ Σ, (t [ < u >/𝔹 ]/𝔹) Σ, β refl refl
l→/𝔹 (bool () b₂)             (β refl refl)
l→/𝔹 (𝔹-rec (bool b₁ b₂) u v) (𝔹-rec-β₁ b) = _ Σ, u Σ, 𝔹-rec-β₁ b₂
l→/𝔹 (𝔹-rec (bool b₁ b₂) u v) (𝔹-rec-β₂ b) = _ Σ, v Σ, 𝔹-rec-β₂ b₂

l→/𝔹 (t · u)     (l· p)       = let _   Σ, t′             Σ, q = l→/𝔹 t p
                                 in _   Σ, (t′ · u)       Σ, (l· q)
l→/𝔹 (t · u)     (·r p)       = let _   Σ, u′             Σ, q = l→/𝔹 u p
                                 in _   Σ, (t · u′)       Σ, (·r q)
l→/𝔹 (ƛ t)       (ƛ p)        = let _   Σ, t′             Σ, q = l→/𝔹 t p
                                 in _   Σ, (ƛ t′)         Σ, (ƛ q)
l→/𝔹 (𝔹-rec t u v) (𝔹-rec₁ p) = let _   Σ, t′             Σ, q = l→/𝔹 t p
                                 in _   Σ, (𝔹-rec t′ u v) Σ, (𝔹-rec₁ q)
l→/𝔹 (𝔹-rec t u v) (𝔹-rec₂ p) = let _   Σ, u′             Σ, q = l→/𝔹 u p
                                 in _   Σ, (𝔹-rec t u′ v) Σ, (𝔹-rec₂ q)
l→/𝔹 (𝔹-rec t u v) (𝔹-rec₃ p) = let _   Σ, v′             Σ, q = l→/𝔹 v p
                                 in _   Σ, (𝔹-rec t u v′) Σ, (𝔹-rec₃ q)

SN~ : t ~/𝔹 u → SN Γ A t → SN Γ A u
SN~ p (acc a) = acc λ q → let _ Σ, p′ Σ, q′ = l→/𝔹 (sym/𝔹 p) q
                           in SN~ (sym/𝔹 p′) (a q′)

Val~ : t ~/𝔹 u → Val Γ A t → Val Γ A u
Val~ {A = 𝔹'}    p tⱽ      = SN~ p tⱽ
Val~ {A = A ⇒ B} p tⱽ δ uⱽ = Val~ (p [ rfl/𝔹* {δ = δ} ]/𝔹 · rfl/𝔹) (tⱽ δ uⱽ)

Val[]→ : (δ : Tms[ q ] Δ Γ) → t [ q→ ]→ u → Val Δ A (t [ δ ]) 
        → Val Δ A (u [ δ ])
Val[]→ δ p t[]ⱽ with p [ δ ]→/𝔹
... | inl p[] = Val→ p[] t[]ⱽ
... | inr p[] = Val~ p[] t[]ⱽ

reify   : Val Γ A t → SN Γ A t
reflect : ¬lam t → ValAcc Γ A t → Val Γ A t
eval    : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Δ A (t [ δ ])


-- The 'SN's are only necessary here to show termination
eval-lam : SN (Γ , A) B t → (∀ {u} → Val Γ A u → Val Γ B (t [ < u > ])) 
          → SN Γ A u → Val Γ A u → Val Γ B ((ƛ t) · u)
          
eval-lam→ : SN (Γ , A) B t → (∀ {u} → Val Γ A u → Val Γ B (t [ < u > ])) 
                → SN Γ A u → Val Γ A u → ValAcc Γ B ((ƛ t) · u)

eval-lam tₛₙ tⱽ uₛₙ uⱽ = reflect tt (eval-lam→ tₛₙ tⱽ uₛₙ uⱽ) 

eval-lam→ (acc f) tⱽ (acc g) uⱽ (β refl refl)  = tⱽ uⱽ
eval-lam→ (acc f) tⱽ (acc g) uⱽ (rw ¬b b) = bool-sn b
eval-lam→ (acc f) tⱽ (acc g) uⱽ (l· (ƛ p))
  = eval-lam (f p) (λ uⱽ′ → Val[]→ (< _ >) p (tⱽ uⱽ′)) (acc g) uⱽ
eval-lam→ (acc f) tⱽ (acc g) uⱽ (·r p) 
  = eval-lam (acc f) tⱽ (g p) (Val→ p uⱽ)

reflect-app : (t · u) [ q→ ]→ v → ¬lam t → ValAcc _ (A ⇒ B) t 
            → SN Γ A u → Val _ _ u → Val _ B v

reflect {A = 𝔹'}            n tⱽ = acc tⱽ                                      
reflect {A = A ⇒ B} {t = t} n tⱽ δ uⱽ 
  = reflect tt (λ where p → reflect-app p (n [ δ ]¬lam) t[]ⱽ (reify uⱽ) uⱽ) 
  where t[]ⱽ : ValAcc _ _ (t [ δ ])
        t[]ⱽ p σ uⱽ with _ Σ, p Σ, refl ← [ δ ]→⁻¹ p = tⱽ p (δ ⨾ σ) uⱽ

reflect-app (rw ¬b b) n tⱽ uₛₙ     uⱽ = bool-sn b
reflect-app (β refl refl)  () tⱽ uₛₙ     uⱽ
reflect-app (l· p)    n tⱽ uₛₙ     uⱽ = tⱽ p id uⱽ
reflect-app (·r p)    n tⱽ (acc a) uⱽ 
  = reflect tt (λ q → reflect-app q n tⱽ (a p) (Val→ p uⱽ))

vz-val : Val (Γ , A) A (` vz)
vz-val = reflect tt λ where (rw ¬b b) → bool-sn b

reify {A = 𝔹'}    tⱽ = tⱽ
reify {A = A ⇒ B} tⱽ = [ id ⁺ A ]sn⁻¹ (SN-l· (reify (tⱽ (id ⁺ A) vz-val)))

lookup : ∀ (i : Var Γ A) (ρ : Env Δ Γ δ) → Val Δ A (i [ δ ])
lookup vz     (ρ , u) = u
lookup (vs i) (ρ , u) = lookup i ρ

eval-𝔹-rec : Val Γ 𝔹' t → SN Γ A u → Val Γ A u → SN Γ A v → Val Γ A v 
           → Val Γ A (𝔹-rec t u v)
eval-𝔹-rec→ : Val Γ 𝔹' t → SN Γ A u₁ → Val Γ A u₁ → SN Γ A u₂ → Val Γ A u₂ 
            → 𝔹-rec t u₁ u₂ [ q→ ]→ v → Val Γ A v 

eval-𝔹-rec tⱽ uˢⁿ uⱽ vˢⁿ vⱽ = reflect tt (eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ)

eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ (𝔹-rec-β₁ b) = uⱽ
eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ (𝔹-rec-β₂ b) = vⱽ
eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ (rw tt b)    = bool-sn b
eval-𝔹-rec→ (acc tⱽ) uˢⁿ uⱽ vˢⁿ vⱽ (𝔹-rec₁ p) = eval-𝔹-rec (tⱽ p) uˢⁿ uⱽ vˢⁿ vⱽ
eval-𝔹-rec→ tⱽ (acc uˢⁿ) uⱽ vˢⁿ vⱽ (𝔹-rec₂ p) 
  = eval-𝔹-rec tⱽ (uˢⁿ p) (Val→ p uⱽ) vˢⁿ vⱽ
eval-𝔹-rec→ tⱽ uˢⁿ uⱽ (acc vˢⁿ) vⱽ (𝔹-rec₃ p) 
  = eval-𝔹-rec tⱽ uˢⁿ uⱽ (vˢⁿ p) (Val→ p vⱽ)

eval (` i)   ρ    = lookup i ρ
eval (t · u) ρ    = eval t ρ id (eval u ρ)
eval (ƛ t) ρ σ uⱽ 
  = eval-lam (reify (eval t (ρ [ σ ⁺ _ ]E , vz-val))) 
              (λ uⱽ′ → eval t ((ρ [ σ ]E) , uⱽ′)) 
              (reify uⱽ) uⱽ

eval true  ρ         = true-sn
eval false ρ         = false-sn
eval (𝔹-rec t u v) ρ = eval-𝔹-rec (eval t ρ) (reify uⱽ) uⱽ (reify vⱽ) vⱽ
  where uⱽ = eval u ρ
        vⱽ = eval v ρ

idᴱ : Env Γ Γ (id[ T ])
idᴱ {Γ = ε}     = ε
idᴱ {Γ = Γ , A} = idᴱ {Γ = Γ} [ id ⁺ A ]E , vz-val

strong-norm : ∀ t → SN Γ A t
strong-norm t = reify (eval t idᴱ)
