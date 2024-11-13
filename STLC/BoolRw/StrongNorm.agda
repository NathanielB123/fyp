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
β         [ δ ]→ = β
rec-true  [ δ ]→ = rec-true
rec-false [ δ ]→ = rec-false
rw ¬b b   [ δ ]→ = rw (¬b [ δ ]¬b) (b [ δ ]b) 
l· p      [ δ ]→ = l· (p [ δ ]→)
·r p      [ δ ]→ = ·r (p [ δ ]→)
𝔹-rec₁ p  [ δ ]→ = 𝔹-rec₁ (p [ δ ]→)
𝔹-rec₂ p  [ δ ]→ = 𝔹-rec₂ (p [ δ ]→)
𝔹-rec₃ p  [ δ ]→ = 𝔹-rec₃ (p [ δ ]→)
(ƛ p)     [ δ ]→ = ƛ (p [ δ ^ _ ]→)

_[_]→β : t →β u → (δ : Tms[ q ] Δ Γ) 
        → (t [ δ ]) →β (u [ δ ])
β         [ δ ]→β = β
rec-true  [ δ ]→β = rec-true
rec-false [ δ ]→β = rec-false
l· p      [ δ ]→β = l· (p [ δ ]→β)
·r p      [ δ ]→β = ·r (p [ δ ]→β)
𝔹-rec₁ p  [ δ ]→β = 𝔹-rec₁ (p [ δ ]→β)
𝔹-rec₂ p  [ δ ]→β = 𝔹-rec₂ (p [ δ ]→β)
𝔹-rec₃ p  [ δ ]→β = 𝔹-rec₃ (p [ δ ]→β)
(ƛ p)     [ δ ]→β = ƛ (p [ δ ^ _ ]→β)

-- These cases are mostly mechanical, but I got bored so I have commented them 
-- out for now
[_]→β⁻¹_ : ∀ (δ : Vars Δ Γ) → (t [ δ ]) →β u
          → ∃ λ u⁻¹ → (t →β u⁻¹) × (u⁻¹ [ δ ] ≡ u)

-- [_]→β⁻¹_ {t = ƛ t} δ (ƛ p) 
--   = let u⁻¹   Σ, p   Σ, q = [_]→β⁻¹_ {t = t} (δ ^ _) p 
--       in ƛ u⁻¹ Σ, ƛ p Σ, cong ƛ_ q

-- -- There is some very careful case-splitting here to avoid LHS-unification 
-- -- issues with 'β'. I wonder if fording would make this neater...
-- [_]→β⁻¹_ {t = t · u · v} δ (l· p) 
--   = let tu⁻¹     Σ, p    Σ, q = [_]→β⁻¹_ {t = t · u} δ p
--      in tu⁻¹ · v Σ, l· p Σ, cong (_· (v [ δ ])) q
-- [_]→β⁻¹_ {t = (ƛ t) · u} δ (l· p) 
--   = let t⁻¹      Σ, p    Σ, q = [_]→β⁻¹_ {t = ƛ t} δ p
--      in t⁻¹ · u Σ, l· p Σ, cong (_· (u [ δ ])) q
-- [_]→β⁻¹_ {t = 𝔹-rec c t u · v} δ (l· p) 
--   = let r⁻¹     Σ, p    Σ, q = [_]→β⁻¹_ {t = 𝔹-rec c t u} δ p
--      in r⁻¹ · v Σ, l· p Σ, cong (_· (v [ δ ])) q

-- [_]→β⁻¹_ {t = ` i · u} δ (·r p) 
--   = let u⁻¹       Σ, p    Σ, q = [_]→β⁻¹_ {t = u} δ p 
--      in ` i · u⁻¹ Σ, ·r p Σ, cong (` (i [ δ ]) ·_) q
-- [_]→β⁻¹_ {t = t · u · v} δ (·r p)
--   = let v⁻¹         Σ, p    Σ, q = [_]→β⁻¹_ {t = v} δ p 
--      in t · u · v⁻¹ Σ, ·r p Σ, cong ((t [ δ ]) · (u [ δ ]) ·_) q
-- [_]→β⁻¹_ {t = (ƛ t) · u} δ (·r p) 
--   = let u⁻¹         Σ, p    Σ, q = [_]→β⁻¹_ {t = u} δ p 
--      in (ƛ t) · u⁻¹ Σ, ·r p Σ, cong ((ƛ t [ δ ^ _ ]) ·_) q
-- [_]→β⁻¹_ {t = 𝔹-rec c t u · v} δ (·r p)
--   = let v⁻¹               Σ, p    Σ, q = [_]→β⁻¹_ {t = v} δ p 
--      in 𝔹-rec c t u · v⁻¹ Σ, ·r p 
--      Σ, cong (𝔹-rec (c [ δ ]) (t [ δ ]) (u [ δ ]) ·_) q

-- [_]→β⁻¹_ {t = 𝔹-rec true t u}  δ rec-true  = t Σ, rec-true Σ, refl
-- [_]→β⁻¹_ {t = 𝔹-rec false t u} δ rec-false = u Σ, rec-false Σ, refl
-- [_]→β⁻¹_ {t = (ƛ t) · u}       δ β         = t [ < u > ] Σ, β Σ, refl

-- TODO
-- [_]→β⁻¹_ {t = 𝔹-rec (` i) t u} δ (𝔹-rec₂ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec (` i) t u} δ (𝔹-rec₃ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec (c₁ · c₂) t u} δ (𝔹-rec₁ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec (c₁ · c₂) t u} δ (𝔹-rec₂ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec (c₁ · c₂) t u} δ (𝔹-rec₃ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec true t u} δ (𝔹-rec₂ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec true t u} δ (𝔹-rec₃ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec false t u} δ (𝔹-rec₂ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec false t u} δ (𝔹-rec₃ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec (𝔹-rec _ _ _) t u} δ (𝔹-rec₁ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec (𝔹-rec _ _ _) t u} δ (𝔹-rec₂ p) = {!   !}
-- [_]→β⁻¹_ {t = 𝔹-rec (𝔹-rec _ _ _) t u} δ (𝔹-rec₃ p) = {!   !}

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

-- Because of 'rec-true'/'rec-false', this is straight-up false!
-- Leaving commented out in case parts of it are helpful later...
-- l→/𝔹 : t₁ ~/𝔹 t₂ → t₁ [ q→ ]→ u₁ → ∃ λ u₂ → u₁ ~/𝔹 u₂ × t₂ [ q→ ]→ u₂
-- l→/𝔹 (bool b₁ b₂)   (rw ¬b b) = ⊥-elim (¬bool← ¬b b₁)
-- l→/𝔹 `rfl           (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
-- l→/𝔹 (_ · _)        (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
-- l→/𝔹 (𝔹-rec _ _ _)  (rw ¬b b) = _ Σ, bool b b Σ, rw tt b
-- l→/𝔹 ((ƛ t) · u) β            = _ Σ, (t [ < u >/𝔹 ]/𝔹) Σ, β
-- l→/𝔹 (𝔹-rec (bool tt b₂) t u) rec-true   = _ Σ, t Σ, {!!}
-- l→/𝔹 (𝔹-rec (bool tt b₂) t u) rec-false  = {!   !}
-- l→/𝔹 (t · u)     (l· p)       = let t⁻¹ Σ, t~       Σ, q = l→/𝔹 t p
--                                  in _   Σ, (t~ · u) Σ, (l· q)
-- l→/𝔹 (t · u)     (·r p)       = let u⁻¹ Σ, u~       Σ, q = l→/𝔹 u p
--                                  in _   Σ, (t · u~) Σ, (·r q)
-- l→/𝔹 (ƛ t)       (ƛ p)        = let t⁻¹ Σ, t~       Σ, q = l→/𝔹 t p
--                                  in _   Σ, (ƛ t~)   Σ, (ƛ q)

SN~ : t ~/𝔹 u → SN Γ A t → SN Γ A u
SN~-helper : t ~/𝔹 u → SN Γ A t → u [ q→ ]→ v → SN Γ A v

SN~ p a = acc (SN~-helper p a)

SN~-helper _ (acc a) (rw ¬b b) = bool-sn b
SN~-helper ((ƛ p) · q) (acc a) β = acc (SN~-helper (p [ < q >/𝔹 ]/𝔹) (a β))
SN~-helper (𝔹-rec p q r) (acc a) rec-true
  -- I want to fill this in with the following case, but Agda's termination
  -- checker is not convinced. There is no guarantee 
  -- 'SN-𝔹-rec₂ (acc a)' ≤ 'acc a' (and this is probably fair)
  -- I would like a way to augment 'SN' with structural orderings on terms
  = {!!} -- acc (SN~-helper q (SN-𝔹-rec₂ (acc a)))
SN~-helper (𝔹-rec p q r) (acc a) rec-false = {!   !}
SN~-helper (p · q) (acc a) (l· r) = {!   !}
SN~-helper (p · q) (acc a) (·r r) = {!   !}
SN~-helper (ƛ p) (acc a) (ƛ q) = {!   !}
SN~-helper (𝔹-rec p q r) (acc a) (𝔹-rec₁ s) = {!!}
SN~-helper (𝔹-rec p q r) (acc a) (𝔹-rec₂ s) = {!!}
SN~-helper (𝔹-rec p q r) (acc a) (𝔹-rec₃ s) = {!!}


-- Old version
-- SN~ p (acc a) = acc (λ q → let u⁻¹ Σ, p′ Σ, q′ = l→/𝔹 (sym/𝔹 p) q 
--                             in SN~ {!sym/𝔹 p′!} (a q′))

Val~ : t ~/𝔹 u → Val Γ A t → Val Γ A u
Val~ {A = 𝔹'}              = SN~
Val~ {A = A ⇒ B} p tⱽ δ uⱽ = Val~ (p [ δ ]~/𝔹 · rfl/𝔹) (tⱽ δ uⱽ)

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
          
eval-lam-acc : SN (Γ , A) B t → (∀ {u} → Val Γ A u → Val Γ B (t [ < u > ])) 
                → SN Γ A u → Val Γ A u → ValAcc Γ B ((ƛ t) · u)

eval-lam tₛₙ tⱽ uₛₙ uⱽ = reflect tt (eval-lam-acc tₛₙ tⱽ uₛₙ uⱽ) 

eval-lam-acc (acc f) tⱽ (acc g) uⱽ β         = tⱽ uⱽ
eval-lam-acc (acc f) tⱽ (acc g) uⱽ (rw ¬b b) = bool-sn b
eval-lam-acc (acc f) tⱽ (acc g) uⱽ (l· (ƛ p))
  = eval-lam (f p) (λ uⱽ′ → Val[]→ (< _ >) p (tⱽ uⱽ′)) (acc g) uⱽ
eval-lam-acc (acc f) tⱽ (acc g) uⱽ (·r p) 
  = eval-lam (acc f) tⱽ (g p) (Val→ p uⱽ)

reflect-app : (t · u) [ q→ ]→ v → ¬lam t → ValAcc _ (A ⇒ B) t 
            → SN Γ A u → Val _ _ u → Val _ B v

reflect {A = 𝔹'}            n tⱽ = acc tⱽ                                      
reflect {A = A ⇒ B} {t = t} n tⱽ δ uⱽ 
  = reflect tt (λ where p → reflect-app p (n [ δ ]¬lam) t[]ⱽ (reify uⱽ) uⱽ) 
  where t[]ⱽ : ValAcc _ _ (t [ δ ])
        t[]ⱽ p σ uⱽ with _ Σ, p Σ, refl ← [ δ ]→⁻¹ p = tⱽ p (δ ⨾ σ) uⱽ

reflect-app (rw ¬b b) n tⱽ uₛₙ     uⱽ = bool-sn b
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

eval (` i)   ρ    = lookup i ρ
eval (t · u) ρ    = eval t ρ id (eval u ρ)
eval (ƛ t) ρ σ uⱽ 
  = eval-lam (reify (eval t (ρ [ σ ⁺ _ ]E , vz-val))) 
              (λ uⱽ′ → eval t ((ρ [ σ ]E) , uⱽ′)) 
              (reify uⱽ) uⱽ

eval true  ρ = true-sn
eval false ρ = false-sn
eval (𝔹-rec c t u) ρ = {!   !}

idᴱ : Env Γ Γ (id[ T ])
idᴱ {Γ = ε}     = ε
idᴱ {Γ = Γ , A} = idᴱ {Γ = Γ} [ id ⁺ A ]E , vz-val

strong-norm : ∀ t → SN Γ A t
strong-norm t = reify (eval t idᴱ)
 