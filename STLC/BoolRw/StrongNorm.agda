{-# OPTIONS --injective-type-constructors --rewriting --prop --show-irrelevant --no-require-unique-meta-solutions #-}

open import Utils
open import Common.Sort

-- open import STLC.BoolRw.Syntax
-- open import STLC.SubstEq
open import STLC.Syntax2
open import STLC.SubstEq2

open import STLC.BoolRw.BoolFlip
open import STLC.BoolRw.Reduction
open import STLC.BoolRw.LogRel
open import STLC.BoolRw.Lemmas

-- Strong normalisation of STLC + Boolean rewrites
-- Based on https://github.com/AndrasKovacs/misc-stuff/blob/master/agda/STLCStrongNorm/StrongNorm.agda
module STLC.BoolRw.StrongNorm where

bool-sn : IsBool t → SN Γ A t
bool-sn {t = true}  tt = true-sn
bool-sn {t = false} tt = false-sn

ValAcc : ∀ Γ A → Tm Γ A → Set
ValAcc Γ A t = ∀ {q→ u} → t [ q→ ]→ u → Val Γ A u

¬lam : Tm Γ A → Set
¬lam (ƛ _)   = ⊥
¬lam (inl t) = ¬lam t
¬lam (inr t) = ¬lam t
¬lam _       = ⊤

_[_]¬lam : ¬lam t → (δ : Vars Δ Γ) → ¬lam (t [ δ ])
_[_]¬lam {t = _ · _}       tt δ = tt
_[_]¬lam {t = true}        tt δ = tt
_[_]¬lam {t = false}       tt δ = tt
_[_]¬lam {t = 𝔹-rec _ _ _} tt δ = tt
_[_]¬lam {t = ` _}         tt δ = tt
_[_]¬lam {t = inl t}       ¬ƛ δ = _[_]¬lam {t = t} ¬ƛ δ
_[_]¬lam {t = inr t}       ¬ƛ δ = _[_]¬lam {t = t} ¬ƛ δ
_[_]¬lam {t = +-rec _ _ _} tt δ = tt

reify   : Val Γ A t → SN Γ A t
reflect : ¬lam t → ValAcc Γ A t → Val Γ A t
eval    : ∀ (t : Tm Γ A) (ρ : Env Δ Γ δ) → Val Δ A (t [ δ ])

-- The 'SN's are only necessary here to show termination
eval-lam : (∀ {u} → Val Γ A u → Val Γ B (t [ < u > ])) 
          → SN (Γ , A) B t → Val (Γ , A) B t → SN Γ A u → Val Γ A u 
          → Val Γ B ((ƛ t) · u)
eval-lam→ : (∀ {u} → Val Γ A u → Val Γ B (t [ < u > ])) 
          → SN (Γ , A) B t → Val (Γ , A) B t → SN Γ A u → Val Γ A u 
          → ValAcc Γ B ((ƛ t) · u)

SN-str : SN (Γ , A) B (t [ wk ]) → SN Γ B t
SN-str (acc tˢⁿ) = acc λ p → SN-str (tˢⁿ (p [ wk ]→))

-- Strengthening of computability predicates
Val-str : Val (Γ , A) B (t [ wk ]) → Val Γ B t

+Val-str∣ : (i : Dec∥ inl/inr (t [ wk ]) ∥) → +Val∣ (Γ , A) B C (t [ wk ]) i
          → +Val∣ Γ B C t (map-Dec [ wk ]i⁻¹_ _[ wk ]i i)

Val-str {B = 𝔹'}     tⱽ          = SN-str tⱽ
Val-str {B = B +' C} {t = t} tⱽ  = +Val-str∣ (inl/inr? (t [ wk ])) tⱽ  
Val-str {B = B ⇒  C} tⱽ δ uⱽ uˢⁿ 
  = Val-str (tⱽ (δ ^ _) (_ ∋ uⱽ [ wk ]V) (uˢⁿ [ wk ]sn))

+Val-str∣ (no  ¬i)            (acc tⱽ) = acc λ p → Val-str (tⱽ (p [ wk ]→))
+Val-str∣ {t = inl _} (yes _) tⱽ       = Val-str tⱽ
+Val-str∣ {t = inr _} (yes _) tⱽ       = Val-str tⱽ

Val→* : t →* u → Val Γ A t → Val Γ A u
Val→* rfl     tⱽ = tⱽ
Val→* (p ∷ q) tⱽ = Val→* q (Val→ p tⱽ)

eval-lam tuⱽ tˢⁿ tⱽ uˢⁿ uⱽ = reflect tt (eval-lam→ tuⱽ tˢⁿ tⱽ uˢⁿ uⱽ)

eval-lam→ tuⱽ tˢⁿ tⱽ uˢⁿ uⱽ (β refl refl) = tuⱽ uⱽ
eval-lam→ tuⱽ tˢⁿ tⱽ uˢⁿ uⱽ (rw ¬b b)     = bool-sn b
eval-lam→ tuⱽ (acc tˢⁿ) tⱽ uˢⁿ uⱽ (l· (ƛ_ {t₂ = t₂} p)) 
  = eval-lam (λ {u = u′} uⱽ′ → case bool? u′ of λ where 
                (inl b)  → Val-str (Val→* (boolsub→ t₂ < b >-) (Val→ p tⱽ))
                (inr ¬b) → Val→ (p [ < ¬b >+ ]→+) (tuⱽ uⱽ′)) 
             (tˢⁿ p) (Val→ p tⱽ) uˢⁿ uⱽ
eval-lam→ tuⱽ tˢⁿ tⱽ (acc uˢⁿ) uⱽ (·r p) 
  = eval-lam tuⱽ tˢⁿ tⱽ (uˢⁿ p) (Val→ p uⱽ)

reflect-app : (t · u) [ q→ ]→ v → ¬lam t → ValAcc _ (A ⇒ B) t 
            → SN Γ A u → Val _ _ u → Val _ B v

reflect {A = 𝔹'}             n tⱽ = acc tⱽ          
reflect {A = A +' B} {t = t} n tⱽ with t | inl/inr? t 
... | _     | no  ¬i = acc λ p → tⱽ p
... | inl t | yes _  = reflect n (λ p → tⱽ (inl p))
... | inr t | yes _  = reflect n (λ p → tⱽ (inr p))
reflect {A = A ⇒ B}  {t = t} n tⱽ δ uⱽ uˢⁿ
  = reflect tt λ p → reflect-app p (_[_]¬lam {t = t} n δ) t[]ⱽ 
                                   uˢⁿ uⱽ
  where t[]ⱽ : ValAcc _ _ (t [ δ ])
        t[]ⱽ p σ uⱽ with _ Σ, p Σ, refl ← [ δ ]→⁻¹ p = tⱽ p (δ ⨾ σ) uⱽ

reflect-app (rw ¬b b)      n  tⱽ uₛₙ     uⱽ = bool-sn b
reflect-app (β refl refl)  () tⱽ uₛₙ     uⱽ
reflect-app (l· p)         n  tⱽ uₛₙ     uⱽ = tⱽ p id uⱽ uₛₙ
reflect-app (·r p)         n  tⱽ (acc a) uⱽ 
  = reflect tt (λ q → reflect-app q n tⱽ (a p) (Val→ p uⱽ))

vz-val : Val (Γ , A) A (` vz)
vz-val = reflect tt λ where (rw ¬b b) → bool-sn b

vz-sn  : SN (Γ , A) A (` vz)
vz-sn = acc λ where (rw ¬b b) → bool-sn b

SN-inl : SN Γ A t → SN Γ (A +' B) (inl t)
SN-inl (acc tˢⁿ) = acc λ where (inl p) → SN-inl (tˢⁿ p)

SN-inr : SN Γ B t → SN Γ (A +' B) (inr t)
SN-inr (acc tˢⁿ) = acc λ where (inr p) → SN-inr (tˢⁿ p)

+reify∣ : (i : Dec∥ inl/inr t ∥) → +Val∣ Γ A B t i → SN Γ (A +' B) t
+reify∣             (no  _) (acc tⱽ) = acc λ q → reify (tⱽ q)
+reify∣ {t = inl _} (yes _) tⱽ       = SN-inl (reify tⱽ)
+reify∣ {t = inr _} (yes _) tⱽ       = SN-inr (reify tⱽ)

reify {A = 𝔹'}     tⱽ = tⱽ
reify {A = A +' B} tⱽ = +reify∣ (inl/inr? _) tⱽ 
reify {A = A ⇒ B}  tⱽ 
  = [ wk ]sn⁻¹ (SN-l· (reify (tⱽ wk vz-val vz-sn)))

lookup : ∀ (i : Var Γ A) (ρ : Env Δ Γ δ) → Val Δ A (i [ δ ])
lookup vz     (ρ , u) = u
lookup (vs i) (ρ , u) = lookup i ρ

eval-𝔹-rec : Val Γ 𝔹' t → SN Γ A u → Val Γ A u → SN Γ A v → Val Γ A v 
           → Val Γ A (𝔹-rec t u v)
eval-𝔹-rec→ : Val Γ 𝔹' t → SN Γ A u₁ → Val Γ A u₁ → SN Γ A u₂ → Val Γ A u₂ 
            → 𝔹-rec t u₁ u₂ [ q→ ]→ v → Val Γ A v 

eval-𝔹-rec tⱽ uˢⁿ uⱽ vˢⁿ vⱽ = reflect tt (eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ)

eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ rec-true  = uⱽ
eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ rec-false = vⱽ
eval-𝔹-rec→ tⱽ uˢⁿ uⱽ vˢⁿ vⱽ (rw tt b) = bool-sn b
eval-𝔹-rec→ (acc tⱽ) uˢⁿ uⱽ vˢⁿ vⱽ (𝔹-rec₁ p) 
  = eval-𝔹-rec (tⱽ p) uˢⁿ uⱽ vˢⁿ vⱽ
eval-𝔹-rec→ tⱽ (acc uˢⁿ) uⱽ vˢⁿ vⱽ (𝔹-rec₂ p) 
  = eval-𝔹-rec tⱽ (uˢⁿ p) (Val→ p uⱽ) vˢⁿ vⱽ
eval-𝔹-rec→ tⱽ uˢⁿ uⱽ (acc vˢⁿ) vⱽ (𝔹-rec₃ p) 
  = eval-𝔹-rec tⱽ uˢⁿ uⱽ (vˢⁿ p) (Val→ p vⱽ)

eval-+-rec : Val Γ (A +' B) t → SN Γ (A +' B) t
           → Val (Γ , A) C u → SN (Γ , A) C u 
           → Val (Γ , B) C v → SN (Γ , B) C v
           → Val Γ C (+-rec t u v)
eval-+-rec→ : Val Γ (A +' B) t → SN Γ (A +' B) t
            → Val (Γ , A) C u₁ → SN (Γ , A) C u₁ 
            → Val (Γ , B) C u₂ → SN (Γ , B) C u₂
            → +-rec t u₁ u₂ [ q→ ]→ v → Val Γ C v

eval-+-rec tⱽ tˢⁿ uⱽ uˢⁿ vⱽ vˢⁿ = reflect tt (eval-+-rec→ tⱽ tˢⁿ uⱽ uˢⁿ vⱽ vˢⁿ)

eval-+-rec→ tⱽ tˢⁿ u₁ⱽ u₁ˢⁿ u₂ⱽ u₂ˢⁿ (rw tt b)  = bool-sn b
eval-+-rec→ tⱽ (acc tˢⁿ) u₁ⱽ u₁ˢⁿ u₂ⱽ u₂ˢⁿ (+-rec₁ p) 
  = eval-+-rec (Val→ p tⱽ) (tˢⁿ p) u₁ⱽ u₁ˢⁿ u₂ⱽ u₂ˢⁿ
eval-+-rec→ tⱽ tˢⁿ u₁ⱽ (acc u₁ˢⁿ) u₂ⱽ u₂ˢⁿ (+-rec₂ p) 
  = eval-+-rec tⱽ tˢⁿ (Val→ p u₁ⱽ) (u₁ˢⁿ p) u₂ⱽ u₂ˢⁿ
eval-+-rec→ tⱽ tˢⁿ u₁ⱽ u₁ˢⁿ u₂ⱽ (acc u₂ˢⁿ) (+-rec₃ p) 
  = eval-+-rec tⱽ tˢⁿ u₁ⱽ u₁ˢⁿ (Val→ p u₂ⱽ) (u₂ˢⁿ p)

idᴱ : Env Γ Γ (id[ T ])

eval (` i)   ρ    = lookup i ρ
eval (t · u) ρ    = eval t ρ id (eval u ρ) (reify (eval u ρ))
eval (ƛ t) ρ σ uⱽ uˢⁿ 
  = eval-lam (λ uⱽ′ → eval t ((ρ [ σ ]E) , uⱽ′))  
             (reify tⱽ) tⱽ
             uˢⁿ uⱽ
    where tⱽ = eval t (ρ [ σ ⁺ _ ]E , vz-val)

eval (𝔹-rec t u v) ρ = eval-𝔹-rec (eval t ρ) (reify uⱽ) uⱽ (reify vⱽ) vⱽ
  where uⱽ = eval u ρ
        vⱽ = eval v ρ
eval (+-rec t u v) ρ = eval-+-rec tⱽ (reify tⱽ) uⱽ (reify uⱽ) vⱽ (reify vⱽ)
  where tⱽ = eval t ρ
        uⱽ = eval u (ρ [ wk ]E , vz-val)
        vⱽ = eval v (ρ [ wk ]E , vz-val)

eval true  ρ   = true-sn
eval false ρ   = false-sn
eval (inl t) ρ = eval t ρ
eval (inr t) ρ = eval t ρ

idᴱ {Γ = ε}     = ε
idᴱ {Γ = Γ , A} = idᴱ {Γ = Γ} [ id ⁺ A ]E , vz-val
   
strong-norm : ∀ t → SN Γ A t
strong-norm t = reify (eval t idᴱ)
        