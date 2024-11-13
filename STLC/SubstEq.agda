{-# OPTIONS --rewriting --prop #-}

import Agda.Builtin.Equality.Rewrite

open import Utils

open import STLC.Syntax

-- Equations abot substitutions
--
-- Proving these using the approach outlined in
-- https://github.com/txa/substitution/blob/main/submission.pdf
-- should not be too tricky, but for now I am a bit bored of proving 
-- substitution lemmas, and will just postulate them
module STLC.SubstEq where

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
  q⊑r : q ⊑ r
  Ξ : Ctx

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
-- https://github.com/agda/agda/issues/7602
T[][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
T[][] {t = t} = [][] {x = t}

{-# REWRITE [][] ⁺⨾ ⨾⁺ id⨾ ⨾id vz[] [id] ⨾⨾ ⊑⨾ ⨾⊑ ⊑⁺ [⊑] [⊑,`] tms⊑-id 
            T[][] #-}
