{-# OPTIONS --rewriting --prop #-}

import Agda.Builtin.Equality.Rewrite

open import Utils
open import Common.Sort
open import Common.SortEq

open import STLC.Syntax

-- Equations abot substitutions
--
-- Proving these using the approach outlined in
-- https://github.com/txa/substitution/blob/main/submission.pdf
-- should not be too tricky, but for now I am a bit bored of proving 
-- substitution lemmas, and will just postulate them
module STLC.SubstEq (𝕏 : Extensions) where

open Parameterised 𝕏

variable
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
  [id,] : x [ (id ⁺ A) , y ] ≡ x
  ⨾⨾    : (δ ⨾ σ) ⨾ ξ ≡ δ ⨾ (σ ⨾ ξ)
  
  ⊑⨾   : {q⊑r : q ⊑ r} {σ : Tms[ s ] Θ Δ} 
       → tms⊑ q⊑r δ ⨾ σ ≡ tms⊑ (⊑⊔s {s = s} q⊑r) (δ ⨾ σ)
  ⨾⊑   : {q⊑r : r ⊑ s} {δ : Tms[ q ] Δ Γ}
       → δ ⨾ tms⊑ q⊑r σ ≡ tms⊑ (s⊔⊑ {s = q} q⊑r) (δ ⨾ σ)
  
  ⊑⁺   : tms⊑ q⊑r δ ⁺ A ≡ tms⊑ q⊑r (δ ⁺ A) 

  [⊑]   : {q⊑r : q ⊑ r} {x : Tm[ s ] Γ A} 
        → x [ tms⊑ q⊑r δ ] ≡ tm⊑ (s⊔⊑ {s = s} q⊑r) (x [ δ ])
  [⊑,`] : x [ (tms⊑ ⊑T δ , (` j)) ] ≡ tm⊑ ⊑T (x [ δ , j ])

  id⁺vs : i [ id ⁺ A ] ≡ vs i

  tms⊑-id : tms⊑ q⊑r δ ≡ δ

-- Epic rewrite fail
-- https://github.com/agda/agda/issues/7602
T[][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
T[][] {t = t} = [][] {x = t}

V[][] : i [ δ ] [ σ ] ≡ i [ δ ⨾ σ ]
V[][] {i = i} = [][] {x = i}

{-# REWRITE [][] ⁺⨾ ⨾⁺ id⨾ ⨾id vz[] [id] ⨾⨾ ⊑⨾ ⨾⊑ ⊑⁺ [⊑] [⊑,`] id⁺vs tms⊑-id 
            T[][] V[][] [id,] #-}
