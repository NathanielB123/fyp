{-# OPTIONS --prop #-}

open import Utils
open import Dependent.SCBool.Syntax

-- Provide an induction principle for eliminating all syntactic sorts 
-- (|Ctx|, |Ty|, |Tm|, |Tms|) at once.
module Dependent.SCBool.MutualInd where

data Sort : Set where
  ctx : Sort
  ty  : Ctx → Sort
  tm  : ∀ Γ → Ty Γ → Sort
  tms : Ctx → Ctx → Sort

Syn : Sort → Set
Syn ctx       = Ctx
Syn (ty Γ)    = Ty Γ
Syn (tm Γ A)  = Tm Γ A
Syn (tms Δ Γ) = Tms Δ Γ

data SortMarker : Sort → Set where
  CTX : SortMarker ctx
  TY  : SortMarker (ty Γ)
  TM  : SortMarker (tm Γ A)
  TMS : SortMarker (tms Δ Γ)

variable
  𝒮 : Sort
