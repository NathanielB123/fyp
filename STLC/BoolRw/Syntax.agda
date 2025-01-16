{-# OPTIONS --prop #-}

module STLC.BoolRw.Syntax where

open import STLC.Syntax public
open Parameterised ƛ∪𝔹∪+ public

{-# DISPLAY _⊢Ctx 𝕏     = Ctx #-}
{-# DISPLAY _⊢Ty 𝕏      = Ty #-}
{-# DISPLAY [_]_⊢Tm q 𝕏 = Tm[ q ] #-}
{-# DISPLAY _⊢Var 𝕏     = Var #-}
{-# DISPLAY _⊢Tm 𝕏      = Tm #-}
{-# DISPLAY _⊢Ne 𝕏      = Ne #-}
{-# DISPLAY _⊢Nf 𝕏      = Nf #-}
