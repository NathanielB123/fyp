{-# OPTIONS --prop #-}

module STLC.BoolRw.Syntax where

open import STLC.Syntax public
open Parameterised ƛ∪𝔹∪+ public

{-# DISPLAY _⊢Ctx _     = Ctx #-}
{-# DISPLAY _⊢Ty _      = Ty #-}
{-# DISPLAY [_]_⊢Tm q _ = Tm[ q ] #-}
{-# DISPLAY _⊢Var _     = Var #-}
{-# DISPLAY _⊢Tm _      = Tm #-}
{-# DISPLAY _⊢Ne _      = Ne #-}
{-# DISPLAY _⊢Nf _      = Nf #-}
