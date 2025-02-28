{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Check.Syntax where

import Check.Utils

type Var = String

data Body a = (Vec a Var) :|- Tm

type family Motive a where
  Motive Z = Maybe Tm
  Motive a = Body a

data Tm = Var String 
        | App Tm Tm 
        | If (Motive (S Z)) Tm Tm Tm
        | SmrtIf (Motive Z) Tm Tm Tm 
        | Transp (Motive (S Z)) Tm Tm
        -- J (Motive (S (S Z))) Tm Tm 
        | Expl (Motive Z) Tm
        | U | B | Bot | Pi Var Tm Tm | Id Tm Tm Tm
        | Lam Var (Maybe Tm) Tm 
        | TT | FF 
        | Rfl Tm
        | Absrd
