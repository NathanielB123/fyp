{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Check.Syntax where
import Check.Utils

type Var = String

data Body a t = (Vec a (Var, t)) :|- Tm
  deriving Show

type family Motive a = r | r -> a where
  Motive Z = Maybe Tm
  Motive a = Body a ()

-- TODO: Maybe consider indexing by 'Sort'. Parsing is top-down, so accounting
-- for 'Sort' should actually be relatively easy!
data Tm = Var String 
        | App Tm Tm 
        | If (Motive (S Z)) Tm Tm Tm
        | SmrtIf (Motive Z) Tm Tm Tm 
        | Transp (Motive (S Z)) Tm Tm
        -- J (Motive (S (S Z))) Tm Tm 
        | Expl (Motive Z) Tm
        | U | B | Bot 
        | Id Tm Tm Tm
        | forall a. Pi (Body (S a) Tm)
        | forall a. Lam (Body (S a) (Maybe Tm)) 
        | TT | FF 
        | Rfl (Maybe Tm)
        | Absrd

deriving instance Show Tm
