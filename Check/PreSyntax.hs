module Check.PreSyntax where

type Var = String

data Motive = [Var] :|- Tm

data Tm = Var String 
        | App Tm Tm 
        | If (Maybe Motive) Tm Tm Tm
        | SmrtIf (Maybe Motive) Tm Tm Tm 
        | Transp Motive Tm Tm 
        | Expl (Maybe Motive) Tm
        | U | B | Bot | Pi Tm Tm | Id Tm Tm Tm
        | Lam Var Tm Tm 
        | TT | FF 
        | Rfl Tm
        | Absrd
