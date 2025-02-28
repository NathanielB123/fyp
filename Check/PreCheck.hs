module Check.PreCheck where

import Check.Utils
import Check.PreSyntax
import Check.Model
import Check.Common

data PreCheckedTm g = forall q. Tm (Tm q g)

preCheck :: SNat g -> PreTm -> TCM (PreCheckedTm g)
preCheck t = _

