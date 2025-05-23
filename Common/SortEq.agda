{-# OPTIONS --prop --rewriting #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils
open import Common.Sort

module Common.SortEq where

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
