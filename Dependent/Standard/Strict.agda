{-# OPTIONS --prop --rewriting --show-irrelevant --mutual-rewriting #-}

open import Utils
open import Utils.IdExtras

-- Strictified syntax
--
-- I.e. substitution is recursive and substitution equations hold definitionally
-- Still ultimately setoid-based because of β/η equations (cannot strictify
-- these without assuming normalisation)
--
-- I haven't yet inserted cases for recursive operations applied to |coe|
-- Given I have committed to interleaving rewrites with definitions, it might
-- also make sense to define recursive functions recursively instead of purely
-- postulating...
module Dependent.Standard.Strict where

infixr 4 _∙~_

data Ctx : Set
data Ty  : Ctx → Set
data Var : ∀ Γ → Ty Γ → Set
data Tm  : ∀ Γ → Ty Γ → Set
data Tms : Ctx → Ctx → Set

variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  i j k i₁ i₂ i₃ : Var Γ A
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  b b₁ b₂ : Bool

data Ctx~ : Ctx → Ctx → Prop
data Ty~  : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂ → Prop
data Var~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Var Γ₁ A₁ → Var Γ₂ A₂ → Prop
data Tm~  : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Prop
data Tms~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂ → Prop

variable
  Γ~ Δ~ Θ~ Γ₁₂~ Γ₂₃~ Δ₁₂~ Δ₂₃~ Γ₁~ Γ₂~ Γ₃~ Γ₄~ : Ctx~ Γ₁ Γ₂
  A~ B~ A₁₂~ A₂₃~ A₁~ A₂~ A₃~ A₄~ : Ty~ _ A₁ A₂
  t~ t₁~ t₂~ : Tm~ _ _ t₁ t₂

data Ctx where
  ε       : Ctx
  _,_     : ∀ Γ → Ty Γ → Ctx

data Ty where
  coe~ : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂

  𝔹 : Ty Γ   
  Π : ∀ A → Ty (Γ , A) → Ty Γ

  if   : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ

postulate
  _[_]T : Ty Γ → Tms Δ Γ → Ty Δ

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  _,_    : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ , A₁) (Γ₂ , A₂)

<_> : Tm Γ A → Tms Γ (Γ , A)

data Tms where
  coe~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂

  ε     : Tms Δ ε
  _,_   : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]T) → Tms Δ (Γ , A) 
  
postulate
  id  : Tms Γ Γ
  _⨾_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  _⁺_ : Tms Δ Γ → ∀ A → Tms (Δ , A) Γ

wk : Tms (Γ , A) Γ
wk = id ⁺ _

data Var where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Var Γ₁ A₁ → Var Γ₂ A₂

  vz : Var (Γ , A) (A [ wk ]T)
  vs : Var Γ B → Var (Γ , A) (B [ wk ]T)

data Tm where  
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂

  `_   : Var Γ A → Tm Γ A
  ƛ_   : Tm (Γ , A) B → Tm Γ (Π A B)
  _·_  : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ < u > ]T)

  TT : Tm Γ 𝔹
  FF : Tm Γ 𝔹
  if : ∀ (t : Tm Γ 𝔹) 
     → Tm Γ (A [ < TT > ]T) 
     → Tm Γ (A [ < FF > ]T)
     → Tm Γ (A [ < t > ]T)

postulate
  lookup : Var Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]T)
  _[_]   : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]T)
  suc    : ∀ A → Tm Γ B → Tm (Γ , A) (B [ wk ]T)

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ , (A [ δ ]T)) (Γ , A)

data Ty~ where
  -- Equivalence
  rfl~ : Ty~ rfl~ A A
  sym~ : Ty~ Γ~ A₁ A₂ → Ty~ (sym~ Γ~) A₂ A₁
  _∙~_ : Ty~ Γ₁₂~ A₁ A₂ → Ty~ Γ₂₃~ A₂ A₃ → Ty~ (Γ₁₂~ ∙~ Γ₂₃~) A₁ A₃

  -- Coherence
  coh : Ty~ Γ~ A (coe~ Γ~ A)

  -- Congruence
  𝔹    : Ty~ Γ~ 𝔹 𝔹
  Π    : ∀ A~ → Ty~ (Γ~ , A~) B₁ B₂ → Ty~ Γ~ (Π A₁ B₁) (Π A₂ B₂)
  if   : Tm~ Γ~ 𝔹 t₁ t₂ → Ty~ Γ~ A₁ A₂ → Ty~ Γ~ B₁ B₂ 
       → Ty~ Γ~ (if t₁ A₁ B₁) (if t₂ A₂ B₂)

  -- Computation
  ifTT : Ty~ rfl~ (if TT A B) A
  ifFF : Ty~ rfl~ (if FF A B) B

-- Additional congruences
postulate
  _[_]T~ : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
         → Ty~ Δ~ (A₁ [ δ₁ ]T) (A₂ [ δ₂ ]T)

-- Strictified computation
postulate  𝔹[] : 𝔹 [ δ ]T ≡ 𝔹
{-# REWRITE 𝔹[] #-}

postulate Π[] : Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T)
{-# REWRITE Π[] #-}

postulate if[]T : if t A B [ δ ]T ≡ if (t [ δ ]) (A [ δ ]T) (B [ δ ]T)
{-# REWRITE if[]T #-}

postulate [id]T : A [ id ]T ≡ A
{-# REWRITE [id]T #-}

-- |id| is not convertible with its unfolding
postulate [id,]T : A [ (id ⁺ B) , (` vz) ]T ≡ A
{-# REWRITE [id,]T #-}

postulate [][]T : A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T
{-# REWRITE [][]T #-}

< t > = id , t

-- Strictified computation
postulate id⨾ : id ⨾ δ ≡ δ
{-# REWRITE id⨾ #-}

postulate ⨾id : δ ⨾ id ≡ δ 
{-# REWRITE ⨾id #-}

postulate ⨾⨾ : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
{-# REWRITE ⨾⨾ #-}

postulate ,⨾ : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , (t [ σ ])
{-# REWRITE ,⨾ #-}

postulate ⨾⁺ : δ ⨾ (σ ⁺ A) ≡ (δ ⨾ σ) ⁺ A
{-# REWRITE ⨾⁺ #-}

postulate 
  ,⁺ : ∀ {δ : Tms Δ Γ} {t : Tm Δ (A [ δ ]T)}
     → (_,_ {A = A} δ t) ⁺ B ≡ (δ ⁺ B) , (suc B t)
{-# REWRITE ,⁺ #-}

postulate id, : id {Γ = Γ , A} ≡ (id ⁺ A) , (` vz)
{-# REWRITE id, #-}

postulate ⁺, : (δ ⁺ A) ⨾ (σ , t) ≡ δ ⨾ σ
{-# REWRITE ⁺, #-}

data Tms~ where
  -- Equivalence
  rfl~ : Tms~ rfl~ rfl~ δ δ
  sym~ : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ (sym~ Δ~) (sym~ Γ~) δ₂ δ₁
  _∙~_ : Tms~ Δ₁₂~ Γ₁₂~ δ₁ δ₂ → Tms~ Δ₂₃~ Γ₂₃~ δ₂ δ₃
       → Tms~ (Δ₁₂~ ∙~ Δ₂₃~) (Γ₁₂~ ∙~ Γ₂₃~) δ₁ δ₃

  -- Coherence
  coh  : Tms~ Δ~ Γ~ δ (coe~ Δ~ Γ~ δ)

  -- Congruence
  ε     : Tms~ Δ~ rfl~ ε ε
  _,_   : ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Tm~ Δ~ (A~ [ δ~ ]T~) t₁ t₂
        → Tms~ Δ~ (Γ~ , A~) (δ₁ , t₁) (δ₂ , t₂)

  -- TODO: do we need η-rules?
  -- The η-rule for |_,_| requires |π₁| and |π₂| operations, which I don't
  -- particularly want to write out all the laws for...
  -- εη : Tms~ Δ~ Γ~ δ ε

-- Additional congruences
postulate
  id~   : Tms~ Γ~ Γ~ id id
  _⨾~_  : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ Θ~ Δ~ σ₁ σ₂ → Tms~ Θ~ Γ~ (δ₁ ⨾ σ₁) (δ₂ ⨾ σ₂)
  _⁺~_  : Tms~ Δ~ Γ~ δ₁ δ₂ → ∀ (A~ : Ty~ Δ~ A₁ A₂) 
        → Tms~ (Δ~ , A~) Γ~ (δ₁ ⁺ A₁) (δ₂ ⁺ A₂)

δ ^ A = (δ ⁺ _) , (` vz)

wk~  : ∀ (A~ : Ty~ Γ~ A₁ A₂) → Tms~ (Γ~ , A~) Γ~ wk wk

data Var~ where
  -- Equivalence
  rfl~ : Var~ rfl~ rfl~ i i
  sym~ : Var~ Γ~ A~ i₁ i₂ → Var~ (sym~ Γ~) (sym~ A~) i₂ i₁
  _∙~_ : Var~ Γ₁₂~ A₁₂~ i₁ i₂ → Var~ Γ₂₃~ A₂₃~ i₂ i₃ 
       → Var~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) i₁ i₃

  -- Congruence
  vz : Var~ (Γ~ , A~) (A~ [ wk~ A~ ]T~) vz vz
  vs : Var~ Γ~ B~ i₁ i₂ → Var~ (Γ~ , A~) (B~ [ wk~ A~ ]T~) (vs i₁) (vs i₂)

-- Strict computation
postulate lookup-vz : lookup vz (δ , t) ≡ t
{-# REWRITE lookup-vz #-}
postulate lookup-vs : lookup (vs i) (δ , t) ≡ lookup i δ
{-# REWRITE lookup-vs #-}

-- Epic rewrite fail
-- https://github.com/agda/agda/issues/7602
lookup-vz₁′ : lookup vz (id , (t [ δ ])) ≡ t [ δ ]
lookup-vz₁′ {t = t} {δ = δ} = lookup-vz {δ = id} {t = t [ δ ]}
{-# REWRITE lookup-vz₁′ #-}

lookup-vz₂′ : lookup vz (id {Γ = Γ} , TT) ≡ TT
lookup-vz₂′ = lookup-vz {δ = id} {t = TT}
{-# REWRITE lookup-vz₂′ #-}

lookup-vz₃′ : lookup vz (id {Γ = Γ} , FF) ≡ FF
lookup-vz₃′ = lookup-vz {δ = id} {t = FF}
{-# REWRITE lookup-vz₃′ #-}

lookup-vz₄′ : ∀ {t : Tm Γ 𝔹} → lookup vz (id , (t [ δ ])) ≡ t [ δ ]
lookup-vz₄′ {δ = δ} {t = t} = lookup-vz {δ = id} {t = t [ δ ]}
{-# REWRITE lookup-vz₄′ #-}

postulate suc`  : suc A (` i) ≡ ` vs i
{-# REWRITE suc` #-}
postulate sucTT : suc A TT ≡ TT
{-# REWRITE sucTT #-}
postulate sucFF : suc A FF ≡ FF
{-# REWRITE sucFF #-}
postulate sucƛ : suc A (ƛ t) ≡ (ƛ t) [ wk ]
{-# REWRITE sucƛ #-}
  -- We could do slightly better here, |suc A (t · u) = suc A t · suc A u|,
  -- plus transports, but ultimately it doesn't really matter. The key
  -- case is to short circuit on variables
postulate suc·  : suc A (t · u) ≡ (t · u) [ wk ]
{-# REWRITE suc· #-}

postulate lookup-id : lookup i id ≡ (` i)
{-# REWRITE lookup-id #-}
postulate lookup-⨾ : lookup i δ [ σ ] ≡ lookup i (δ ⨾ σ)
{-# REWRITE lookup-⨾ #-}

postulate [id] : t [ id ] ≡ t 
{-# REWRITE [id] #-}
postulate [][] : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]
{-# REWRITE [][] #-}

postulate `[] : (` i) [ δ ] ≡ lookup i δ
{-# REWRITE `[] #-}
postulate ƛ[] : (ƛ t) [ δ ] ≡ ƛ (t [ δ ^ A ])
{-# REWRITE ƛ[] #-}
postulate ·[]  : (t · u) [ δ ] ≡ (t [ δ ]) · (u [ δ ])
{-# REWRITE ·[] #-}

postulate TT[] : TT [ δ ] ≡ TT
{-# REWRITE TT[] #-}
postulate FF[] : FF [ δ ] ≡ FF
{-# REWRITE FF[] #-}

postulate 
  if[] : if {A = A} t u v [ δ ] 
       ≡ if {A = A [ δ ^ 𝔹 ]T} (t [ δ ]) (u [ δ ]) (v [ δ ])
{-# REWRITE if[] #-}

-- Should be implied by the other rewrites, but #7602 strikes again
postulate wkvz : Tms~ rfl~ rfl~ ((wk ^ A) ⨾ < ` vz >) id

-- The proof is something along the lines of
-- wkvz = ,⨾~
--     ∙~ _,_ {A~ = rfl~} (⁺,~ ∙~ ⨾id~) 
--            (sym~ coh ∙~ sym~ coh [ rfl~ ]~ ∙~ `[]~ ∙~ lookup-vz~ ∙~ sym~ coh) 
--     ∙~ sym~ id,~

<_>~ : Tm~ Γ~ A~ t₁ t₂ → Tms~ Γ~ (Γ~ , A~) < t₁ > < t₂ >

data Tm~ where
  -- Equivalence
  rfl~ : Tm~ rfl~ rfl~ t t
  sym~ : Tm~ Γ~ A~ t₁ t₂ → Tm~ (sym~ Γ~) (sym~ A~) t₂ t₁
  _∙~_ : Tm~ Γ₁₂~ A₁₂~ t₁ t₂ → Tm~ Γ₂₃~ A₂₃~ t₂ t₃ 
       → Tm~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) t₁ t₃

  -- Coherence
  coh  : Tm~ Γ~ A~ t (coe~ Γ~ A~ t)

  --Congruence  
  `_   : Var~ Γ~ A~ i₁ i₂ → Tm~ Γ~ A~ (` i₁) (` i₂)
  ƛ_   : Tm~ (Γ~ , A~) B~ t₁ t₂ → Tm~ Γ~ (Π A~ B~) (ƛ t₁) (ƛ t₂)
  _·_  : Tm~ Γ~ (Π A~ B~) t₁ t₂ → ∀ (u~ : Tm~ Γ~ A~ u₁ u₂)
       → Tm~ Γ~ (B~ [ < u~ >~ ]T~) (t₁ · u₁) (t₂ · u₂) 

  TT   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 TT TT
  FF   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 FF FF
  if   : ∀ (A~ : Ty~ (Γ~ , 𝔹) A₁ A₂) (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
       → Tm~ Γ~ (A~ [ < TT Γ~ >~ ]T~) u₁ u₂
       → Tm~ Γ~ (A~ [ < FF Γ~ >~ ]T~) v₁ v₂
       → Tm~ Γ~ (A~ [ < t~ >~ ]T~) 
                (if {A = A₁} t₁ u₁ v₁) (if {A = A₂} t₂ u₂ v₂)

  -- Computation
  ifTT : Tm~ rfl~ rfl~ (if {A = A} TT u v) u
  ifFF : Tm~ rfl~ rfl~ (if {A = A} FF u v) v

  β    : Tm~ rfl~ rfl~ ((ƛ t) · u) (t [ < u > ])
  η    : Tm~ rfl~ (Π rfl~ (rfl~ [ sym~ wkvz ]T~))
             t (ƛ_ {A = A} ((t [ wk ]) · (` vz))) 

-- Additional congruences
postulate
  lookup~ : Var~ Γ~ A~ i₁ i₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
          → Tm~ Δ~ (A~ [ δ~ ]T~) (lookup i₁ δ₁) (lookup i₂ δ₂)
  _[_]~ : Tm~ Γ~ A~ t₁ t₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
        → Tm~ Δ~ (A~ [ δ~ ]T~) (t₁ [ δ₁ ]) (t₂ [ δ₂ ]) 
  suc~  : Tm~ Γ~ B~ t₁ t₂ → ∀ (A~ : Ty~ Γ~ A₁ A₂)
        → Tm~ (Γ~ , A~) (B~ [ wk~ A~ ]T~) (suc A₁ t₁) (suc A₂ t₂)

<_>~ {A~ = A~} t~ = _,_ {A~ = A~} id~ t~
wk~ A~ = id~ ⁺~ A~
