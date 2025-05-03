{-# OPTIONS --prop --show-irrelevant #-}

open import Utils

-- A CwF-inspired presentation of SCᴮᵒᵒˡ
--
-- Currently uses explicit substitutions (we might want to try out strictifying 
-- later, but I thought it would be nice to at least have one fully explicit 
-- version)
--
-- Should be a nice setting to do a soundness proof.
module Dependent.SCBool.Syntax where

infixr 4 _∙~_

data Ctx : Set
data Ty  : Ctx → Set
data Tm  : ∀ Γ → Ty Γ → Set
data Tms : Ctx → Ctx → Set

variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ τ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  b b₁ b₂ : Bool

data Ctx~ : Ctx → Ctx → Prop
data Ty~  : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂ → Prop
data Tm~  : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Prop
data Tms~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂ → Prop

variable
  Γ~ Δ~ Θ~ Γ₁₂~ Γ₂₃~ Δ₁₂~ Δ₂₃~ : Ctx~ Γ₁ Γ₂
  A~ A₁₂~ A₂₃~ : Ty~ _ A₁ A₂
  t~ t₁~ t₂~ : Tm~ _ _ t₁ t₂

-- Forward reference can be avoided by defining |Ctx|/|Ty|/|Tm|/|Tms| mutually
-- in a single (telescopic) inductive definition or by using an 
-- inductive-inductive predicate
𝔹′ : Ty Γ

data Ctx where
  ε       : Ctx
  _,_     : ∀ Γ → Ty Γ → Ctx
  _,_>rw_ : ∀ Γ → Tm Γ 𝔹′ → Bool → Ctx

𝔹~′ : Ty~ Γ~ 𝔹′ 𝔹′

data Ty where
  coe~ : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂

  𝔹 : Ty Γ   
  Π : ∀ A → Ty (Γ , A) → Ty Γ

  if   : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ
  _[_] : Ty Γ → Tms Δ Γ → Ty Δ
  
𝔹′ = 𝔹

⌜_⌝𝔹 : Bool → Tm Γ 𝔹
_[_]′ : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  _,_    : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ , A₁) (Γ₂ , A₂)
  _,_>rw : ∀ Γ~ → Tm~ Γ~ 𝔹~′ t₁ t₂ → Ctx~ (Γ₁ , t₁ >rw b) (Γ₂ , t₂ >rw b)

𝔹[]′ : Ty~ rfl~ (𝔹 [ δ ]) 𝔹

data Tms where
  coe~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂

  ε     : Tms Δ ε
  _,_   : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]) → Tms Δ (Γ , A) 
  -- We do some Fording here to enforce that |t [ δ ]| and |⌜ b ⌝𝔹| are 
  -- structural sub-terms.
  ,rwℱ : ∀ (δ : Tms Δ Γ) {u} → t [ δ ]′ ≡ u → ⌜ b ⌝𝔹 ≡ v 
         → Tm~ rfl~ 𝔹[]′ u v
         → Tms Δ (Γ , t >rw b)
  id  : Tms Γ Γ
  _⨾_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ

  π₁   : Tms Δ (Γ , A) → Tms Δ Γ
  π₁rw : Tms Δ (Γ , t >rw b) → Tms Δ Γ

pattern _,rw_ δ t~ = ,rwℱ δ refl refl t~

data Tm where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂
  
  ƛ_   : Tm (Γ , A) B → Tm Γ (Π A B)
  ƛ⁻¹_ : Tm Γ (Π A B) → Tm (Γ , A) B

  TT : Tm Γ 𝔹
  FF : Tm Γ 𝔹
  if : ∀ (t : Tm Γ 𝔹) 
     → Tm (Γ , t >rw true) (A [ π₁rw id ]) 
     → Tm (Γ , t >rw false) (A [ π₁rw id ])
     → Tm Γ A

  π₂   : ∀ (δ : Tms Δ (Γ , A)) → Tm Δ (A [ π₁ δ ])
  _[_] : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])

⌜ true  ⌝𝔹 = TT
⌜ false ⌝𝔹 = FF

_[_]′ = _[_]

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
  _[_] : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
       → Ty~ Δ~ (A₁ [ δ₁ ]) (A₂ [ δ₂ ])

  -- Computation
  𝔹[]  : Ty~ rfl~ (𝔹 [ δ ]) 𝔹
  [][] : Ty~ rfl~ (A [ δ ] [ σ ]) (A [ δ ⨾ σ ])
  [id] : Ty~ rfl~ (A [ id ]) A

𝔹~′ = 𝔹
𝔹[]′ = 𝔹[]

data _⊢_>rw_ : ∀ Γ → Tm Γ 𝔹 → Bool → Set where
  rzℱ   : ∀ {B} → B ≡ Ty.𝔹 {Γ = Γ , t >rw b}
        → (Γ , t >rw b) ⊢ coe~ rfl~ 𝔹[] (t [ π₁rw id ]) >rw b
  rs    : Γ ⊢ t >rw b → (Γ , A) ⊢ coe~ rfl~ 𝔹[] (t [ π₁ id ]) >rw b
  rsrw  : Γ ⊢ t >rw b₁ → (Γ , u >rw b₂) ⊢ coe~ rfl~ 𝔹[] (t [ π₁rw id ]) >rw b₁

pattern rz = rzℱ refl

π₂rw′ : ∀ (δ : Tms Δ (Γ , t >rw b)) → Tm~ rfl~ 𝔹[] (t [ π₁rw δ ]) ⌜ b ⌝𝔹

,rw⨾-helper : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹 
            → Tm~ rfl~ 𝔹[]′ (t [ δ ⨾ σ ]′) ⌜ b ⌝𝔹

data Tms~ where
  -- Equivalence
  rfl~ : Tms~ rfl~ rfl~ δ δ
  sym~ : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ (sym~ Δ~) (sym~ Γ~) δ₂ δ₁
  _∙~_ : Tms~ Δ₁₂~ Γ₁₂~ δ₁ δ₂ → Tms~ Δ₂₃~ Γ₂₃~ δ₂ δ₃
       → Tms~ (Δ₁₂~ ∙~ Δ₂₃~) (Γ₁₂~ ∙~ Γ₂₃~) δ₁ δ₃

  -- Coherence
  coh  : Tms~ Δ~ Γ~ δ (coe~ Δ~ Γ~ δ)

  -- Congruence
  _,_   : ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Tm~ Δ~ (A~ [ δ~ ]) t₁ t₂
        → Tms~ Δ~ (Γ~ , A~) (δ₁ , t₁) (δ₂ , t₂)
  ,rw~  : ∀ {Δ~ : Ctx~ Δ₁ Δ₂} (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
            {t₁~ : Tm~ rfl~ _ _ ⌜ b ⌝𝔹}            
        → Tms~ Δ~ (Γ~ , t~ >rw) (δ₁ ,rw t₁~) (δ₂ ,rw t₂~) 
  
  id   : Tms~ Γ~ Γ~ id id
  _⨾_  : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ Θ~ Δ~ σ₁ σ₂ → Tms~ Θ~ Γ~ (δ₁ ⨾ σ₁) (δ₂ ⨾ σ₂)
  π₁rw : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂)
       → Tms~ Δ~ (Γ~ , t~ >rw) δ₁ δ₂ → Tms~ Δ~ Γ~ (π₁rw δ₁) (π₁rw δ₂)

  -- Computation
  εη   : Tms~ rfl~ rfl~ δ ε
  ,η   : Tms~ rfl~ rfl~ δ (π₁ δ , π₂ δ)
  πrwη : Tms~ rfl~ rfl~ (π₁rw δ ,rw π₂rw′ {b = b} δ) δ

  π₁rw, : ∀ {δ : Tms Δ Γ} {t~ : Tm~ _ _ (t [ δ ]) ⌜ b ⌝𝔹} 
        → Tms~ rfl~ rfl~ (π₁rw (δ ,rw t~)) δ

  π₁⨾   : Tms~ rfl~ rfl~ (π₁ (δ ⨾ σ)) (π₁ δ ⨾ σ)
  π₁rw⨾ : Tms~ rfl~ rfl~ (π₁rw (δ ⨾ σ)) (π₁rw δ ⨾ σ)

  id⨾ : Tms~ rfl~ rfl~ (id ⨾ δ) δ
  ⨾id : Tms~ rfl~ rfl~ (δ ⨾ id) δ

  ,⨾   : Tms~ rfl~ rfl~ ((δ , t) ⨾ σ) ((δ ⨾ σ) , (coe~ rfl~ [][] (t [ σ ])))
  ,rw⨾ : {σ : Tms Θ Δ} {t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹} 
       → Tms~ rfl~ rfl~ ((δ ,rw t~) ⨾ σ) ((δ ⨾ σ) ,rw ,rw⨾-helper t~)

⌜⌝𝔹 : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 (⌜ b ⌝𝔹) (⌜ b ⌝𝔹)
⌜⌝𝔹[] : Tm~ rfl~ 𝔹[] (⌜ b ⌝𝔹 [ δ ]) (⌜ b ⌝𝔹)

wk<b> : Ty~ (rfl~ {Γ = Γ}) (A [ π₁rw id ] [ id ,rw (⌜⌝𝔹[] {b = b})  ]) A
wk<b> = [][] ∙~ rfl~ [ sym~ π₁rw⨾ ∙~ π₁rw (⌜⌝𝔹 rfl~) id⨾ ∙~ π₁rw, ] ∙~ [id]

data Tm~ where
  -- Equivalence
  rfl~ : Tm~ rfl~ rfl~ t t
  sym~ : Tm~ Γ~ A~ t₁ t₂ → Tm~ (sym~ Γ~) (sym~ A~) t₂ t₁
  _∙~_ : Tm~ Γ₁₂~ A₁₂~ t₁ t₂ → Tm~ Γ₂₃~ A₂₃~ t₂ t₃ 
       → Tm~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) t₁ t₃

  -- Coherence
  coh  : Tm~ Γ~ A~ t (coe~ Γ~ A~ t)

  --Congruence
  rw   : Γ ⊢ t >rw b → Tm~ rfl~ rfl~ t ⌜ b ⌝𝔹
  
  TT : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 TT TT
  FF : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 FF FF
  if : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
     → Tm~ (Γ~ , t~ >rw) (A~ [ π₁rw t~ id ]) u₁ u₂
     → Tm~ (Γ~ , t~ >rw) (A~ [ π₁rw t~ id ]) v₁ v₂
     → Tm~ Γ~ A~ (if t₁ u₁ v₁) (if t₂ u₂ v₂)
    
  _[_] : Tm~ Γ~ A~ t₁ t₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ δ~ ]) (t₁ [ δ₁ ]) (t₂ [ δ₂ ]) 

  π₂rw : ∀ (δ : Tms Δ (Γ , t >rw b)) → Tm~ rfl~ 𝔹[] (t [ π₁rw δ ]) ⌜ b ⌝𝔹

  -- Computation
  TT[] : Tm~ rfl~ 𝔹[] (TT [ δ ]) TT
  FF[] : Tm~ rfl~ 𝔹[] (FF [ δ ]) FF

  [id] : Tm~ rfl~ [id] (t [ id ]) t
  [][] : Tm~ rfl~ [][] (t [ δ ] [ σ ]) (t [ δ ⨾ σ ])

  ifTT : Tm~ rfl~ (sym~ wk<b>) (if TT u v) (u [ id ,rw TT[] ])
  ifFF : Tm~ rfl~ (sym~ wk<b>) (if FF u v) (v [ id ,rw FF[] ])

  π₂⨾ : Tm~ rfl~ (rfl~ [ π₁⨾ ] ∙~ sym~ {Γ~ = Γ~} [][]) (π₂ (δ ⨾ σ)) (π₂ δ [ σ ])

⌜⌝𝔹 {b = true}  = TT
⌜⌝𝔹 {b = false} = FF

⌜⌝𝔹[] {b = true}  = TT[]
⌜⌝𝔹[] {b = false} = FF[]

,rw⨾-helper t~ 
  =  sym~ {Γ~ = rfl~} [][] ∙~ (t~ [ rfl~ ]) ∙~ ⌜⌝𝔹[]
  
π₂rw′ = π₂rw

-- In an inconsistent context, all terms are convertible
-- Therefore, decidability of conversion is dependent on decidability of
-- context consistency
incon : Tm~ (rfl~ {Γ = Γ₁}) rfl~ TT FF
      → Tm~ {Γ₁ = Γ₁} {Γ₂ = Γ₂} Γ~ A~ t₁ t₂
incon {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ~ = Γ~} {A~ = A~} {t₁ = t₁} {t₂ = t₂} TF~ 
  = sym~ if~t₁ ∙~ if~if ∙~ if~t₂
  where 
    TF~′ : Tm~ Γ~ 𝔹 TT FF
    TF~′ = TF~ ∙~ FF Γ~

    if~t₁ : Tm~ rfl~ rfl~ 
              (if TT 
                  (t₁ [ π₁rw id ])
                  (coe~ (sym~ Γ~) (sym~ A~) t₂ [ π₁rw id ])) 
              t₁ 
    if~t₁ =  ifTT ∙~ [][] ∙~ rfl~ [ sym~ π₁rw⨾ ∙~ π₁rw (TT rfl~) id⨾ ∙~ π₁rw, ] 
          ∙~ [id]
    if~if : Tm~ Γ~ A~
              (if TT 
                  (t₁ [ π₁rw id ])
                  (coe~ (sym~ Γ~) (sym~ A~) t₂ [ π₁rw id ])) 
              (if FF 
                  (coe~ Γ~ A~ t₁ [ π₁rw id ])
                  (t₂ [ π₁rw id ]))
    if~if = if TF~′ (coh [ π₁rw TF~′ id ]) (sym~ coh [ π₁rw TF~′ id ])
    if~t₂ : Tm~ rfl~ rfl~ 
              (if FF 
                  (coe~ Γ~ A~ t₁ [ π₁rw id ])
                  (t₂ [ π₁rw id ])) 
              t₂
    if~t₂ =  ifFF ∙~ [][] ∙~ rfl~ [ sym~ π₁rw⨾ ∙~ π₁rw (FF rfl~) id⨾ ∙~ π₁rw, ] 
          ∙~ [id]
 