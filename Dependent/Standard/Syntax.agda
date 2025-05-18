{-# OPTIONS --prop --show-irrelevant #-}

open import Utils

-- Ordinary dependent types
module Dependent.Standard.Syntax where

infixr 4 _∙~_

data Ctx : Set
data Ty  : Ctx → Set
data Tm  : ∀ Γ → Ty Γ → Set
data Tms : Ctx → Ctx → Set

variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  b b₁ b₂ : Bool

data Ctx~ : Ctx → Ctx → Prop
data Ty~  : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂ → Prop
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
  _[_] : Ty Γ → Tms Δ Γ → Ty Δ

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  -- Note we don't need a case for |ε| because it takes no arguments
  _,_ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ , A₁) (Γ₂ , A₂)
 

<_> : Tm Γ A → Tms Γ (Γ , A)

data Tms where
  coe~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂

  ε     : Tms Δ ε
  _,_   : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]) → Tms Δ (Γ , A) 
  
  id   : Tms Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  
  π₁   : Tms Δ (Γ , A) → Tms Δ Γ
  
data Tm where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂
  
  ƛ_   : Tm (Γ , A) B → Tm Γ (Π A B)
  ƛ⁻¹_ : Tm Γ (Π A B) → Tm (Γ , A) B

  TT : Tm Γ 𝔹
  FF : Tm Γ 𝔹
  if : ∀ (t : Tm Γ 𝔹) 
     → Tm Γ (A [ < TT > ]) 
     → Tm Γ (A [ < FF > ])
     → Tm Γ (A [ < t > ])

  π₂   : ∀ (δ : Tms Δ (Γ , A)) → Tm Δ (A [ π₁ δ ])
  _[_] : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ , A) Γ
δ ⁺ A = δ ⨾ π₁ id

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ , (A [ δ ])) (Γ , A)

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
  if   : Tm~ Γ~ 𝔹 t₁ t₂ → Ty~ Γ~ A₁ A₂ → Ty~ Γ~ B₁ B₂ 
       → Ty~ Γ~ (if t₁ A₁ B₁) (if t₂ A₂ B₂)

  -- Computation
  ifTT : Ty~ rfl~ (if TT A B) A
  ifFF : Ty~ rfl~ (if FF A B) B

  𝔹[]  : Ty~ rfl~ (𝔹 [ δ ]) 𝔹
  Π[]  : Ty~ rfl~ (Π A B [ δ ]) (Π (A [ δ ]) (B [ δ ^ A ]))
  if[] : Ty~ rfl~ (if t A B [ δ ]) 
                  (if (coe~ rfl~ 𝔹[] (t [ δ ])) (A [ δ ]) (B [ δ ]))
  [id] : Ty~ rfl~ (A [ id ]) A
  [][] : Ty~ rfl~ (A [ δ ] [ σ ]) (A [ δ ⨾ σ ])

< t > = id , coe~ rfl~ (sym~ [id]) t

δ ^ A = (δ ⁺ _) , (coe~ rfl~ [][] (π₂ id))

_·_ : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ id , coe~ rfl~ (sym~ [id]) u ])
t · u = (ƛ⁻¹ t) [ id , coe~ rfl~ (sym~ [id]) u ]

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
  _,_   : ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Tm~ Δ~ (A~ [ δ~ ]) t₁ t₂
        → Tms~ Δ~ (Γ~ , A~) (δ₁ , t₁) (δ₂ , t₂)
  
  id   : Tms~ Γ~ Γ~ id id
  _⨾_  : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ Θ~ Δ~ σ₁ σ₂ → Tms~ Θ~ Γ~ (δ₁ ⨾ σ₁) (δ₂ ⨾ σ₂)
  
  π₁   : ∀ (A~ : Ty~ Γ~ A₁ A₂) → Tms~ Δ~ (Γ~ , A~) δ₁ δ₂ 
       → Tms~ Δ~ Γ~ (π₁ δ₁) (π₁ δ₂)

  -- Computation
  εη   : Tms~ rfl~ rfl~ δ ε
  ,η   : Tms~ rfl~ rfl~ δ (π₁ δ , π₂ δ)

  π₁,   : Tms~ rfl~ rfl~ (π₁ (δ , t)) δ

  π₁⨾   : Tms~ rfl~ rfl~ (π₁ (δ ⨾ σ)) (π₁ δ ⨾ σ)

  id⨾ : Tms~ rfl~ rfl~ (id ⨾ δ) δ
  ⨾id : Tms~ rfl~ rfl~ (δ ⨾ id) δ
  ⨾⨾  : Tms~ rfl~ rfl~ ((δ ⨾ σ) ⨾ γ) (δ ⨾ (σ ⨾ γ))

  ,⨾   : Tms~ rfl~ rfl~ ((δ , t) ⨾ σ) ((δ ⨾ σ) , (coe~ rfl~ [][] (t [ σ ])))
 
wk<>    : Tms~ rfl~ rfl~ (π₁ id ⨾ < t >) id
<>-comm : Tms~ rfl~ rfl~ ((δ ^ _) ⨾ < t [ δ ] >) (< t > ⨾ δ)

if[]-lemma : Ty~ rfl~ (A [ coe~ (rfl~ , 𝔹[]) rfl~ (δ ^ _) ] 
                         [ < coe~ rfl~ 𝔹[] (t [ δ ]) > ])
                      (A [ < t > ] [ δ ])

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
  ƛ_   : Tm~ (Γ~ , A~) B~ t₁ t₂ → Tm~ Γ~ (Π A~ B~) (ƛ t₁) (ƛ t₂)
  ƛ⁻¹_ : Tm~ Γ~ (Π A~ B~) t₁ t₂ → Tm~ (Γ~ , A~) B~ (ƛ⁻¹ t₁) (ƛ⁻¹ t₂)
  TT   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 TT TT
  FF   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 FF FF
  if   : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
       → Tm~ Γ~ (A~ [ < TT Γ~ >~ ]) u₁ u₂
       → Tm~ Γ~ (A~ [ < FF Γ~ >~ ]) v₁ v₂
       → Tm~ Γ~ (A~ [ < t~ >~ ]) 
                (if t₁ u₁ v₁) (if t₂ u₂ v₂)
    
  _[_] : Tm~ Γ~ A~ t₁ t₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ δ~ ]) (t₁ [ δ₁ ]) (t₂ [ δ₂ ]) 
  π₂   : ∀ (δ~ : Tms~ Δ~ (Γ~ , A~) δ₁ δ₂)  
       → Tm~ Δ~ (A~ [ π₁ A~ δ~ ]) (π₂ δ₁) (π₂ δ₂) 

  -- Computation
  ƛ[]   : Tm~ rfl~ Π[] ((ƛ t) [ δ ]) (ƛ (t [ δ ^ A ]))
  TT[]  : Tm~ rfl~ 𝔹[] (TT [ δ ]) TT
  FF[]  : Tm~ rfl~ 𝔹[] (FF [ δ ]) FF
  if[]  : Tm~ rfl~ (sym~ if[]-lemma)
              (if t u v [ δ ]) 
              (if (coe~ rfl~ 𝔹[] (t [ δ ])) 
                  (coe~ rfl~ (sym~ if[]-lemma ∙~ rfl~ [ < sym~ coh ∙~ TT[] >~ ]) 
                        (u [ δ ])) 
                  (coe~ rfl~ (sym~ if[]-lemma ∙~ rfl~ [ < sym~ coh ∙~ FF[] >~ ]) 
                        (v [ δ ])))

  [id] : Tm~ rfl~ [id] (t [ id ]) t 
  [][] : Tm~ rfl~ [][] (t [ δ ] [ σ ]) (t [ δ ⨾ σ ])

  ifTT : Tm~ rfl~ rfl~ (if TT u v) u
  ifFF : Tm~ rfl~ rfl~ (if FF u v) v

  β    : Tm~ rfl~ rfl~ (ƛ⁻¹ ƛ t) t
  η    : Tm~ rfl~ rfl~ (ƛ ƛ⁻¹ t) t

  π₂, : Tm~ rfl~ (rfl~ [ π₁, ]) (π₂ (δ , t)) t

  -- Note this is what we would expect from |π₂[]|, but reversed
  π₂⨾ : Tm~ rfl~ (rfl~ [ π₁⨾ ] ∙~ sym~ [][]) (π₂ (δ ⨾ σ)) (π₂ δ [ σ ])

<_>~ {A~ = A~} t~ = _,_ {A~ = A~} id (sym~ coh ∙~ t~ ∙~ coh)

wk<> = sym~ π₁⨾ ∙~ π₁ rfl~ id⨾ ∙~ π₁,

<>-comm = ,⨾ ∙~ (_,_ {A~ = rfl~} 
                     (⨾⨾ ∙~ (rfl~ ⨾ wk<>) ∙~ ⨾id ∙~ sym~ id⨾) 
                     (sym~ coh ∙~ sym~ coh [ rfl~ ] ∙~ sym~ π₂⨾ 
                     ∙~ π₂ {A~ = rfl~} id⨾ ∙~ π₂, ∙~ sym~ coh ∙~ coh [ rfl~ ] 
                     ∙~ coh)) 
       ∙~ sym~ ,⨾

if[]-lemma = [][] ∙~ rfl~ [ (sym~ coh ⨾ < sym~ coh >~) ∙~ <>-comm ] ∙~ sym~ [][]

 
coeTm~ : Tm~ Γ~ A~ t₁ t₂ 
       → Tm~ (sym~ Γ₁~ ∙~ Γ~ ∙~ Γ₂~) (sym~ A₁~ ∙~ A~ ∙~ A₂~) 
             (coe~ Γ₁~ A₁~ t₁) (coe~ Γ₂~ A₂~ t₂)
coeTm~ t~ = sym~ coh ∙~ t~ ∙~ coh

-- We derive the substitution law for |ƛ⁻¹| as in 
-- https://people.cs.nott.ac.uk/psztxa/publ/tt-in-tt.pdf
ƛ⁻¹[] : Tm~ rfl~ rfl~ ((ƛ⁻¹ t) [ δ ^ A ]) (ƛ⁻¹ (coe~ rfl~ Π[] (t [ δ ])))
ƛ⁻¹[] =  sym~ β ∙~ ƛ⁻¹_ {A~ = rfl~} {B~ = rfl~} (coh {A~ = rfl~} 
      ∙~ coeTm~ (sym~ ƛ[] ∙~ η [ rfl~ ]))
