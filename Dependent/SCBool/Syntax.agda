{-# OPTIONS --prop --show-irrelevant --safe #-}

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

-- Forward references can be avoided by defining |Ctx|/|Ty|/|Tm|/|Sub[_]| 
-- mutually in a single (telescopic) inductive definition or by using 
-- inductive-inductive predicates
𝔹′ : Ty Γ

data Ctx where
  •       : Ctx
  _▷_     : ∀ Γ → Ty Γ → Ctx
  _▷_>eq_ : ∀ Γ → Tm Γ 𝔹′ → Bool → Ctx

𝔹~′ : Ty~ Γ~ 𝔹′ 𝔹′

data Ty where
  coe~ : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂

  𝔹 : Ty Γ   
  Π : ∀ A → Ty (Γ ▷ A) → Ty Γ

  IF    : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ
  _[_]  : Ty Γ → Tms Δ Γ → Ty Δ
  
𝔹′ = 𝔹

⌜_⌝𝔹 : Bool → Tm Γ 𝔹
_[_]′ : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  _▷_    : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ ▷ A₁) (Γ₂ ▷ A₂)
  _▷_>eq : ∀ Γ~ → Tm~ Γ~ 𝔹~′ t₁ t₂ → Ctx~ (Γ₁ ▷ t₁ >eq b) (Γ₂ ▷ t₂ >eq b)

𝔹[]′ : Ty~ rfl~ (𝔹 [ δ ]) 𝔹

data Tms where
  coe~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂

  ε     : Tms Δ •
  _,_   : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]) → Tms Δ (Γ ▷ A) 
  -- We do some Fording here to enforce that |t [ δ ]| is considered a 
  -- structural subterm.
  ,eqℱ  : ∀ (δ : Tms Δ Γ) {u} → t [ δ ]′ ≡ u
        → Tm~ rfl~ 𝔹[]′ (t [ δ ]′) ⌜ b ⌝𝔹
        → Tms Δ (Γ ▷ t >eq b)
  
  id   : Tms Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  
  π₁   : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₁eq : Tms Δ (Γ ▷ t >eq b) → Tms Δ Γ

pattern _,eq_ δ t~ = ,eqℱ δ refl t~

data Tm where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂
  
  ƛ_   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  ƛ⁻¹_ : Tm Γ (Π A B) → Tm (Γ ▷ A) B

  TT : Tm Γ 𝔹
  FF : Tm Γ 𝔹
  if : ∀ (t : Tm Γ 𝔹) 
     → Tm (Γ ▷ t >eq true) (A [ π₁eq id ]) 
     → Tm (Γ ▷ t >eq false) (A [ π₁eq id ])
     → Tm Γ A

  π₂   : ∀ (δ : Tms Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ])
  _[_] : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])

⌜ true  ⌝𝔹 = TT
⌜ false ⌝𝔹 = FF

_[_]′ = _[_]

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ ▷ A) Γ
δ ⁺ A = δ ⨾ π₁ id

_⁺eq_ : Tms Δ Γ → ∀ t → Tms (Δ ▷ t >eq b) Γ
δ ⁺eq t = δ ⨾ π₁eq id

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ ▷ (A [ δ ])) (Γ ▷ A)

data Ty~ where
  -- Equivalence
  rfl~ : Ty~ rfl~ A A
  sym~ : Ty~ Γ~ A₁ A₂ → Ty~ (sym~ Γ~) A₂ A₁
  _∙~_ : Ty~ Γ₁₂~ A₁ A₂ → Ty~ Γ₂₃~ A₂ A₃ → Ty~ (Γ₁₂~ ∙~ Γ₂₃~) A₁ A₃

  -- Coherence
  coh : Ty~ Γ~ A (coe~ Γ~ A)

  -- Congruence
  𝔹    : Ty~ Γ~ 𝔹 𝔹
  Π    : ∀ A~ → Ty~ (Γ~ ▷ A~) B₁ B₂ → Ty~ Γ~ (Π A₁ B₁) (Π A₂ B₂)
  _[_] : ∀ (A~ : Ty~ Γ~ A₁ A₂) (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
       → Ty~ Δ~ (A₁ [ δ₁ ]) (A₂ [ δ₂ ])
  IF   : Tm~ Γ~ 𝔹 t₁ t₂ → Ty~ Γ~ A₁ A₂ → Ty~ Γ~ B₁ B₂ 
       → Ty~ Γ~ (IF t₁ A₁ B₁) (IF t₂ A₂ B₂)

  -- Computation
  IF-TT : Ty~ rfl~ (IF TT A B) A
  IF-FF : Ty~ rfl~ (IF FF A B) B

  𝔹[]  : Ty~ rfl~ (𝔹 [ δ ]) 𝔹
  Π[]  : Ty~ rfl~ (Π A B [ δ ]) (Π (A [ δ ]) (B [ δ ^ A ]))
  IF[] : Ty~ rfl~ (IF t A B [ δ ]) 
                  (IF (coe~ rfl~ 𝔹[] (t [ δ ])) (A [ δ ]) (B [ δ ]))
  [id] : Ty~ rfl~ (A [ id ]) A
  [][] : Ty~ rfl~ (A [ δ ] [ σ ]) (A [ δ ⨾ σ ])

𝔹~′ = 𝔹
𝔹[]′ = 𝔹[]

δ ^ A = (δ ⁺ _) , (coe~ rfl~ [][] (π₂ id))

_·_ : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ id , coe~ rfl~ (sym~ [id]) u ])
t · u = (ƛ⁻¹ t) [ id , coe~ rfl~ (sym~ [id]) u ]

π₂eq′ : ∀ (δ : Tms Δ (Γ ▷ t >eq b)) → Tm~ rfl~ 𝔹[] (t [ π₁eq δ ]) ⌜ b ⌝𝔹

,eq⨾-helper : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹 
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
  ε     : Tms~ Δ~ rfl~ ε ε
  _,_   : ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Tm~ Δ~ (A~ [ δ~ ]) t₁ t₂
        → Tms~ Δ~ (Γ~ ▷ A~) (δ₁ , t₁) (δ₂ , t₂)
  ,eq~  : ∀ {Δ~ : Ctx~ Δ₁ Δ₂} (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
            {t₁~ : Tm~ rfl~ _ _ ⌜ b ⌝𝔹}            
        → Tms~ Δ~ (Γ~ ▷ t~ >eq) (δ₁ ,eq t₁~) (δ₂ ,eq t₂~) 
  
  id   : Tms~ Γ~ Γ~ id id
  _⨾_  : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ Θ~ Δ~ σ₁ σ₂ → Tms~ Θ~ Γ~ (δ₁ ⨾ σ₁) (δ₂ ⨾ σ₂)
  
  π₁   : ∀ (A~ : Ty~ Γ~ A₁ A₂) → Tms~ Δ~ (Γ~ ▷ A~) δ₁ δ₂ 
       → Tms~ Δ~ Γ~ (π₁ δ₁) (π₁ δ₂)
  π₁eq : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂)
       → Tms~ Δ~ (Γ~ ▷ t~ >eq) δ₁ δ₂ → Tms~ Δ~ Γ~ (π₁eq δ₁) (π₁eq δ₂)

  -- Computation
  εη   : Tms~ rfl~ rfl~ δ ε
  ,η   : Tms~ rfl~ rfl~ δ (π₁ δ , π₂ δ)
  ,eqη : Tms~ rfl~ rfl~ (π₁eq δ ,eq π₂eq′ {b = b} δ) δ

  π₁,   : Tms~ rfl~ rfl~ (π₁ (δ , t)) δ
  π₁eq, : ∀ {δ : Tms Δ Γ} {t~ : Tm~ _ _ (t [ δ ]) ⌜ b ⌝𝔹} 
        → Tms~ rfl~ rfl~ (π₁eq (δ ,eq t~)) δ

  π₁⨾   : Tms~ rfl~ rfl~ (π₁ (δ ⨾ σ)) (π₁ δ ⨾ σ)
  π₁eq⨾ : Tms~ rfl~ rfl~ (π₁eq (δ ⨾ σ)) (π₁eq δ ⨾ σ)

  id⨾ : Tms~ rfl~ rfl~ (id ⨾ δ) δ
  ⨾id : Tms~ rfl~ rfl~ (δ ⨾ id) δ
  ⨾⨾  : Tms~ rfl~ rfl~ ((δ ⨾ σ) ⨾ γ) (δ ⨾ (σ ⨾ γ))

  ,⨾   : Tms~ rfl~ rfl~ ((δ , t) ⨾ σ) ((δ ⨾ σ) , (coe~ rfl~ [][] (t [ σ ])))
  ,eq⨾ : ∀ {δ : Tms Δ Γ} {σ : Tms Θ Δ} {t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹} 
       → Tms~ rfl~ rfl~ ((δ ,eq t~) ⨾ σ) ((δ ⨾ σ) ,eq ,eq⨾-helper t~)

_^eq_ : ∀ (δ : Tms Δ Γ) t 
      → Tms (Δ ▷ coe~ rfl~ 𝔹[] (t [ δ ]) >eq b) (Γ ▷ t >eq b)

⌜⌝𝔹 : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 (⌜ b ⌝𝔹) (⌜ b ⌝𝔹)
⌜⌝𝔹[] : Tm~ rfl~ 𝔹[] (⌜ b ⌝𝔹 [ δ ]) (⌜ b ⌝𝔹)

wk<>eq : Ty~ (rfl~ {Γ = Γ}) (A [ π₁eq id ] [ id ,eq (⌜⌝𝔹[] {b = b}) ]) A
wk<>eq = [][] ∙~ rfl~ [ sym~ π₁eq⨾ ∙~ π₁eq (⌜⌝𝔹 rfl~) id⨾ ∙~ π₁eq, ] ∙~ [id]

wk^eq : Ty~ rfl~ (A [ π₁eq {b = b} id ] [ δ ^eq t ]) (A [ δ ] [ π₁eq id ])

-- foo : Ty~ (rfl~ {Γ = Γ}) (A [ π₁eq id ] [ δ ^eq t ]) (A [ δ ] [ π₁eq id ])
-- foo = [][] Ty~.∙~ rfl~ [ sym~ π₁eq⨾ ∙~ π₁eq {!⌜⌝𝔹 rfl~!} id⨾ ∙~ π₁eq, ]

data Tm~ where
  -- Equivalence
  rfl~ : Tm~ rfl~ rfl~ t t
  sym~ : Tm~ Γ~ A~ t₁ t₂ → Tm~ (sym~ Γ~) (sym~ A~) t₂ t₁
  _∙~_ : Tm~ Γ₁₂~ A₁₂~ t₁ t₂ → Tm~ Γ₂₃~ A₂₃~ t₂ t₃ 
       → Tm~ (Γ₁₂~ ∙~ Γ₂₃~) (A₁₂~ ∙~ A₂₃~) t₁ t₃

  -- Coherence
  coh  : Tm~ Γ~ A~ t (coe~ Γ~ A~ t)

  --Congruence  
  ƛ_   : Tm~ (Γ~ ▷ A~) B~ t₁ t₂ → Tm~ Γ~ (Π A~ B~) (ƛ t₁) (ƛ t₂)
  ƛ⁻¹_ : Tm~ Γ~ (Π A~ B~) t₁ t₂ → Tm~ (Γ~ ▷ A~) B~ (ƛ⁻¹ t₁) (ƛ⁻¹ t₂)
  TT   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 TT TT
  FF   : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 FF FF
  if   : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂) 
       → Tm~ (Γ~ ▷ t~ >eq) (A~ [ π₁eq t~ id ]) u₁ u₂
       → Tm~ (Γ~ ▷ t~ >eq) (A~ [ π₁eq t~ id ]) v₁ v₂
       → Tm~ Γ~ A~ (if t₁ u₁ v₁) (if t₂ u₂ v₂)
    
  _[_] : Tm~ Γ~ A~ t₁ t₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ δ~ ]) (t₁ [ δ₁ ]) (t₂ [ δ₂ ]) 
  π₂   : ∀ (δ~ : Tms~ Δ~ (Γ~ ▷ A~) δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ π₁ A~ δ~ ]) (π₂ δ₁) (π₂ δ₂) 

  -- Projection
  π₂eq : ∀ (δ : Tms Δ (Γ ▷ t >eq b)) → Tm~ rfl~ 𝔹[] (t [ π₁eq δ ]) ⌜ b ⌝𝔹

  -- Computation
  ƛ[]   : Tm~ rfl~ Π[] ((ƛ t) [ δ ]) (ƛ (t [ δ ^ A ]))
  TT[]  : Tm~ rfl~ 𝔹[] (TT [ δ ]) TT
  FF[]  : Tm~ rfl~ 𝔹[] (FF [ δ ]) FF
  if[]  : Tm~ rfl~ rfl~ (if t u v [ δ ]) 
                        (if (coe~ rfl~ 𝔹[] (t [ δ ])) 
                        (coe~ rfl~ wk^eq (u [ δ ^eq t ])) 
                        (coe~ rfl~ wk^eq (v [ δ ^eq t ])))

  [id] : Tm~ rfl~ [id] (t [ id ]) t
  [][] : Tm~ rfl~ [][] (t [ δ ] [ σ ]) (t [ δ ⨾ σ ])

  𝔹β₁ : Tm~ rfl~ (sym~ wk<>eq) (if TT u v) (u [ id ,eq TT[] ])
  𝔹β₂ : Tm~ rfl~ (sym~ wk<>eq) (if FF u v) (v [ id ,eq FF[] ])

  Πβ : Tm~ rfl~ rfl~ (ƛ⁻¹ ƛ t) t
  Πη : Tm~ rfl~ rfl~ (ƛ ƛ⁻¹ t) t

  π₂, : Tm~ rfl~ (rfl~ [ π₁, ]) (π₂ (δ , t)) t

  -- Note this is what we would expect from |π₂[]|, but reversed
  π₂⨾ : Tm~ rfl~ (rfl~ [ π₁⨾ ] ∙~ sym~ {Γ~ = Γ~} [][]) (π₂ (δ ⨾ σ)) (π₂ δ [ σ ])

⌜⌝𝔹 {b = true}  = TT
⌜⌝𝔹 {b = false} = FF

⌜⌝𝔹[] {b = true}  = TT[]
⌜⌝𝔹[] {b = false} = FF[]

,eq⨾-helper t~ 
  =  sym~ {Γ~ = rfl~} [][] ∙~ (t~ [ rfl~ ]) ∙~ ⌜⌝𝔹[]
  
π₂eq′ = π₂eq

δ ^eq t = (δ ⁺eq _) ,eq (sym~ [][] ∙~ coh [ rfl~ ] ∙~ π₂eq id)

wk^eq = [][] ∙~ rfl~ [ sym~ π₁eq⨾ ∙~ π₁eq rfl~ id⨾ ∙~ π₁eq, ] ∙~ sym~ [][]

coeTm~ : Tm~ Γ~ A~ t₁ t₂ 
       → Tm~ (sym~ Γ₁~ ∙~ Γ~ ∙~ Γ₂~) (sym~ A₁~ ∙~ A~ ∙~ A₂~) 
             (coe~ Γ₁~ A₁~ t₁) (coe~ Γ₂~ A₂~ t₂)
coeTm~ t~ = sym~ coh ∙~ t~ ∙~ coh

-- We derive the substitution law for |ƛ⁻¹| as in 
-- https://people.cs.nott.ac.uk/psztxa/publ/tt-in-tt.pdf
ƛ⁻¹[] : Tm~ rfl~ rfl~ ((ƛ⁻¹ t) [ δ ^ A ]) (ƛ⁻¹ (coe~ rfl~ Π[] (t [ δ ])))
ƛ⁻¹[] =  sym~ Πβ ∙~ ƛ⁻¹_ {A~ = rfl~} {B~ = rfl~} (coh {A~ = rfl~} 
      ∙~ coeTm~ (sym~ ƛ[] ∙~ Πη [ rfl~ ]))

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
                  (t₁ [ π₁eq id ])
                  (coe~ (sym~ Γ~) (sym~ A~) t₂ [ π₁eq id ])) 
              t₁ 
    if~t₁ =  𝔹β₁ ∙~ [][] ∙~ rfl~ [ sym~ π₁eq⨾ ∙~ π₁eq (TT rfl~) id⨾ ∙~ π₁eq, ] 
          ∙~ [id]
    if~if : Tm~ Γ~ A~
              (if TT 
                  (t₁ [ π₁eq id ])
                  (coe~ (sym~ Γ~) (sym~ A~) t₂ [ π₁eq id ])) 
              (if FF 
                  (coe~ Γ~ A~ t₁ [ π₁eq id ])
                  (t₂ [ π₁eq id ]))
    if~if = if TF~′ (coh [ π₁eq TF~′ id ]) (sym~ coh [ π₁eq TF~′ id ])
    if~t₂ : Tm~ rfl~ rfl~ 
              (if FF 
                  (coe~ Γ~ A~ t₁ [ π₁eq id ])
                  (t₂ [ π₁eq id ])) 
              t₂
    if~t₂ =  𝔹β₂ ∙~ [][] ∙~ rfl~ [ sym~ π₁eq⨾ ∙~ π₁eq (FF rfl~) id⨾ ∙~ π₁eq, ] 
          ∙~ [id]

eq : Tm~ (rfl~ {Γ = Γ ▷ t >eq b}) 𝔹[] (t [ π₁eq id ]) ⌜ b ⌝𝔹
eq = π₂eq id
