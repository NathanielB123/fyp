{-# OPTIONS --prop --show-irrelevant #-}

open import Utils

-- For "true" SCDef (i.e. the theory which I aim to prove normalisation for)
-- we need a bunch of side-conditions ensuring that the LHSs of rewrites do not
-- overlap (no critical pairs).
--
-- These side conditions are an absolute nightmare in Agda, so I have elided
-- them.
module Dependent.SCDef.Syntax where

infixr 4 _∙~_

-- In an ordinary CwF, the objects are contexts and the morphisms are 
-- substitutions
-- In SCDef, we have to worry two categories - that of signature weakenings
-- (objects are signatures) and substitutions (objects are paired-up signatures 
-- and contexts)
data Sig : Set
data Ctx  : Sig → Set

variable
  Ψ Φ Ξ Ψ₁ Ψ₂ Ψ₃ Φ₁ Φ₂ Φ₃ : Sig
  
data Ty : Ctx Ψ → Set
data Tm : ∀ (Γ : Ctx Ψ) → Ty Γ → Set
data Wk : Sig → Sig → Set
data Tms : Ctx Φ → Ctx Ψ → Set

variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx Ψ
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  φ ψ ξ ξ₁ ξ₂ ξ₃ : Wk Φ Ψ
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Tms Δ Γ
  b b₁ b₂ : Bool

-- We don't define conversion for signatures only because it simply isn't 
-- necessary (a truly faithful translation of a QIIT-based definition would
-- include it though)
--
-- We also don't explicitly define equivalence of weakenings. We consider all
-- weakenings that map between equal signatures to be equal. 
data Ctx~ : Ctx Ψ → Ctx Ψ → Prop
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
  •       : Ctx Ψ
  _▷_     : ∀ (Γ : Ctx Ψ) → Ty Γ → Ctx Ψ
  _▷_>eq_ : ∀ (Γ : Ctx Ψ) → Tm Γ 𝔹′ → Bool → Ctx Ψ

  _[_]    : Ctx Ψ → Wk Φ Ψ → Ctx Φ

data Ty where
  coe~ : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂

  𝔹   : Ty Γ   
  Π   : ∀ A → Ty (Γ ▷ A) → Ty Γ

  if    : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ
  _[_]  : Ty Γ → Tms Δ Γ → Ty Δ
  
𝔹′ = 𝔹

𝔹~′ : Ty~ Γ~ 𝔹′ 𝔹′
⌜_⌝𝔹 : Bool → Tm Γ 𝔹
_[_]′ : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])
rflCtx′ : Ctx~ Γ Γ
𝔹[]′ : Ty~ rflCtx′ (𝔹 [ δ ]) 𝔹

wkeq : Tms (Γ ▷ t >eq b) Γ

data Sig where
  •                  : Sig
  _▷_⇒_if_≔_∣_ : ∀ Ψ (Γ : Ctx Ψ) A → (t : Tm Γ 𝔹′) 
               → Tm (Γ ▷ t >eq true) (A [ wkeq ]) 
               → Tm (Γ ▷ t >eq false) (A [ wkeq ])
               → Sig

data Wk where
  id  : Wk Ψ Ψ
  _⨾_ : Wk Φ Ψ → Wk Ξ Φ → Wk Ξ Ψ
  wk𝒮 : Wk (Ψ ▷ Γ ⇒ A if t ≔ u ∣ v) Ψ

data Tms where
  coe~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂

  ε     : Tms {Φ = Ψ} {Ψ = Ψ} Δ •
  _,_   : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]) → Tms Δ (Γ ▷ A) 
  -- We do some Fording here to enforce that |t [ δ ]| is considered a 
  -- structural subterm.
  ,eqℱ : ∀ (δ : Tms Δ Γ) {u} → t [ δ ]′ ≡ u
         → Tm~ rflCtx′ 𝔹[]′ (t [ δ ]′) ⌜ b ⌝𝔹
         → Tms Δ (Γ ▷ t >eq b)
  
  id   : Tms {Ψ = Ψ} Γ Γ
  _⨾_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  
  wk𝒮  : Tms (Γ [ wk𝒮 {t = t} {u = u} {v = v} ]) Γ

  π₁   : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₁eq : Tms Δ (Γ ▷ t >eq b) → Tms Δ Γ

pattern _,eq_ δ t~ = ,eqℱ δ refl t~ 

data Tm where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂
  
  ƛ_   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  ƛ⁻¹_ : Tm Γ (Π A B) → Tm (Γ ▷ A) B

  TT : Tm Γ 𝔹
  FF : Tm Γ 𝔹
  
  call : Tm {Ψ = Ψ ▷ Γ ⇒ A if t ≔ u ∣ v} (Γ [ wk𝒮 ]) (A [ wk𝒮 ])

  π₂   : ∀ (δ : Tms Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ])
  _[_] : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])

⌜ true  ⌝𝔹 = TT
⌜ false ⌝𝔹 = FF

_[_]′ = _[_]

wk : Tms (Γ ▷ A) Γ
wk   = π₁ id
wkeq = π₁eq id

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ ▷ A) Γ
δ ⁺ A = δ ⨾ wk

_⁺eq_ : Tms Δ Γ → ∀ t → Tms (Δ ▷ t >eq b) Γ
δ ⁺eq t = δ ⨾ wkeq

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ ▷ (A [ δ ])) (Γ ▷ A)

-- Substitutions embed signature weakenings
⌜_⌝𝒮 : ∀ (δ : Wk Φ Ψ) → Tms (Γ [ δ ]) Γ

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  _▷_    : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ ▷ A₁) (Γ₂ ▷ A₂)
  _▷_>eq : ∀ Γ~ → Tm~ Γ~ 𝔹~′ t₁ t₂ → Ctx~ (Γ₁ ▷ t₁ >eq b) (Γ₂ ▷ t₂ >eq b)

  -- All weakenings are convertible
  _[] : Ctx~ Γ₁ Γ₂ → Ctx~ (Γ₁ [ ξ₁ ]) (Γ₂ [ ξ₂ ])  

  -- Computation
  •[]     : Ctx~ (• [ ξ ]) •
  ▷[]ℱ    : ∀ {⌜ξ⌝ : Tms _ Γ} → ⌜ ξ ⌝𝒮 ≡ ⌜ξ⌝
          → Ctx~ ((Γ ▷ A) [ ξ ])
                 ((Γ [ ξ ]) ▷ (A [ ⌜ ξ ⌝𝒮 ]))
  ▷>eq[] : Ctx~ ((Γ ▷ t >eq b) [ ξ ]) 
                ((Γ [ ξ ]) ▷ (coe~ rfl~ 𝔹[]′ (t [ ⌜ ξ ⌝𝒮 ] )) >eq b) 
  
  [id] : Ctx~ (Γ [ id ]) Γ
  [][] : Ctx~ (Γ [ φ ] [ ψ ]) (Γ [ φ ⨾ ψ ])

pattern ▷[] = ▷[]ℱ refl

rflCtx′ = rfl~

⌜ id    ⌝𝒮 = coe~ (sym~ [id]) rfl~ id
⌜ δ ⨾ σ ⌝𝒮 = coe~ [][] rfl~ (⌜ δ ⌝𝒮 ⨾ ⌜ σ ⌝𝒮)
⌜ wk𝒮   ⌝𝒮 = wk𝒮

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

𝔹~′ = 𝔹
𝔹[]′ = 𝔹[]

δ ^ A = (δ ⁺ _) , (coe~ rfl~ [][] (π₂ id))

_·_ : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ id , coe~ rfl~ (sym~ [id]) u ])
t · u = (ƛ⁻¹ t) [ id , coe~ rfl~ (sym~ [id]) u ]

,eq⨾-helper : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹 
            → Tm~ rfl~ 𝔹[]′ (t [ δ ⨾ σ ]′) ⌜ b ⌝𝔹

π₂eq′ : ∀ (δ : Tms Δ (Γ ▷ t >eq b)) → Tm~ rfl~ 𝔹[] (t [ π₁eq δ ]) ⌜ b ⌝𝔹

data Tms~ where
  -- Equivalence
  rfl~ : Tms~ rfl~ rfl~ δ δ
  sym~ : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ (sym~ Δ~) (sym~ Γ~) δ₂ δ₁
  _∙~_ : Tms~ Δ₁₂~ Γ₁₂~ δ₁ δ₂ → Tms~ Δ₂₃~ Γ₂₃~ δ₂ δ₃
       → Tms~ (Δ₁₂~ ∙~ Δ₂₃~) (Γ₁₂~ ∙~ Γ₂₃~) δ₁ δ₃

  -- Coherence
  coh  : Tms~ Δ~ Γ~ δ (coe~ Δ~ Γ~ δ)

  -- Congruence
  ε     : Tms~ Δ~ rfl~ (ε {Ψ = Ψ}) ε
  _,_   : ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) → Tm~ Δ~ (A~ [ δ~ ]) t₁ t₂
        → Tms~ Δ~ (Γ~ ▷ A~) (δ₁ , t₁) (δ₂ , t₂)
  ,eq~  : ∀ {Δ~ : Ctx~ {Ψ = Ψ} Δ₁ Δ₂} (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
            {t₁~ : Tm~ rfl~ _ _ ⌜ b ⌝𝔹}            
        → Tms~ Δ~ (Γ~ ▷ t~ >eq) (δ₁ ,eq t₁~) (δ₂ ,eq t₂~) 
  
  id   : Tms~ Γ~ Γ~ id id
  _⨾_  : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ Θ~ Δ~ σ₁ σ₂ → Tms~ Θ~ Γ~ (δ₁ ⨾ σ₁) (δ₂ ⨾ σ₂)
  
  π₁   : ∀ (A~ : Ty~ Γ~ A₁ A₂) → Tms~ Δ~ (Γ~ ▷ A~) δ₁ δ₂ 
       → Tms~ Δ~ Γ~ (π₁ δ₁) (π₁ δ₂)
  π₁eq : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂)
       → Tms~ Δ~ (Γ~ ▷ t~ >eq) δ₁ δ₂ → Tms~ Δ~ Γ~ (π₁eq δ₁) (π₁eq δ₂)

  wk𝒮 : Tms~ (Γ~ []) Γ~ (wk𝒮 {t = t} {u = u} {v = v}) wk𝒮

  -- Computation
  εη   : Tms~ rfl~ rfl~ δ ε
  ,η   : Tms~ rfl~ rfl~ δ (π₁ δ , π₂ δ)
  ,eqη : Tms~ rfl~ rfl~ (π₁eq δ ,eq π₂eq′ {b = b} δ) δ

  π₁,   : Tms~ rfl~ rfl~ (π₁ (δ , t)) δ
  π₁eq, : ∀ {δ : Tms {Φ = Φ} {Ψ = Ψ} Δ Γ} {t~ : Tm~ _ _ (t [ δ ]) ⌜ b ⌝𝔹} 
        → Tms~ rfl~ rfl~ (π₁eq (δ ,eq t~)) δ

  π₁⨾   : Tms~ rfl~ rfl~ (π₁ (δ ⨾ σ)) (π₁ δ ⨾ σ)
  π₁eq⨾ : Tms~ rfl~ rfl~ (π₁eq (δ ⨾ σ)) (π₁eq δ ⨾ σ)

  id⨾ : Tms~ rfl~ rfl~ (id ⨾ δ) δ
  ⨾id : Tms~ rfl~ rfl~ (δ ⨾ id) δ
  ⨾⨾  : Tms~ rfl~ rfl~ ((δ ⨾ σ) ⨾ γ) (δ ⨾ (σ ⨾ γ))

  wk⨾π₁   : Tms~ rfl~ rfl~ (wk𝒮 ⨾ π₁ δ) (π₁ (wk𝒮 ⨾ coe~ rfl~ (sym~ ▷[]) δ))
  wk⨾π₁eq : Tms~ rfl~ rfl~ (wk𝒮 ⨾ π₁eq δ) 
                           (π₁eq (wk𝒮 ⨾ coe~ rfl~ (sym~ ▷>eq[]) δ))

  ,⨾   : Tms~ rfl~ rfl~ ((δ , t) ⨾ σ) ((δ ⨾ σ) , (coe~ rfl~ [][] (t [ σ ])))
  ,eq⨾ : {σ : Tms {Φ = Φ} {Ψ = Ψ} Θ Δ} {t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹} 
       → Tms~ rfl~ rfl~ ((δ ,eq t~) ⨾ σ) ((δ ⨾ σ) ,eq ,eq⨾-helper t~)

rflTm′ : Tm~ rfl~ rfl~ t t

wk-comm : Tms~ (▷>eq[] {t = t} {b = b}) rfl~ 
               (π₁eq id ⨾ wk𝒮 {t = u₁} {u = u₂} {v = u₃}) 
               (wk𝒮 ⨾ π₁eq id)
wk-comm =  sym~ π₁eq⨾ ∙~ (π₁eq rflTm′ (id⨾ ∙~ coh {Δ~ = ▷>eq[]} {Γ~ = rfl~} 
        ∙~ sym~ ⨾id ∙~ sym~ coh ⨾ coh)) ∙~ sym~ wk⨾π₁eq

⌜⌝𝔹 : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 (⌜ b ⌝𝔹) (⌜ b ⌝𝔹)
⌜⌝𝔹[] : Tm~ rfl~ 𝔹[] (⌜ b ⌝𝔹 [ δ ]) (⌜ b ⌝𝔹)

wk<>eq : Tms~ rfl~ rfl~ (π₁eq id ⨾ (δ ,eq t~)) δ
wk<>eq = sym~ π₁eq⨾ ∙~ π₁eq rflTm′ id⨾ ∙~ π₁eq,

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
  
  _[_] : Tm~ Γ~ A~ t₁ t₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ δ~ ]) (t₁ [ δ₁ ]) (t₂ [ δ₂ ]) 
  π₂   : ∀ (δ~ : Tms~ Δ~ (Γ~ ▷ A~) δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ π₁ A~ δ~ ]) (π₂ δ₁) (π₂ δ₂) 

  -- Projection
  π₂eq : ∀ (δ : Tms Δ (Γ ▷ t >eq b)) → Tm~ rfl~ 𝔹[] (t [ π₁eq δ ]) ⌜ b ⌝𝔹

  -- Computation
  ƛ[]    : Tm~ rfl~ Π[] ((ƛ t) [ δ ]) (ƛ (t [ δ ^ A ]))
  TT[]   : Tm~ rfl~ 𝔹[] (TT [ δ ]) TT
  FF[]   : Tm~ rfl~ 𝔹[] (FF [ δ ]) FF
  
  [id] : Tm~ rfl~ [id] (t [ id ]) t
  [][] : Tm~ rfl~ [][] (t [ δ ] [ σ ]) (t [ δ ⨾ σ ])


  -- Calls to definitions reduce exactly when the neutral they block on
  -- reduces to a closed Boolean
  callTT : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ wk𝒮 ⨾ δ ]) TT)
         → Tm~ rfl~ ([][] ∙~ rfl~ [  rfl~ ⨾ sym~ wk<>eq ∙~ sym~ ⨾⨾ 
                          ∙~ sym~ wk-comm ⨾ coh ∙~ ⨾⨾ ] 
                          ∙~ sym~ [][])
               (call {t = t} {u = u} [ δ ])
               (u [ wk𝒮 ⨾ coe~ rfl~ (sym~ (▷>eq[] {b = true})) 
                                (δ ,eq (sym~ coh [ rfl~ ] ∙~ [][] ∙~ t~)) ])
  callFF : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ wk𝒮 ⨾ δ ]) FF)
         → Tm~ rfl~ ([][] ∙~ rfl~ [  rfl~ ⨾ sym~ wk<>eq ∙~ sym~ ⨾⨾ 
                          ∙~ sym~ wk-comm ⨾ coh ∙~ ⨾⨾ ] 
                          ∙~ sym~ [][])
               (call {t = t} {v = v} [ δ ])
               (v [ wk𝒮 ⨾ coe~ rfl~ (sym~ (▷>eq[] {b = false})) 
                                (δ ,eq (sym~ coh [ rfl~ ] ∙~ [][] ∙~ t~)) ])

  β : Tm~ rfl~ rfl~ (ƛ⁻¹ ƛ t) t
  η : Tm~ rfl~ rfl~ (ƛ ƛ⁻¹ t) t

  π₂, : Tm~ rfl~ (rfl~ [ π₁, ]) (π₂ (δ , t)) t

  -- Note this is what we would expect from |π₂[]|, but reversed
  π₂⨾ : Tm~ rfl~ (rfl~ [ π₁⨾ ] ∙~ sym~ {Γ~ = Γ~} [][]) (π₂ (δ ⨾ σ)) (π₂ δ [ σ ])

rflTm′ = rfl~

⌜⌝𝔹 {b = true}  = TT
⌜⌝𝔹 {b = false} = FF

⌜⌝𝔹[] {b = true}  = TT[]
⌜⌝𝔹[] {b = false} = FF[]

,eq⨾-helper t~ 
  =  sym~ {Γ~ = rfl~} [][] ∙~ (t~ [ rfl~ ]) ∙~ ⌜⌝𝔹[]
  
π₂eq′ = π₂eq

coeTm~ : Tm~ Γ~ A~ t₁ t₂ 
       → Tm~ (sym~ Γ₁~ ∙~ Γ~ ∙~ Γ₂~) (sym~ A₁~ ∙~ A~ ∙~ A₂~) 
             (coe~ Γ₁~ A₁~ t₁) (coe~ Γ₂~ A₂~ t₂)
coeTm~ t~ = sym~ coh ∙~ t~ ∙~ coh

-- We derive the substitution law for |ƛ⁻¹| as in 
-- https://people.cs.nott.ac.uk/psztxa/publ/tt-in-tt.pdf
ƛ⁻¹[] : Tm~ rfl~ rfl~ ((ƛ⁻¹ t) [ δ ^ A ]) (ƛ⁻¹ (coe~ rfl~ Π[] (t [ δ ])))
ƛ⁻¹[] =  sym~ β ∙~ ƛ⁻¹_ {A~ = rfl~} {B~ = rfl~} (coh {A~ = rfl~} 
      ∙~ coeTm~ (sym~ ƛ[] ∙~ η [ rfl~ ]))
 