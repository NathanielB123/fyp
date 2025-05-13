{-# OPTIONS --prop --show-irrelevant --safe #-}

open import Utils

module Dependent.SCDef.Syntax where

infixr 4 _∙~_

-- Substitutions can be restricted to only signature mappings if necessary
data SubSort : Set where
  SIG CTX : SubSort


data Sig : Set
data Ctx  : Sig → Set

obj : SubSort → Set
obj SIG = Sig
obj CTX = Σ Sig Ctx

data Sub[_] : ∀ q → obj q → obj q → Set

variable
  q : SubSort
  -- Heavily relies on definitional injectivity
  Ψ Φ Ξ Ψ₁ Ψ₂ Ψ₃ Φ₁ Φ₂ Φ₃ : obj q
  
Tms : Ctx Φ → Ctx Ψ → Set
Tms Δ Γ = Sub[ CTX ] (_ Σ, Δ) (_ Σ, Γ)

Wk : Sig → Sig → Set
Wk = Sub[ SIG ]

data Ty : Ctx Ψ → Set
data Tm : ∀ (Γ : Ctx Ψ) → Ty Γ → Set

variable
  Γ Δ Θ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : Ctx Ψ
  A B C A₁ A₂ A₃ B₁ B₂ : Ty Γ
  t u v t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm Γ A
  δ σ γ δ₁ δ₂ δ₃ σ₁ σ₂ : Sub[ q ] Φ Ψ
  b b₁ b₂ : Bool

-- We don't define conversion for signatures only because it simply isn't 
-- necessary (a truly faithful translation of a QIIT-based definition would
-- include it though)
data Ctx~ : Ctx Ψ → Ctx Ψ → Prop
data Ty~  : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂ → Prop
data Tm~  : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Prop
data Wk~ : Wk Φ Ψ → Wk Φ Ψ → Prop
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
  ε       : Ctx Ψ
  _,_     : ∀ (Γ : Ctx Ψ) → Ty Γ → Ctx Ψ
  _,_>rw_ : ∀ (Γ : Ctx Ψ) → Tm Γ 𝔹′ → Bool → Ctx Ψ

  _[_]    : Ctx Ψ → Wk Φ Ψ → Ctx Φ

data Ty where
  coe~ : Ctx~ Γ₁ Γ₂ → Ty Γ₁ → Ty Γ₂

  𝔹   : Ty Γ   
  Π   : ∀ A → Ty (Γ , A) → Ty Γ

  if    : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ
  _[_]  : Ty Γ → Tms Δ Γ → Ty Δ
  
𝔹′ = 𝔹

𝔹~′ : Ty~ Γ~ 𝔹′ 𝔹′
⌜_⌝𝔹 : Bool → Tm Γ 𝔹
_[_]′ : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])
rflCtx′ : Ctx~ Γ Γ
𝔹[]′ : Ty~ rflCtx′ (𝔹 [ δ ]) 𝔹

id′ : Wk Ψ Ψ

wkrw : Tms (Γ , t >rw b) Γ

data Sig where
  ε                   : Sig
  _,def_⇒_if_then_else_ : ∀ Ψ (Γ : Ctx Ψ) A → (t : Tm Γ 𝔹′) 
                        → Tm (Γ , t >rw true) (A [ wkrw ]) 
                        → Tm (Γ , t >rw false) (A [ wkrw ])
                        → Sig

sig[_] : ∀ q → obj q → Sig
sig[ SIG ] Ψ        = Ψ
sig[ CTX ] (Ψ Σ, Γ) = Ψ

adddef[_]_,_⇒_if_then_else_ : ∀ q Ψ (Γ : Ctx (sig[ q ] Ψ)) A → (t : Tm Γ 𝔹′) 
                            → Tm (Γ , t >rw true) (A [ wkrw ]) 
                            → Tm (Γ , t >rw false) (A [ wkrw ])
                            → obj q

data Sub[_] where
  coe~ : Ctx~ Δ₁ Δ₂ → Ctx~ Γ₁ Γ₂ → Tms Δ₁ Γ₁ → Tms Δ₂ Γ₂

  -- If we want to carve out a subset of |Tms| that avoids needing to deal with
  -- adding rewrites to the context, we can combine |ε| and |id| into:
  -- > ε : ∀ 𝒯 → Tms (Γ ++ 𝒯) Γ
  -- And remove |π₁rw|

  ε     : Tms {Ψ = Ψ} Δ ε
  _,_   : ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ]) → Tms Δ (Γ , A) 
  -- We do some Fording here to enforce that |t [ δ ]| is considered a 
  -- structural subterm.
  ,rwℱ : ∀ (δ : Tms Δ Γ) {u} → t [ δ ]′ ≡ u
         → Tm~ rflCtx′ 𝔹[]′ (t [ δ ]′) ⌜ b ⌝𝔹
         → Tms Δ (Γ , t >rw b)
  
  id   : Sub[ q ] Ψ Ψ
  _⨾_  : Sub[ q ] Φ Ψ → Sub[ q ] Ξ Φ → Sub[ q ] Ξ Ψ
  
  wk𝒮  : Sub[ q ] (adddef[ q ] Ψ , Γ ⇒ A if t then u else v) Ψ

  π₁   : Tms Δ (Γ , A) → Tms Δ Γ
  π₁rw : Tms Δ (Γ , t >rw b) → Tms Δ Γ

pattern _,rw_ δ t~ = ,rwℱ δ refl t~ 

id′ = id

adddef[ SIG ] Ψ        , Δ ⇒ A if t then u else v 
  = Ψ ,def Δ ⇒ A if t then u else v
adddef[ CTX ] (Ψ Σ, Γ) , Δ ⇒ A if t then u else v 
  = Ψ ,def Δ ⇒ A if t then u else v Σ, Γ [ wk𝒮 ]

data Tm where
  coe~ : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂
  
  ƛ_   : Tm (Γ , A) B → Tm Γ (Π A B)
  ƛ⁻¹_ : Tm Γ (Π A B) → Tm (Γ , A) B

  TT : Tm Γ 𝔹
  FF : Tm Γ 𝔹
  
  call : (δ : Tms {Ψ = Ψ ,def Δ ⇒ A if t then u else v} Γ (Δ [ wk𝒮 ])) 
       → Tm Γ (A [ wk𝒮 ⨾ δ ])

  π₂   : ∀ (δ : Tms Δ (Γ , A)) → Tm Δ (A [ π₁ δ ])
  _[_] : Tm Γ A → ∀ (δ : Tms Δ Γ) → Tm Δ (A [ δ ])

⌜ true  ⌝𝔹 = TT
⌜ false ⌝𝔹 = FF

_[_]′ = _[_]

wk : Tms (Γ , A) Γ
wk   = π₁ id
wkrw = π₁rw id

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ , A) Γ
δ ⁺ A = δ ⨾ wk

_⁺rw_ : Tms Δ Γ → ∀ t → Tms (Δ , t >rw b) Γ
δ ⁺rw t = δ ⨾ wkrw

_^_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ , (A [ δ ])) (Γ , A)

-- Substitutions embed signature weakenings
⌜_⌝𝒮 : ∀ (δ : Wk Φ Ψ) → Tms (Γ [ δ ]) Γ

data Ctx~ where
  -- Equivalence
  rfl~ : Ctx~ Γ Γ
  sym~ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₁
  _∙~_ : Ctx~ Γ₁ Γ₂ → Ctx~ Γ₂ Γ₃ → Ctx~ Γ₁ Γ₃

  -- Congruence
  _,_    : ∀ Γ~ → Ty~ Γ~ A₁ A₂ → Ctx~ (Γ₁ , A₁) (Γ₂ , A₂)
  _,_>rw : ∀ Γ~ → Tm~ Γ~ 𝔹~′ t₁ t₂ → Ctx~ (Γ₁ , t₁ >rw b) (Γ₂ , t₂ >rw b)

  _[_] : Ctx~ Γ₁ Γ₂ → Wk~ δ₁ δ₂ → Ctx~ (Γ₁ [ δ₁ ]) (Γ₂ [ δ₂ ])  

  -- Computation
  ε[]    : Ctx~ (ε [ δ ]) ε
  ,[]    : Ctx~ ((Γ , A) [ δ ])
                ((Γ [ δ ]) , (A [ ⌜ δ ⌝𝒮 ]))
  ,>rw[] : Ctx~ ((Γ , t >rw b) [ δ ]) 
                ((Γ [ δ ]) , (coe~ rfl~ 𝔹[]′ (t [ ⌜ δ ⌝𝒮 ] )) >rw b) 
  
  [id] : Ctx~ (Γ [ id ]) Γ
  [][] : Ctx~ (Γ [ δ ] [ σ ]) (Γ [ δ ⨾ σ ])

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

𝔹~′ = 𝔹
𝔹[]′ = 𝔹[]

δ ^ A = (δ ⁺ _) , (coe~ rfl~ [][] (π₂ id))

_·_ : Tm Γ (Π A B) → ∀ (u : Tm Γ A) → Tm Γ (B [ id , coe~ rfl~ (sym~ [id]) u ])
t · u = (ƛ⁻¹ t) [ id , coe~ rfl~ (sym~ [id]) u ]

,rw⨾-helper : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹 
            → Tm~ rfl~ 𝔹[]′ (t [ δ ⨾ σ ]′) ⌜ b ⌝𝔹

data Wk~ where
  rfl~ : Wk~ δ δ
  sym~ : Wk~ δ₁ δ₂ → Wk~ δ₂ δ₁
  _∙~_ : Wk~ δ₁ δ₂ → Wk~ δ₂ δ₃ → Wk~ δ₁ δ₃

  ⨾⨾  : Wk~ (δ ⨾ (σ ⨾ γ)) ((δ ⨾ σ) ⨾ γ)
  id⨾ : Wk~ (id ⨾ δ) δ
  ⨾id : Wk~ (δ ⨾ id) δ

π₂rw′ : ∀ (δ : Tms Δ (Γ , t >rw b)) → Tm~ rfl~ 𝔹[] (t [ π₁rw δ ]) ⌜ b ⌝𝔹

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
        → Tms~ Δ~ (Γ~ , A~) (δ₁ , t₁) (δ₂ , t₂)
  ,rw~  : ∀ {Δ~ : Ctx~ {Ψ = Ψ} Δ₁ Δ₂} (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
            {t₁~ : Tm~ rfl~ _ _ ⌜ b ⌝𝔹}            
        → Tms~ Δ~ (Γ~ , t~ >rw) (δ₁ ,rw t₁~) (δ₂ ,rw t₂~) 
  
  id   : Tms~ Γ~ Γ~ id id
  _⨾_  : Tms~ Δ~ Γ~ δ₁ δ₂ → Tms~ Θ~ Δ~ σ₁ σ₂ → Tms~ Θ~ Γ~ (δ₁ ⨾ σ₁) (δ₂ ⨾ σ₂)
  
  π₁   : ∀ (A~ : Ty~ Γ~ A₁ A₂) → Tms~ Δ~ (Γ~ , A~) δ₁ δ₂ 
       → Tms~ Δ~ Γ~ (π₁ δ₁) (π₁ δ₂)
  π₁rw : ∀ (t~ : Tm~ Γ~ 𝔹 t₁ t₂)
       → Tms~ Δ~ (Γ~ , t~ >rw) δ₁ δ₂ → Tms~ Δ~ Γ~ (π₁rw δ₁) (π₁rw δ₂)

  wk𝒮 : Tms~ (Γ~ [ rfl~ ]) Γ~ (wk𝒮 {t = t} {u = u} {v = v}) wk𝒮

  -- Computation
  εη   : Tms~ rfl~ rfl~ δ ε
  ,η   : Tms~ rfl~ rfl~ δ (π₁ δ , π₂ δ)
  ,rwη : Tms~ rfl~ rfl~ (π₁rw δ ,rw π₂rw′ {b = b} δ) δ

  π₁,   : Tms~ rfl~ rfl~ (π₁ (δ , t)) δ
  π₁rw, : ∀ {δ : Tms {Φ = Φ} {Ψ = Ψ} Δ Γ} {t~ : Tm~ _ _ (t [ δ ]) ⌜ b ⌝𝔹} 
        → Tms~ rfl~ rfl~ (π₁rw (δ ,rw t~)) δ

  π₁⨾   : Tms~ rfl~ rfl~ (π₁ (δ ⨾ σ)) (π₁ δ ⨾ σ)
  π₁rw⨾ : Tms~ rfl~ rfl~ (π₁rw (δ ⨾ σ)) (π₁rw δ ⨾ σ)

  id⨾ : Tms~ rfl~ rfl~ (id ⨾ δ) δ
  ⨾id : Tms~ rfl~ rfl~ (δ ⨾ id) δ
  ⨾⨾  : Tms~ rfl~ rfl~ ((δ ⨾ σ) ⨾ γ) (δ ⨾ (σ ⨾ γ))


  wk⨾π₁   : Tms~ rfl~ rfl~ (wk𝒮 ⨾ π₁ δ) (π₁ (wk𝒮 ⨾ coe~ rfl~ (sym~ ,[]) δ))
  wk⨾π₁rw : Tms~ rfl~ rfl~ (wk𝒮 ⨾ π₁rw δ) 
                           (π₁rw (wk𝒮 ⨾ coe~ rfl~ (sym~ ,>rw[]) δ))

  ,⨾   : Tms~ rfl~ rfl~ ((δ , t) ⨾ σ) ((δ ⨾ σ) , (coe~ rfl~ [][] (t [ σ ])))
  ,rw⨾ : {σ : Tms {Φ = Φ} {Ψ = Ψ} Θ Δ} {t~ : Tm~ rfl~ 𝔹[] (t [ δ ]) ⌜ b ⌝𝔹} 
       → Tms~ rfl~ rfl~ ((δ ,rw t~) ⨾ σ) ((δ ⨾ σ) ,rw ,rw⨾-helper t~)

rflTm′ : Tm~ rfl~ rfl~ t t

wk-comm : Tms~ (,>rw[] {t = t}) rfl~ 
               (π₁rw id ⨾ wk𝒮 {t = u₁} {u = u₂} {v = u₃}) 
               (wk𝒮 ⨾ π₁rw id)
wk-comm =  sym~ π₁rw⨾ ∙~ (π₁rw rflTm′ (id⨾ ∙~ coh {Δ~ = ,>rw[]} {Γ~ = rfl~} 
        ∙~ sym~ ⨾id ∙~ sym~ coh ⨾ coh)) ∙~ sym~ wk⨾π₁rw

⌜⌝𝔹 : ∀ (Γ~ : Ctx~ Γ₁ Γ₂) → Tm~ Γ~ 𝔹 (⌜ b ⌝𝔹) (⌜ b ⌝𝔹)
⌜⌝𝔹[] : Tm~ rfl~ 𝔹[] (⌜ b ⌝𝔹 [ δ ]) (⌜ b ⌝𝔹)

wk<>rw : Tms~ rfl~ rfl~ (π₁rw id ⨾ (δ ,rw t~)) δ
wk<>rw = sym~ π₁rw⨾ ∙~ π₁rw rflTm′ id⨾ ∙~ π₁rw,

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
  
  _[_] : Tm~ Γ~ A~ t₁ t₂ → ∀ (δ~ : Tms~ Δ~ Γ~ δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ δ~ ]) (t₁ [ δ₁ ]) (t₂ [ δ₂ ]) 
  π₂   : ∀ (δ~ : Tms~ Δ~ (Γ~ , A~) δ₁ δ₂) 
       → Tm~ Δ~ (A~ [ π₁ A~ δ~ ]) (π₂ δ₁) (π₂ δ₂) 

  -- Projection
  π₂rw : ∀ (δ : Tms Δ (Γ , t >rw b)) → Tm~ rfl~ 𝔹[] (t [ π₁rw δ ]) ⌜ b ⌝𝔹

  -- Computation
  ƛ[]   : Tm~ rfl~ Π[] ((ƛ t) [ δ ]) (ƛ (t [ δ ^ A ]))
  TT[]  : Tm~ rfl~ 𝔹[] (TT [ δ ]) TT
  FF[]  : Tm~ rfl~ 𝔹[] (FF [ δ ]) FF
  
  [id] : Tm~ rfl~ [id] (t [ id ]) t
  [][] : Tm~ rfl~ [][] (t [ δ ] [ σ ]) (t [ δ ⨾ σ ])

  call[] : Tm~ rfl~ ([][] ∙~ rfl~ [ ⨾⨾ ]) 
               (call {t = t} {u = u} {v = v} δ [ σ ]) 
               (call (δ ⨾ σ))

  -- Calls to definitions reduce exactly when the neutral they block on
  -- reduces to a closed Boolean
  callTT : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ wk𝒮 ⨾ δ ]) TT)
         → Tm~ rfl~ 
               (  rfl~ [  rfl~ ⨾ sym~ wk<>rw ∙~ sym~ ⨾⨾ 
                       ∙~ sym~ wk-comm ⨾ coh ∙~ ⨾⨾ ] 
               ∙~ sym~ [][])
               (call {t = t} {u = u} δ) 
               (u [ wk𝒮 ⨾ coe~ rfl~ (sym~ ,>rw[]) 
                               (δ ,rw (sym~ coh [ rfl~ ] ∙~ [][] ∙~ t~)) ])
  callFF : ∀ (t~ : Tm~ rfl~ 𝔹[] (t [ wk𝒮 ⨾ δ ]) FF)
         → Tm~ rfl~ 
               (  rfl~ [  rfl~ ⨾ sym~ wk<>rw ∙~ sym~ ⨾⨾ 
                       ∙~ sym~ wk-comm ⨾ coh ∙~ ⨾⨾ ] 
               ∙~ sym~ [][])
               (call {t = t} {v = v} δ) 
               (v [ wk𝒮 ⨾ coe~ rfl~ (sym~ (,>rw[] {b = false})) 
                               (δ ,rw (sym~ coh [ rfl~ ] ∙~ [][] ∙~ t~)) ])

  β    : Tm~ rfl~ rfl~ (ƛ⁻¹ ƛ t) t
  η    : Tm~ rfl~ rfl~ (ƛ ƛ⁻¹ t) t

  π₂, : Tm~ rfl~ (rfl~ [ π₁, ]) (π₂ (δ , t)) t

  -- Note this is what we would expect from |π₂[]|, but reversed
  π₂⨾ : Tm~ rfl~ (rfl~ [ π₁⨾ ] ∙~ sym~ {Γ~ = Γ~} [][]) (π₂ (δ ⨾ σ)) (π₂ δ [ σ ])

rflTm′ = rfl~

⌜⌝𝔹 {b = true}  = TT
⌜⌝𝔹 {b = false} = FF

⌜⌝𝔹[] {b = true}  = TT[]
⌜⌝𝔹[] {b = false} = FF[]

,rw⨾-helper t~ 
  =  sym~ {Γ~ = rfl~} [][] ∙~ (t~ [ rfl~ ]) ∙~ ⌜⌝𝔹[]
  
π₂rw′ = π₂rw

coeTm~ : Tm~ Γ~ A~ t₁ t₂ 
       → Tm~ (sym~ Γ₁~ ∙~ Γ~ ∙~ Γ₂~) (sym~ A₁~ ∙~ A~ ∙~ A₂~) 
             (coe~ Γ₁~ A₁~ t₁) (coe~ Γ₂~ A₂~ t₂)
coeTm~ t~ = sym~ coh ∙~ t~ ∙~ coh

-- We derive the substitution law for |ƛ⁻¹| as in 
-- https://people.cs.nott.ac.uk/psztxa/publ/tt-in-tt.pdf
ƛ⁻¹[] : Tm~ rfl~ rfl~ ((ƛ⁻¹ t) [ δ ^ A ]) (ƛ⁻¹ (coe~ rfl~ Π[] (t [ δ ])))
ƛ⁻¹[] =  sym~ β ∙~ ƛ⁻¹_ {A~ = rfl~} {B~ = rfl~} (coh {A~ = rfl~} 
      ∙~ coeTm~ (sym~ ƛ[] ∙~ η [ rfl~ ]))
 