{-# OPTIONS --prop #-}

open import Utils
open import Common.Sort

module STLC.Syntax where

record Extensions : Set where
  constructor ⟨ƛ≔_,⊤≔_,𝔹≔_,+≔_,×≔_,ℕ≔_⟩
  field
    ƛ? : Bool
    ⊤? : Bool
    𝔹? : Bool
    +? : Bool
    ×? : Bool
    ℕ? : Bool
open Extensions public

all : Extensions
all .ƛ? = true
all .⊤? = true
all .𝔹? = true
all .+? = true
all .×? = true
all .ℕ? = true

none : Extensions
none .ƛ? = false
none .⊤? = false
none .𝔹? = false
none .+? = false
none .×? = false
none .ℕ? = false

unit : Extensions
unit = record none {⊤? = true}

ƛ∪𝔹∪+ : Extensions
ƛ∪𝔹∪+ = record none {ƛ? = true; 𝔹? = true; +? = true}

variable
  𝕏 : Extensions
  b₁ b₂ b₃ b₄ b₅ : Bool

pattern 𝕏∪ƛ = ⟨ƛ≔ true ,⊤≔ _ ,𝔹≔ _ ,+≔ _ ,×≔ _ ,ℕ≔ _ ⟩
pattern 𝕏∪⊤ = ⟨ƛ≔ _ ,⊤≔ true ,𝔹≔ _ ,+≔ _ ,×≔ _ ,ℕ≔ _ ⟩
pattern 𝕏∪𝔹 = ⟨ƛ≔ _ ,⊤≔ _ ,𝔹≔ true ,+≔ _ ,×≔ _ ,ℕ≔ _ ⟩
pattern 𝕏∪+ = ⟨ƛ≔ _ ,⊤≔ _ ,𝔹≔ _ ,+≔ true ,×≔ _ ,ℕ≔ _ ⟩
pattern 𝕏∪× = ⟨ƛ≔ _ ,⊤≔ _ ,𝔹≔ _ ,+≔ _ ,×≔ true ,ℕ≔ _ ⟩
pattern 𝕏∪ℕ = ⟨ƛ≔ _ ,⊤≔ _ ,𝔹≔ _ ,+≔ _ ,×≔ _ ,ℕ≔ true ⟩

module Syntax where
  infixr 5 _⇒_
  infixl 4  _,_
  infix  5  ƛ_
  infixl 6  _·_
  infix  7  `_

  data Ctx (ex : Extensions) : Set
  data Ty  : Extensions → Set
  data Tm[_] : Sort → ∀ 𝕏 → Ctx 𝕏 → Ty 𝕏 → Set
  Var = Tm[ V ]
  Tm  = Tm[ T ]

  variable
    Γ Δ Θ : Ctx 𝕏
    A B C : Ty 𝕏
    A₁ A₂ A₃ B₁ B₂ B₃ C₁ C₂ C₃ : Ty 𝕏
    i j k : Var 𝕏 Γ A
    t u v : Tm 𝕏 Γ A
    t₁ t₂ t₃ u₁ u₂ u₃ v₁ v₂ v₃ : Tm 𝕏 Γ A
    x y z : Tm[ q ] 𝕏 Γ A
    x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : Tm[ q ] 𝕏 Γ A

  data Ctx 𝕏 where
    ε   : Ctx 𝕏
    _,_ : Ctx 𝕏 → Ty 𝕏 → Ctx 𝕏

  data Ty where
    _⇒_  : Ty 𝕏 → Ty 𝕏 → Ty 𝕏
    ⊤'   : let 𝕏 = ⟨ƛ≔ b₁ ,⊤≔ true ,𝔹≔ b₂ ,+≔ b₃ ,×≔ b₄ ,ℕ≔ b₅ ⟩ 
        in Ty 𝕏
    𝔹'   : let 𝕏 = ⟨ƛ≔ b₁ ,⊤≔ b₂ ,𝔹≔ true ,+≔ b₃ ,×≔ b₄ ,ℕ≔ b₅ ⟩
         in Ty 𝕏
    _+'_ : let 𝕏 = ⟨ƛ≔ b₁ ,⊤≔ b₂ ,𝔹≔ b₃ ,+≔ true ,×≔ b₄ ,ℕ≔ b₅ ⟩ 
        in Ty 𝕏 → Ty 𝕏 → Ty 𝕏
    _×'_ : let 𝕏 = ⟨ƛ≔ b₁ ,⊤≔ b₂ ,𝔹≔ b₃ ,+≔ b₄ ,×≔ true ,ℕ≔ b₅ ⟩
        in Ty 𝕏 → Ty 𝕏 → Ty 𝕏
    ℕ'   : let 𝕏 = ⟨ƛ≔ b₁ ,⊤≔ b₂ ,𝔹≔ b₃ ,+≔ b₄ ,×≔ b₅ ,ℕ≔ true ⟩
        in Ty 𝕏

  data Tm[_] where
    vz    : Var _ (Γ , A) A
    vs    : Var _ Γ B → Var 𝕏 (Γ , A) B
    
    `_    : Var 𝕏 Γ A → Tm 𝕏 Γ A
    _·_   : Tm 𝕏 Γ (A ⇒ B) → Tm 𝕏 Γ A → Tm 𝕏 Γ B
    ƛ_    : Tm 𝕏∪ƛ (Γ , A) B → Tm 𝕏∪ƛ Γ (A ⇒ B)
    
    ⟨⟩    : Tm 𝕏∪⊤ Γ ⊤'

    true  : Tm 𝕏∪𝔹 Γ 𝔹'
    false : Tm 𝕏∪𝔹 Γ 𝔹'
    𝔹-rec : Tm 𝕏∪𝔹 Γ 𝔹' → Tm 𝕏∪𝔹 Γ A → Tm 𝕏∪𝔹 Γ A → Tm 𝕏∪𝔹 Γ A 

    inl   : Tm 𝕏∪+ Γ A → Tm _ Γ (A +' B)
    inr   : Tm 𝕏∪+ Γ B → Tm _ Γ (A +' B)
    +-rec : Tm 𝕏∪+ Γ (A +' B) → Tm 𝕏∪+ (Γ , A) C → Tm 𝕏∪+ (Γ , B) C → Tm 𝕏∪+ Γ C

    fst   : Tm 𝕏∪× Γ (A ×' B) → Tm 𝕏∪× Γ A
    snd   : Tm 𝕏∪× Γ (A ×' B) → Tm 𝕏∪× Γ B
    ⟨_,_⟩ : Tm 𝕏∪× Γ A → Tm 𝕏∪× Γ B → Tm 𝕏∪× Γ (A ×' B)

    ze    : Tm 𝕏∪ℕ Γ ℕ' 
    su    : Tm 𝕏∪ℕ Γ ℕ' → Tm 𝕏∪ℕ Γ ℕ'
    ℕ-rec : Tm 𝕏∪ℕ Γ ℕ' → Tm 𝕏∪ℕ Γ A → Tm 𝕏∪ℕ (Γ , A) A → Tm 𝕏∪ℕ Γ A

  data Ne : ∀ 𝕏 → Ctx 𝕏 → Ty 𝕏 → Set
  data Nf : ∀ 𝕏 → Ctx 𝕏 → Ty 𝕏 → Set

  data Ne where
    `_    : Var 𝕏 Γ A → Ne 𝕏 Γ A
    _·_   : Ne 𝕏 Γ (A ⇒ B) → Nf 𝕏 Γ A → Ne 𝕏 Γ B
    
    𝔹-rec : Ne 𝕏∪𝔹 Γ 𝔹' → Nf 𝕏∪𝔹 Γ A → Nf 𝕏∪𝔹 Γ A → Ne 𝕏∪𝔹 Γ A 

  data Nf where
    ne  : Ne 𝕏 Γ A → Nf 𝕏 Γ A
    ƛ_  : Nf 𝕏∪ƛ (Γ , A) B → Nf 𝕏∪ƛ Γ (A ⇒ B)
    
    true  : Nf 𝕏∪𝔹 Γ 𝔹'
    false : Nf 𝕏∪𝔹 Γ 𝔹'

module Parameterised (𝕏 : Extensions) where
  open Syntax renaming 
    (Ctx to _⊢Ctx; Ty to _⊢Ty; Tm[_] to [_]_⊢Tm; Tm to _⊢Tm; Var to _⊢Var
    ; Ne to _⊢Ne; Nf to _⊢Nf) 
    public
  Ctx   = 𝕏 ⊢Ctx
  Ty    = 𝕏 ⊢Ty
  Tm[_] = [_] 𝕏 ⊢Tm
  Tm    = 𝕏 ⊢Tm
  Var   = 𝕏 ⊢Var
  Ne    = 𝕏 ⊢Ne
  Nf    = 𝕏 ⊢Nf

  tm⊑ : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
  tm⊑ {q = V} {r = T} _ i = ` i
  tm⊑ {q = V} {r = V} _ i = i
  tm⊑ {q = T} {r = T} _ t = t

  ne→tm : Ne Γ A → Tm Γ A
  nf→tm : Nf Γ A → Tm Γ A

  ne→tm (` i)         = ` i
  ne→tm (t · u)       = ne→tm t · nf→tm u
  ne→tm (𝔹-rec c t u) = 𝔹-rec (ne→tm c) (nf→tm t) (nf→tm u)

  nf→tm (ne t) = ne→tm t
  nf→tm (ƛ t)  = ƛ nf→tm t
  nf→tm true   = true
  nf→tm false  = false

  -- TODO: Move 'Tms' out of the parameterised module to avoid case splitting
  -- pain (https://github.com/agda/agda/issues/3209)
  data Tms[_] (q : Sort) : Ctx → Ctx → Set where
    ε   : Tms[ q ] Δ ε
    _,_ : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ , A)

  variable
    δ σ ξ δ₁ δ₂ δ₃ σ₁ σ₂ σ₃ ξ₁ ξ₂ ξ₃ : Tms[ q ] Δ Γ

  Vars = Tms[ V ]
  Tms  = Tms[ T ]

  vz[_] : ∀ q → Tm[ q ] (Γ , A) A
  vz[ V ] = vz
  vz[ T ] = ` vz

  suc[_] : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ , A) B
  _⁺_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) Γ
  _^_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) (Γ , A)
  _[_]   : Tm[ q ] Γ A → Tms[ s ] Δ Γ → Tm[ q ⊔ s ] Δ A 
  id : Vars Γ Γ

  id′ : Sort → Vars Γ Γ

  id = id′ V
  {-# INLINE id #-} 

  id′ {Γ = ε}     _ = ε
  id′ {Γ = Γ , A} _ = id ^ A

  suc[ V ]   = vs
  suc[ T ] t = t [ id ⁺ _ ]

  ε       ⁺ A = ε
  (δ , t) ⁺ A = (δ ⁺ A) , suc[ _ ] t

  δ ^ A = (δ ⁺ A) , vz[ _ ]

  vz          [ δ , t ] = t
  vs i        [ δ , t ] = i [ δ ]
  (` i)       [ δ ]     = tm⊑ ⊑T (i [ δ ])
  (t · u)     [ δ ]     = t [ δ ] · u [ δ ]
  (ƛ t)       [ δ ]     = ƛ (t [ δ ^ _ ])
  ⟨⟩          [ δ ]     = ⟨⟩
  true        [ δ ]     = true
  false       [ δ ]     = false
  𝔹-rec c t u [ δ ]     = 𝔹-rec (c [ δ ]) (t [ δ ]) (u [ δ ])
  inl t       [ δ ]     = inl (t [ δ ])
  inr t       [ δ ]     = inr (t [ δ ])
  +-rec s l r [ δ ]     = +-rec (s [ δ ]) (l [ δ ^ _ ]) (r [ δ ^ _ ])
  fst t       [ δ ]     = fst (t [ δ ])
  snd t       [ δ ]     = snd (t [ δ ])
  ⟨ t , u ⟩   [ δ ]     = ⟨ t [ δ ] , u [ δ ] ⟩
  ze          [ δ ]     = ze
  su t        [ δ ]     = su (t [ δ ])
  ℕ-rec n z s [ δ ]     = ℕ-rec (n [ δ ]) (z [ δ ]) (s [ δ ^ _ ]) 
  
  _[_]ne : Ne Γ A → Vars Δ Γ → Ne Δ A
  _[_]nf : Nf Γ A → Vars Δ Γ → Nf Δ A

  (` i)       [ δ ]ne = ` (i [ δ ])
  (t · u)     [ δ ]ne = t [ δ ]ne · u [ δ ]nf
  𝔹-rec c t u [ δ ]ne = 𝔹-rec (c [ δ ]ne) (t [ δ ]nf) (u [ δ ]nf)

  ne t  [ δ ]nf = ne (t [ δ ]ne)
  (ƛ t) [ δ ]nf = ƛ  (t [ δ ^ _ ]nf)
  true  [ δ ]nf = true
  false [ δ ]nf = false

  _⨾_ : Tms[ q ] Δ Γ → Tms[ r ] Θ Δ → Tms[ q ⊔ r ] Θ Γ
  ε       ⨾ σ = ε
  (δ , x) ⨾ σ = (δ ⨾ σ) , (x [ σ ])

  tms⊑ : q ⊑ r → Tms[ q ] Δ Γ → Tms[ r ] Δ Γ
  tms⊑ p ε       = ε
  tms⊑ p (δ , x) = tms⊑ p δ , tm⊑ p x

  id[_]  : ∀ q → Tms[ q ] Γ Γ
  id[ _ ] = tms⊑ V⊑ id
  
  <_> : Tm Γ A → Tms[ T ] Γ (Γ , A)
  < t > = id[ T ] , t

  ƛ⁻¹_ : Tm Γ (A ⇒ B) → Tm (Γ , A) B
  ƛ⁻¹ t = t [ id ⁺ _ ] · (` vz)

  wk : Tms[ V ] (Γ , A) Γ
  wk = id ⁺ _
  