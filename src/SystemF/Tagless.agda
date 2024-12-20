module Tagless where

open import Level
open import Data.Fin
open import Data.Nat
open import Data.String
open import Data.List
open import Data.Vec

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

-- syntax

Ident = String

variable n : ℕ

lof : ℕ → Level
lof ℕ.zero = Level.zero
lof (ℕ.suc n) = Level.suc (lof n)

module try1 where

  -- polymorphic unit
  data ⊤ {ℓ} : Set ℓ where
    tt : ⊤

  data Type n : Set where
    `_ : Fin n → Type n
    _⇒_ : Type n → Type n → Type n
    `∀α,_ : Type (ℕ.suc n) → Type n
    𝟙 : Type n

  ⟦_⟧ : Type n → (l : ℕ) → Vec (Set (lof l)) n → Set (lof l)
  ⟦ ` x ⟧ l η = Data.Vec.lookup η x
  ⟦ T₁ ⇒ T₂ ⟧ l η = ⟦ T₁ ⟧ l η → ⟦ T₂ ⟧ l η
  ⟦ `∀α, T ⟧ ℕ.zero η = {!!}
  ⟦ `∀α, T ⟧ (ℕ.suc l) η = (α : Set (lof l)) → ⟦ T ⟧ (ℕ.suc l) ({!!} ∷ η)
  ⟦ 𝟙 ⟧ l η = ⊤

module try2 where

  open import Data.Unit

  -- level environments
  LEnv = List ℕ
  variable Δ : LEnv

  data _∈_ : ℕ → LEnv → Set where
    here  : ∀ {l ls} → l ∈ (l ∷ ls)
    there : ∀ {l l′ ls} → l ∈ ls → l ∈ (l′ ∷ ls)

  data Type (Δ : LEnv) : Set where
    `_ : n ∈ Δ → Type Δ
    _⇒_ : Type Δ → Type Δ → Type Δ
    `∀α_,_ : (lev : ℕ) → Type (lev ∷ Δ) → Type Δ
    𝟙 : Type Δ

  -- level of type according to Leivant'91
  level : Type Δ → ℕ
  level (`_ {lev} x) = lev
  level (T₁ ⇒ T₂) = level T₁ Data.Nat.⊔ level T₂
  level (`∀α q , T) = ℕ.suc q Data.Nat.⊔ level T
  level 𝟙 = ℕ.zero

  lof-⊔ : ∀ l₁ l₂ → lof (l₁ Data.Nat.⊔ l₂) ≡ lof l₁ Level.⊔ lof l₂
  lof-⊔ ℕ.zero l₂ = refl
  lof-⊔ (ℕ.suc l₁) ℕ.zero = refl
  lof-⊔ (ℕ.suc l₁) (ℕ.suc l₂) = cong Level.suc (lof-⊔ l₁ l₂)


  Env* : LEnv → Setω
  Env* Δ = ∀ {l} → l ∈ Δ → Set (lof l)

  -- the meaning of a stratified type in terms of Agda universes
  ⟦_⟧ : (T : Type Δ) → Env* Δ → Set (lof (level T))
  ⟦ ` x ⟧ η = η x
  ⟦ T₁ ⇒ T₂ ⟧ η with
    (⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η)
  ... | S rewrite lof-⊔ (level T₁) (level T₂) = S
  ⟦ `∀α lev , T ⟧ η with
    ((α : Set (lof lev)) → ⟦ T ⟧ λ{ here → α ; (there x) → η x})
  ... | S rewrite lof-⊔ (ℕ.suc lev) (level T) = S
  ⟦ 𝟙 ⟧ η = ⊤

  -- type environments
  data TEnv : LEnv → Set where

    ∅    : TEnv []
    _◁*_ : (l : ℕ) → TEnv Δ → TEnv (l ∷ Δ)
    _◁_  : Type Δ → TEnv Δ → TEnv Δ
  
  data inn : ∀ {Δ} → Type Δ → TEnv Δ → Set where
    here  : ∀ {T Γ} → inn {Δ} T (T ◁ Γ)
    there : ∀ {T T′ Γ} → inn {Δ} T Γ → inn {Δ} T (T′ ◁ Γ)
    tskip : ∀ {T l Γ} → inn {Δ} T Γ → inn {!!} (l ◁* Γ)

  data Expr : (Δ : LEnv) → TEnv Δ → Type Δ → Set where
    `_   : ∀ {T : Type Δ}{Γ : TEnv Δ} → inn T Γ → Expr Δ Γ T
    ƛ_   : ∀ {T T′ : Type Δ}{Γ : TEnv Δ} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
    _·_  : ∀ {T T′ : Type Δ}{Γ : TEnv Δ} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
    Λα_⇒_ : ∀ {Γ : TEnv Δ} → (l : ℕ) → {T : Type (l ∷ Δ)} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
    -- _∙_  : ∀ {l : ℕ}{T : Type (l ∷ Δ)}{Γ : TEnv Δ} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ) → Expr Δ Γ {!!}


  Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
  Env Δ Γ η = ∀ {T : Type Δ} → (x : inn T Γ) → ⟦ T ⟧ η

  E⟦_⟧ : ∀ {T : Type Δ}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
  E⟦ ` x ⟧ η γ = γ x
  E⟦ ƛ_ {T = T}{T′ = T′} e ⟧ η γ
    with (⟦ T ⟧ η → ⟦ T′ ⟧ η) in eq
  ... | S = {!!}
  E⟦ e₁ · e₂ ⟧ η γ
    with E⟦ e₁ ⟧ η γ | E⟦ e₂ ⟧ η γ
  ... | v₁ | v₂ = {!!}
  E⟦ Λα l ⇒ e ⟧ η γ = {!!}

module attempt3 where

  open import Data.Unit using (⊤)
  open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
  open import Function using (id)

  -- level environments
  LEnv = List Level
  variable
    Δ : LEnv
    ℓ  ℓ′ ℓ₁ ℓ₂ : Level

  data _∈_ : Level → LEnv → Set where
    here  : ∀ {l ls} → l ∈ (l ∷ ls)
    there : ∀ {l l′ ls} → l ∈ ls → l ∈ (l′ ∷ ls)

  data Type (Δ : LEnv) : Level → Set where
    `_ : ℓ ∈ Δ → Type Δ ℓ
    _⇒_ : Type Δ ℓ₁ → Type Δ ℓ₂ → Type Δ (ℓ₁ Level.⊔ ℓ₂)
    `∀α_,_ : ∀ ℓ₁ {ℓ₂} → Type (ℓ₁ ∷ Δ) ℓ₂ → Type Δ (Level.suc ℓ₁ Level.⊔ ℓ₂)
    𝟙 : Type Δ Level.zero

  levelₜ : Type Δ ℓ → Level
  levelₜ{ℓ = ℓ} _ = ℓ 

  module att3-1 where
    Env* : LEnv → Setω
    Env* Δ = ∀ {l} → l ∈ Δ → Set l

    ext* : Set ℓ → Env* Δ → Env* (ℓ ∷ Δ)
    ext* s η here = s
    ext* s η (there x) = η x

    ⟦_⟧ : Type Δ ℓ → Env* Δ → Set ℓ
    ⟦ ` x ⟧ η = η x
    ⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
    ⟦ `∀α ℓ₁ , T ⟧ η = ∀ α → ⟦ T ⟧ (ext* α η)
    ⟦ 𝟙 ⟧ η = ⊤

  module att3-2 where
    -- without Setω
    ⊔* : LEnv → Level
    ⊔* [] = Level.zero
    ⊔* (ℓ ∷ Δ) = (Level.suc ℓ) Level.⊔ ⊔* Δ

    Env* : (Δ : LEnv) → Set (⊔* Δ)
    Env* [] = ⊤
    Env* (ℓ ∷ Δ) = Set ℓ × Env* Δ

    ext* : Set ℓ → Env* Δ → Env* (ℓ ∷ Δ)
    ext* s η = s , η

    lookupₜ : ∀ {ℓ}{Δ} → Env* Δ → ℓ ∈ Δ → Set ℓ
    lookupₜ (s , _) here = s
    lookupₜ (_ , η) (there x) = lookupₜ η x

    ⟦_⟧ : (t : Type Δ ℓ) → (η : Env* Δ) → Set ℓ
    ⟦ ` x ⟧ η = lookupₜ η x
    ⟦ t₁ ⇒ t₂ ⟧ η = ⟦ t₁ ⟧ η → ⟦ t₂ ⟧ η
    ⟦ `∀α ℓ₁ , t ⟧ η = ∀ α → ⟦ t ⟧ (ext* α η)
    ⟦ 𝟙 ⟧ η = ⊤

    𝓣 : Type Δ ℓ → Env* Δ → Set (Level.suc ℓ)
    𝓣 t η = Σ (Set _) (λ s → s × s ≡ ⟦ t ⟧ η)

    return : {t : Type Δ ℓ} {η : Env* Δ} → ⟦ t ⟧ η → 𝓣 t η
    return v = _ , v , refl

    _>>=_ : {t₁ : Type Δ ℓ₁} {t₂ : Type Δ ℓ₂} {η : Env* Δ} → 𝓣 t₁ η → (⟦ t₁ ⟧ η → 𝓣 t₂ η) → 𝓣 t₂ η
    _>>=_ (_ , a , refl) f = f a
    

  -- type environments
  data TEnv : LEnv → Set where
    ∅    : TEnv []
    _◁*_ : (ℓ : Level) → TEnv Δ → TEnv (ℓ ∷ Δ)
    _◁_  : Type Δ ℓ → TEnv Δ → TEnv Δ

  ⊔** : TEnv Δ → Level
  ⊔** ∅ = Level.zero
  ⊔** (ℓ ◁* Γ) = ⊔** Γ
  ⊔** (t ◁ Γ) = levelₜ t Level.⊔ ⊔** Γ
  
  postulate
    -- standard renamings
    weakenₜ : Type Δ ℓ → Type (ℓ′ ∷ Δ) ℓ
    -- standard substitutions
    sub0ₜ : (T : Type (ℓ′ ∷ Δ) ℓ) → (T′ : Type Δ ℓ′) → Type Δ ℓ

  data inn : ∀ {Δ}{ℓ} → Type Δ ℓ → TEnv Δ → Set where
    here  : ∀ {T Γ} → inn {Δ}{ℓ} T (T ◁ Γ)
    there : ∀ {T : Type Δ ℓ}{T′ : Type Δ ℓ′}{Γ} → inn {Δ}{ℓ} T Γ → inn {Δ} T (T′ ◁ Γ)
    tskip : ∀ {T : Type Δ ℓ}{l Γ} → inn {Δ}{ℓ} T Γ → inn (weakenₜ T) (l ◁* Γ)

  data Expr : (Δ : LEnv) → TEnv Δ → Type Δ ℓ → Set where
    `_   : ∀ {T : Type Δ ℓ}{Γ : TEnv Δ} → inn T Γ → Expr Δ Γ T
    ƛ_   : ∀ {T : Type Δ ℓ}{ T′ : Type Δ ℓ′}{Γ : TEnv Δ} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
    _·_  : ∀ {T : Type Δ ℓ}{ T′ : Type Δ ℓ′}{Γ : TEnv Δ} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
    Λα_⇒_ : ∀ {Γ : TEnv Δ} → (l : Level) → {T : Type (l ∷ Δ) ℓ′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
    _∙_  : ∀{T : Type (ℓ′ ∷ Δ) ℓ}{Γ : TEnv Δ} → Expr Δ Γ (`∀α ℓ′ , T) → (T′ : Type Δ ℓ′) → Expr Δ Γ (sub0ₜ T T′)


  open att3-2

  postulate
    -- substitutions and denotational semantics
    weak-ext : {s : Set ℓ′} {T : Type Δ ℓ} → (η : Env* Δ) →  ⟦ T ⟧ η ≡ ⟦ weakenₜ T ⟧ (ext* s η)
    sub0-ext : {T  : Type (ℓ′ ∷ Δ) ℓ} {T′ : Type Δ ℓ′} (η  : Env* Δ) →  ⟦ T ⟧ (ext* (⟦ T′ ⟧ η) η) ≡ ⟦ sub0ₜ T T′ ⟧ η
  
  Env : (Δ : LEnv) → (Γ : TEnv Δ) → (η : Env* Δ) → Set (⊔** Γ)
  Env .[] ∅ η = ⊤
  Env .(ℓ ∷ _) (ℓ ◁* Γ) (s , η) = Env _ Γ η
  Env Δ (t ◁ Γ) η = ⟦ t ⟧ η × Env Δ Γ η


  module use-𝓣 where
    lookupₓ : ∀ {T : Type Δ ℓ} {Γ : TEnv Δ} {η : Env* Δ} → (γ : Env Δ Γ η) → (x : inn T Γ) → 𝓣 T η
    lookupₓ (v , _) here = _ , v , refl
    lookupₓ (_ , γ) (there x) = lookupₓ γ x
    lookupₓ {η = _ , η} γ (tskip x)
      with lookupₓ γ x
    ... | s , v , refl = s , v , weak-ext η

    E⟦_⟧ : ∀ {T : Type Δ ℓ}{Γ : TEnv Δ} → (e : Expr Δ Γ T) → (η : Env* Δ) → (γ : Env Δ Γ η) → 𝓣 T η
    E⟦ ` x ⟧ η γ = lookupₓ γ x
    E⟦ ƛ e ⟧ η γ = _ , {!λ x → E⟦ e ⟧ η (x , γ)!} , {!!}
    E⟦ e₁ · e₂ ⟧ η γ
      with E⟦ e₁ ⟧ η γ | E⟦ e₂ ⟧ η γ
    ... | fst , vfun , refl | fst₁ , varg , refl = _ , vfun varg , refl
    E⟦ Λα l ⇒ e ⟧ η γ = {!!}
    E⟦ e ∙ T′ ⟧ η γ
      with E⟦ e ⟧ η γ
    ... | fst , v , refl = _ , v (⟦ T′ ⟧ η) , sub0-ext η
    -- for the remaining cases, we need to change the meaning of the function type and the universal type
    -- ⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → 𝓣 T₂ η
    -- ⟦ ∀α l , T ⟧ η = λ α → 𝓣 T (ext α η)


  lookupₓ : ∀ {T : Type Δ ℓ} {Γ : TEnv Δ} {η : Env* Δ} → (γ : Env Δ Γ η) → (x : inn T Γ) → ⟦ T ⟧ η
  lookupₓ (v , _) here = v
  lookupₓ (_ , γ) (there x) = lookupₓ γ x
  lookupₓ {η = _ , η} γ (tskip x) = subst id (weak-ext η) (lookupₓ γ x)


  E⟦_⟧ : ∀ {T : Type Δ ℓ}{Γ : TEnv Δ} → (e : Expr Δ Γ T) → (η : Env* Δ) → (γ : Env Δ Γ η) → ⟦ T ⟧ η
  E⟦ ` x ⟧ η γ = lookupₓ γ x
  E⟦ ƛ e ⟧ η γ = λ x → E⟦ e ⟧ η (x , γ)
  E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
  E⟦ Λα l ⇒ e ⟧ η γ = λ α → E⟦ e ⟧ (α , η) γ
  E⟦ e ∙ T′ ⟧ η γ = subst id (sub0-ext η) (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
