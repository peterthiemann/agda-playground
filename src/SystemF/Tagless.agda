module Tagless where

open import Level
open import Data.Fin
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.String
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Vec
open import Data.Unit using (⊤)
open import Function using (id)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

-- syntax

Ident = String

variable n : ℕ

lof : ℕ → Level
lof ℕ.zero = Level.zero
lof (ℕ.suc n) = Level.suc (lof n)


module version1 where
  -- natural numbers as levels
  Lvl = ℕ

  -- level environments
  LEnv = List Lvl
  variable Δ : LEnv
  variable l l₁ l₂ l′ : Lvl

  data Type (Δ : LEnv) : Lvl → Set where
    `_ : l ∈ Δ → Type Δ l
    _`⇒_ : Type Δ l₁ → Type Δ l₂ → Type Δ (l₁ ⊔ℕ l₂)
    `∀α_,_ : (lev : ℕ) → Type (lev ∷ Δ) l → Type Δ (ℕ.suc lev ⊔ℕ l)
    𝟙 : Type Δ ℕ.zero

  postulate
    -- standard renamings
    weakenₜ : Type Δ l → Type (l′ ∷ Δ) l
    -- standard single substitutions
    sub0ₜ : (T : Type (l′ ∷ Δ) l) → (T′ : Type Δ l′) → Type Δ l

  lof-⊔ : ∀ l₁ l₂ → lof (l₁ ⊔ℕ l₂) ≡ lof l₁ ⊔ lof l₂
  lof-⊔ ℕ.zero l₂ = refl
  lof-⊔ (ℕ.suc l₁) ℕ.zero = refl
  lof-⊔ (ℕ.suc l₁) (ℕ.suc l₂) = cong Level.suc (lof-⊔ l₁ l₂)


  Env* : LEnv → Setω
  Env* Δ = ∀ {l} → l ∈ Δ → Set (lof l)

  ext* : Set (lof l) → Env* Δ → Env* (l ∷ Δ)
  ext* s η (here refl) = s
  ext* s η (there x) = η x

  -- the meaning of a stratified type in terms of Agda universes
  ⟦_⟧ : (T : Type Δ l) → Env* Δ → Set (lof l)
  ⟦ ` x ⟧ η = η x
  ⟦  _`⇒_ {l₁ = l₁}{l₂ = l₂} T₁ T₂ ⟧ η rewrite lof-⊔ l₁ l₂ = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
  ⟦ `∀α_,_ {l = l} lev T ⟧ η rewrite lof-⊔ (ℕ.suc lev) l = (α : Set (lof lev)) → ⟦ T ⟧ (ext* α η)
  ⟦ 𝟙 ⟧ η = ⊤


  postulate
    -- interaction of weakening and env extension
    weaken-ext : ∀ {lev} {T : Type Δ l} {α : Set (lof lev)} {η : Env* Δ} → ⟦ T ⟧ η ≡ ⟦ weakenₜ {l′ = lev} T ⟧ (ext* α η)
    -- interaction of single substitution and env extension
    sub-ext : ∀ {lev} {T : Type Δ lev} {T₁ : Type (lev ∷ Δ) l} {η : Env* Δ} → ⟦ T₁ ⟧ (ext* (⟦ T ⟧ η) η) ≡ ⟦ sub0ₜ T₁ T ⟧ η


  -- type environments
  data TEnv : LEnv → Set where

    ∅    : TEnv []
    _◁*_ : (l : Lvl) → TEnv Δ → TEnv (l ∷ Δ)
    _◁_  : Type Δ l → TEnv Δ → TEnv Δ
  
  data inn : Type Δ l → TEnv Δ → Set where
    here  : ∀ {T : Type Δ l} {Γ} → inn {Δ} T (T ◁ Γ)
    there : ∀ {T : Type Δ l} {T′ : Type Δ l′} {Γ} → inn {Δ} T Γ → inn {Δ} T (T′ ◁ Γ)
    tskip : ∀ {T : Type Δ l} {lev} {Γ} → inn {Δ} T Γ → inn (weakenₜ T) (lev ◁* Γ)

  data Expr {Δ : LEnv} (Γ : TEnv Δ) : Type Δ l → Set where
    `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Γ T
    ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr (T ◁ Γ) T′ → Expr Γ (T `⇒ T′)
    _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Γ (T `⇒ T′) → Expr Γ T → Expr Γ T′
    Λα_⇒_ : ∀ (lev : ℕ) → {T : Type (lev ∷ Δ) l} → Expr (lev ◁* Γ) T → Expr Γ (`∀α lev , T)
    _∙_  : ∀ {lev : Lvl} {T : Type (lev ∷ Δ) l} → Expr Γ (`∀α lev , T) → (T′ : Type Δ lev) → Expr Γ (sub0ₜ T T′)

  Env : {Δ : LEnv} → TEnv Δ → Env* Δ → Setω
  Env {Δ} Γ η = ∀ {l}{T : Type Δ l} → (x : inn T Γ) → ⟦ T ⟧ η

  ext : {Γ : TEnv Δ} {T : Type Δ l} (η : Env* Δ) → ⟦ T ⟧ η → Env Γ η → Env (T ◁ Γ) η
  ext η v γ here = v
  ext η v γ (there x) = γ x

  ext-t : {Γ : TEnv Δ} {lev : Lvl} {α : Set (lof lev)} → (η : Env* Δ) → Env Γ η → Env (lev ◁* Γ) (ext* α η)
  ext-t η γ (tskip x) = subst id weaken-ext (γ x)

  E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Γ T → (η : Env* Δ) → Env Γ η → ⟦ T ⟧ η
  E⟦ ` x ⟧ η γ = γ x
  E⟦ ƛ_ {l = l₁}{l′ = l₂}{T = T}{T′ = T′} e ⟧ η γ
    rewrite lof-⊔ l₁ l₂ = λ v → E⟦ e ⟧ η (ext η v γ)
  E⟦ _·_ {l = l₁}{l′ = l₂} e₁ e₂ ⟧ η γ
    with E⟦ e₁ ⟧ η γ
  ... | v₁
    rewrite lof-⊔ l₁ l₂ = v₁ (E⟦ e₂ ⟧ η γ)
  E⟦ Λα_⇒_ {l = l} lev e ⟧ η γ
    rewrite lof-⊔ (ℕ.suc lev) l = λ (α : Set (lof lev)) → E⟦ e ⟧ (ext* α η) (ext-t η γ)
  E⟦ _∙_ {l = l}{lev = lev} e T ⟧ η γ
    with E⟦ e ⟧ η γ
  ... | v rewrite lof-⊔ (ℕ.suc lev) l =
    let r = v (⟦ T ⟧ η)
    in subst id sub-ext r


module attempt3 where

  open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
  open import Function using (id)

  -- level environments
  LEnv = List Level
  variable
    Δ : LEnv
    ℓ  ℓ′ ℓ₁ ℓ₂ : Level

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
    ext* s η (here refl) = s
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
    lookupₜ (s , _) (here refl) = s
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
