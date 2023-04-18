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
