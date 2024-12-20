module Universes where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Empty renaming (⊥ to Zero)
open import Data.Unit renaming (⊤ to One)
open import Data.Bool using () renaming (Bool to Two)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃-syntax)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)

-- preamble of chapter 6

sum : ∀ n → (Fin n → ℕ) → ℕ
sum zero _ = 0
sum (suc n) f = f zero +ℕ (sum n (f ∘ suc))

prod : ∀ n → (Fin n → ℕ) → ℕ
prod zero f = 1
prod (suc n) f = f zero *ℕ (prod n (f ∘ suc))

module X1 where
  data FTy : Set
  # : FTy → ℕ

  data FTy where
    fin : ℕ → FTy
    σ π : (S : FTy) (T : Fin (# S) → FTy) → FTy

  # (fin n) = n
  # (σ T f) = sum (# T) (# ∘ f)
  # (π T f) = prod (# T) (# ∘ f)

  _ : # (σ (fin 101) λ s → fin (toℕ s)) ≡ 5050
  _ = refl

module X2 where
  data FTy : Set
  FEI : FTy → Set

  data FTy where
    fin : ℕ → FTy
    σ π : (S : FTy) (T : FEI S → FTy) → FTy

  FEI (fin n) = Fin n
  FEI (σ T₁ T₂) = Σ (FEI T₁) (FEI ∘ T₂)
  FEI (π T₁ T₂) = (s : FEI T₁) → (FEI ∘ T₂) s
    

-- section 4: Indexed Containers

record _▷_ (I J : Set) : Set₁ where
  constructor _◁_$_
  field
    ShIx : J → Set
    PoIx : (j : J) → ShIx j → Set
    riIx : (j : J) (s : ShIx j) (p : PoIx j s) → I
  ⟦_⟧ᵢ : (I → Set) → (J → Set)
  ⟦_⟧ᵢ X j = Σ (ShIx j) λ s → (p : PoIx j s) → X (riIx j s p)
open _▷_ public

-- section 4.1


data ITree {J : Set} (C : J ▷ J) (j : J) : Set where
  ⟨_⟩ : ⟦ C ⟧ᵢ (ITree C) j → ITree C j


-- universes

mutual
  data TU : Set where
    Zero′ One′ Two′ : TU
    Σ′ Π′ : (S : TU) (T : ⟦ S ⟧TU → TU) → TU
    Tree′ : (I : TU)
            (F : ⟦ I ⟧TU → Σ TU λ S →
                 ⟦ S ⟧TU → Σ TU λ P →
                 ⟦ P ⟧TU → ⟦ I ⟧TU)
            (i : ⟦ I ⟧TU) → TU
  ⟦_⟧TU : TU → Set
  ⟦ Zero′ ⟧TU = Zero
  ⟦ One′ ⟧TU = One
  ⟦ Two′ ⟧TU = Two
  ⟦ Σ′ S T ⟧TU = Σ ⟦ S ⟧TU λ s → ⟦ T s ⟧TU
  ⟦ Π′ S T ⟧TU = (s : ⟦ S ⟧TU) → ⟦ T s ⟧TU
  ⟦ Tree′ I F i ⟧TU = ITree
                      ( (λ i → ⟦ proj₁ (F i) ⟧TU)
                      ◁ (λ i s → ⟦ proj₁ (proj₂ (F i) s) ⟧TU)
                      $ (λ i s p → proj₂ (proj₂ (F i) s) p)
                      ) i


-- stlc in TU

module stlc-in-TU where
  -- types
  data Type : Set where
    Base : Type
    _⇒_ : Type → Type → Type

  encode : Type → TU
  encode Base = One′
  encode (t ⇒ t₁) = Π′ (encode t) (λ _ → encode t₁)

  ⟦_⟧ₜ : (t : Type) → Set
  ⟦ t ⟧ₜ = ⟦ encode t ⟧TU


  data Env : Set where
    ∅ : Env
    _,_ : Type → Env → Env

  encode-env : Env → TU
  encode-env ∅ = One′
  encode-env (A , Γ) = Σ′ (encode A) (λ _ → encode-env Γ)

  ⟦_⟧E : Env → Set
  ⟦ Γ ⟧E = ⟦ encode-env Γ ⟧TU

  data _∋_ : Env → Type → Set where
    Z : ∀{t}{Γ} → (t , Γ) ∋ t
    S : ∀{t}{t′}{Γ} → Γ ∋ t → (t′ , Γ) ∋ t

  lookup : ∀{Γ}{t} → ⟦ Γ ⟧E → Γ ∋ t → ⟦ t ⟧ₜ
  lookup (v , _) Z = v
  lookup (_ , γ) (S x) = lookup γ x

  data Expr : Env → Type → Set where
    Unit : ∀{Γ} → Expr Γ Base
    Var  : ∀{Γ} {t} → Γ ∋ t → Expr Γ t
    Lam  : ∀{Γ} {t′}{t} → Expr (t′ , Γ) t → Expr Γ (t′ ⇒ t)
    App  : ∀{Γ} {t′}{t} → Expr Γ (t′ ⇒ t) → Expr Γ t′ → Expr Γ t

  ⟦_⟧ₑ : ∀{Γ}{t} → (e : Expr Γ t) → (γ : ⟦ Γ ⟧E) → ⟦ t ⟧ₜ
  ⟦ Unit ⟧ₑ γ = tt
  ⟦ Var x ⟧ₑ γ = lookup γ x
  ⟦ Lam e ⟧ₑ γ = λ v → ⟦ e ⟧ₑ (v , γ)
  ⟦ App e e₁ ⟧ₑ γ = ⟦ e ⟧ₑ γ (⟦ e₁ ⟧ₑ γ)

-- section 4.8.3 powerset and families

Pow : Set₁ → Set₁
Pow X = X → Set
Fam : Set₁ → Set₁
Fam X = Σ Set λ I → I → X

----------------------------------------------------------------------
-- 6.3 a cumulative universe

mutual
  data NU (X : Fam Set) : Set where
    U′ : NU X
    El′ : proj₁ X → NU X
    Nat′ : NU X
    Π′ Σ′ : (S : NU X) (T : ⟦ S ⟧NU → NU X) → NU X
  ⟦_⟧NU : ∀ {X} → NU X → Set
  ⟦_⟧NU {U , El } U′ = U
  ⟦_⟧NU {U , El }(El′ T ) = El T
  ⟦ Nat′ ⟧NU = ℕ
  ⟦ Π′ S T ⟧NU = (s : ⟦ S ⟧NU) → ⟦ T s ⟧NU
  ⟦ Σ′ S T ⟧NU = Σ (⟦ S ⟧NU) λ s → ⟦ T s ⟧NU

EMPTY : Fam Set
EMPTY = Zero , (λ{()})

-- -- this definition does not reduce to a pair as long as the level is unknown
-- LEVEL : ℕ → Fam Set
-- LEVEL zero = NU EMPTY , ⟦_⟧NU
-- LEVEL (suc n) = NU (LEVEL n) , ⟦_⟧NU

LEVEL go : ℕ → Fam Set

LEVEL l = NU (go l) , ⟦_⟧NU

go zero = EMPTY
go (suc n) = LEVEL n

CODE : ℕ → Set
CODE l = proj₁ (LEVEL l)

-- five different names for ℕ → ℕ

n0 : CODE 0
n0 = Π′ Nat′ (λ x → Nat′)

n1 : CODE 1
n1 = Π′ Nat′ (λ _ → Nat′)

n2 : CODE 1
n2 = El′ n0

n3 : CODE 1
n3 = Π′ (El′ Nat′) (λ _ → El′ Nat′)

n4 : CODE 2
n4 = El′ n2

n5 : CODE 0
n5 = Π′ U′ λ{()}

n6 : CODE 1
n6 = Π′ U′ λ x → U′

module stratified-in-NU where
  -- denotational semantics of stratified system F in NU

  -- open import Level
  open import Data.List using (List; []; _∷_)

  Level = ℕ

  variable l l′ l₁ l₂ l₃ : Level

  --! TF >

  -- level environments

  --! LEnv
  LEnv = List Level

  variable Δ Δ₁ Δ₂ Δ₃ : LEnv

  -- type variables

  data _∈_ : Level → LEnv → Set where
    here   : l ∈ (l ∷ Δ)
    there  : l ∈ Δ → l ∈ (l′ ∷ Δ)

  Δ-level : LEnv → Level
  Δ-level [] = 0
  Δ-level (x ∷ Δ) = suc x ⊔ Δ-level Δ

  -- types

  --! Type
  data Type Δ : Level → Set where
    `ℕ      : Type Δ zero
    _⇒_     : (T₁ : Type Δ l₁) (T₂ : Type Δ l₂) → Type Δ (l₁ ⊔ l₂)
    `_      : (α : l ∈ Δ) → Type Δ l
    `∀α_,_  : (l : Level) (T : Type (l ∷ Δ) l′) → Type Δ (suc l ⊔ l′)

  -- property of Nat._⊔_
  lub-to-diff : l ≡ l₁ ⊔ l₂ → ∃[ n₁ ] ∃[ n₂ ] n₁ +ℕ l₁ ≡ l × n₂ +ℕ l₂ ≡ l
  lub-to-diff {l₁ = zero}{l₂ = l₂} refl = l₂ , 0 , +-identityʳ l₂ , refl
  lub-to-diff {l₁ = suc l₁} {l₂ = zero} refl = 0 , suc l₁ , refl , cong suc (+-identityʳ l₁)
  lub-to-diff {l₁ = suc l₁} {l₂ = suc l₂} refl
    with lub-to-diff {l₁ = l₁}{l₂ = l₂} refl
  ... | n₁ , n₂ , eq₁ , eq₂
    = n₁ , n₂ , trans (+-suc n₁ l₁) (cong suc eq₁) , trans (+-suc n₂ l₂) (cong suc eq₂)

  lifter : ∀ {n} → CODE l → CODE (n +ℕ l)
  lifter {n = zero} v = v
  lifter {n = suc n} v = El′ (lifter v)

  encode : Type Δ l → CODE l
  encode `ℕ = Nat′
  encode (_⇒_ {l₁}{l₂} T₁ T₂)
    with lub-to-diff {l₁ = l₁}{l₂ = l₂} refl
  ... | n₂ , n₁ , eq₁ , eq₂
    = Π′ (subst CODE eq₁ (lifter (encode T₁))) λ _ →
          subst CODE eq₂ (lifter (encode T₂))
  encode (` x) = U′
  encode (`∀α_,_ {l′ = l′} l T₁)
    with lub-to-diff {l₁ = suc l}{l₂ = l′} refl
  ... | n₁ , n₂ , eq₁ , eq₂
    = Π′ U′ (λ x → subst CODE eq₂ (lifter (encode T₁)))

  variable T T′ T₁ T₂ : Type Δ l

  -- semantic environments (mapping level l to an element of Set l)

  --! TEnv
  Env* : LEnv → Set
  Env* Δ = ∀ {l} → l ∈ Δ → CODE (Δ-level Δ)

  lookup : Env* Δ
  lookup here = U′
  lookup {Δ = l ∷ Δ} (there {l′ = l′} x)
    with lub-to-diff {l₁ = suc l′} {l₂ = Δ-level Δ} refl
  ... | n₁ , n₂ , eq₁ , eq₂ = subst CODE eq₂ (lifter (lookup x))

  variable
    η η₁ η₂ : Env* Δ  

  -- lookup : l ∈ Δ → Env* Δ → Set l
  -- lookup here      (x ∷ _) = x
  -- lookup (there x) (_ ∷ η) = lookup x η

  -- apply-env : Env* Δ → l ∈ Δ → Set l
  -- apply-env η x = lookup x η

  -- the meaning of a stratified type in terms of NU

  -- --! TSem
  -- ⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
  -- ⟦ `ℕ         ⟧ η = ℕ
  -- ⟦ T₁ ⇒ T₂    ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
  -- ⟦ ` α        ⟧ η = lookup α η  
  -- ⟦ `∀α l , T  ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)

  --! TSem
  -- incorrect
  ⟦_⟧ : (T : Type Δ l) (η : Env* Δ) → Set
  ⟦ T ⟧ η = ⟦ encode T ⟧NU


module stlc-in-NU where

  F : Fam Set
  proj₁ F = One
  proj₂ F = λ x → One

  -- types
  data Type : Set where
    Base : Type
    _⇒_ : Type → Type → Type

  encode : Type → NU F
  encode Base = Nat′
  encode (t ⇒ t₁) = Π′ (encode t) (λ _ → encode t₁)

  ⟦_⟧ₜ : (t : Type) → Set
  ⟦ t ⟧ₜ = ⟦ encode t ⟧NU

  data Env : Set where
    ∅ : Env
    _,_ : Type → Env → Env

  ⟦_⟧E : Env → Set
  ⟦ ∅ ⟧E = One
  ⟦ t , Γ ⟧E = ⟦ t ⟧ₜ × ⟦ Γ ⟧E


  data _∋_ : Env → Type → Set where
    Z : ∀{t}{Γ} → (t , Γ) ∋ t
    S : ∀{t}{t′}{Γ} → Γ ∋ t → (t′ , Γ) ∋ t

  lookup : ∀{Γ}{t} → ⟦ Γ ⟧E → Γ ∋ t → ⟦ t ⟧ₜ
  lookup (v , _) Z = v
  lookup (_ , γ) (S x) = lookup γ x

  data Expr : Env → Type → Set where
    Unit : ∀{Γ} → Expr Γ Base
    Var  : ∀{Γ} {t} → Γ ∋ t → Expr Γ t
    Lam  : ∀{Γ} {t′}{t} → Expr (t′ , Γ) t → Expr Γ (t′ ⇒ t)
    App  : ∀{Γ} {t′}{t} → Expr Γ (t′ ⇒ t) → Expr Γ t′ → Expr Γ t

  ⟦_⟧ₑ : ∀{Γ}{t} → (e : Expr Γ t) → (γ : ⟦ Γ ⟧E) → ⟦ t ⟧ₜ
  ⟦ Unit ⟧ₑ γ = zero
  ⟦ Var x ⟧ₑ γ = lookup γ x
  ⟦ Lam e ⟧ₑ γ = λ s → ⟦ e ⟧ₑ (s , γ)
  ⟦ App e e₁ ⟧ₑ γ = ⟦ e ⟧ₑ γ (⟦ e₁ ⟧ₑ γ)
  
