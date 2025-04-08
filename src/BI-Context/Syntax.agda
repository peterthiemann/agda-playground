{-# OPTIONS --allow-unsolved-metas #-}
module Syntax where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Function using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)

postulate
  funext : {A B : Set}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

variable n : ℕ

data Dir : Set where
  Left Right Unord : Dir

-- effects

infixl 10 _⊔_
infix 5 _⊑_

data Eff : Set where
  Pure Impure : Eff

_⊔_ : Eff → Eff → Eff
Pure ⊔ ε = ε
Impure ⊔ ε = Impure

variable ε ε₁ ε₂ : Eff

is-pure : Eff → Set
is-pure ε = ε ≡ Pure

data _⊑_ : Eff → Eff → Set where
  ⊑-refl : ε ⊑ ε
  ⊑-pi : Pure ⊑ Impure

⊑-top : ε ⊑ Impure
⊑-top {Pure} = ⊑-pi
⊑-top {Impure} = ⊑-refl

⊑-impure : ε₁ ⊑ ε₂ → ε₁ ≡ Impure → ε₂ ≡ Impure
⊑-impure ⊑-refl refl = refl

⊑-mon :  ε₁ ⊑ ε₂ → ε₁ ⊔ ε ⊑ ε₂ ⊔ ε
⊑-mon ⊑-refl = ⊑-refl
⊑-mon ⊑-pi = ⊑-top

-- types and session types

infixl 10 _⨾_
infix 5 _≃_

data Session : Set
data Type : Set where

  Unit : Type
  _⇒[_,_]_ : Type → Dir → Eff → Type → Type
  _⊗[_]_   : Type → Dir → Type → Type
  ΣΣ       : (Fin n → Type) → Type
  Chan     : Session → Type

data Session where
  Skip : Session
  _⨾_ : Session → Session → Session
  Close Wait : Session
  !!_ : Type → Session
  ??_ : Type → Session
  ⊕ : (Fin n → Session) → Session
  & : (Fin n → Session) → Session
  Return Acq : Session

variable T T₁ T₂ : Type
variable S S₁ S₂ S₃ : Session

data _≃_ : Session → Session → Set where
  ≃-refl : S ≃ S
  ≃-sym : S₁ ≃ S₂ → S₂ ≃ S₁
  ≃-trans : S₁ ≃ S₂ → S₂ ≃ S₃ → S₁ ≃ S₃
  ≃-unit-left : Skip ⨾ S ≃ S
  ≃-unit-right : S ⨾ Skip ≃ S
  ≃-assoc : (S₁ ⨾ S₂) ⨾ S₃ ≃ S₁ ⨾ (S₂ ⨾ S₃)
  ≃-cong-⨾-l : S₁ ≃ S₂ → S₁ ⨾ S ≃ S₂ ⨾ S
  ≃-cong-⨾-r : S₁ ≃ S₂ → S ⨾ S₁ ≃ S ⨾ S₂
  ≃-cong-⊕ : ∀{f : Fin n → Session} → ⊕ f ⨾ S ≃ ⊕ λ i → f i ⨾ S
  ≃-cong-& : ∀{f : Fin n → Session} → & f ⨾ S ≃ ⊕ λ i → f i ⨾ S

dual : Session → Session
dual Skip = Skip
dual (S₁ ⨾ S₂) = dual S₁ ⨾ dual S₂
dual Close = Wait
dual Wait = Close
dual (!! T) = ?? T
dual (?? T) = !! T
dual (⊕ f) = & (dual ∘ f)
dual (& f) = ⊕ (dual ∘ f)
dual Return = Return
dual Acq = Acq

dual-involutive : ∀ S → S ≡ dual (dual S)
dual-involutive Skip = refl
dual-involutive (S₁ ⨾ S₂) = cong₂ _⨾_ (dual-involutive S₁) (dual-involutive S₂)
dual-involutive Close = refl
dual-involutive Wait = refl
dual-involutive (!! T) = refl
dual-involutive (?? T) = refl
dual-involutive (⊕ f) = cong ⊕ (funext (λ x → dual-involutive (f x)))
dual-involutive (& f) = cong & (funext (λ x → dual-involutive (f x)))
dual-involutive Return = refl
dual-involutive Acq = refl

-- contexts and patterns

data Context : Set where
  ∅ : Context
  $[_] : Type → Context
  _⨾_ : Context → Context → Context
  _∥_ : Context → Context → Context

is-null-context : Context → Set
is-null-context ∅ = ⊤
is-null-context $[ x ] = ⊥
is-null-context (Γ₁ ⨾ Γ₂) = is-null-context Γ₁ × is-null-context Γ₂
is-null-context (Γ₁ ∥ Γ₂) = is-null-context Γ₁ × is-null-context Γ₂

data Pattern : Set where
  ⟪⟫ : Pattern
  _⨾ˡ_ : Pattern → Context → Pattern
  _⨾ʳ_ : Context → Pattern → Pattern
  _∥_ : Pattern → Context → Pattern

is-left-pattern : Pattern → Set
is-left-pattern ⟪⟫ = ⊤
is-left-pattern (𝓖 ⨾ˡ Γ) = is-left-pattern 𝓖
is-left-pattern (Γ ⨾ʳ 𝓖) = is-null-context Γ × is-left-pattern 𝓖
is-left-pattern (𝓖 ∥ Γ) = is-left-pattern 𝓖

variable
  Γ Γ₁ Γ₂ Γ₃ Γ₄ Γ′ : Context
  𝓖 𝓖₁ 𝓖₂ : Pattern

ctx-pattern-fill : Pattern → Context → Context
ctx-pattern-fill ⟪⟫ Γ = Γ
ctx-pattern-fill (𝓖 ⨾ˡ Γ₂) Γ = ctx-pattern-fill 𝓖 Γ ⨾ Γ₂
ctx-pattern-fill (Γ₁ ⨾ʳ 𝓖) Γ = Γ₁ ⨾ ctx-pattern-fill 𝓖 Γ
ctx-pattern-fill (𝓖 ∥ Γ₂) Γ = ctx-pattern-fill 𝓖 Γ ∥ Γ₂

_↓_ = ctx-pattern-fill

ctx-extend : Dir → Context → Type → Context
ctx-extend Left Γ T = $[ T ] ⨾ Γ
ctx-extend Right Γ T = Γ ⨾ $[ T ]
ctx-extend Unord Γ T = $[ T ] ∥ Γ

data ctx-split : Dir → Context → Context → Context → Set where
  ctx-split-unord    : ctx-split Unord Γ₁ Γ₂ (Γ₁ ∥ Γ₂)
  ctx-split-left     : ctx-split Left Γ₁ Γ₂ (Γ₂ ⨾ Γ₁)
  ctx-split-right    : ctx-split Right Γ₁ Γ₂ (Γ₁ ⨾ Γ₂)

data _≅_ : Context → Context → Set where
  ≅-refl : Γ ≅ Γ
  ≅-sym  : Γ₁ ≅ Γ₂ → Γ₂ ≅ Γ₁
  ≅-trans : Γ₁ ≅ Γ₂ → Γ₂ ≅ Γ₃ → Γ₁ ≅ Γ₃
  ∅-unit-⨾-left   : (∅ ⨾ Γ) ≅ Γ
  ∅-unit-⨾-right  : (Γ ⨾ ∅) ≅ Γ
  ∅-unit-∥-left   : (∅ ∥ Γ) ≅ Γ
  ⨾-assoc         : ((Γ₁ ⨾ Γ₂) ⨾ Γ₃) ≅ (Γ₁ ⨾ (Γ₂ ⨾ Γ₃))
  ∥-assoc         : ((Γ₁ ∥ Γ₂) ∥ Γ₃) ≅ (Γ₁ ∥ (Γ₂ ∥ Γ₃))
  ∥-comm          : (Γ₁ ∥ Γ₂) ≅ (Γ₂ ∥ Γ₁)
  ⨾-cong-left      : Γ₁ ≅ Γ₂ → (Γ₁ ⨾ Γ₃) ≅ (Γ₂ ⨾ Γ₃)
  ⨾-cong-right     : Γ₁ ≅ Γ₂ → (Γ₃ ⨾ Γ₁) ≅ (Γ₃ ⨾ Γ₂)
  ∥-cong-left      : Γ₁ ≅ Γ₂ → (Γ₁ ∥ Γ₃) ≅ (Γ₂ ∥ Γ₃)

∥-cong-right :  Γ₁ ≅ Γ₂ → (Γ ∥ Γ₁) ≅ (Γ ∥ Γ₂)
∥-cong-right Γ₁≅Γ₂ = ≅-trans ∥-comm (≅-trans (∥-cong-left Γ₁≅Γ₂) ∥-comm)

∅-unit-∥-right   : (Γ ∥ ∅) ≅ Γ
∅-unit-∥-right = ≅-trans ∥-comm ∅-unit-∥-left

data _≼_ : Context → Context → Set where
  ≼-≅ : Γ₁ ≅ Γ₂ → Γ₁ ≼ Γ₂
  ≼-trans : Γ₁ ≼ Γ₂ → Γ₂ ≼ Γ₃ → Γ₁ ≼ Γ₃
  ≼-weak : ((Γ₁ ⨾ Γ₂) ∥ (Γ₃ ⨾ Γ₄)) ≼ ((Γ₁ ∥ Γ₃) ⨾ (Γ₂ ∥ Γ₄))
  ≼-⨾-cong-left : Γ₁ ≼ Γ₂ → (Γ₁ ⨾ Γ₃) ≼ (Γ₂ ⨾ Γ₃)
  ≼-⨾-cong-right : Γ₁ ≼ Γ₂ → (Γ₃ ⨾ Γ₁) ≼ (Γ₃ ⨾ Γ₂)
  ≼-∥-cong-left : Γ₁ ≼ Γ₂ → (Γ₁ ∥ Γ₃) ≼ (Γ₂ ∥ Γ₃)

≼-pattern-cong : Γ₂ ≼ Γ₁ → (𝓖 ↓ Γ₂) ≼ (𝓖 ↓ Γ₁)
≼-pattern-cong {𝓖 = ⟪⟫} Γ₂≼Γ₁ = Γ₂≼Γ₁
≼-pattern-cong {𝓖 = 𝓖 ⨾ˡ Γ} Γ₂≼Γ₁ = ≼-⨾-cong-left (≼-pattern-cong Γ₂≼Γ₁)
≼-pattern-cong {𝓖 = Γ ⨾ʳ 𝓖} Γ₂≼Γ₁ = ≼-⨾-cong-right (≼-pattern-cong Γ₂≼Γ₁)
≼-pattern-cong {𝓖 = 𝓖 ∥ Γ} Γ₂≼Γ₁ = ≼-∥-cong-left (≼-pattern-cong Γ₂≼Γ₁)

data _∋_ : Context → Type → Set where
  here   : $[ T ] ∋ T
  left-⨾ : Γ₁ ∋ T → (Γ₁ ⨾ Γ₂) ∋ T
  right-⨾ : Γ₂ ∋ T → (Γ₁ ⨾ Γ₂) ∋ T
  left-∥ : Γ₁ ∋ T → (Γ₁ ∥ Γ₂) ∋ T
  right-∥ : Γ₂ ∋ T → (Γ₁ ∥ Γ₂) ∋ T

-- expressions

data eff-split : Dir → Eff → Eff → Set where
  eff-split-unord : eff-split Unord ε₁ ε₂
  eff-split-left  : eff-split Left Pure ε₂
  eff-split-right : eff-split Right ε₁ Pure


data Expr : Context → Type → Eff → Set where
  var  : Expr $[ T ] T Pure
  lam  : (d : Dir) → Expr (ctx-extend d Γ T₁) T₂ ε → Expr Γ (T₁ ⇒[ d , ε ] T₂) Pure
  app  : (d : Dir) → ctx-split d Γ₁ Γ₂ Γ → eff-split d ε₁ ε₂
       → Expr Γ₁ (T₂ ⇒[ d , ε ] T₁) ε₁ → Expr Γ₂ T₂ ε₂
       → Expr Γ T₁ (ε₁ ⊔ ε₂ ⊔ ε)
  unit : Expr ∅ Unit Pure
  _⨾_   : Expr Γ Unit ε₁ → Expr (𝓖 ↓ ∅) T ε₂ → (ε₁ ≡ Impure → is-left-pattern 𝓖)
        → Expr (𝓖 ↓ Γ) T (ε₁ ⊔ ε₂)
  let1  : Expr Γ T₁ ε₁ → Expr (𝓖 ↓ $[ T₁ ]) T ε₂ → (ε₁ ≡ Impure → is-left-pattern 𝓖)
        → Expr (𝓖 ↓ Γ) T (ε₁ ⊔ ε₂)
  prod : (d : Dir) → ctx-split d Γ₁ Γ₂ Γ → eff-split d ε₁ ε₂
       → Expr Γ₁ T₁ ε₁ → Expr Γ₂ T₂ ε₂
       → Expr Γ (T₁ ⊗[ d ] T₂) (ε₁ ⊔ ε₂)
  case-⊗ : (d : Dir) → Expr Γ (T₁ ⊗[ d ] T₂) ε₁ →  Expr (𝓖 ↓ ctx-extend d ($[ T₁ ]) T₂) T ε₂ → (ε₁ ≡ Impure → is-left-pattern 𝓖)
         → Expr (𝓖 ↓ Γ) T (ε₁ ⊔ ε₂)
  inj   : ∀{f : Fin n → Type} → (i : Fin n) → Expr Γ (f i) ε → Expr Γ (ΣΣ f) ε
  case-ΣΣ : ∀{f : Fin n → Type} → Expr Γ (ΣΣ f) ε₁ → ((i : Fin n) → Expr (𝓖 ↓ $[ f i ]) T ε₂) → (ε₁ ≡ Impure → is-left-pattern 𝓖)
          → Expr (𝓖 ↓ Γ) T (ε₁ ⊔ ε₂)
  sub : Γ₂ ≼ Γ₁ → ε₁ ⊑ ε₂ → Expr Γ₁ T ε₁ → Expr Γ₂ T ε₂

-- processes

data Bind : Set where
  ● : Bind
  _⨾_ _∥_ : Bind → Bind → Bind

variable b b₁ b₂ b₃ b₄ : Bind

data _⊢_↝_ : Session → Bind → Context → Set where
  b-var  : S ⊢ ● ↝ $[ Chan S ]
  b-lsplit : S₁ ⊢ b₁ ↝ Γ₁ →  S₂ ⊢ b₂ ↝ Γ₂ → (S₁ ⨾ S₂) ⊢ (b₁ ⨾ b₂) ↝ (Γ₁ ⨾ Γ₂)
  b-rsplit : (S₁ ⨾ Return) ⊢ b₁ ↝ Γ₁ → (Acq ⨾ S₂) ⊢ b₂ ↝ Γ₂ → (S₁ ⨾ S₂) ⊢ (b₁ ∥ b₂) ↝ (Γ₁ ∥ Γ₂)
  b-conv : S₁ ≃ S₂ → S₁ ⊢ b ↝ Γ → S₂ ⊢ b ↝ Γ

data Proc : Context → Set where
  ⟨_⟩ : Expr Γ Unit ε → Proc Γ
  mix : (Γ₁ ∥ Γ₂) ≅ Γ → Proc Γ₁ → Proc Γ₂ → Proc Γ
  ν : (b₁ b₂ : Bind) → (S : Session) → S ⊢ b₁ ↝ Γ₁ → dual S ⊢ b₂ ↝ Γ₂ → Proc ((Γ₁ ∥ Γ₂) ∥ Γ) → Proc Γ

variable P P₁ P₂ P₃ : Proc Γ

p-conv : Γ₁ ≅ Γ₂ → Proc Γ₁ → Proc Γ₂
p-conv Γ₁≅Γ₂ ⟨ M ⟩ = ⟨ (sub (≼-≅ (≅-sym Γ₁≅Γ₂)) ⊑-refl M) ⟩
p-conv Γ₁≅Γ₂ (mix Γ≅ P₁ P₂) = mix (≅-trans Γ≅ Γ₁≅Γ₂) P₁ P₂
p-conv Γ₁≅Γ₂ (ν b₁ b₂ S Sb₁ Sb₂ P) = ν b₁ b₂ S Sb₁ Sb₂ (p-conv (∥-cong-right Γ₁≅Γ₂) P)

-- congruence
-- Q: is it too specific to ask for ∅-unit-∥-left in ≣-unit-left and ≣-unit-right?
-- Q: -""- for ≅-refl in ≣-assoc

data _≣_ : Proc Γ → Proc Γ → Set where
  ≣-unit-left : mix ∅-unit-∥-left ⟨ unit ⟩ P ≣ P
  ≣-unit-right : mix ∅-unit-∥-right P ⟨ unit ⟩ ≣ P
  ≣-comm : ∀ (Γ≅Γ′ : (Γ₁ ∥ Γ₂) ≅ Γ) → mix Γ≅Γ′ P₁ P₂ ≣ mix (≅-trans ∥-comm Γ≅Γ′) P₂ P₁
  ≣-assoc : mix ≅-refl P₁ (mix ≅-refl P₂ P₃) ≣ mix ∥-assoc (mix ≅-refl P₁ P₂) P₃
  ≣-swap : ∀ {Sb₁ : S ⊢ b₁ ↝ Γ₁} {Sb₂ : dual S ⊢ b₂ ↝ Γ₂}
    → ν{Γ = Γ} b₁ b₂ S Sb₁ Sb₂ P
    ≣ ν{Γ = Γ} b₂ b₁ (dual S) Sb₂ (subst (_⊢ b₁ ↝ Γ₁) (dual-involutive S) Sb₁) (p-conv (∥-cong-left ∥-comm) P)
  ≣-extend : ∀ {P₃ : Proc Γ₃}{Sb₁ : S ⊢ b₁ ↝ Γ₁} {Sb₂ : dual S ⊢ b₂ ↝ Γ₂}
    → mix ≅-refl P₃ (ν{Γ = Γ} b₁ b₂ S Sb₁ Sb₂ P)
    ≣ ν{Γ = (Γ₃ ∥ Γ)} b₁ b₂ S Sb₁ Sb₂ (mix (≅-trans (≅-sym ∥-assoc) (≅-trans (∥-cong-left ∥-comm) ∥-assoc)) P₃ P)
  ≣-res-comm : ∀{Sb₁ : S₁ ⊢ b₁ ↝ Γ₁} {Sb₂ : dual S₁ ⊢ b₂ ↝ Γ₂}{Sb₃ : S₂ ⊢ b₃ ↝ Γ₃} {Sb₄ : dual S₂ ⊢ b₄ ↝ Γ₄} →
    (ν b₁ b₂ S₁ Sb₁ Sb₂ (ν b₃ b₄ S₂ Sb₃ Sb₄ P))
    ≣ ν b₃ b₄ S₂ Sb₃ Sb₄ (ν b₁ b₂ S₁ Sb₁ Sb₂ (p-conv (≅-trans (≅-sym ∥-assoc) (≅-trans (∥-cong-left ∥-comm) ∥-assoc)) P))
