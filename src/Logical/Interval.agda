module Interval where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ;zero;suc) renaming (_≤_ to _≤ℕ_; _⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _*_ to _*ℕ_; _⊓_ to _⊓ℕ_)
open import Data.Nat.Properties using (≤-refl; *-zeroʳ; +-identityʳ)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

-- intervals on natural numbers

record Ivl : Set where
  constructor ⟪_,_⟫
  field
    lo : ℕ
    hi : Maybe ℕ

_∈∈_ : ℕ → Ivl → Set
n ∈∈ ⟪ lo , just hi ⟫ = lo ≤ℕ n × n ≤ℕ hi
n ∈∈ ⟪ lo , nothing ⟫ = lo ≤ℕ n

_⊔M_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
just x ⊔M just x₁ = just (x ⊔ℕ x₁)
just x ⊔M nothing = just x
nothing ⊔M x₁ = x₁

_≤M_ : Maybe ℕ → Maybe ℕ → Set
x ≤M nothing = ⊤
just x ≤M just x₁ = x ≤ℕ x₁
nothing ≤M just x₁ = ⊥

_*M_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
just x *M just x₁ = just (x *ℕ x₁)
just zero *M nothing = just zero
just (suc x) *M nothing = nothing
nothing *M just zero = just zero
nothing *M just (suc x) = nothing
nothing *M nothing = nothing

_+M_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
just x +M just x₁ = just (x +ℕ x₁)
just x +M nothing = nothing
nothing +M x₁ = nothing

≤M-refl : ∀ {x} → x ≤M x
≤M-refl {just x} = ≤-refl
≤M-refl {nothing} = tt

*M-zero-left : ∀ {x} → just 0 *M x ≡ just 0
*M-zero-left {just x} = refl
*M-zero-left {nothing} = refl

*M-zero-right : ∀ {x} → x *M just 0 ≡ just 0
*M-zero-right {just x} = cong just (*-zeroʳ x)
*M-zero-right {nothing} = refl

*M-identity-left : ∀ {x} → just 1 *M x ≡ x
*M-identity-left {just x} = cong just (+-identityʳ x)
*M-identity-left {nothing} = refl

_⊔_ : Ivl → Ivl → Ivl
⟪ lo , hi ⟫ ⊔ ⟪ lo₁ , hi₁ ⟫ = ⟪ lo ⊓ℕ lo₁ , hi ⊔M hi₁ ⟫

_≤_ : Ivl → Ivl → Set
⟪ lo , hi ⟫ ≤ ⟪ lo₁ , hi₁ ⟫ = lo₁ ≤ℕ lo × (hi ≤M hi₁)

_*_ : Ivl → Ivl → Ivl
⟪ lo , hi ⟫ * ⟪ lo₁ , hi₁ ⟫ = ⟪ lo *ℕ lo₁ , hi *M hi₁ ⟫

_+_ : Ivl → Ivl → Ivl
⟪ lo , hi ⟫ + ⟪ lo₁ , hi₁ ⟫ = ⟪ lo +ℕ lo₁ , hi +M hi₁ ⟫
