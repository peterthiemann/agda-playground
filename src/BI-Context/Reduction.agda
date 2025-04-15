module Reduction where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Function using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)

open import Syntax

-- expression reduction

data _⟶_ : Expr Γ T ε → Expr Γ T ε → Set where

  β-unit : ∀{M : Expr (𝓖 ↓ ∅) T ε} {cc} {gg} → (unit ⨾ M) cc gg ⟶ M

  cc-sub-⨾ : ∀{Γ₂≼Γ₁ : Γ₂ ≼ Γ₁} {ε₁⊑ε₂ : ε₁ ⊑ ε₂} {L}{M : Expr (𝓖 ↓ ∅) T ε} {cc} {gg}
           → (sub-ctx Γ₂≼Γ₁ ε₁⊑ε₂ L ⨾ M) cc gg
           ⟶ sub-ctx (≼-pattern-cong Γ₂≼Γ₁) (⊑-mon ε₁⊑ε₂) ((L ⨾ M) (cc ∘ ⊑-impure ε₁⊑ε₂) refl)

  β-let  : ∀ {L : Expr Γ T₁ ε₁}{M : Expr (𝓖 ↓ $[ T₁ ]) T ε₂}{cc}
         → let1 L M cc refl
         ⟶ {!!}

  cc-sub-let :  ∀{Γ₂≼Γ₁ : Γ₂ ≼ Γ₁} {ε₁⊑ε₂ : ε₁ ⊑ ε₂} {L : Expr Γ₁ T₁ ε₁}{M : Expr (𝓖 ↓ $[ T₁ ]) T ε} {cc} {gg}
         → let1 (sub-ctx Γ₂≼Γ₁ ε₁⊑ε₂ L) M cc gg
         ⟶ sub-ctx (≼-pattern-cong Γ₂≼Γ₁) (⊑-mon ε₁⊑ε₂) (let1 L M (cc ∘ ⊑-impure ε₁⊑ε₂) refl)
