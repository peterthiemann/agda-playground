module DVector where

open import Level
open import Data.Nat
open import Data.Fin

extend : ∀ {ℓ}{A : Set ℓ}{n} → ((i : Fin n) → A) → A → (i : Fin (ℕ.suc n)) → A
extend f a zero = a
extend f a (suc i) = f i

data DVec {ℓ} : (n : ℕ) → (Fin n → Set ℓ) → Set (Level.suc ℓ) where
  []  : DVec 0 (λ())
  _∷_ : ∀ {n}{F : Fin n → Set ℓ}{A : Set ℓ} → A → DVec n F → DVec (ℕ.suc n) (extend F A)
