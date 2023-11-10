module Arithmetic.Gauss where

open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

sumup : ℕ → ℕ
sumup zero = 0
sumup (suc n) = sumup n + suc n

gauss : ∀ n → 2 * sumup n ≡ n * suc n
gauss zero = refl
gauss (suc n) =
  begin
    2 * sumup (suc n)
  ≡⟨ cong (sumup n + suc n +_) (+-assoc (sumup n) (suc n) zero) ⟩
    sumup n + suc n + (sumup n + (suc n + zero))
  ≡⟨ +-assoc (sumup n) (suc n) (sumup n + (suc n + zero)) ⟩
    sumup n + (suc n + (sumup n + (suc n + zero)))
  ≡⟨ cong (sumup n +_) (+-comm (suc n) (sumup n + (suc n + zero))) ⟩
    sumup n + (sumup n + (suc n + zero) + suc n)
  ≡⟨ cong (sumup n +_) (+-assoc (sumup n) (suc n + zero) (suc n)) ⟩
    sumup n + (sumup n + (suc n + zero + suc n))
  ≡⟨ sym (+-assoc (sumup n) (sumup n) (suc n + zero + suc n)) ⟩
    sumup n + sumup n + (suc n + zero + suc n)
  ≡⟨ cong (sumup n + sumup n +_) (cong (_+ suc n) (+-comm (suc n) zero)) ⟩
    sumup n + sumup n + (suc n + suc n)
  ≡⟨ cong (λ K → sumup n + K + (suc n + suc n)) (sym (+-identityʳ (sumup n))) ⟩
    sumup n + (sumup n + 0) + (suc n + suc n)
  ≡⟨ refl ⟩
    2 * sumup n + (suc n + suc n)
  ≡⟨ cong (_+ (suc n + suc n)) (gauss n) ⟩
    n * suc n + (suc n + suc n)
  ≡⟨ sym (+-assoc (n * suc n) (suc n) (suc n)) ⟩
    n * suc n + suc n + suc n
  ≡⟨ cong (_+ suc n) (+-comm (n * suc n) (suc n)) ⟩
    suc n + n * suc n + suc n
  ≡⟨ refl ⟩
    suc n * suc n + suc n
  ≡⟨ +-comm (suc n * suc n) (suc n) ⟩
    suc n + suc n * suc n
  ≡⟨ refl ⟩
    suc (suc n) * suc n
  ≡⟨ *-comm (suc (suc n)) (suc n) ⟩
    suc n * suc (suc n)
  ∎
