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

open import Data.Product

even-n*n+1 : ∀ n → ∃[ m ] (m + m ≡ suc n * n)
even-n*n+1 zero = 0 , refl
even-n*n+1 (suc n) with even-n*n+1 n
... | m , m+m≡n+1*n =
  suc n + m ,
  (begin
    suc n + m + (suc n + m)
  ≡⟨ +-assoc (suc n) m (suc n + m) ⟩
    suc n + (m + (suc n + m))
  ≡⟨ cong (suc n +_) (begin 
                       m + (suc n + m)
                     ≡⟨ +-suc m (n + m) ⟩
                       suc (m + (n + m))
                     ≡⟨ cong suc (+-comm m (n + m) ) ⟩
                       suc (n + m + m)
                     ≡⟨ cong suc (+-assoc n m m) ⟩
                       suc (n + (m + m))
                     ∎) ⟩
    suc (n + suc (n + (m + m)))
  ≡⟨ cong (λ N → suc (n + suc (n + N))) m+m≡n+1*n ⟩
    suc (n + suc (n + suc n * n))
  ≡⟨ cong (λ N → suc (n + suc (n + N))) (*-comm (suc n) n) ⟩
    suc (n + suc (n + n * suc n))
  ∎)

next-n*n+1*n+2 : ∀ n → ∃[ m ] (m + m + m ≡ suc (suc n) * (suc n * n))
next-n*n+1*n+2 zero = 0 , refl
next-n*n+1*n+2 (suc n) with next-n*n+1*n+2 n
... | m , m+m+m≡n+2*n+1*n =
  {!!} ,
  {!!}


mult-up : ℕ → ℕ → ℕ
mult-up zero n = 1
mult-up (suc k) n = mult-up k (suc n) * n

mult-up-property : ∀ k n → mult-up k (suc n) * n ≡ (k + n) * mult-up k n
mult-up-property zero n = *-comm 1 n
mult-up-property (suc k) n
  with mult-up-property k n
... | ih = {!!}

mult-up-lemma : ∀ k n → ∃[ m ] (mult-up (suc k) n ≡ (k + n) * m)
mult-up-lemma k n =
  mult-up k n ,
  (begin
    mult-up k (suc n) * n
  ≡⟨ mult-up-property k n ⟩
    (k + n) * mult-up k n
  ∎)

-- mult-up-lemma zero n = 1 ,
--   (begin
--     n + 0
--   ≡⟨ *-comm 1 n ⟩
--     n * 1
--   ∎)
-- mult-up-lemma (suc k) n = {!!}

-- in full generality:
-- ∀ k n → ∃[ m ] (suc k * m ≡ mult-up k n)

-- ∃[ m ] ( suc k * m ≡ n * (n + 1) * ... * (n + k))

-- n ≡ 0:
--     let m := 0

-- suc n: (n + 1) * (n + 2) * ... * (n + k) * (n + k + 1)
--        = (n + 1) * (n + 2) * ... * (n + k) * n   +             (n + 1) * (n + 2) * ... * (n + k) * (k + 1)
--   =(IH)= (k + 1) * m                             +   (k + 1) * (n + 1) * (n + 2) * ... * (n + k)
--   let m' = m + (n + 1) * (n + 2) * ... * (n + k)
--        = (k + 1) * m'
