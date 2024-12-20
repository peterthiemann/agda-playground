module VectorReverse where

open import Data.Vec
open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

module contradictory where
  bad : Set
  bad = zero ≡ suc zero

  postulate
    contra : zero ≡ suc zero

  crush : ∀ n → zero ≡ n
  crush zero = refl
  crush (suc n) rewrite sym (crush n) = contra

variable
  A : Set
  n m : ℕ

data Vec′ (A : Set) : ℕ → Set where
  []  : Vec′ A zero
  _∷_ : ∀ {n} → A → Vec′ A n → Vec′ A (suc n)

append : ∀ {A m n} → Vec′ A m → Vec′ A n → Vec′ A (m + n)
append [] W = W
append {A}{suc m}{n} (x ∷ V) W = x ∷ append V W

module standard-does-not-work-well where

  revAcc : Vec A n → Vec A m → Vec A (n + m)
  revAcc [] ys = ys
  revAcc {n = suc n}{m = m} (x ∷ xs) ys
    with revAcc xs (x ∷ ys)
  ... | r
    rewrite +-suc n m = r

  vreverse : Vec A n → Vec A n
  vreverse {n = n} xs
    with revAcc xs []
  ... | r
    rewrite +-identityʳ n = r

module very-explicit-does-not-work-either where
  _+-acc_  : ℕ → ℕ → ℕ
  zero +-acc zero = zero
  zero +-acc suc m = suc m
  suc n +-acc zero = suc n
  suc n +-acc suc m = n +-acc (suc (suc m))

  revAcc : Vec A n → Vec A m → Vec A (n +-acc m)
  revAcc [] [] = []
  revAcc [] (y ∷ ys) = y ∷ ys
  revAcc (x ∷ xs) [] = {!revAcc xs (x ∷ [])!}
  revAcc (x ∷ xs) (y ∷ ys) = revAcc xs (x ∷ y ∷ ys)

  vreverse : Vec A n → Vec A n
  vreverse xs = {!revAcc xs []!}



_+-acc_ : ℕ → ℕ → ℕ
zero +-acc m = m
suc n +-acc m = n +-acc suc m

+-acc-+ : ∀ n m → n +-acc m ≡ n + m
+-acc-+ zero m = refl
+-acc-+ (suc n) m rewrite +-acc-+ n (suc m) = +-suc n m

revAcc : Vec A n → Vec A m → Vec A (n +-acc m)
revAcc [] ys = ys
revAcc (x ∷ xs) ys = revAcc xs (x ∷ ys)

vreverse : Vec A n → Vec A n
vreverse {n = n} xs
  with revAcc xs []
... | r
  rewrite +-acc-+ n 0 | +-identityʳ n = r
