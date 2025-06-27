module Auxiliary where

open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _<_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (<ᵇ⇒<; +-suc; +-identityʳ; n≤1+n; m≤m+n) renaming (≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import Data.Fin using (Fin; zero; suc; fromℕ; fromℕ<; inject≤)

open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; map; take)
open import Data.List.Properties using (length-++; ++-identityʳ; ++-assoc)

open import Data.Product using (∃-syntax; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; dcong)


-- some Fin lemmas

inject≤-refl : ∀ {n} (i : Fin n) → inject≤ i ≤ℕ-refl ≡ i
inject≤-refl zero = refl
inject≤-refl (suc i) = cong suc (inject≤-refl i)

inject≤-trans : ∀ {n}{m}{o} (i : Fin n) {n≤m : n ≤ℕ m} {m≤o : m ≤ℕ o} → inject≤ (inject≤ i n≤m) m≤o ≡ inject≤ i (≤ℕ-trans n≤m m≤o)
inject≤-trans {n = suc n}{m = suc m}{o = suc o} zero = refl
inject≤-trans {n = suc n} {m = suc m} {o = suc o} (suc i) {s≤s n≤m} {s≤s m≤o} = cong suc (inject≤-trans i {n≤m} {m≤o})

fromℕ-inject≤ : ∀ {m}{n}{i} → (n≤m : n ≤ℕ m) → (i< : i < n) → fromℕ< (≤ℕ-trans i< n≤m) ≡ inject≤ (fromℕ< i<) n≤m
fromℕ-inject≤ {m} {suc n} {zero} (s≤s n≤m) (s≤s i<) = refl
fromℕ-inject≤ {m} {suc n} {suc i} (s≤s n≤m) (s≤s i<) = cong suc (fromℕ-inject≤ n≤m i<)

-- Nat lemmas

≡⇒≤ : ∀ {x y : ℕ} → x ≡ y → x ≤ℕ y
≡⇒≤ refl = ≤ℕ-refl

-- List lemmas

length-≤ : ∀ {a}{A : Set a} (xs ys : List A) → length xs ≤ℕ length (xs ++ ys)
length-≤ [] ys = z≤n
length-≤ (x ∷ xs) ys = s≤s (length-≤ xs ys)

lookup-++ : ∀ {a} {A : Set a} → (xs ys : List A) → (i : Fin (length xs))
  → lookup xs i ≡ lookup (xs ++ ys) (inject≤ i (≤ℕ-trans (m≤m+n (length xs) (length ys)) (≡⇒≤ (sym (length-++ xs)))))
lookup-++ (x ∷ xs) ys zero = refl
lookup-++ (x ∷ xs) ys (suc i) = lookup-++ xs ys i

length-< : ∀ {a} {A : Set a} → (y : A) (xs ys : List A) → length xs < length (xs ++ (y ∷ ys))
length-< y [] ys = s≤s z≤n
length-< y (x ∷ xs) ys = s≤s (length-< y xs ys)

lookup-last : ∀ {a} {A : Set a} → (y : A) (xs : List A) → lookup (xs ++ [ y ]) (fromℕ< (length-< y xs [])) ≡ y
lookup-last y [] = refl
lookup-last y (x ∷ xs) = lookup-last y xs

lookup-from-i : ∀ {a}{A : Set a} (xs : List A) {ys : List A} {i}
  → (i< : i < length xs)
  → lookup (xs ++ ys) (fromℕ< (≤ℕ-trans i< (length-≤ xs ys))) ≡ lookup xs (fromℕ< i<)
lookup-from-i (x ∷ xs) {i = zero} i< = refl
lookup-from-i (x ∷ xs) {i = suc i} (s≤s i<) = lookup-from-i xs i<

lookup-from-i′ : ∀ {a}{A : Set a} (xs : List A) {ys zs : List A} {i}
  → (i< : i < length xs)
  → (eq : xs ++ ys ≡ zs)
  → lookup zs (fromℕ< (≤ℕ-trans i< (subst (λ zs → length xs ≤ℕ length zs) eq (length-≤ xs ys)))) ≡ lookup xs (fromℕ< i<)
lookup-from-i′ xs i< refl = lookup-from-i xs i<

-- List prefixes (unused)

_≼_ : ∀ {a}{A : Set a} → List A → List A → Set a
xs ≼ xs′ = ∃[ ys ] xs ++ ys ≡ xs′

≼-refl : ∀ {a}{A : Set a}{xs : List A} → xs ≼ xs
≼-refl {xs = xs} = [] , ++-identityʳ xs

≼-trans : ∀ {a}{A : Set a}{xs xs′ xs″ : List A} → xs ≼ xs′ → xs′ ≼ xs″ → xs ≼ xs″
≼-trans {xs = xs} (ys1 , eq1) (ys2 , eq2) rewrite sym eq2 | sym eq1 = (ys1 ++ ys2) , sym (++-assoc xs ys1 ys2)

