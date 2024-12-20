
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; _≟_; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; dcong; subst; trans)
open import Function using (_∘_)

module FreshList where

-- Exercise 6.1 from Datatypes of datatypes
module FRESHLIST (X : Set) (Xeq? : (x x′ : X) → Dec (x ≡ x′)) where
  infixr 30 _,_
  mutual
    data FreshList : Set where
      []  : FreshList
      _,_ : (x : X) (xs : FreshList) {ok : x ∉ xs} → FreshList

    _∉_ : (x : X) (xs : FreshList) → Set
    x ∉ [] = ⊤
    x ∉ (x₁ , xs)
      with Xeq? x x₁
    ... | yes refl = ⊥
    ... | no  x≢x₁ = x ∉ xs


open FRESHLIST ℕ _≟_

fl0 : FreshList 
fl0 = []

fl1 : FreshList
fl1 = 1 , []

fl2 : FreshList
fl2 = 1 , 2 , []

{- rejected
fl3 : FreshList
fl3 = 1 , 1 , []
-}

-- section 6.1 from Dod

data RecR : Set₁ where
  ⟨⟩ : RecR
  _,_ : (A : Set) (R : A → RecR) → RecR

⟦_⟧RR : RecR → Set
⟦ ⟨⟩ ⟧RR = ⊤
⟦ A , R ⟧RR = Σ A (λ a → ⟦ R a ⟧RR)

-- exercise 6.2

sizeRR : (R : RecR) → ⟦ R ⟧RR → ℕ
sizeRR ⟨⟩ tt = zero
sizeRR (A , R) ⟨ a , r ⟩ = suc (sizeRR (R a) r)

TyRR : (R : RecR) (r : ⟦ R ⟧RR) (i : Fin (sizeRR R r)) → Set
TyRR ⟨⟩ tt ()
TyRR (A , R) ⟨ a , r ⟩ zero = A
TyRR (A , R) ⟨ a , r ⟩ (suc i) = TyRR (R a) r i

vaRR : (R : RecR) (r : ⟦ R ⟧RR) (i : Fin (sizeRR R r)) → TyRR R r i
vaRR ⟨⟩ tt ()
vaRR (A , R) ⟨ a , r ⟩ zero = a
vaRR (A , R) ⟨ a , r ⟩ (suc i) = vaRR (R a) r i

mutual
  data RecL : Set₁ where
    𝓔 : RecL
    _,_ : (R : RecL) → (A : ⟦ R ⟧RL → Set) → RecL
  ⟦_⟧RL : RecL → Set
  ⟦ 𝓔 ⟧RL = ⊤
  ⟦ R , A ⟧RL = Σ ⟦ R ⟧RL A

-- exercise 6.3

sizeRL : RecL → ℕ
sizeRL 𝓔 = zero
sizeRL (R , A) = suc (sizeRL R)

TyRL : (R : RecL) → (i : Fin (sizeRL R)) → (r : ⟦ R ⟧RL) → Set
TyRL 𝓔 () r
TyRL (R , A) zero ⟨ r , a ⟩ = A r
TyRL (R , A) (suc i) ⟨ r , a ⟩ = TyRL R i r

vaRL : (R : RecL) → (i : Fin (sizeRL R)) → (r : ⟦ R ⟧RL) → TyRL R i r
vaRL 𝓔 () r
vaRL (R , A) zero ⟨ r , a ⟩ = a
vaRL (R , A) (suc i) ⟨ r , a ⟩ = vaRL R i r

TruncRL : (R : RecL) → (i : Fin (sizeRL R)) → RecL
TruncRL 𝓔 ()
TruncRL (R , A) zero = R , A
TruncRL (R , A) (suc i) = TruncRL R i

truncRL : (R : RecL) (i : Fin (sizeRL R)) (r : ⟦ R ⟧RL) → ⟦ TruncRL R i ⟧RL
truncRL 𝓔 () r
truncRL (R , A) zero r = r
truncRL (R , A) (suc i) ⟨ r , a ⟩ = truncRL R i r

-- 6.1.1 Manifest fields

data Manifest {A : Set} : A → Set where
  ⟪_⟫ :  (a : A) → Manifest a


mutual
  data RecM : ℕ → Set₁ where
    𝓔 : RecM zero
    _,_ : {n : ℕ} (R : RecM n) (A : ⟦ R ⟧RM → Set) → RecM (suc n)
    _,_∋_ : {n : ℕ} (R : RecM n) (A : ⟦ R ⟧RM → Set) (a : (r : ⟦ R ⟧RM) → A r) → RecM (suc n)
  ⟦_⟧RM : {n : ℕ} → RecM n → Set
  ⟦ 𝓔 ⟧RM = ⊤
  ⟦ R , A ⟧RM = Σ ⟦ R ⟧RM A
  ⟦ R , A ∋ a ⟧RM = Σ ⟦ R ⟧RM (Manifest ∘ a)

TyRM : {n : ℕ} (R : RecM n) → (i : Fin n) → (r : ⟦ R ⟧RM) → Set
TyRM 𝓔 () r
TyRM (R , A) zero ⟨ r , a ⟩ = A r
TyRM (R , A) (suc i) ⟨ r , a ⟩ = TyRM R i r
TyRM (R , A ∋ a) zero ⟨ r , _ ⟩ = A r
TyRM (R , A ∋ a) (suc i) ⟨ r , _ ⟩ = TyRM R i r

vaRM : {n : ℕ} (R : RecM n) → (i : Fin n) → (r : ⟦ R ⟧RM) → TyRM R i r
vaRM 𝓔 () r
vaRM (R , A) zero ⟨ r , a ⟩ = a
vaRM (R , A) (suc i) ⟨ r , a ⟩ = vaRM R i r
vaRM (R , A ∋ a) zero ⟨ r , _ ⟩ = a r
vaRM (R , A ∋ a) (suc i) ⟨ r , _ ⟩ = vaRM R i r


