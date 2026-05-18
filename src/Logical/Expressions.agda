module Expressions where

open import Level using (Level) renaming (zero to lzero)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Function using (_∘_)

open import Types

data Expr (n : ℕ) : Set where
  ε   : Expr n
  _·_ : Expr n → Expr n → Expr n
  var : Fin n → Expr n
  cst : ℕ → Expr n
  abs : Ty → Expr (suc n) → Expr n
  mab : NTy → Expr (suc n) → Expr n
  app : Expr n → Expr n → Expr n

mapE : ∀ {m n} → (Expr m → Expr n) → Expr m → Expr n
mapE f ε = ε
mapE f (e₁ · e₂) = mapE f e₁ · mapE f e₂
mapE f (var x) = f (var x)
mapE f (cst x) = f (cst x)
mapE f (abs x e) = f (abs x e)
mapE f (mab x e) = f (mab x e)
mapE f (app e e₁) = f (app e e₁)

lengthE : ∀ {n} → Expr n → ℕ
lengthE ε = 0
lengthE (e₁ · e₂) = lengthE e₁ +ℕ lengthE e₂
lengthE (var x) = 1
lengthE (cst x) = 1
lengthE (abs x e) = 1
lengthE (mab x e) = 1
lengthE (app e e₁) = 1

NonEmpty : ∀ {n} → Expr n → Set
NonEmpty e = e ≡ ε → ⊥

NonConcat : ∀ {n} → Expr n → Set
NonConcat e = ∀ {e₁ e₂} → e ≡ (e₁ · e₂) → ⊥

Atomic : ∀ {n} → Expr n → Set
Atomic e = NonEmpty e × NonConcat e

data ALL (P : Expr zero → Set) : Expr zero → Set where
  Aε : ALL P ε
  _A·_ : ∀ {e₁}{e₂} → ALL P e₁ → ALL P e₂ → ALL P (e₁ · e₂)
  AP : ∀ {e}
    {e≢ε : e ≡ ε → ⊥}
    {e≢· : ∀ {e₁ e₂} → e ≡ (e₁ · e₂) → ⊥}
    → P e
    → ALL P e

mapALL : ∀ {e : Expr zero} {P Q : Pred (Expr zero) lzero} → (∀ {x} → P x → Q x) → ALL P e → ALL Q e
mapALL P⇒Q Aε = Aε
mapALL P⇒Q (ap A· ap₁) = (mapALL P⇒Q ap) A· (mapALL P⇒Q ap₁)
mapALL P⇒Q (AP {e≢ε = e≢ε} {e≢· = e≢·} x) = AP {e≢ε = e≢ε} {e≢· = e≢·} (P⇒Q x)

AP-cst : ∀ {P} {k} → P (cst k) → ALL P (cst k)
AP-cst p = AP {e≢ε = λ ()} {e≢· = λ ()} p

AP-abs : ∀ {P} {μ} {e*} → P (abs μ e*) → ALL P (abs μ e*)
AP-abs p = AP {e≢ε = λ ()} {e≢· = λ ()} p

AP-mab : ∀ {P} {ημ} {e*} → P (mab ημ e*) → ALL P (mab ημ e*)
AP-mab p = AP {e≢ε = λ ()} {e≢· = λ ()} p

foldALL : ∀ {n} {e : Expr zero} {P : Pred (Expr zero) lzero} → (∀ {x} → P x → Expr n) → ALL P e → Expr n
foldALL f Aε = ε
foldALL f (a A· a₁) = (foldALL f a) · (foldALL f a₁)
foldALL f (AP Pe) = f Pe

mapE-foldALL : ∀ {m n} {e : Expr zero} {P : Pred (Expr zero) lzero} → (g : ∀ {x} → P x → Expr n) → (f : Expr n → Expr m) → (f-map : ∀ {e} → mapE f e ≡ f e) →  (ap : ALL P e) → mapE f (foldALL g ap) ≡ foldALL (f ∘ g) ap
mapE-foldALL g f f-map Aε = refl
mapE-foldALL g f f-map (ap A· ap₁) = cong₂ _·_ (mapE-foldALL g f f-map ap) (mapE-foldALL g f f-map ap₁)
mapE-foldALL g f f-map (AP ap) = f-map
