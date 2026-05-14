module Expressions where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin)

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
