module Substitution where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Expressions

private
  variable m n : ℕ

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

extRen : Ren m n → Ren (suc m) (suc n)
extRen ρ Fin.zero = Fin.zero
extRen ρ (Fin.suc x) = Fin.suc (ρ x)

ren : Ren m n → Expr m → Expr n
ren ρ ε = ε
ren ρ (e₁ · e₂) = ren ρ e₁ · ren ρ e₂
ren ρ (var x) = var (ρ x)
ren ρ (cst k) = cst k
ren ρ (abs μ e) = abs μ (ren (extRen ρ) e)
ren ρ (mab ημ e) = mab ημ (ren (extRen ρ) e)
ren ρ (app e e₁) = app (ren ρ e) (ren ρ e₁)
ren ρ (mtc e₁ e₂ e₃) = mtc e₁ (ren ρ e₂) (ren ρ e₃)

weaken : Expr m → Expr (suc m)
weaken = ren Fin.suc

Sub : ℕ → ℕ → Set
Sub m n = Fin m → Expr n

liftSub : Sub m n → Sub (suc m) (suc n)
liftSub σ Fin.zero = var Fin.zero
liftSub σ (Fin.suc x) = weaken (σ x)

sub : Sub m n → Expr m → Expr n
sub σ ε = ε
sub σ (e₁ · e₂) = sub σ e₁ · sub σ e₂
sub σ (var x) = σ x
sub σ (cst k) = cst k
sub σ (abs μ e) = abs μ (sub (liftSub σ) e)
sub σ (mab ημ e) = mab ημ (sub (liftSub σ) e)
sub σ (app e e₁) = app (sub σ e) (sub σ e₁)
sub σ (mtc e₁ e₂ e₃) = mtc e₁ (sub σ e₂) (sub σ e₃)

sub₁σ : Expr n → Sub (suc n) n
sub₁σ e Fin.zero = e
sub₁σ e (Fin.suc x) = var x

sub₁ : Expr n → Expr (suc n) → Expr n
sub₁ e = sub (sub₁σ e)

extSub : Sub m n → Expr n → Sub (suc m) n
extSub σ e Fin.zero = e
extSub σ e (Fin.suc x) = σ x

-- composition of renamings and substitutions

liftSub-cong : ∀ {k m}{σ τ : Sub k m}
  → (∀ x → σ x ≡ τ x)
  → ∀ x → liftSub σ x ≡ liftSub τ x
liftSub-cong σ≡τ Fin.zero = refl
liftSub-cong σ≡τ (Fin.suc x) rewrite σ≡τ x = refl

sub-cong : ∀ {k m}{σ τ : Sub k m}
  → (∀ x → σ x ≡ τ x)
  → ∀ e → sub σ e ≡ sub τ e
sub-cong σ≡τ ε = refl
sub-cong σ≡τ (e₁ · e₂)
  rewrite sub-cong σ≡τ e₁
        | sub-cong σ≡τ e₂
  = refl
sub-cong σ≡τ (var x) = σ≡τ x
sub-cong σ≡τ (cst x) = refl
sub-cong σ≡τ (abs μ e)
  rewrite sub-cong (liftSub-cong σ≡τ) e
  = refl
sub-cong σ≡τ (mab ημ e)
  rewrite sub-cong (liftSub-cong σ≡τ) e
  = refl
sub-cong σ≡τ (app e₁ e₂)
  rewrite sub-cong σ≡τ e₁
        | sub-cong σ≡τ e₂
  = refl
sub-cong σ≡τ (mtc e₁ e₂ e₃)
  rewrite sub-cong σ≡τ e₂
        | sub-cong σ≡τ e₃
  = refl

extRen-cong : ∀ {k m}{ρ ξ : Ren k m}
  → (∀ x → ρ x ≡ ξ x)
  → ∀ x → extRen ρ x ≡ extRen ξ x
extRen-cong ρ≡ξ Fin.zero = refl
extRen-cong ρ≡ξ (Fin.suc x) rewrite ρ≡ξ x = refl

ren-cong : ∀ {k m}{ρ ξ : Ren k m}
  → (∀ x → ρ x ≡ ξ x)
  → ∀ e → ren ρ e ≡ ren ξ e
ren-cong ρ≡ξ ε = refl
ren-cong ρ≡ξ (e₁ · e₂)
  rewrite ren-cong ρ≡ξ e₁
        | ren-cong ρ≡ξ e₂
  = refl
ren-cong ρ≡ξ (var x) rewrite ρ≡ξ x = refl
ren-cong ρ≡ξ (cst x) = refl
ren-cong ρ≡ξ (abs μ e)
  rewrite ren-cong (extRen-cong ρ≡ξ) e
  = refl
ren-cong ρ≡ξ (mab ημ e)
  rewrite ren-cong (extRen-cong ρ≡ξ) e
  = refl
ren-cong ρ≡ξ (app e₁ e₂)
  rewrite ren-cong ρ≡ξ e₁
        | ren-cong ρ≡ξ e₂
  = refl
ren-cong ρ≡ξ (mtc e₁ e₂ e₃)
  rewrite ren-cong ρ≡ξ e₂
        | ren-cong ρ≡ξ e₃
  = refl

ren-comp : ∀ {k m ℓ}{ρ : Ren k m}{ξ : Ren m ℓ}{e : Expr k}
  → ren ξ (ren ρ e) ≡ ren (ξ ∘ ρ) e
ren-comp {e = ε} = refl
ren-comp {ρ = ρ} {ξ = ξ} {e = e₁ · e₂}
  rewrite ren-comp {ρ = ρ} {ξ = ξ} {e = e₁}
        | ren-comp {ρ = ρ} {ξ = ξ} {e = e₂}
  = refl
ren-comp {e = var x} = refl
ren-comp {e = cst x} = refl
ren-comp {ρ = ρ} {ξ = ξ} {e = abs μ e}
  rewrite ren-comp {ρ = extRen ρ} {ξ = extRen ξ} {e = e}
        | ren-cong {ρ = extRen ξ ∘ extRen ρ} {ξ = extRen (ξ ∘ ρ)}
            (λ { Fin.zero → refl ; (Fin.suc x) → refl }) e
  = refl
ren-comp {ρ = ρ} {ξ = ξ} {e = mab ημ e}
  rewrite ren-comp {ρ = extRen ρ} {ξ = extRen ξ} {e = e}
        | ren-cong {ρ = extRen ξ ∘ extRen ρ} {ξ = extRen (ξ ∘ ρ)}
            (λ { Fin.zero → refl ; (Fin.suc x) → refl }) e
  = refl
ren-comp {ρ = ρ} {ξ = ξ} {e = app e₁ e₂}
  rewrite ren-comp {ρ = ρ} {ξ = ξ} {e = e₁}
        | ren-comp {ρ = ρ} {ξ = ξ} {e = e₂}
  = refl
ren-comp {ρ = ρ} {ξ = ξ} {e = mtc e₁ e₂ e₃}
  rewrite ren-comp {ρ = ρ} {ξ = ξ} {e = e₂}
        | ren-comp {ρ = ρ} {ξ = ξ} {e = e₃}
  = refl

sub-ren : ∀ {k m n}{ρ : Ren k m}{σ : Sub m n}{e : Expr k}
  → sub σ (ren ρ e) ≡ sub (σ ∘ ρ) e
sub-ren {e = ε} = refl
sub-ren {ρ = ρ} {σ = σ} {e = e₁ · e₂}
  rewrite sub-ren {ρ = ρ} {σ = σ} {e = e₁}
        | sub-ren {ρ = ρ} {σ = σ} {e = e₂}
  = refl
sub-ren {e = var x} = refl
sub-ren {e = cst x} = refl
sub-ren {ρ = ρ} {σ = σ} {e = abs μ e}
  rewrite sub-ren {ρ = extRen ρ} {σ = liftSub σ} {e = e}
        | sub-cong
            {σ = liftSub σ ∘ extRen ρ}
            {τ = liftSub (σ ∘ ρ)}
            (λ { Fin.zero → refl ; (Fin.suc x) → refl }) e
  = refl
sub-ren {ρ = ρ} {σ = σ} {e = mab ημ e}
  rewrite sub-ren {ρ = extRen ρ} {σ = liftSub σ} {e = e}
        | sub-cong
            {σ = liftSub σ ∘ extRen ρ}
            {τ = liftSub (σ ∘ ρ)}
            (λ { Fin.zero → refl ; (Fin.suc x) → refl }) e
  = refl
sub-ren {ρ = ρ} {σ = σ} {e = app e₁ e₂}
  rewrite sub-ren {ρ = ρ} {σ = σ} {e = e₁}
        | sub-ren {ρ = ρ} {σ = σ} {e = e₂}
  = refl
sub-ren {ρ = ρ} {σ = σ} {e = mtc e₁ e₂ e₃}
  rewrite sub-ren {ρ = ρ} {σ = σ} {e = e₂}
        | sub-ren {ρ = ρ} {σ = σ} {e = e₃}
  = refl

ren-ext-weaken : ∀ {k m}{ρ : Ren k m}{e : Expr k}
  → ren (extRen ρ) (weaken e) ≡ weaken (ren ρ e)
ren-ext-weaken {ρ = ρ} {e = e}
  rewrite ren-comp {ρ = Fin.suc} {ξ = extRen ρ} {e = e}
        | ren-comp {ρ = ρ} {ξ = Fin.suc} {e = e}
        | ren-cong {ρ = extRen ρ ∘ Fin.suc} {ξ = Fin.suc ∘ ρ} (λ x → refl) e
  = refl

ren-sub : ∀ {k m n}{ρ : Ren m n}{σ : Sub k m}{e : Expr k}
  → ren ρ (sub σ e) ≡ sub (λ x → ren ρ (σ x)) e
ren-sub {e = ε} = refl
ren-sub {ρ = ρ} {σ = σ} {e = e₁ · e₂}
  rewrite ren-sub {ρ = ρ} {σ = σ} {e = e₁}
        | ren-sub {ρ = ρ} {σ = σ} {e = e₂}
  = refl
ren-sub {e = var x} = refl
ren-sub {e = cst x} = refl
ren-sub {ρ = ρ} {σ = σ} {e = abs μ e}
  rewrite ren-sub {ρ = extRen ρ} {σ = liftSub σ} {e = e}
        | sub-cong
            {σ = (λ x → ren (extRen ρ) (liftSub σ x))}
            {τ = liftSub (λ x → ren ρ (σ x))}
            (λ { Fin.zero → refl ; (Fin.suc x) → ren-ext-weaken {ρ = ρ} {e = σ x} }) e
  = refl
ren-sub {ρ = ρ} {σ = σ} {e = mab ημ e}
  rewrite ren-sub {ρ = extRen ρ} {σ = liftSub σ} {e = e}
        | sub-cong
            {σ = (λ x → ren (extRen ρ) (liftSub σ x))}
            {τ = liftSub (λ x → ren ρ (σ x))}
            (λ { Fin.zero → refl ; (Fin.suc x) → ren-ext-weaken {ρ = ρ} {e = σ x} }) e
  = refl
ren-sub {ρ = ρ} {σ = σ} {e = app e₁ e₂}
  rewrite ren-sub {ρ = ρ} {σ = σ} {e = e₁}
        | ren-sub {ρ = ρ} {σ = σ} {e = e₂}
  = refl
ren-sub {ρ = ρ} {σ = σ} {e = mtc e₁ e₂ e₃}
  rewrite ren-sub {ρ = ρ} {σ = σ} {e = e₂}
        | ren-sub {ρ = ρ} {σ = σ} {e = e₃}
  = refl

sub-id : ∀ {k}{e : Expr k} → sub (λ x → var x) e ≡ e
sub-id {e = ε} = refl
sub-id {e = e₁ · e₂}
  rewrite sub-id {e = e₁}
        | sub-id {e = e₂}
  = refl
sub-id {e = var x} = refl
sub-id {e = cst x} = refl
sub-id {e = abs μ e}
  rewrite sub-cong {σ = liftSub (λ x → var x)} {τ = (λ x → var x)}
            (λ { Fin.zero → refl ; (Fin.suc x) → refl }) e
        | sub-id {e = e}
  = refl
sub-id {e = mab ημ e}
  rewrite sub-cong {σ = liftSub (λ x → var x)} {τ = (λ x → var x)}
            (λ { Fin.zero → refl ; (Fin.suc x) → refl }) e
        | sub-id {e = e}
  = refl
sub-id {e = app e₁ e₂}
  rewrite sub-id {e = e₁}
        | sub-id {e = e₂}
  = refl
sub-id {e = mtc e₁ e₂ e₃}
  rewrite sub-id {e = e₂}
        | sub-id {e = e₃}
  = refl

sub₁-weaken : ∀ {m}{v : Expr m}{e : Expr m} → sub₁ v (weaken e) ≡ e
sub₁-weaken {v = v} {e = e}
  rewrite sub-ren {ρ = Fin.suc} {σ = sub₁σ v} {e = e}
  = sub-id

sub-lift-weaken : ∀ {k m}{τ : Sub k m}{e : Expr k}
  → sub (liftSub τ) (weaken e) ≡ weaken (sub τ e)
sub-lift-weaken {τ = τ} {e = e}
  rewrite sub-ren {ρ = Fin.suc} {σ = liftSub τ} {e = e}
        | ren-sub {ρ = Fin.suc} {σ = τ} {e = e}
  = sub-cong (λ x → refl) e

sub-comp : ∀ {k m n}{σ : Sub k m}{τ : Sub m n}{e : Expr k}
  → sub τ (sub σ e) ≡ sub (λ x → sub τ (σ x)) e
sub-comp {e = ε} = refl
sub-comp {σ = σ} {τ = τ} {e = e₁ · e₂}
  rewrite sub-comp {σ = σ} {τ = τ} {e = e₁}
        | sub-comp {σ = σ} {τ = τ} {e = e₂}
  = refl
sub-comp {e = var x} = refl
sub-comp {e = cst x} = refl
sub-comp {σ = σ} {τ = τ} {e = abs μ e}
  rewrite sub-comp {σ = liftSub σ} {τ = liftSub τ} {e = e}
        | sub-cong
            {σ = (λ x → sub (liftSub τ) (liftSub σ x))}
            {τ = liftSub (λ x → sub τ (σ x))}
            (λ { Fin.zero → refl ; (Fin.suc x) → sub-lift-weaken {τ = τ} {e = σ x} }) e
  = refl
sub-comp {σ = σ} {τ = τ} {e = mab ημ e}
  rewrite sub-comp {σ = liftSub σ} {τ = liftSub τ} {e = e}
        | sub-cong
            {σ = (λ x → sub (liftSub τ) (liftSub σ x))}
            {τ = liftSub (λ x → sub τ (σ x))}
            (λ { Fin.zero → refl ; (Fin.suc x) → sub-lift-weaken {τ = τ} {e = σ x} }) e
  = refl
sub-comp {σ = σ} {τ = τ} {e = app e₁ e₂}
  rewrite sub-comp {σ = σ} {τ = τ} {e = e₁}
        | sub-comp {σ = σ} {τ = τ} {e = e₂}
  = refl
sub-comp {σ = σ} {τ = τ} {e = mtc e₁ e₂ e₃}
  rewrite sub-comp {σ = σ} {τ = τ} {e = e₂}
        | sub-comp {σ = σ} {τ = τ} {e = e₃}
  = refl

sub-ext-lift : {σ : Sub n m}{v : Expr m}{e : Expr (suc n)} → sub (extSub σ v) e ≡ sub₁ v (sub (liftSub σ) e)
sub-ext-lift {σ = σ} {v = v} {e = e}
  rewrite sub-comp {σ = liftSub σ} {τ = sub₁σ v} {e = e}
  = sub-cong pointwise e
  where
    pointwise : ∀ x → extSub σ v x ≡ sub (sub₁σ v) (liftSub σ x)
    pointwise Fin.zero = refl
    pointwise (Fin.suc x) rewrite sub₁-weaken {v = v} {e = σ x} = refl

-- substitution and mapE

mapE-sub : {σ : Sub n m} (e : Expr n) → mapE (sub σ) e ≡ sub σ e
mapE-sub ε = refl
mapE-sub (e · e₁) = cong₂ _·_ (mapE-sub e) (mapE-sub e₁)
mapE-sub (var x) = refl
mapE-sub (cst k) = refl
mapE-sub (abs μ e) = cong (abs μ) refl
mapE-sub (mab ημ e) = cong (mab ημ) refl
mapE-sub (app e e₁) = refl
mapE-sub (mtc e₁ e₂ e₃) = refl
