module Numeri where

open import Level using (Level) renaming (zero to lzero)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_⊔_ to _⊔ℕ_; _⊓_ to _⊓ℕ_; _≤_ to _≤ℕ_; _*_ to _*ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; *-zeroʳ; ≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; length; map; concat; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Function using (_∘_)

open import Interval


-- numeri

data Num : Set where
  `- `! `? `* `+ : Num

data _<:₀_ : Num → Num → Set where
  <:₀-refl : ∀ {num} → num <:₀ num
  <:₀--? : `- <:₀ `?
  <:₀--* : `- <:₀ `*
  <:₀-!? : `! <:₀ `?
  <:₀-!* : `! <:₀ `*
  <:₀-!+ : `! <:₀ `+
  <:₀-?* : `? <:₀ `*
  <:₀-+* : `+ <:₀ `*

<:₀-trans : ∀ {n m o} → n <:₀ m → m <:₀ o → n <:₀ o
<:₀-trans <:₀-refl <:₀-refl = <:₀-refl
<:₀-trans <:₀-refl <:₀--? = <:₀--?
<:₀-trans <:₀-refl <:₀--* = <:₀--*
<:₀-trans <:₀-refl <:₀-!? = <:₀-!?
<:₀-trans <:₀-refl <:₀-!* = <:₀-!*
<:₀-trans <:₀-refl <:₀-!+ = <:₀-!+
<:₀-trans <:₀-refl <:₀-?* = <:₀-?*
<:₀-trans <:₀-refl <:₀-+* = <:₀-+*
<:₀-trans <:₀--? <:₀-refl = <:₀--?
<:₀-trans <:₀--? <:₀-?* = <:₀--*
<:₀-trans <:₀--* <:₀-refl = <:₀--*
<:₀-trans <:₀-!? <:₀-refl = <:₀-!?
<:₀-trans <:₀-!? <:₀-?* = <:₀-!*
<:₀-trans <:₀-!* <:₀-refl = <:₀-!*
<:₀-trans <:₀-!+ <:₀-refl = <:₀-!+
<:₀-trans <:₀-!+ <:₀-+* = <:₀-!*
<:₀-trans <:₀-?* <:₀-refl = <:₀-?*
<:₀-trans <:₀-+* <:₀-refl = <:₀-+*

𝓝⟦_⟧ : Num → Ivl
𝓝⟦ `- ⟧ = ⟪ 0 , just 0 ⟫
𝓝⟦ `! ⟧ = ⟪ 1 , just 1 ⟫
𝓝⟦ `? ⟧ = ⟪ 0 , just 1 ⟫
𝓝⟦ `* ⟧ = ⟪ 0 , nothing ⟫
𝓝⟦ `+ ⟧ = ⟪ 1 , nothing ⟫

ADD : Num → Num → Num
ADD `- y = y
ADD `! `- = `!
ADD `! `! = `+
ADD `! `? = `+
ADD `! `* = `+
ADD `! `+ = `+
ADD `? `- = `?
ADD `? `! = `+
ADD `? `? = `*
ADD `? `* = `*
ADD `? `+ = `+
ADD `* `- = `*
ADD `* `! = `+
ADD `* `? = `*
ADD `* `* = `*
ADD `* `+ = `+
ADD `+ `- = `+
ADD `+ `! = `+
ADD `+ `? = `+
ADD `+ `* = `+
ADD `+ `+ = `+

ADD-zero : ∀ η₁ η₂ → `- ≡ ADD η₁ η₂ → `- ≡ η₁ × `- ≡ η₂
ADD-zero `- `- x = x , x
ADD-zero `! `- ()
ADD-zero `! `! ()
ADD-zero `! `? ()
ADD-zero `! `* ()
ADD-zero `! `+ ()
ADD-zero `? `- ()
ADD-zero `? `! ()
ADD-zero `? `? ()
ADD-zero `? `* ()
ADD-zero `? `+ ()
ADD-zero `* `- ()
ADD-zero `* `! ()
ADD-zero `* `? ()
ADD-zero `* `* ()
ADD-zero `* `+ ()
ADD-zero `+ `- ()
ADD-zero `+ `! ()
ADD-zero `+ `? ()
ADD-zero `+ `* ()
ADD-zero `+ `+ ()

ADD-one : ∀ η₁ η₂ → `! ≡ ADD η₁ η₂ → (`! ≡ η₁ × `- ≡ η₂) ⊎ (`- ≡ η₁ × `! ≡ η₂)
ADD-one `- `- ()
ADD-one `- `! x = inj₂ (refl , refl)
ADD-one `- `? ()
ADD-one `- `* ()
ADD-one `- `+ ()
ADD-one `! `- x = inj₁ (refl , refl)
ADD-one `! `! ()
ADD-one `! `? ()
ADD-one `! `* ()
ADD-one `! `+ ()
ADD-one `? `- ()
ADD-one `? `! ()
ADD-one `? `? ()
ADD-one `? `* ()
ADD-one `? `+ ()
ADD-one `* `- ()
ADD-one `* `! ()
ADD-one `* `? ()
ADD-one `* `* ()
ADD-one `* `+ ()
ADD-one `+ `- ()
ADD-one `+ `! ()
ADD-one `+ `? ()
ADD-one `+ `* ()
ADD-one `+ `+ ()

ADD-opt : ∀ η₁ η₂ → `? ≡ ADD η₁ η₂ → (`- ≡ η₁ × `? ≡ η₂) ⊎ (`? ≡ η₁ × `- ≡ η₂)
ADD-opt `- `- ()
ADD-opt `- `! ()
ADD-opt `- `? x = inj₁ (refl , refl)
ADD-opt `- `* ()
ADD-opt `- `+ ()
ADD-opt `! `- ()
ADD-opt `! `! ()
ADD-opt `! `? ()
ADD-opt `! `* ()
ADD-opt `! `+ ()
ADD-opt `? `- x = inj₂ (refl , refl)
ADD-opt `? `! ()
ADD-opt `? `? ()
ADD-opt `? `* ()
ADD-opt `? `+ ()
ADD-opt `* `- ()
ADD-opt `* `! ()
ADD-opt `* `? ()
ADD-opt `* `* ()
ADD-opt `* `+ ()
ADD-opt `+ `- ()
ADD-opt `+ `! ()
ADD-opt `+ `? ()
ADD-opt `+ `* ()
ADD-opt `+ `+ ()

num-to-star : ∀ η → η <:₀ `*
num-to-star `- = <:₀--*
num-to-star `! = <:₀-!*
num-to-star `? = <:₀-?*
num-to-star `* = <:₀-refl
num-to-star `+ = <:₀-+*

ADD-both-one-super : ∀ {η₁ η₂}
  → `! <:₀ η₁
  → `! <:₀ η₂
  → `+ <:₀ ADD η₁ η₂
ADD-both-one-super <:₀-refl <:₀-refl = <:₀-refl
ADD-both-one-super <:₀-refl <:₀-!? = <:₀-refl
ADD-both-one-super <:₀-refl <:₀-!* = <:₀-refl
ADD-both-one-super <:₀-refl <:₀-!+ = <:₀-refl
ADD-both-one-super <:₀-!? <:₀-refl = <:₀-refl
ADD-both-one-super <:₀-!? <:₀-!? = <:₀-+*
ADD-both-one-super <:₀-!? <:₀-!* = <:₀-+*
ADD-both-one-super <:₀-!? <:₀-!+ = <:₀-refl
ADD-both-one-super <:₀-!* <:₀-refl = <:₀-refl
ADD-both-one-super <:₀-!* <:₀-!? = <:₀-+*
ADD-both-one-super <:₀-!* <:₀-!* = <:₀-+*
ADD-both-one-super <:₀-!* <:₀-!+ = <:₀-refl
ADD-both-one-super <:₀-!+ <:₀-refl = <:₀-refl
ADD-both-one-super <:₀-!+ <:₀-!? = <:₀-refl
ADD-both-one-super <:₀-!+ <:₀-!* = <:₀-refl
ADD-both-one-super <:₀-!+ <:₀-!+ = <:₀-refl

ADD-sound : (η₁ η₂ : Num) → (𝓝⟦ η₁ ⟧ + 𝓝⟦ η₂ ⟧) ≤ 𝓝⟦ ADD η₁ η₂ ⟧
ADD-sound `- `- = z≤n , z≤n
ADD-sound `- `! = (s≤s z≤n) , (s≤s z≤n)
ADD-sound `- `? = z≤n , (s≤s z≤n)
ADD-sound `- `* = z≤n , tt
ADD-sound `- `+ = s≤s z≤n , tt
ADD-sound `! `- = s≤s z≤n , s≤s z≤n
ADD-sound `! `! = s≤s z≤n , tt
ADD-sound `! `? = s≤s z≤n , tt
ADD-sound `! `* = s≤s z≤n , tt
ADD-sound `! `+ = s≤s z≤n , tt
ADD-sound `? `- = z≤n , s≤s z≤n
ADD-sound `? `! = s≤s z≤n , tt
ADD-sound `? `? = z≤n , tt
ADD-sound `? `* = z≤n , tt
ADD-sound `? `+ = s≤s z≤n , tt
ADD-sound `* `- = z≤n , tt
ADD-sound `* `! = s≤s z≤n , tt
ADD-sound `* `? = z≤n , tt
ADD-sound `* `* = z≤n , tt
ADD-sound `* `+ = s≤s z≤n , tt
ADD-sound `+ `- = s≤s z≤n , tt
ADD-sound `+ `! = s≤s z≤n , tt
ADD-sound `+ `? = s≤s z≤n , tt
ADD-sound `+ `* = s≤s z≤n , tt
ADD-sound `+ `+ = s≤s z≤n , tt

data MUL : Num → Num → Num → Set where
  m0-left : ∀ {η} → MUL `- η `-
  m0-right : ∀ {η} → MUL η `- `-
  m1-left : ∀ {η} → MUL `! η η
  m1-right : ∀ {η} → MUL `! η η
  m2-diag : MUL `? `? `?
  m3-diag : MUL `+ `+ `+
  m4-diag : MUL `* `* `*
  m23     : MUL `? `+ `*
  m32     : MUL `+ `? `*
  m24     : MUL `? `* `*
  m42     : MUL `* `? `*
  m34     : MUL `+ `* `*
  m43     : MUL `* `+ `*
  
ADD-left-empty-super : ∀ {η₁ η₂} → `- <:₀ η₁ → η₂ <:₀ ADD η₁ η₂
ADD-left-empty-super {η₁ = `- } {η₂} <:₀-refl = <:₀-refl
ADD-left-empty-super {η₁ = `? } {η₂ = `- } <:₀--? = <:₀--?
ADD-left-empty-super {η₁ = `? } {η₂ = `! } <:₀--? = <:₀-!+
ADD-left-empty-super {η₁ = `? } {η₂ = `? } <:₀--? = <:₀-?*
ADD-left-empty-super {η₁ = `? } {η₂ = `* } <:₀--? = <:₀-refl
ADD-left-empty-super {η₁ = `? } {η₂ = `+ } <:₀--? = <:₀-refl
ADD-left-empty-super {η₁ = `* } {η₂ = `- } <:₀--* = <:₀--*
ADD-left-empty-super {η₁ = `* } {η₂ = `! } <:₀--* = <:₀-!+
ADD-left-empty-super {η₁ = `* } {η₂ = `? } <:₀--* = <:₀-?*
ADD-left-empty-super {η₁ = `* } {η₂ = `* } <:₀--* = <:₀-refl
ADD-left-empty-super {η₁ = `* } {η₂ = `+ } <:₀--* = <:₀-refl

ADD-right-empty-super : ∀ {η₁ η₂} → `- <:₀ η₂ → η₁ <:₀ ADD η₁ η₂
ADD-right-empty-super {η₁ = `- } {η₂ = `- } <:₀-refl = <:₀-refl
ADD-right-empty-super {η₁ = `! } {η₂ = `- } <:₀-refl = <:₀-refl
ADD-right-empty-super {η₁ = `? } {η₂ = `- } <:₀-refl = <:₀-refl
ADD-right-empty-super {η₁ = `* } {η₂ = `- } <:₀-refl = <:₀-refl
ADD-right-empty-super {η₁ = `+ } {η₂ = `- } <:₀-refl = <:₀-refl
ADD-right-empty-super {η₁ = `- } {η₂ = `? } <:₀--? = <:₀--?
ADD-right-empty-super {η₁ = `! } {η₂ = `? } <:₀--? = <:₀-!+
ADD-right-empty-super {η₁ = `? } {η₂ = `? } <:₀--? = <:₀-?*
ADD-right-empty-super {η₁ = `* } {η₂ = `? } <:₀--? = <:₀-refl
ADD-right-empty-super {η₁ = `+ } {η₂ = `? } <:₀--? = <:₀-refl
ADD-right-empty-super {η₁ = `- } {η₂ = `* } <:₀--* = <:₀--*
ADD-right-empty-super {η₁ = `! } {η₂ = `* } <:₀--* = <:₀-!+
ADD-right-empty-super {η₁ = `? } {η₂ = `* } <:₀--* = <:₀-?*
ADD-right-empty-super {η₁ = `* } {η₂ = `* } <:₀--* = <:₀-refl
ADD-right-empty-super {η₁ = `+ } {η₂ = `* } <:₀--* = <:₀-refl
ADD-assoc : ∀ η₁ η₂ η₃ → ADD (ADD η₁ η₂) η₃ ≡ ADD η₁ (ADD η₂ η₃)
ADD-assoc `- `- `- = refl
ADD-assoc `- `- `! = refl
ADD-assoc `- `- `? = refl
ADD-assoc `- `- `* = refl
ADD-assoc `- `- `+ = refl
ADD-assoc `- `! `- = refl
ADD-assoc `- `! `! = refl
ADD-assoc `- `! `? = refl
ADD-assoc `- `! `* = refl
ADD-assoc `- `! `+ = refl
ADD-assoc `- `? `- = refl
ADD-assoc `- `? `! = refl
ADD-assoc `- `? `? = refl
ADD-assoc `- `? `* = refl
ADD-assoc `- `? `+ = refl
ADD-assoc `- `* `- = refl
ADD-assoc `- `* `! = refl
ADD-assoc `- `* `? = refl
ADD-assoc `- `* `* = refl
ADD-assoc `- `* `+ = refl
ADD-assoc `- `+ `- = refl
ADD-assoc `- `+ `! = refl
ADD-assoc `- `+ `? = refl
ADD-assoc `- `+ `* = refl
ADD-assoc `- `+ `+ = refl
ADD-assoc `! `- `- = refl
ADD-assoc `! `- `! = refl
ADD-assoc `! `- `? = refl
ADD-assoc `! `- `* = refl
ADD-assoc `! `- `+ = refl
ADD-assoc `! `! `- = refl
ADD-assoc `! `! `! = refl
ADD-assoc `! `! `? = refl
ADD-assoc `! `! `* = refl
ADD-assoc `! `! `+ = refl
ADD-assoc `! `? `- = refl
ADD-assoc `! `? `! = refl
ADD-assoc `! `? `? = refl
ADD-assoc `! `? `* = refl
ADD-assoc `! `? `+ = refl
ADD-assoc `! `* `- = refl
ADD-assoc `! `* `! = refl
ADD-assoc `! `* `? = refl
ADD-assoc `! `* `* = refl
ADD-assoc `! `* `+ = refl
ADD-assoc `! `+ `- = refl
ADD-assoc `! `+ `! = refl
ADD-assoc `! `+ `? = refl
ADD-assoc `! `+ `* = refl
ADD-assoc `! `+ `+ = refl
ADD-assoc `? `- `- = refl
ADD-assoc `? `- `! = refl
ADD-assoc `? `- `? = refl
ADD-assoc `? `- `* = refl
ADD-assoc `? `- `+ = refl
ADD-assoc `? `! `- = refl
ADD-assoc `? `! `! = refl
ADD-assoc `? `! `? = refl
ADD-assoc `? `! `* = refl
ADD-assoc `? `! `+ = refl
ADD-assoc `? `? `- = refl
ADD-assoc `? `? `! = refl
ADD-assoc `? `? `? = refl
ADD-assoc `? `? `* = refl
ADD-assoc `? `? `+ = refl
ADD-assoc `? `* `- = refl
ADD-assoc `? `* `! = refl
ADD-assoc `? `* `? = refl
ADD-assoc `? `* `* = refl
ADD-assoc `? `* `+ = refl
ADD-assoc `? `+ `- = refl
ADD-assoc `? `+ `! = refl
ADD-assoc `? `+ `? = refl
ADD-assoc `? `+ `* = refl
ADD-assoc `? `+ `+ = refl
ADD-assoc `* `- `- = refl
ADD-assoc `* `- `! = refl
ADD-assoc `* `- `? = refl
ADD-assoc `* `- `* = refl
ADD-assoc `* `- `+ = refl
ADD-assoc `* `! `- = refl
ADD-assoc `* `! `! = refl
ADD-assoc `* `! `? = refl
ADD-assoc `* `! `* = refl
ADD-assoc `* `! `+ = refl
ADD-assoc `* `? `- = refl
ADD-assoc `* `? `! = refl
ADD-assoc `* `? `? = refl
ADD-assoc `* `? `* = refl
ADD-assoc `* `? `+ = refl
ADD-assoc `* `* `- = refl
ADD-assoc `* `* `! = refl
ADD-assoc `* `* `? = refl
ADD-assoc `* `* `* = refl
ADD-assoc `* `* `+ = refl
ADD-assoc `* `+ `- = refl
ADD-assoc `* `+ `! = refl
ADD-assoc `* `+ `? = refl
ADD-assoc `* `+ `* = refl
ADD-assoc `* `+ `+ = refl
ADD-assoc `+ `- `- = refl
ADD-assoc `+ `- `! = refl
ADD-assoc `+ `- `? = refl
ADD-assoc `+ `- `* = refl
ADD-assoc `+ `- `+ = refl
ADD-assoc `+ `! `- = refl
ADD-assoc `+ `! `! = refl
ADD-assoc `+ `! `? = refl
ADD-assoc `+ `! `* = refl
ADD-assoc `+ `! `+ = refl
ADD-assoc `+ `? `- = refl
ADD-assoc `+ `? `! = refl
ADD-assoc `+ `? `? = refl
ADD-assoc `+ `? `* = refl
ADD-assoc `+ `? `+ = refl
ADD-assoc `+ `* `- = refl
ADD-assoc `+ `* `! = refl
ADD-assoc `+ `* `? = refl
ADD-assoc `+ `* `* = refl
ADD-assoc `+ `* `+ = refl
ADD-assoc `+ `+ `- = refl
ADD-assoc `+ `+ `! = refl
ADD-assoc `+ `+ `? = refl
ADD-assoc `+ `+ `* = refl
ADD-assoc `+ `+ `+ = refl

ADD-monotone-left : ∀ {η₁ η₂ η₃} → η₁ <:₀ η₂ → ADD η₁ η₃ <:₀ ADD η₂ η₃
ADD-monotone-left <:₀-refl = <:₀-refl
ADD-monotone-left {η₃ = `- } <:₀--? = <:₀--?
ADD-monotone-left {η₃ = `! } <:₀--? = <:₀-!+
ADD-monotone-left {η₃ = `? } <:₀--? = <:₀-?*
ADD-monotone-left {η₃ = `* } <:₀--? = <:₀-refl
ADD-monotone-left {η₃ = `+ } <:₀--? = <:₀-refl
ADD-monotone-left {η₃ = `- } <:₀--* = <:₀--*
ADD-monotone-left {η₃ = `! } <:₀--* = <:₀-!+
ADD-monotone-left {η₃ = `? } <:₀--* = <:₀-?*
ADD-monotone-left {η₃ = `* } <:₀--* = <:₀-refl
ADD-monotone-left {η₃ = `+ } <:₀--* = <:₀-refl
ADD-monotone-left {η₃ = `- } <:₀-!? = <:₀-!?
ADD-monotone-left {η₃ = `! } <:₀-!? = <:₀-refl
ADD-monotone-left {η₃ = `? } <:₀-!? = <:₀-+*
ADD-monotone-left {η₃ = `* } <:₀-!? = <:₀-+*
ADD-monotone-left {η₃ = `+ } <:₀-!? = <:₀-refl
ADD-monotone-left {η₃ = `- } <:₀-!* = <:₀-!*
ADD-monotone-left {η₃ = `! } <:₀-!* = <:₀-refl
ADD-monotone-left {η₃ = `? } <:₀-!* = <:₀-+*
ADD-monotone-left {η₃ = `* } <:₀-!* = <:₀-+*
ADD-monotone-left {η₃ = `+ } <:₀-!* = <:₀-refl
ADD-monotone-left {η₃ = `- } <:₀-!+ = <:₀-!+
ADD-monotone-left {η₃ = `! } <:₀-!+ = <:₀-refl
ADD-monotone-left {η₃ = `? } <:₀-!+ = <:₀-refl
ADD-monotone-left {η₃ = `* } <:₀-!+ = <:₀-refl
ADD-monotone-left {η₃ = `+ } <:₀-!+ = <:₀-refl
ADD-monotone-left {η₃ = `- } <:₀-?* = <:₀-?*
ADD-monotone-left {η₃ = `! } <:₀-?* = <:₀-refl
ADD-monotone-left {η₃ = `? } <:₀-?* = <:₀-refl
ADD-monotone-left {η₃ = `* } <:₀-?* = <:₀-refl
ADD-monotone-left {η₃ = `+ } <:₀-?* = <:₀-refl
ADD-monotone-left {η₃ = `- } <:₀-+* = <:₀-+*
ADD-monotone-left {η₃ = `! } <:₀-+* = <:₀-refl
ADD-monotone-left {η₃ = `? } <:₀-+* = <:₀-+*
ADD-monotone-left {η₃ = `* } <:₀-+* = <:₀-+*
ADD-monotone-left {η₃ = `+ } <:₀-+* = <:₀-refl
ADD-empty-super : ∀ {η₁ η₂} → `- <:₀ η₁ → `- <:₀ η₂ → `- <:₀ ADD η₁ η₂
ADD-empty-super <:₀-refl η₂<: = η₂<:
ADD-empty-super <:₀--? <:₀-refl = <:₀--?
ADD-empty-super <:₀--? <:₀--? = <:₀--*
ADD-empty-super <:₀--? <:₀--* = <:₀--*
ADD-empty-super <:₀--* <:₀-refl = <:₀--*
ADD-empty-super <:₀--* <:₀--? = <:₀--*
ADD-empty-super <:₀--* <:₀--* = <:₀--*

ADD-self-super : ∀ {η}
  → `+ <:₀ η
  → ADD η η <:₀ η
ADD-self-super <:₀-refl = <:₀-refl
ADD-self-super <:₀-+* = <:₀-refl

ADD-self-super-mul : ∀ {η₁ η₂ η′ η₃ η}
  → `+ <:₀ η₁
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → ADD η η <:₀ η
ADD-self-super-mul () m0-left m₂
ADD-self-super-mul +<:η₁ m0-right m0-left = <:₀-refl
ADD-self-super-mul +<:η₁ m0-right m0-right = <:₀-refl
ADD-self-super-mul () m1-left m₂
ADD-self-super-mul () m1-right m₂
ADD-self-super-mul () m2-diag m₂
ADD-self-super-mul <:₀-refl m3-diag m3-diag = <:₀-refl
ADD-self-super-mul <:₀-refl m3-diag m0-right = <:₀-refl
ADD-self-super-mul <:₀-refl m3-diag m32 = <:₀-refl
ADD-self-super-mul <:₀-refl m3-diag m34 = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m0-right = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m4-diag = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m42 = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m43 = <:₀-refl
ADD-self-super-mul () m23 m₂
ADD-self-super-mul <:₀-refl m32 m0-right = <:₀-refl
ADD-self-super-mul <:₀-refl m32 m4-diag = <:₀-refl
ADD-self-super-mul <:₀-refl m32 m42 = <:₀-refl
ADD-self-super-mul <:₀-refl m32 m43 = <:₀-refl
ADD-self-super-mul () m24 m₂
ADD-self-super-mul <:₀-+* m42 m0-right = <:₀-refl
ADD-self-super-mul <:₀-+* m42 m4-diag = <:₀-refl
ADD-self-super-mul <:₀-+* m42 m42 = <:₀-refl
ADD-self-super-mul <:₀-+* m42 m43 = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m0-right = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m4-diag = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m42 = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m43 = <:₀-refl
ADD-self-super-mul <:₀-+* m43 m0-right = <:₀-refl
ADD-self-super-mul <:₀-+* m43 m4-diag = <:₀-refl
ADD-self-super-mul <:₀-+* m43 m42 = <:₀-refl
ADD-self-super-mul <:₀-+* m43 m43 = <:₀-refl

ADD-self-super-plus : ∀ {η′ η₃ η}
  → `+ <:₀ η₃
  → MUL η′ η₃ η
  → ADD η η <:₀ η
ADD-self-super-plus +<:η₃ m0-left = <:₀-refl
ADD-self-super-plus () m0-right
ADD-self-super-plus <:₀-refl m1-left = <:₀-refl
ADD-self-super-plus <:₀-+* m1-left = <:₀-refl
ADD-self-super-plus <:₀-refl m1-right = <:₀-refl
ADD-self-super-plus <:₀-+* m1-right = <:₀-refl
ADD-self-super-plus () m2-diag
ADD-self-super-plus <:₀-refl m3-diag = <:₀-refl
ADD-self-super-plus <:₀-+* m4-diag = <:₀-refl
ADD-self-super-plus <:₀-refl m23 = <:₀-refl
ADD-self-super-plus () m32
ADD-self-super-plus <:₀-+* m24 = <:₀-refl
ADD-self-super-plus () m42
ADD-self-super-plus <:₀-+* m34 = <:₀-refl
ADD-self-super-plus <:₀-refl m43 = <:₀-refl

ADD-self-super-mul-left : ∀ {η₁ η₂ η}
  → `+ <:₀ η₁
  → MUL η₁ η₂ η
  → ADD η η <:₀ η
ADD-self-super-mul-left <:₀-refl m0-right = <:₀-refl
ADD-self-super-mul-left <:₀-refl m3-diag = <:₀-refl
ADD-self-super-mul-left <:₀-refl m32 = <:₀-refl
ADD-self-super-mul-left <:₀-refl m34 = <:₀-refl
ADD-self-super-mul-left <:₀-+* m0-right = <:₀-refl
ADD-self-super-mul-left <:₀-+* m4-diag = <:₀-refl
ADD-self-super-mul-left <:₀-+* m42 = <:₀-refl
ADD-self-super-mul-left <:₀-+* m43 = <:₀-refl

MUL-left-empty : ∀ {η₁ η₂ η} → `- <:₀ η₁ → MUL η₁ η₂ η → `- <:₀ η
MUL-left-empty η₁<: m0-left = <:₀-refl
MUL-left-empty η₁<: m0-right = <:₀-refl
MUL-left-empty () m1-left
MUL-left-empty () m1-right
MUL-left-empty <:₀--? m2-diag = <:₀--?
MUL-left-empty () m3-diag
MUL-left-empty <:₀--* m4-diag = <:₀--*
MUL-left-empty <:₀--? m23 = <:₀--*
MUL-left-empty () m32
MUL-left-empty <:₀--? m24 = <:₀--*
MUL-left-empty <:₀--* m42 = <:₀--*
MUL-left-empty () m34
MUL-left-empty <:₀--* m43 = <:₀--*

MUL-right-empty : ∀ {η₁ η₂ η} → `- <:₀ η₂ → MUL η₁ η₂ η → `- <:₀ η
MUL-right-empty η₂<: m0-left = <:₀-refl
MUL-right-empty η₂<: m0-right = <:₀-refl
MUL-right-empty η₂<: m1-left = η₂<:
MUL-right-empty η₂<: m1-right = η₂<:
MUL-right-empty <:₀--? m2-diag = <:₀--?
MUL-right-empty () m3-diag
MUL-right-empty <:₀--* m4-diag = <:₀--*
MUL-right-empty () m23
MUL-right-empty <:₀--? m32 = <:₀--*
MUL-right-empty <:₀--* m24 = <:₀--*
MUL-right-empty <:₀--? m42 = <:₀--*
MUL-right-empty <:₀--* m34 = <:₀--*
MUL-right-empty () m43

MUL-left-one-super : ∀ {η₁ η₂ η} → `! <:₀ η₁ → MUL η₁ η₂ η → η₂ <:₀ η
MUL-left-one-super () m0-left
MUL-left-one-super !<:η₁ m0-right = <:₀-refl
MUL-left-one-super <:₀-refl m1-left = <:₀-refl
MUL-left-one-super <:₀-refl m1-right = <:₀-refl
MUL-left-one-super <:₀-!? m2-diag = <:₀-refl
MUL-left-one-super <:₀-!+ m3-diag = <:₀-refl
MUL-left-one-super <:₀-!* m4-diag = <:₀-refl
MUL-left-one-super <:₀-!? m23 = <:₀-+*
MUL-left-one-super <:₀-!+ m32 = <:₀-?*
MUL-left-one-super <:₀-!? m24 = <:₀-refl
MUL-left-one-super <:₀-!* m42 = <:₀-?*
MUL-left-one-super <:₀-!+ m34 = <:₀-refl
MUL-left-one-super <:₀-!* m43 = <:₀-+*

MUL-right-one-super : ∀ {η₁ η₂ η} → `! <:₀ η₂ → MUL η₁ η₂ η → η₁ <:₀ η
MUL-right-one-super !<:η₂ m0-left = <:₀-refl
MUL-right-one-super () m0-right
MUL-right-one-super !<:η₂ m1-left = !<:η₂
MUL-right-one-super !<:η₂ m1-right = !<:η₂
MUL-right-one-super <:₀-!? m2-diag = <:₀-refl
MUL-right-one-super <:₀-!+ m3-diag = <:₀-refl
MUL-right-one-super <:₀-!* m4-diag = <:₀-refl
MUL-right-one-super <:₀-!+ m23 = <:₀-?*
MUL-right-one-super <:₀-!? m32 = <:₀-+*
MUL-right-one-super <:₀-!* m24 = <:₀-?*
MUL-right-one-super <:₀-!? m42 = <:₀-refl
MUL-right-one-super <:₀-!* m34 = <:₀-+*
MUL-right-one-super <:₀-!+ m43 = <:₀-refl

MUL-sound : ∀ η₁ η₂ {η} → MUL η₁ η₂ η → (𝓝⟦ η₁ ⟧ * 𝓝⟦ η₂ ⟧) ≤ 𝓝⟦ η ⟧
MUL-sound η₁ η₂ {η} m0-left rewrite *M-zero-left {𝓝⟦ η₂ ⟧ .Ivl.hi} = z≤n , z≤n
MUL-sound η₁ η₂ {η} m0-right rewrite *M-zero-right {𝓝⟦ η₁ ⟧ .Ivl.hi} = z≤n , z≤n
MUL-sound η₁ η₂ {η} m1-left rewrite +-identityʳ (𝓝⟦ η₂ ⟧ .Ivl.lo) | *M-identity-left {𝓝⟦ η₂ ⟧ .Ivl.hi} = ≤-refl , ≤M-refl
MUL-sound η₁ η₂ {η} m1-right rewrite +-identityʳ (𝓝⟦ η₂ ⟧ .Ivl.lo) | *M-identity-left {𝓝⟦ η₂ ⟧ .Ivl.hi} = ≤-refl , ≤M-refl
MUL-sound η₁ η₂ {η} m2-diag = z≤n , (s≤s z≤n)
MUL-sound η₁ η₂ {η} m3-diag = (s≤s z≤n) , tt
MUL-sound η₁ η₂ {η} m4-diag = z≤n , tt
MUL-sound η₁ η₂ {η} m23 = z≤n , tt
MUL-sound η₁ η₂ {η} m32 = z≤n , tt
MUL-sound η₁ η₂ {η} m24 = z≤n , tt
MUL-sound η₁ η₂ {η} m42 = z≤n , tt
MUL-sound η₁ η₂ {η} m34 = z≤n , tt
MUL-sound η₁ η₂ {η} m43 = z≤n , tt
