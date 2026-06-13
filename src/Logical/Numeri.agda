module Numeri where

open import Level using (Level) renaming (zero to lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_⊔_ to _⊔ℕ_; _⊓_ to _⊓ℕ_; _≤_ to _≤ℕ_; _*_ to _*ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; *-zeroʳ; *-identityʳ; ≤-refl; ≤-trans; ≤-antisym; m≤n+m; m≤m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; length; map; concat; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Function using (_∘_)

open import Interval


-- numeri

data Num : Set where
  `- `! `? `* `+ : Num

_≟Num_ : (η η′ : Num) → Dec (η ≡ η′)
`- ≟Num `- = yes refl
`- ≟Num `! = no λ ()
`- ≟Num `? = no λ ()
`- ≟Num `* = no λ ()
`- ≟Num `+ = no λ ()
`! ≟Num `- = no λ ()
`! ≟Num `! = yes refl
`! ≟Num `? = no λ ()
`! ≟Num `* = no λ ()
`! ≟Num `+ = no λ ()
`? ≟Num `- = no λ ()
`? ≟Num `! = no λ ()
`? ≟Num `? = yes refl
`? ≟Num `* = no λ ()
`? ≟Num `+ = no λ ()
`* ≟Num `- = no λ ()
`* ≟Num `! = no λ ()
`* ≟Num `? = no λ ()
`* ≟Num `* = yes refl
`* ≟Num `+ = no λ ()
`+ ≟Num `- = no λ ()
`+ ≟Num `! = no λ ()
`+ ≟Num `? = no λ ()
`+ ≟Num `* = no λ ()
`+ ≟Num `+ = yes refl

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
ADD `+ η = `+

ADD-comm : ∀ {η₁ η₂} → ADD η₁ η₂ ≡ ADD η₂ η₁
ADD-comm {`- } {`- } = refl
ADD-comm {`- } {`!} = refl
ADD-comm {`- } {`?} = refl
ADD-comm {`- } {`*} = refl
ADD-comm {`- } {`+} = refl
ADD-comm {`!} {`- } = refl
ADD-comm {`!} {`!} = refl
ADD-comm {`!} {`?} = refl
ADD-comm {`!} {`*} = refl
ADD-comm {`!} {`+} = refl
ADD-comm {`?} {`- } = refl
ADD-comm {`?} {`!} = refl
ADD-comm {`?} {`?} = refl
ADD-comm {`?} {`*} = refl
ADD-comm {`?} {`+} = refl
ADD-comm {`*} {`- } = refl
ADD-comm {`*} {`!} = refl
ADD-comm {`*} {`?} = refl
ADD-comm {`*} {`*} = refl
ADD-comm {`*} {`+} = refl
ADD-comm {`+} {`- } = refl
ADD-comm {`+} {`!} = refl
ADD-comm {`+} {`?} = refl
ADD-comm {`+} {`*} = refl
ADD-comm {`+} {`+} = refl

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


ADD-suc : ∀ {η}{k} → k ∈∈ 𝓝⟦ η ⟧ → suc k ∈∈ 𝓝⟦ ADD `! η ⟧
ADD-suc {`- } (0≤k , k≤0) = s≤s 0≤k , s≤s k≤0
ADD-suc {`!} (1≤k , k≤1) = s≤s z≤n
ADD-suc {`?} (0≤k , k≤1) = s≤s 0≤k
ADD-suc {`*} k∈ = s≤s k∈
ADD-suc {`+} k∈ = s≤s z≤n

ADD-suc? : ∀ {η}{k} → k ∈∈ 𝓝⟦ η ⟧ → suc k ∈∈ 𝓝⟦ ADD `? η ⟧
ADD-suc? {`- } (0≤k , k≤0) = z≤n , s≤s k≤0
ADD-suc? {`!} k∈ = s≤s z≤n
ADD-suc? {`?} k∈ = z≤n
ADD-suc? {`*} k∈ = z≤n
ADD-suc? {`+} k∈ = s≤s z≤n

suc-not-empty : ∀ {η}{k} → suc k ∈∈ 𝓝⟦ η ⟧ → η ≢ `-
suc-not-empty {`- } () η≡ε
suc-not-empty {`!} suck∈ ()
suc-not-empty {`?} suck∈ ()
suc-not-empty {`*} suck∈ ()
suc-not-empty {`+} suck∈ ()

DEC : Num → Num
DEC `- = `-
DEC `! = `-
DEC `? = `-
DEC `* = `*
DEC `+ = `*

DEC-sound : ∀ {η}{k} → (k∈ : suc k ∈∈ 𝓝⟦ η ⟧) → k ∈∈ 𝓝⟦ DEC η ⟧
DEC-sound {`!} (s≤s z≤n , s≤s z≤n) = z≤n , z≤n
DEC-sound {`?} (z≤n , s≤s z≤n) = z≤n , z≤n
DEC-sound {`*} k∈ = z≤n
DEC-sound {`+} k∈ = z≤n

DEC-complete : ∀ {η}{k} → η ≢ `- → (k∈ : k ∈∈ 𝓝⟦ DEC η ⟧) → suc k ∈∈ 𝓝⟦ η ⟧
DEC-complete {`- } η≢ k∈ = ⊥-elim (η≢ refl)
DEC-complete {`!} η≢ (0≤k , k≤0) = s≤s 0≤k , s≤s k≤0
DEC-complete {`?} η≢ k∈ = z≤n , s≤s (k∈ .proj₂)
DEC-complete {`*} η≢ k∈ = z≤n
DEC-complete {`+} η≢ k∈ = s≤s k∈

ADD-DEC : ∀ {η₁ η₂} {k} → η₁ ≢ `- → k ∈∈ 𝓝⟦ ADD (DEC η₁) η₂ ⟧ → suc k ∈∈ 𝓝⟦ ADD η₁ η₂ ⟧
ADD-DEC {`- } {η₂} η≢ k∈ = ⊥-elim (η≢ refl)
ADD-DEC {`!} {η₂} η≢ k∈ = ADD-suc k∈
ADD-DEC {`?} {η₂} η≢ k∈ = ADD-suc? k∈
ADD-DEC {`*} {`- } η≢ k∈ = z≤n
ADD-DEC {`*} {`!} η≢ k∈ = s≤s z≤n
ADD-DEC {`*} {`?} η≢ k∈ = z≤n
ADD-DEC {`*} {`*} η≢ k∈ = z≤n
ADD-DEC {`*} {`+} η≢ k∈ = s≤s z≤n
ADD-DEC {`+} {η₂} η≢ k∈ = s≤s z≤n

EXT0 : Num → Num
EXT0 `- = `-
EXT0 `! = `?
EXT0 `? = `?
EXT0 `* = `*
EXT0 `+ = `*

EXT0-super : ∀ {η} → η <:₀ EXT0 η
EXT0-super {`- } = <:₀-refl
EXT0-super {`!} = <:₀-!?
EXT0-super {`?} = <:₀-refl
EXT0-super {`*} = <:₀-refl
EXT0-super {`+} = <:₀-+*

EXT0-empty : ∀ {η} → `- <:₀ EXT0 η
EXT0-empty {`- } = <:₀-refl
EXT0-empty {`!} = <:₀--?
EXT0-empty {`?} = <:₀--?
EXT0-empty {`*} = <:₀--*
EXT0-empty {`+} = <:₀--*

EXT0-monotone : ∀ {η₁ η₂}
  → η₁ <:₀ η₂
  → EXT0 η₁ <:₀ EXT0 η₂
EXT0-monotone <:₀-refl = <:₀-refl
EXT0-monotone <:₀--? = <:₀--?
EXT0-monotone <:₀--* = <:₀--*
EXT0-monotone <:₀-!? = <:₀-refl
EXT0-monotone <:₀-!* = <:₀-?*
EXT0-monotone <:₀-!+ = <:₀-?*
EXT0-monotone <:₀-?* = <:₀-?*
EXT0-monotone <:₀-+* = <:₀-refl

EXT0-sound-0 : ∀ η → 0 ∈∈ 𝓝⟦ EXT0 η ⟧
EXT0-sound-0 `- = z≤n , z≤n
EXT0-sound-0 `! = z≤n , z≤n
EXT0-sound-0 `? = z≤n , z≤n
EXT0-sound-0 `* = z≤n
EXT0-sound-0 `+ = z≤n

EXT0-sound-1 : ∀ η {k} → k ∈∈ 𝓝⟦ η ⟧ → k ∈∈ 𝓝⟦ EXT0 η ⟧
EXT0-sound-1 `- k∈ = k∈
EXT0-sound-1 `! k∈ = z≤n , k∈ .proj₂
EXT0-sound-1 `? k∈ = k∈
EXT0-sound-1 `* k∈ = k∈
EXT0-sound-1 `+ k∈ = z≤n

data MUL : Num → Num → Num → Set where
  m0-left : ∀ {η} → MUL `- η `-
  m0-right : ∀ {η} → MUL η `- `-
  m1-left : ∀ {η} → MUL `! η η
  m1-right : ∀ {η} → MUL η `! η
  m2-diag : MUL `? `? `?
  m3-diag : MUL `+ `+ `+
  m4-diag : MUL `* `* `*
  m23     : MUL `? `+ `*
  m32     : MUL `+ `? `*
  m24     : MUL `? `* `*
  m42     : MUL `* `? `*
  m34     : MUL `+ `* `*
  m43     : MUL `* `+ `*

MUL₀ : Num → Num → Num
MUL₀ `- η₂ = `-
MUL₀ `! η₂ = η₂
MUL₀ `? `- = `-
MUL₀ `? `! = `?
MUL₀ `? `? = `?
MUL₀ `? `* = `*
MUL₀ `? `+ = `*
MUL₀ `* `- = `-
MUL₀ `* `! = `*
MUL₀ `* `? = `*
MUL₀ `* `* = `*
MUL₀ `* `+ = `*
MUL₀ `+ `- = `-
MUL₀ `+ `! = `+
MUL₀ `+ `? = `*
MUL₀ `+ `* = `*
MUL₀ `+ `+ = `+

MUL₀-sound : ∀ η₁ η₂ → MUL η₁ η₂ (MUL₀ η₁ η₂)
MUL₀-sound `- η₂ = m0-left
MUL₀-sound `! η₂ = m1-left
MUL₀-sound `? `- = m0-right
MUL₀-sound `? `! = m1-right
MUL₀-sound `? `? = m2-diag
MUL₀-sound `? `* = m24
MUL₀-sound `? `+ = m23
MUL₀-sound `* `- = m0-right
MUL₀-sound `* `! = m1-right
MUL₀-sound `* `? = m42
MUL₀-sound `* `* = m4-diag
MUL₀-sound `* `+ = m43
MUL₀-sound `+ `- = m0-right
MUL₀-sound `+ `! = m1-right
MUL₀-sound `+ `? = m32
MUL₀-sound `+ `* = m34
MUL₀-sound `+ `+ = m3-diag

MUL₀-complete : ∀ {η₁ η₂ η} → MUL η₁ η₂ η → MUL₀ η₁ η₂ <:₀ η
MUL₀-complete m0-left = <:₀-refl
MUL₀-complete {η₁ = `- } m0-right = <:₀-refl
MUL₀-complete {η₁ = `!} m0-right = <:₀-refl
MUL₀-complete {η₁ = `?} m0-right = <:₀-refl
MUL₀-complete {η₁ = `*} m0-right = <:₀-refl
MUL₀-complete {η₁ = `+} m0-right = <:₀-refl
MUL₀-complete m1-left = <:₀-refl
MUL₀-complete {η₁ = `- } m1-right = <:₀-refl
MUL₀-complete {η₁ = `!} m1-right = <:₀-refl
MUL₀-complete {η₁ = `?} m1-right = <:₀-refl
MUL₀-complete {η₁ = `*} m1-right = <:₀-refl
MUL₀-complete {η₁ = `+} m1-right = <:₀-refl
MUL₀-complete m2-diag = <:₀-refl
MUL₀-complete m3-diag = <:₀-refl
MUL₀-complete m4-diag = <:₀-refl
MUL₀-complete m23 = <:₀-refl
MUL₀-complete m32 = <:₀-refl
MUL₀-complete m24 = <:₀-refl
MUL₀-complete m42 = <:₀-refl
MUL₀-complete m34 = <:₀-refl
MUL₀-complete m43 = <:₀-refl

MUL₀-monotone-left : ∀ {η₁ η₂ η₃}
  → η₁ <:₀ η₂
  → MUL₀ η₁ η₃ <:₀ MUL₀ η₂ η₃
MUL₀-monotone-left <:₀-refl = <:₀-refl
MUL₀-monotone-left {η₃ = `- } <:₀--? = <:₀-refl
MUL₀-monotone-left {η₃ = `!} <:₀--? = <:₀--?
MUL₀-monotone-left {η₃ = `?} <:₀--? = <:₀--?
MUL₀-monotone-left {η₃ = `*} <:₀--? = <:₀--*
MUL₀-monotone-left {η₃ = `+} <:₀--? = <:₀--*
MUL₀-monotone-left {η₃ = `- } <:₀--* = <:₀-refl
MUL₀-monotone-left {η₃ = `!} <:₀--* = <:₀--*
MUL₀-monotone-left {η₃ = `?} <:₀--* = <:₀--*
MUL₀-monotone-left {η₃ = `*} <:₀--* = <:₀--*
MUL₀-monotone-left {η₃ = `+} <:₀--* = <:₀--*
MUL₀-monotone-left {η₃ = `- } <:₀-!? = <:₀-refl
MUL₀-monotone-left {η₃ = `!} <:₀-!? = <:₀-!?
MUL₀-monotone-left {η₃ = `?} <:₀-!? = <:₀-refl
MUL₀-monotone-left {η₃ = `*} <:₀-!? = <:₀-refl
MUL₀-monotone-left {η₃ = `+} <:₀-!? = <:₀-+*
MUL₀-monotone-left {η₃ = `- } <:₀-!* = <:₀-refl
MUL₀-monotone-left {η₃ = `!} <:₀-!* = <:₀-!*
MUL₀-monotone-left {η₃ = `?} <:₀-!* = <:₀-?*
MUL₀-monotone-left {η₃ = `*} <:₀-!* = <:₀-refl
MUL₀-monotone-left {η₃ = `+} <:₀-!* = <:₀-+*
MUL₀-monotone-left {η₃ = `- } <:₀-!+ = <:₀-refl
MUL₀-monotone-left {η₃ = `!} <:₀-!+ = <:₀-!+
MUL₀-monotone-left {η₃ = `?} <:₀-!+ = <:₀-?*
MUL₀-monotone-left {η₃ = `*} <:₀-!+ = <:₀-refl
MUL₀-monotone-left {η₃ = `+} <:₀-!+ = <:₀-refl
MUL₀-monotone-left {η₃ = `- } <:₀-?* = <:₀-refl
MUL₀-monotone-left {η₃ = `!} <:₀-?* = <:₀-?*
MUL₀-monotone-left {η₃ = `?} <:₀-?* = <:₀-?*
MUL₀-monotone-left {η₃ = `*} <:₀-?* = <:₀-refl
MUL₀-monotone-left {η₃ = `+} <:₀-?* = <:₀-refl
MUL₀-monotone-left {η₃ = `- } <:₀-+* = <:₀-refl
MUL₀-monotone-left {η₃ = `!} <:₀-+* = <:₀-+*
MUL₀-monotone-left {η₃ = `?} <:₀-+* = <:₀-refl
MUL₀-monotone-left {η₃ = `*} <:₀-+* = <:₀-refl
MUL₀-monotone-left {η₃ = `+} <:₀-+* = <:₀-+*

MUL₀-monotone-right : ∀ {η₁ η₂ η₃}
  → η₂ <:₀ η₃
  → MUL₀ η₁ η₂ <:₀ MUL₀ η₁ η₃
MUL₀-monotone-right <:₀-refl = <:₀-refl
MUL₀-monotone-right {η₁ = `- } <:₀--? = <:₀-refl
MUL₀-monotone-right {η₁ = `!} <:₀--? = <:₀--?
MUL₀-monotone-right {η₁ = `?} <:₀--? = <:₀--?
MUL₀-monotone-right {η₁ = `*} <:₀--? = <:₀--*
MUL₀-monotone-right {η₁ = `+} <:₀--? = <:₀--*
MUL₀-monotone-right {η₁ = `- } <:₀--* = <:₀-refl
MUL₀-monotone-right {η₁ = `!} <:₀--* = <:₀--*
MUL₀-monotone-right {η₁ = `?} <:₀--* = <:₀--*
MUL₀-monotone-right {η₁ = `*} <:₀--* = <:₀--*
MUL₀-monotone-right {η₁ = `+} <:₀--* = <:₀--*
MUL₀-monotone-right {η₁ = `- } <:₀-!? = <:₀-refl
MUL₀-monotone-right {η₁ = `!} <:₀-!? = <:₀-!?
MUL₀-monotone-right {η₁ = `?} <:₀-!? = <:₀-refl
MUL₀-monotone-right {η₁ = `*} <:₀-!? = <:₀-refl
MUL₀-monotone-right {η₁ = `+} <:₀-!? = <:₀-+*
MUL₀-monotone-right {η₁ = `- } <:₀-!* = <:₀-refl
MUL₀-monotone-right {η₁ = `!} <:₀-!* = <:₀-!*
MUL₀-monotone-right {η₁ = `?} <:₀-!* = <:₀-?*
MUL₀-monotone-right {η₁ = `*} <:₀-!* = <:₀-refl
MUL₀-monotone-right {η₁ = `+} <:₀-!* = <:₀-+*
MUL₀-monotone-right {η₁ = `- } <:₀-!+ = <:₀-refl
MUL₀-monotone-right {η₁ = `!} <:₀-!+ = <:₀-!+
MUL₀-monotone-right {η₁ = `?} <:₀-!+ = <:₀-?*
MUL₀-monotone-right {η₁ = `*} <:₀-!+ = <:₀-refl
MUL₀-monotone-right {η₁ = `+} <:₀-!+ = <:₀-refl
MUL₀-monotone-right {η₁ = `- } <:₀-?* = <:₀-refl
MUL₀-monotone-right {η₁ = `!} <:₀-?* = <:₀-?*
MUL₀-monotone-right {η₁ = `?} <:₀-?* = <:₀-?*
MUL₀-monotone-right {η₁ = `*} <:₀-?* = <:₀-refl
MUL₀-monotone-right {η₁ = `+} <:₀-?* = <:₀-refl
MUL₀-monotone-right {η₁ = `- } <:₀-+* = <:₀-refl
MUL₀-monotone-right {η₁ = `!} <:₀-+* = <:₀-+*
MUL₀-monotone-right {η₁ = `?} <:₀-+* = <:₀-refl
MUL₀-monotone-right {η₁ = `*} <:₀-+* = <:₀-refl
MUL₀-monotone-right {η₁ = `+} <:₀-+* = <:₀-+*

MUL₀-monotone : ∀ {η₁ η₂ η₁′ η₂′}
  → η₁ <:₀ η₁′
  → η₂ <:₀ η₂′
  → MUL₀ η₁ η₂ <:₀ MUL₀ η₁′ η₂′
MUL₀-monotone {η₂ = η₂} {η₁′ = η₁′} η₁<:η₁′ η₂<:η₂′ =
  <:₀-trans
    (MUL₀-monotone-left {η₃ = η₂} η₁<:η₁′)
    (MUL₀-monotone-right {η₁ = η₁′} η₂<:η₂′)
  
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

ADD-monotone-right : ∀ {η₁ η₂ η₃}
  → η₂ <:₀ η₃
  → ADD η₁ η₂ <:₀ ADD η₁ η₃
ADD-monotone-right {η₁} {η₂} {η₃} η₂<:η₃
  rewrite ADD-comm {η₁} {η₂}
        | ADD-comm {η₁} {η₃}
  = ADD-monotone-left η₂<:η₃

ADD-monotone-both : ∀ {η₁ η₂ η₁′ η₂′}
  → η₁ <:₀ η₁′
  → η₂ <:₀ η₂′
  → ADD η₁ η₂ <:₀ ADD η₁′ η₂′
ADD-monotone-both η₁<:η₁′ η₂<:η₂′ =
  <:₀-trans (ADD-monotone-left η₁<:η₁′) (ADD-monotone-right η₂<:η₂′)

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
ADD-self-super-mul +<:η₁ m0-right m1-right = <:₀-refl
ADD-self-super-mul () m1-left m₂
ADD-self-super-mul <:₀-refl m1-right m0-right = <:₀-refl
ADD-self-super-mul <:₀-refl m1-right m1-right = <:₀-refl
ADD-self-super-mul <:₀-refl m1-right m3-diag = <:₀-refl
ADD-self-super-mul <:₀-refl m1-right m32 = <:₀-refl
ADD-self-super-mul <:₀-refl m1-right m34 = <:₀-refl
ADD-self-super-mul <:₀-+* m1-right m0-right = <:₀-refl
ADD-self-super-mul <:₀-+* m1-right m1-right = <:₀-refl
ADD-self-super-mul <:₀-+* m1-right m4-diag = <:₀-refl
ADD-self-super-mul <:₀-+* m1-right m42 = <:₀-refl
ADD-self-super-mul <:₀-+* m1-right m43 = <:₀-refl
ADD-self-super-mul () m2-diag m₂
ADD-self-super-mul <:₀-refl m3-diag m3-diag = <:₀-refl
ADD-self-super-mul <:₀-refl m3-diag m0-right = <:₀-refl
ADD-self-super-mul <:₀-refl m3-diag m1-right = <:₀-refl
ADD-self-super-mul <:₀-refl m3-diag m32 = <:₀-refl
ADD-self-super-mul <:₀-refl m3-diag m34 = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m0-right = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m1-right = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m4-diag = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m42 = <:₀-refl
ADD-self-super-mul <:₀-+* m4-diag m43 = <:₀-refl
ADD-self-super-mul () m23 m₂
ADD-self-super-mul <:₀-refl m32 m0-right = <:₀-refl
ADD-self-super-mul <:₀-refl m32 m1-right = <:₀-refl
ADD-self-super-mul <:₀-refl m32 m4-diag = <:₀-refl
ADD-self-super-mul <:₀-refl m32 m42 = <:₀-refl
ADD-self-super-mul <:₀-refl m32 m43 = <:₀-refl
ADD-self-super-mul () m24 m₂
ADD-self-super-mul <:₀-+* m42 m0-right = <:₀-refl
ADD-self-super-mul <:₀-+* m42 m1-right = <:₀-refl
ADD-self-super-mul <:₀-+* m42 m4-diag = <:₀-refl
ADD-self-super-mul <:₀-+* m42 m42 = <:₀-refl
ADD-self-super-mul <:₀-+* m42 m43 = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m0-right = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m1-right = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m4-diag = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m42 = <:₀-refl
ADD-self-super-mul <:₀-refl m34 m43 = <:₀-refl
ADD-self-super-mul <:₀-+* m43 m0-right = <:₀-refl
ADD-self-super-mul <:₀-+* m43 m1-right = <:₀-refl
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
ADD-self-super-plus () m1-right
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
ADD-self-super-mul-left <:₀-refl m1-right = <:₀-refl
ADD-self-super-mul-left <:₀-refl m3-diag = <:₀-refl
ADD-self-super-mul-left <:₀-refl m32 = <:₀-refl
ADD-self-super-mul-left <:₀-refl m34 = <:₀-refl
ADD-self-super-mul-left <:₀-+* m0-right = <:₀-refl
ADD-self-super-mul-left <:₀-+* m1-right = <:₀-refl
ADD-self-super-mul-left <:₀-+* m4-diag = <:₀-refl
ADD-self-super-mul-left <:₀-+* m42 = <:₀-refl
ADD-self-super-mul-left <:₀-+* m43 = <:₀-refl

MUL-left-empty : ∀ {η₁ η₂ η} → `- <:₀ η₁ → MUL η₁ η₂ η → `- <:₀ η
MUL-left-empty η₁<: m0-left = <:₀-refl
MUL-left-empty η₁<: m0-right = <:₀-refl
MUL-left-empty () m1-left
MUL-left-empty <:₀-refl m1-right = <:₀-refl
MUL-left-empty <:₀--? m1-right = <:₀--?
MUL-left-empty <:₀--* m1-right = <:₀--*
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
MUL-right-empty () m1-right
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
MUL-left-one-super <:₀-!? m1-right = <:₀-!?
MUL-left-one-super <:₀-!* m1-right = <:₀-!*
MUL-left-one-super <:₀-!+ m1-right = <:₀-!+
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
MUL-right-one-super <:₀-refl m1-right = <:₀-refl
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
MUL-sound η₁ η₂ {η} m1-right rewrite *-identityʳ (𝓝⟦ η₁ ⟧ .Ivl.lo) | *M-identity-right {𝓝⟦ η₁ ⟧ .Ivl.hi} = ≤-refl , ≤M-refl
MUL-sound η₁ η₂ {η} m2-diag = z≤n , (s≤s z≤n)
MUL-sound η₁ η₂ {η} m3-diag = (s≤s z≤n) , tt
MUL-sound η₁ η₂ {η} m4-diag = z≤n , tt
MUL-sound η₁ η₂ {η} m23 = z≤n , tt
MUL-sound η₁ η₂ {η} m32 = z≤n , tt
MUL-sound η₁ η₂ {η} m24 = z≤n , tt
MUL-sound η₁ η₂ {η} m42 = z≤n , tt
MUL-sound η₁ η₂ {η} m34 = z≤n , tt
MUL-sound η₁ η₂ {η} m43 = z≤n , tt

<:₀-subset : ∀ {η η′} {k} → η <:₀ η′ → k ∈∈ 𝓝⟦ η ⟧ → k ∈∈ 𝓝⟦ η′ ⟧
<:₀-subset <:₀-refl k∈ = k∈
<:₀-subset <:₀--? (0≤k , z≤n) = 0≤k , z≤n
<:₀-subset <:₀--* (0≤k , k≤0) = 0≤k
<:₀-subset <:₀-!? (1≤k , k≤1) = z≤n , k≤1
<:₀-subset <:₀-!* (1≤k , k≤1) = z≤n
<:₀-subset <:₀-!+ (1≤k , k≤1) = 1≤k
<:₀-subset <:₀-?* (0≤k , k≤1) = 0≤k
<:₀-subset <:₀-+* k∈ = z≤n

ADD-0-k : ∀ {η₁}{η₂}{k} → 0 ∈∈ 𝓝⟦ η₁ ⟧ → k ∈∈ 𝓝⟦ η₂ ⟧ → k ∈∈ 𝓝⟦ ADD η₁ η₂ ⟧
ADD-0-k {`- } {`- } 0∈ k∈ = k∈
ADD-0-k {`- } {`!} 0∈ k∈ = k∈
ADD-0-k {`- } {`?} 0∈ k∈ = k∈
ADD-0-k {`- } {`*} 0∈ k∈ = k∈
ADD-0-k {`- } {`+} 0∈ k∈ = k∈
ADD-0-k {`?} {`- } 0∈ (0≤k , k≤0) = 0≤k , ≤-trans k≤0 z≤n
ADD-0-k {`?} {`!} 0∈ k∈ = k∈ .proj₁
ADD-0-k {`?} {`?} 0∈ k∈ = k∈ .proj₁
ADD-0-k {`?} {`*} 0∈ k∈ = k∈
ADD-0-k {`?} {`+} 0∈ k∈ = k∈
ADD-0-k {`*} {`- } 0∈ k∈ = k∈ .proj₁
ADD-0-k {`*} {`!} 0∈ k∈ = k∈ .proj₁
ADD-0-k {`*} {`?} 0∈ k∈ = k∈ .proj₁
ADD-0-k {`*} {`*} 0∈ k∈ = k∈
ADD-0-k {`*} {`+} 0∈ k∈ = k∈

ADD-k-0 : ∀ {η₁}{η₂}{k} → k ∈∈ 𝓝⟦ η₁ ⟧ → 0 ∈∈ 𝓝⟦ η₂ ⟧ → k ∈∈ 𝓝⟦ ADD η₁ η₂ ⟧
ADD-k-0  {η₁}{η₂} k∈ 0∈ rewrite ADD-comm {η₁}{η₂} = ADD-0-k 0∈ k∈

ADD-i-j : ∀ {η₁}{η₂}{j}{k} → j ∈∈ 𝓝⟦ η₁ ⟧ → k ∈∈ 𝓝⟦ η₂ ⟧ → (j +ℕ k) ∈∈ 𝓝⟦ ADD η₁ η₂ ⟧
ADD-i-j {`- } {η₂} (0≤j , j≤0) k∈ rewrite ≤-antisym j≤0 0≤j = k∈
ADD-i-j {`!} {η₂} (1≤j , j≤1) k∈ rewrite ≤-antisym j≤1 1≤j = ADD-suc k∈
ADD-i-j {`?} {`- } {j} {k} j∈ (0≤k , k≤0)
  rewrite ≤-antisym k≤0 0≤k
        | +-identityʳ j
  = j∈
ADD-i-j {`?} {`!} {j} {k} j∈ (1≤k , k≤1) = ≤-trans 1≤k (m≤n+m k j)
ADD-i-j {`?} {`?} j∈ k∈ = z≤n
ADD-i-j {`?} {`*} j∈ k∈ = z≤n
ADD-i-j {`?} {`+} {j} {k} j∈ k∈ = ≤-trans k∈ (m≤n+m k j)

ADD-i-j {`*} {`- } j∈ k∈ = z≤n
ADD-i-j {`*} {`!} {j} {k} j∈ (1≤k , k≤1) = ≤-trans 1≤k (m≤n+m k j)
ADD-i-j {`*} {`?} j∈ k∈ = z≤n
ADD-i-j {`*} {`*} j∈ k∈ = z≤n
ADD-i-j {`*} {`+} {j} {k} j∈ k∈ = ≤-trans k∈ (m≤n+m k j)

ADD-i-j {`+} {η₂} {j} {k} j∈ k∈ = ≤-trans j∈ (m≤m+n j k)

numOfLen : ℕ → Num
numOfLen zero = `-
numOfLen (suc zero) = `!
numOfLen (suc (suc _)) = `+

numOfLen-sound : ∀ n → n ∈∈ 𝓝⟦ numOfLen n ⟧
numOfLen-sound zero = z≤n , z≤n
numOfLen-sound (suc zero) = s≤s z≤n , s≤s z≤n
numOfLen-sound (suc (suc n)) = s≤s z≤n

numOfLen-sub : ∀ {n η} → n ∈∈ 𝓝⟦ η ⟧ → numOfLen n <:₀ η
numOfLen-sub {zero} {`- } n∈ = <:₀-refl
numOfLen-sub {zero} {`!} (() , k≤1)
numOfLen-sub {zero} {`?} n∈ = <:₀--?
numOfLen-sub {zero} {`*} n∈ = <:₀--*
numOfLen-sub {zero} {`+} ()
numOfLen-sub {suc zero} {`- } (0≤n , ())
numOfLen-sub {suc zero} {`!} n∈ = <:₀-refl
numOfLen-sub {suc zero} {`?} n∈ = <:₀-!?
numOfLen-sub {suc zero} {`*} n∈ = <:₀-!*
numOfLen-sub {suc zero} {`+} n∈ = <:₀-!+
numOfLen-sub {suc (suc n)} {`- } (0≤n , ())
numOfLen-sub {suc (suc n)} {`!} (1≤n , s≤s ())
numOfLen-sub {suc (suc n)} {`?} (0≤n , s≤s ())
numOfLen-sub {suc (suc n)} {`*} n∈ = <:₀-+*
numOfLen-sub {suc (suc n)} {`+} n∈ = <:₀-refl

numOfLen-add-super : ∀ n₁ n₂ → ADD (numOfLen n₁) (numOfLen n₂) <:₀ numOfLen (n₁ +ℕ n₂)
numOfLen-add-super zero zero = <:₀-refl
numOfLen-add-super zero (suc zero) = <:₀-refl
numOfLen-add-super zero (suc (suc n₂)) = <:₀-refl
numOfLen-add-super (suc zero) zero = <:₀-refl
numOfLen-add-super (suc zero) (suc zero) = <:₀-refl
numOfLen-add-super (suc zero) (suc (suc n₂)) = <:₀-refl
numOfLen-add-super (suc (suc n₁)) zero = <:₀-refl
numOfLen-add-super (suc (suc n₁)) (suc zero) = <:₀-refl
numOfLen-add-super (suc (suc n₁)) (suc (suc n₂)) = <:₀-refl
