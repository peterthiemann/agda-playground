module Michelson.DecEquality where

open import Data.Nat using (ℕ; _≟_)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

{-
_≟T_ : (t₁ : Type) (t₂ : Type) → Dec (t₁ ≡ t₂)
address ≟T address = yes refl
big-map s₁ s₂ ≟T big-map t₁ t₂
  with s₁ ≟T t₁ | s₂ ≟T t₂
... | no ¬p | no ¬p₁ = no (λ {refl → ¬p refl})
... | no ¬p | yes p = no (λ {refl → ¬p refl})
... | yes p | no ¬p = no (λ {refl → ¬p refl})
... | yes refl | yes refl = yes refl
bls12-381-fr ≟T bls12-381-fr = yes refl
bls12-381-g1 ≟T bls12-381-g1 = yes refl
bls12-381-g2 ≟T bls12-381-g2 = yes refl
bool ≟T bool = yes refl
bytes ≟T bytes = yes refl
chain-id ≟T chain-id = yes refl
contract s ≟T contract t
  with s ≟T t
... | yes refl = yes refl
... | no s≢t = no λ{ refl → s≢t refl}
int ≟T int = yes refl
key ≟T key = yes refl
key-hash ≟T key-hash = yes refl
lambda s₁ s₂ ≟T lambda t₁ t₂
  with s₁ ≟T t₁ | s₂ ≟T t₂
... | no ¬p | no ¬p₁ = no (λ {refl → ¬p refl})
... | no ¬p | yes p = no (λ {refl → ¬p refl})
... | yes p | no ¬p = no (λ {refl → ¬p refl})
... | yes refl | yes refl = yes refl
list s ≟T list t
  with s ≟T t
... | yes refl = yes refl
... | no s≢t = no λ{ refl → s≢t refl}
map s₁ s₂ ≟T map t₁ t₂
  with s₁ ≟T t₁ | s₂ ≟T t₂
... | no ¬p | no ¬p₁ = no (λ {refl → ¬p refl})
... | no ¬p | yes p = no (λ {refl → ¬p refl})
... | yes p | no ¬p = no (λ {refl → ¬p refl})
... | yes refl | yes refl = yes refl
mutez ≟T mutez = yes refl
nat ≟T nat = yes refl
never ≟T never = yes refl
operation ≟T operation = yes refl
option s ≟T option t
  with s ≟T t
... | yes refl = yes refl
... | no s≢t = no λ{ refl → s≢t refl}
or s₁ s₂ ≟T or t₁ t₂
  with s₁ ≟T t₁ | s₂ ≟T t₂
... | no ¬p | no ¬p₁ = no (λ {refl → ¬p refl})
... | no ¬p | yes p = no (λ {refl → ¬p refl})
... | yes p | no ¬p = no (λ {refl → ¬p refl})
... | yes refl | yes refl = yes refl
pair s₁ s₂ ≟T pair t₁ t₂
  with s₁ ≟T t₁ | s₂ ≟T t₂
... | no ¬p | no ¬p₁ = no (λ {refl → ¬p refl})
... | no ¬p | yes p = no (λ {refl → ¬p refl})
... | yes p | no ¬p = no (λ {refl → ¬p refl})
... | yes refl | yes refl = yes refl
sapling-state m ≟T sapling-state n
  with m ≟ n
... | yes refl = yes refl
... | no s≢t = no λ{ refl → s≢t refl}
sapling-transation m ≟T sapling-transation n
  with m ≟ n
... | yes refl = yes refl
... | no s≢t = no λ{ refl → s≢t refl}
set s ≟T set t
  with s ≟T t
... | yes refl = yes refl
... | no s≢t = no λ{ refl → s≢t refl}
signature ≟T signature = yes refl
string ≟T string = yes refl
ticket s ≟T ticket t
  with s ≟T t
... | yes refl = yes refl
... | no s≢t = no λ{ refl → s≢t refl}
timestamp ≟T timestamp = yes refl
unit ≟T unit = yes refl
t₁ ≟T t₂ = no λ{ x → {!x!}}
-}
