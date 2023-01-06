module Michelson.Types where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)

data Type : Set where
  address : Type
  big-map : Type → Type → Type
  bls12-381-fr : Type
  bls12-381-g1 : Type
  bls12-381-g2 : Type
  bool : Type
  bytes : Type
  chain-id : Type
  contract : Type → Type
  int : Type
  key : Type
  key-hash : Type
  lambda : Type → Type → Type
  list : Type → Type
  map : Type → Type → Type
  mutez : Type
  nat : Type
  never : Type
  operation : Type
  option : Type → Type
  or : Type → Type → Type
  pair : Type → Type → Type
  sapling-state : ℕ → Type
  sapling-transation : ℕ → Type
  set : Type → Type
  signature : Type
  string : Type
  ticket : Type → Type
  timestamp : Type
  unit : Type

Comparable : Type → Set
Comparable address = ⊤
Comparable (big-map t₁ t₂) = ⊥
Comparable bls12-381-fr = ⊥
Comparable bls12-381-g1 = ⊥
Comparable bls12-381-g2 = ⊥
Comparable bool = ⊤
Comparable bytes = ⊤
Comparable chain-id = ⊤
Comparable (contract t) = ⊥
Comparable int = ⊤
Comparable key = ⊤
Comparable key-hash = ⊤
Comparable (lambda t₁ t₂) = ⊥
Comparable (list t) = ⊥
Comparable (map t₁ t₂) = ⊥
Comparable mutez = ⊤
Comparable nat = ⊤
Comparable never = ⊤
Comparable operation = ⊥
Comparable (option t) = Comparable t
Comparable (or t₁ t₂) = Comparable t₁ × Comparable t₂
Comparable (pair t₁ t₂) = Comparable t₁ × Comparable t₂
Comparable (sapling-state x) = ⊥
Comparable (sapling-transation x) = ⊥
Comparable (set t) = ⊥
Comparable signature = ⊤
Comparable string = ⊤
Comparable (ticket t) = ⊥
Comparable timestamp = ⊤
Comparable unit = ⊤

Passable : Type → Set
Passable address = ⊤
Passable (big-map t₁ t₂) = ⊤
Passable bls12-381-fr = ⊤
Passable bls12-381-g1 = ⊤
Passable bls12-381-g2 = ⊤
Passable bool = ⊤
Passable bytes = ⊤
Passable chain-id = ⊤
Passable (contract t) = ⊤
Passable int = ⊤
Passable key = ⊤
Passable key-hash = ⊤
Passable (lambda t₁ t₂) = ⊤
Passable (list t) = ⊤
Passable (map t₁ t₂) = ⊤
Passable mutez = ⊤
Passable nat = ⊤
Passable never = ⊤
Passable operation = ⊥
Passable (option t) = Passable t
Passable (or t₁ t₂) = Passable t₁ × Passable t₂
Passable (pair t₁ t₂) = Passable t₁ × Passable t₂
Passable (sapling-state x) = ⊤
Passable (sapling-transation x) = ⊤
Passable (set t) = ⊤
Passable signature = ⊤
Passable string = ⊤
Passable (ticket t) = ⊤
Passable timestamp = ⊤
Passable unit = ⊤

Pushable : Type → Set
Pushable address = ⊤
Pushable (big-map t₁ t₂) = ⊥
Pushable bls12-381-fr = ⊤
Pushable bls12-381-g1 = ⊤
Pushable bls12-381-g2 = ⊤
Pushable bool = ⊤
Pushable bytes = ⊤
Pushable chain-id = ⊤
Pushable (contract t) = ⊥
Pushable int = ⊤
Pushable key = ⊤
Pushable key-hash = ⊤
Pushable (lambda t₁ t₂) = ⊤
Pushable (list t) = ⊤
Pushable (map t₁ t₂) = ⊤
Pushable mutez = ⊤
Pushable nat = ⊤
Pushable never = ⊤
Pushable operation = ⊥
Pushable (option t) = Pushable t
Pushable (or t₁ t₂) = Pushable t₁ × Pushable t₂
Pushable (pair t₁ t₂) = Pushable t₁ × Pushable t₂
Pushable (sapling-state x) = ⊥
Pushable (sapling-transation x) = ⊤
Pushable (set t) = ⊤
Pushable signature = ⊤
Pushable string = ⊤
Pushable (ticket t) = ⊥
Pushable timestamp = ⊤
Pushable unit = ⊤

data NotImplemented : Set where

record Address : Set where

record ChainId : Set where

record Contract (ty : Type) : Set where

record KeyHash : Set where
  field
    hashcode : String

record Mutez : Set where
  field
    amount : ℕ
record MSet (A : Set) : Set where
  field
    contents : List A
record Timestamp : Set where
  field
    instant : ℤ

record Code (pty : Type) (sty : Type) : Set where

data Operation : Set where
  CREATE-CONTRACT : (pty : Type) (sty : Type) → Code pty sty → Operation
  SET-DELEGATE    : Maybe KeyHash → Operation
  TRANSFER-TOKENS : (ty : Type) → Mutez → Contract ty → Operation

T⟦_⟧ : Type → Set
T⟦ address ⟧ = Address
T⟦ big-map t t₁ ⟧ = NotImplemented
T⟦ bls12-381-fr ⟧ = NotImplemented
T⟦ bls12-381-g1 ⟧ = NotImplemented
T⟦ bls12-381-g2 ⟧ = NotImplemented
T⟦ bool ⟧ = Bool
T⟦ bytes ⟧ = NotImplemented
T⟦ chain-id ⟧ = ChainId
T⟦ contract t ⟧ = Contract t
T⟦ int ⟧ = ℤ
T⟦ key ⟧ = NotImplemented
T⟦ key-hash ⟧ = KeyHash
T⟦ lambda t₁ t₂ ⟧ = T⟦ t₁ ⟧ → T⟦ t₂ ⟧
T⟦ list t ⟧ = List T⟦ t ⟧
T⟦ map t₁ t₂ ⟧ = List (T⟦ t₁ ⟧ × T⟦ t₂ ⟧)
T⟦ mutez ⟧ = Mutez
T⟦ nat ⟧ = ℕ
T⟦ never ⟧ = ⊥
T⟦ operation ⟧ = Operation
T⟦ option t ⟧ = Maybe T⟦ t ⟧
T⟦ or t₁ t₂ ⟧ = T⟦ t₁ ⟧ ⊎ T⟦ t₂ ⟧
T⟦ pair t₁ t₂ ⟧ = T⟦ t₁ ⟧ × T⟦ t₂ ⟧
T⟦ sapling-state x ⟧ = NotImplemented
T⟦ sapling-transation x ⟧ = NotImplemented
T⟦ set t ⟧ = MSet T⟦ t ⟧
T⟦ signature ⟧ = NotImplemented
T⟦ string ⟧ = String
T⟦ ticket t ⟧ = NotImplemented
T⟦ timestamp ⟧ = Timestamp
T⟦ unit ⟧ = ⊤

