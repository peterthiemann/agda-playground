{-# OPTIONS --no-positivity-check #-}
module Michelson.Types where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List using (List) renaming (map to mapᴸ)
open import Data.Maybe using (Maybe) renaming (map to mapᴹ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⁺)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

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


variable
  t t₁ t₂ : Type

data Literal : Type → Set where
  L-nat   : ℕ → Literal nat
  L-bool  : Bool → Literal bool
  L-int   : ℤ → Literal int
  L-unit  : Literal unit
  L-list  : List (Literal t)  → Literal (list t)
  L-pair  : Literal t₁ × Literal t₂ → Literal (pair t₁ t₂)
  L-or    : Literal t₁ ⊎ Literal t₂ → Literal (or t₁ t₂)
  L-maybe : Maybe (Literal t) → Literal (option t)


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

Storable : Type → Set
Storable address = ⊤
Storable (big-map t₁ t₂) = ⊤
Storable bls12-381-fr = ⊤
Storable bls12-381-g1 = ⊤
Storable bls12-381-g2 = ⊤
Storable bool = ⊤
Storable bytes = ⊤
Storable chain-id = ⊤
Storable (contract t) = ⊥
Storable int = ⊤
Storable key = ⊤
Storable key-hash = ⊤
Storable (lambda t₁ t₂) = ⊤
Storable (list t) = ⊤
Storable (map t₁ t₂) = ⊤
Storable mutez = ⊤
Storable nat = ⊤
Storable never = ⊤
Storable operation = ⊥
Storable (option t) = Storable t
Storable (or t₁ t₂) = Storable t₁ × Storable t₂
Storable (pair t₁ t₂) = Storable t₁ × Storable t₂
Storable (sapling-state x) = ⊤
Storable (sapling-transation x) = ⊤
Storable (set t) = ⊤
Storable signature = ⊤
Storable string = ⊤
Storable (ticket t) = ⊤
Storable timestamp = ⊤
Storable unit = ⊤

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

Packable : Type → Set
Packable address = ⊤
Packable (big-map t₁ t₂) = ⊥
Packable bls12-381-fr = ⊤
Packable bls12-381-g1 = ⊤
Packable bls12-381-g2 = ⊤
Packable bool = ⊤
Packable bytes = ⊤
Packable chain-id = ⊤
Packable (contract t) = ⊤
Packable int = ⊤
Packable key = ⊤
Packable key-hash = ⊤
Packable (lambda t₁ t₂) = ⊤
Packable (list t) = ⊤
Packable (map t₁ t₂) = ⊤
Packable mutez = ⊤
Packable nat = ⊤
Packable never = ⊤
Packable operation = ⊥
Packable (option t) = Packable t
Packable (or t₁ t₂) = Packable t₁ × Packable t₂
Packable (pair t₁ t₂) = Packable t₁ × Packable t₂
Packable (sapling-state x) = ⊥
Packable (sapling-transation x) = ⊤
Packable (set t) = ⊤
Packable signature = ⊤
Packable string = ⊤
Packable (ticket t) = ⊥
Packable timestamp = ⊤
Packable unit = ⊤

Big-map-value : Type → Set
Big-map-value address = ⊤
Big-map-value (big-map t₁ t₂) = ⊥
Big-map-value bls12-381-fr = ⊤
Big-map-value bls12-381-g1 = ⊤
Big-map-value bls12-381-g2 = ⊤
Big-map-value bool = ⊤
Big-map-value bytes = ⊤
Big-map-value chain-id = ⊤
Big-map-value (contract t) = ⊥
Big-map-value int = ⊤
Big-map-value key = ⊤
Big-map-value key-hash = ⊤
Big-map-value (lambda t₁ t₂) = ⊤
Big-map-value (list t) = ⊤
Big-map-value (map t₁ t₂) = ⊤
Big-map-value mutez = ⊤
Big-map-value nat = ⊤
Big-map-value never = ⊤
Big-map-value operation = ⊥
Big-map-value (option t) = Big-map-value t
Big-map-value (or t₁ t₂) = Big-map-value t₁ × Big-map-value t₂
Big-map-value (pair t₁ t₂) = Big-map-value t₁ × Big-map-value t₂
Big-map-value (sapling-state x) = ⊥
Big-map-value (sapling-transation x) = ⊤
Big-map-value (set t) = ⊤
Big-map-value signature = ⊤
Big-map-value string = ⊤
Big-map-value (ticket t) = ⊤
Big-map-value timestamp = ⊤
Big-map-value unit = ⊤

Duplicable : Type → Set
Duplicable address = ⊤
Duplicable (big-map t₁ t₂) = ⊤
Duplicable bls12-381-fr = ⊤
Duplicable bls12-381-g1 = ⊤
Duplicable bls12-381-g2 = ⊤
Duplicable bool = ⊤
Duplicable bytes = ⊤
Duplicable chain-id = ⊤
Duplicable (contract t) = ⊤
Duplicable int = ⊤
Duplicable key = ⊤
Duplicable key-hash = ⊤
Duplicable (lambda t₁ t₂) = ⊤
Duplicable (list t) = ⊤
Duplicable (map t₁ t₂) = ⊤
Duplicable mutez = ⊤
Duplicable nat = ⊤
Duplicable never = ⊤
Duplicable operation = ⊥
Duplicable (option t) = Duplicable t
Duplicable (or t₁ t₂) = Duplicable t₁ × Duplicable t₂
Duplicable (pair t₁ t₂) = Duplicable t₁ × Duplicable t₂
Duplicable (sapling-state x) = ⊤
Duplicable (sapling-transation x) = ⊤
Duplicable (set t) = ⊤
Duplicable signature = ⊤
Duplicable string = ⊤
Duplicable (ticket t) = ⊥
Duplicable timestamp = ⊤
Duplicable unit = ⊤


data Instruction : Set where
  -- control structures
  APPLY EXEC FAILWITH : Instruction
  IF IF-CONS IF-LEFT IF-NONE : List Instruction → List Instruction → Instruction
  ITER ITER′ : List Instruction → Instruction
  LAMBDA LAMBDA-REC : Type → Type → List Instruction → Instruction
  LOOP LOOP-LEFT : List Instruction → Instruction
  -- stack manipulation
  DIG : ℕ → Instruction
  DIP : ℕ → List Instruction → Instruction
  DROP : ℕ → Instruction
  DUG : ℕ → Instruction
  DUP : ℕ → Instruction
  PUSH : (t : Type) → Literal t → Instruction
  SWAP : Instruction
  -- arithmetic operations
  ABS ADD COMPARE EDIV : Instruction
  EQ GE GT INT ISNAT LE LSL LSR LT : Instruction
  MUL NEG NEQ SUB : Instruction
  -- boolean operations
  AND NOT OR XOR : Instruction
  -- cryptographic operations
  -- ...
  -- blockchain operations
  ADDRESS AMOUNT BALANCE CHAIN-ID : Instruction
  CONTRACT : Type → Instruction
  CREATE-CONTRACT : (pty : Type) (sty : Type) (inss : List Instruction) → Instruction
  IMPLICIT-ACCOUNT LEVEL NOW SELF SELF-ADDRESS SENDER SET-DELEGATE SOURCE TOTAL-VOTING-POWER TRANSFER-TOKENS VOTING-POWER : Instruction
  -- operations on data structures
  CAR CDR CONCAT CONS : Instruction
  EMPTY-BIG-MAP EMPTY-MAP : Type → Type → Instruction
  EMPTY-SET : Type → Instruction
  GET : Instruction
  GET-N : ℕ → Instruction
  GET-AND-UPDATE : Instruction
  LEFT : Type → Instruction
  MAP MAP′ MAP″ : List Instruction → Instruction
  MEM NEVER : Instruction
  NIL NONE : Type → Instruction
  PACK : Instruction
  PAIR : ℕ → Instruction
  RIGHT SIZE SLICE SOME UNIT : Instruction
  UNPAIR : ℕ → Instruction
  UPDATE : Instruction
  UPDATE-N : ℕ → Instruction

data NotImplemented : Set where

record Address : Set where
  field
    rep : String

_≟A_ : (a₁ a₂ : Address) → Dec (a₁ ≡ a₂)
a₁ ≟A a₂
  with Address.rep a₁ ≟S Address.rep a₂
... | no ¬p = no (λ{ refl → ¬p refl})
... | yes refl = yes refl

record ChainId : Set where
  field
    rep : ℕ

record Contract (ty : Type) : Set where
  field
    rep : Address

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

record Code : Set where
  field
    paramty : Type
    storety : Type
    body    : List Instruction

data Operation : Set

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

-- Operation is not strictly positive because of the back reference to T⟦_⟧
-- however, ¬ Passable Operation, so that the potentially cyclic case runs empty
data Operation where
  CREATE-CONTRACT : Address → (pty : Type) (sty : Type) → List Instruction → Operation
  SET-DELEGATE    : Address → Maybe KeyHash → Operation
  TRANSFER-TOKENS : (ty : Type) → Passable ty → T⟦ ty ⟧ → Mutez → Contract ty → Operation

L⟦_⟧ : Literal t → T⟦ t ⟧
L⟦ L-nat x ⟧ = x
L⟦ L-bool x ⟧ = x
L⟦ L-int x ⟧ = x
L⟦ L-unit ⟧ = tt
L⟦ L-list x ⟧ = mapᴸ L⟦_⟧ x
L⟦ L-pair (x₁ , x₂) ⟧ = L⟦ x₁ ⟧ , L⟦ x₂ ⟧
L⟦ L-or x ⟧ = map⁺ L⟦_⟧ L⟦_⟧ x
L⟦ L-maybe x ⟧ = mapᴹ L⟦_⟧ x

