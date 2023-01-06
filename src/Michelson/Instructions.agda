module Michelson.Instructions where

open import Data.Bool using (Bool; true; false; _∧_) renaming (_≟_ to _≟ᴮ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; reverse) renaming (map to mapᴸ)
open import Data.Unit using (⊤; tt)

open import Data.Product using (Σ; proj₁; proj₂; _,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []

open import Data.Nat using (ℕ; _+_) renaming (_≟_ to _≟ᴺ_)
open import Data.Integer using (ℤ; ∣_∣; +_) renaming (_≟_ to _≟ℤ_; _+_ to _+ℤ_)
open import Data.String using (String) renaming (_≟_ to _≟S_)

open import Michelson.Types

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
  PUSH : (t : Type) → T⟦ t ⟧ → Instruction
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
  -- ...
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

variable
  ty : Type
  tys : List Type

Typing : Set₁
Typing = List Type → List Type → Set

data _/_⇒_ : Instruction → Typing where
  ⊢ABS₁  : ABS / (int ∷ tys) ⇒ (nat ∷ tys)
  ⊢ADD₁  : ADD / (nat ∷ nat ∷ tys) ⇒ (nat ∷ tys)
  ⊢ADD₂  : ADD / (nat ∷ int ∷ tys) ⇒ (int ∷ tys)
  ⊢ADD₃  : ADD / (int ∷ nat ∷ tys) ⇒ (int ∷ tys)
  ⊢ADD₄  : ADD / (int ∷ int ∷ tys) ⇒ (int ∷ tys)
  ⊢ADD₅  : ADD / (timestamp ∷ int ∷ tys) ⇒ (timestamp ∷ tys)
  ⊢ADD₆  : ADD / (int ∷ timestamp ∷ tys) ⇒ (timestamp ∷ tys)
  ⊢ADD₇  : ADD / (mutez ∷ mutez ∷ tys) ⇒ (mutez ∷ tys)
  ⊢ADD₈  : ADD / (bls12-381-g1 ∷ bls12-381-g1 ∷ tys) ⇒ (bls12-381-g1 ∷ tys)
  ⊢ADD₉  : ADD / (bls12-381-g2 ∷ bls12-381-g2 ∷ tys) ⇒ (bls12-381-g2 ∷ tys)
  ⊢ADD₁₀ : ADD / (bls12-381-fr ∷ bls12-381-fr ∷ tys) ⇒ (bls12-381-fr ∷ tys)
  ⊢COMPARE₁ : (cty : Type) → Comparable cty → COMPARE / (cty ∷ cty ∷ tys) ⇒ (bool ∷ tys)

  ⊢PUSH₁ : ∀ {x} → (PUSH ty x) / tys ⇒ (ty ∷ tys)

data _//_⇒_ : List Instruction → Typing where
  []  : [] // tys ⇒ tys
  _∷_ : ∀ {ins inss} {tys₁ tys₂ tys₃}
    → ins / tys₁ ⇒ tys₂
    → inss // tys₂ ⇒ tys₃
    → (ins ∷ inss) // tys₁ ⇒ tys₃

prg₁ : List Instruction
prg₁ = PUSH nat 40 ∷ PUSH nat 2 ∷ ADD ∷ []

⊢prg₁ : prg₁ // tys ⇒ (nat ∷ tys)
⊢prg₁ = ⊢PUSH₁ ∷ (⊢PUSH₁ ∷ (⊢ADD₁ ∷ []))

prg₂ : List Instruction
prg₂ = PUSH nat 40 ∷ PUSH nat 2 ∷ COMPARE ∷ []

⊢prg₂ : prg₂ // tys ⇒ (bool ∷ tys)
⊢prg₂ = ⊢PUSH₁ ∷ (⊢PUSH₁ ∷ (⊢COMPARE₁ nat tt ∷ []))
  
-- execution

Typed : Set
Typed = Σ Type T⟦_⟧

∥_∥ : Typed → Type
∥_∥ = proj₁

∥_∥* : List Typed → List Type
∥_∥* = mapᴸ ∥_∥


compare : ∀ {cty} → Comparable cty → T⟦ cty ⟧ → T⟦ cty ⟧ → Bool
compare {address} comp v₁ v₂ = {!!}
compare {bool} comp v₁ v₂ = ⌊ v₁ ≟ᴮ v₂ ⌋
compare {chain-id} comp v₁ v₂ = {!!}
compare {int} comp v₁ v₂ = ⌊ v₁ ≟ℤ v₂ ⌋
compare {key-hash} comp v₁ v₂ = ⌊ KeyHash.hashcode v₁ ≟S KeyHash.hashcode v₂ ⌋
compare {mutez} comp v₁ v₂ = ⌊ Mutez.amount v₁ ≟ᴺ Mutez.amount v₂ ⌋
compare {nat} comp v₁ v₂ = ⌊ v₁ ≟ᴺ v₂ ⌋
compare {option cty} comp (just v₁) (just v₂) = compare comp v₁ v₂
compare {option cty} comp (just x) nothing = false
compare {option cty} comp nothing (just x) = false
compare {option cty} comp nothing nothing = true
compare {or cty cty₁} (comp₁ , comp₂) (inj₁ x₁) (inj₁ x₂) = compare comp₁ x₁ x₂
compare {or cty cty₁} comp (inj₁ x) (inj₂ y) = false
compare {or cty cty₁} comp (inj₂ y) (inj₁ x) = false
compare {or cty cty₁} (comp₁ , comp₂) (inj₂ y₁) (inj₂ y₂) = compare comp₂ y₁ y₂
compare {pair cty cty₁} (comp₁ , comp₂) v₁ v₂ = compare comp₁ (proj₁ v₁) (proj₁ v₂) ∧ compare comp₂ (proj₂ v₁) (proj₂ v₂)
compare {string} comp v₁ v₂ = ⌊ v₁ ≟S v₂ ⌋
compare {timestamp} comp v₁ v₂ = ⌊ Timestamp.instant v₁ ≟ℤ Timestamp.instant v₂ ⌋
compare {unit} comp v₁ v₂ = true

Stepping : Set₁
Stepping = List Typed → List Typed → Set

variable
  tyds  : List Typed
  n₁ n₂ : ℕ
  z₁ z₂ : ℤ
  m₁ m₂ : Mutez
  t₁ t₂ : Timestamp

SingleStep : Set₁
SingleStep = List Typed → Typed → Set

data _/_↓_ : Instruction → SingleStep where
  ⊢ABS₁  : ABS / [_]   (int , z₁)           ↓ (nat , ∣ z₁ ∣)
  ⊢ADD₁  : ADD / [_,_] (nat , n₁) (nat , n₂) ↓ (nat , n₁ + n₂)
  ⊢ADD₂  : ADD / [_,_] (nat , n₁) (int , z₂) ↓ (int , (+ n₁) +ℤ z₂ )
  ⊢ADD₃  : ADD / [_,_] (int , z₁) (nat , n₂) ↓ (int , z₁ +ℤ (+ n₂))
  ⊢ADD₄  : ADD / [_,_] (int , z₁) (int , z₂) ↓ (int , z₁ +ℤ z₂)
  ⊢ADD₅  : ADD / [_,_] (timestamp , t₁) (int , z₂) ↓ (timestamp , record { instant = Timestamp.instant t₁ +ℤ z₂ })
  ⊢ADD₆  : ADD / [_,_] (int , z₁) (timestamp , t₂) ↓ (timestamp , record { instant = z₁ +ℤ Timestamp.instant t₂ })
  ⊢ADD₇  : ADD / [_,_] (mutez , m₁) (mutez , m₂) ↓ (mutez , record { amount = Mutez.amount m₁ + Mutez.amount m₂ })


data _/_↝_ : Instruction → Stepping where
  single : ∀ {tyds : List Typed} {ins ts-in t-out}
    → ins / ts-in ↓ t-out
    → ins / ts-in ++ tyds ↝ (t-out ∷ tyds)
  -- ⊢ADD₈  : ADD / (bls12-381-g1 ∷ bls12-381-g1 ∷ tys) ⇒ (bls12-381-g1 ∷ tys)
  -- ⊢ADD₉  : ADD / (bls12-381-g2 ∷ bls12-381-g2 ∷ tys) ⇒ (bls12-381-g2 ∷ tys)
  -- ⊢ADD₁₀ : ADD / (bls12-381-fr ∷ bls12-381-fr ∷ tys) ⇒ (bls12-381-fr ∷ tys)
  ⊢COMPARE₁ : (cty : Type) → {v₁ v₂ : T⟦ cty ⟧} → (comp : Comparable cty)
    → COMPARE / ((cty , v₁) ∷ (cty , v₂) ∷ tyds) ↝ ((bool , compare comp v₁ v₂) ∷ tyds)

  ⊢PUSH₁ : ∀ {x} → (PUSH ty x) / tyds ↝ ((ty , x) ∷ tyds)
  
data _//_↝_ : List Instruction → Stepping where
  []  : [] // tyds ↝ tyds
  _∷_ : ∀ {ins inss} {tyds₁ tyds₂ tyds₃}
    → ins / tyds₁ ↝ tyds₂
    → inss // tyds₂ ↝ tyds₃
    → (ins ∷ inss) // tyds₁ ↝ tyds₃

⊨prg₁ : prg₁ // tyds ↝ ((nat , 42) ∷ tyds)
⊨prg₁ = ⊢PUSH₁ ∷ (⊢PUSH₁ ∷ (single ⊢ADD₁ ∷ []))

⊨prg₂ : prg₂ // tyds ↝ ((bool , false) ∷ tyds)
⊨prg₂ = ⊢PUSH₁ ∷ (⊢PUSH₁ ∷ (⊢COMPARE₁ nat tt ∷ []))


single-stepping-is-typed : ∀ {ins tyds-in tyds-out}
  → ins / tyds-in ↝ tyds-out
  → ins / ∥ tyds-in ∥* ⇒ ∥ tyds-out ∥*
single-stepping-is-typed (single ⊢ABS₁) = ⊢ABS₁
single-stepping-is-typed (single ⊢ADD₁) = ⊢ADD₁
single-stepping-is-typed (single ⊢ADD₂) = ⊢ADD₂
single-stepping-is-typed (single ⊢ADD₃) = ⊢ADD₃
single-stepping-is-typed (single ⊢ADD₄) = ⊢ADD₄
single-stepping-is-typed (single ⊢ADD₅) = ⊢ADD₅
single-stepping-is-typed (single ⊢ADD₆) = ⊢ADD₆
single-stepping-is-typed (single ⊢ADD₇) = ⊢ADD₇
single-stepping-is-typed (⊢COMPARE₁ cty comp) = ⊢COMPARE₁ cty comp
single-stepping-is-typed ⊢PUSH₁ = ⊢PUSH₁

stepping-is-typed : ∀ {inss tyds-in tyds-out}
  → inss // tyds-in ↝ tyds-out
  → inss // ∥ tyds-in ∥* ⇒ ∥ tyds-out ∥*
stepping-is-typed [] = []
stepping-is-typed (single-step ∷ stepping) = single-stepping-is-typed single-step ∷ stepping-is-typed stepping


-- configuration

record Configuration : Set where
  constructor ⟪_,_,_⟫
  field
    prg : List Instruction
    stk : List Typed
    shadow-stk : List Typed

variable
  ins : Instruction
  inss : List Instruction
  shadow : List Typed

data conf-step : Configuration → Configuration → Set where
  simple : ∀ {ins tyds-in tyds-out}
    → ins / tyds-in ↝ tyds-out
    → conf-step ⟪ ins ∷ inss , tyds-in , shadow ⟫ ⟪ inss , tyds-out , shadow ⟫

  ⊢ITER₁ : ∀ {inss-body xs} → conf-step ⟪ ITER inss-body ∷ inss , (list ty , xs) ∷ tyds , shadow ⟫
                                        ⟪ ITER′ inss-body ∷ inss , tyds , (list ty , xs) ∷ shadow ⟫
  ⊢ITER₂ : ∀ {inss-body}
    → conf-step ⟪ ITER′ inss-body ∷ inss , tyds , (list ty , []) ∷ shadow ⟫
                ⟪                   inss , tyds ,                  shadow ⟫
  ⊢ITER₃ : ∀ {inss-body x xs}
    → conf-step ⟪              ITER′ inss-body ∷ inss ,            tyds , (list ty , x ∷ xs) ∷ shadow ⟫
                ⟪ inss-body ++ ITER′ inss-body ∷ inss , (ty , x) ∷ tyds , (list ty ,     xs) ∷ shadow ⟫

  ⊢MAP₁  : ∀ {inss-body xs ty-out}
    → conf-step ⟪ MAP inss-body ∷ inss , (list ty , xs) ∷ tyds , shadow ⟫
                ⟪ MAP′ inss-body ∷ inss , tyds , (list ty-out , []) ∷ (list ty , xs) ∷ shadow ⟫

  ⊢MAP₂  : ∀ {inss-body ty-out ys}
    → conf-step ⟪ MAP′ inss-body ∷ inss ,                              tyds , (list ty-out , ys) ∷ (list ty , []) ∷ shadow ⟫
                ⟪                  inss , (list ty-out , reverse ys) ∷ tyds ,                                       shadow ⟫

  ⊢MAP₃  : ∀ {inss-body ty-out ys x xs}
    → conf-step ⟪ MAP′ inss-body ∷ inss ,                              tyds , (list ty-out , ys) ∷ (list ty , x ∷ xs) ∷ shadow ⟫
                ⟪ inss-body ++ MAP″ inss-body ∷ inss ,       (ty , x) ∷ tyds , (list ty-out , ys) ∷ (list ty ,     xs) ∷ shadow ⟫

  ⊢MAP₄  : ∀ {inss-body ty-out y ys xs}
    → conf-step ⟪ MAP″ inss-body ∷ inss ,               (ty-out , y) ∷ tyds , (list ty-out ,     ys) ∷ (list ty , xs) ∷ shadow ⟫
                ⟪ MAP′ inss-body ∷ inss ,                              tyds , (list ty-out , y ∷ ys) ∷ (list ty , xs) ∷ shadow ⟫

-- block chain stuff for a single contract

record ContractState (ty : Type) : Set where
  field
    amount : Mutez
    balance : Mutez
    chainId : ChainId
    active-contracts : List (Address × (∃[ ty ] Contract ty))
    level : ℕ
    now : Timestamp
    self : Contract ty
    self-address : Address
    sender : Address
    source : Address
    total-voting-power : ℕ
    voting-power : KeyHash → ℕ

postulate
  getContract  : ContractState ty → Address → Maybe (∃[ ty ] Contract ty)
  freshAddress : ContractState ty → Address × ContractState ty


{-
data ⊢ADD : Typing where
  ⊢ADD₁  : ⊢ADD [ nat , nat ] [ nat ]
  ⊢ADD₂  : ⊢ADD [ nat , int ] [ int ]
  ⊢ADD₃  : ⊢ADD [ int , nat ] [ int ]
  ⊢ADD₄  : ⊢ADD [ int , int ] [ int ]
  ⊢ADD₅  : ⊢ADD [ timestamp , int ] [ timestamp ]
  ⊢ADD₆  : ⊢ADD [ int , timestamp ] [ timestamp ]
  ⊢ADD₇  : ⊢ADD [ mutez , mutez ] [ mutez ]
  ⊢ADD₈  : ⊢ADD [ bls12-381-g1 , bls12-381-g1 ] [ bls12-381-g1 ]
  ⊢ADD₉  : ⊢ADD [ bls12-381-g2 , bls12-381-g2 ] [ bls12-381-g2 ]
  ⊢ADD₁₀ : ⊢ADD [ bls12-381-fr , bls12-381-fr ] [ bls12-381-fr ]

data ⊢COMPARE : Typing where
  ⊢COMPARE₁ : (cty : Type) → Comparable cty → ⊢COMPARE [ cty , cty ] [ bool ]

data ⊢EDIV : Typing where
  ⊢EDIV₁ : ⊢EDIV [ nat , nat ] [ option (pair nat nat) ]
  ⊢EDIV₂ : ⊢EDIV [ nat , int ] [ option (pair int nat) ]
  ⊢EDIV₃ : ⊢EDIV [ int , nat ] [ option (pair int nat) ]
  ⊢EDIV₄ : ⊢EDIV [ int , int ] [ option (pair int nat) ]
  ⊢EDIV₅ : ⊢EDIV [ mutez , nat ] [ option (pair mutez mutez) ]
  ⊢EDIV₆ : ⊢EDIV [ mutez , mutez ] [ option (pair nat mutez) ]

data ⊢EQ : Typing where
  ⊢EQ₁ : ⊢EQ [ int ] [ bool ]

data ⊢GE : Typing where
  ⊢GE₁ : ⊢GE [ int ] [ bool ]

data ⊢GT : Typing where
  ⊢GT₁ : ⊢GT [ int ] [ bool ]

data ⊢LE : Typing where
  ⊢LE₁ : ⊢LE [ int ] [ bool ]

data ⊢LT : Typing where
  ⊢LT₁ : ⊢LT [ int ] [ bool ]

-}
