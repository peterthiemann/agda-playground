module Michelson.Instructions where

open import Data.Bool using (Bool; true; false; _∧_) renaming (_≟_ to _≟ᴮ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; reverse) renaming (map to mapᴸ)
open import Data.Unit using (⊤; tt)

open import Data.Product using (Σ; proj₁; proj₂; _,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

open import Data.Nat using (ℕ; _+_; _≤_) renaming (_≟_ to _≟ᴺ_)
open import Data.Integer using (ℤ; ∣_∣; +_) renaming (_≟_ to _≟ℤ_; _+_ to _+ℤ_)
open import Data.String using (String) renaming (_≟_ to _≟S_)

open import Michelson.Types

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

  ⊢PUSH₁ : ∀ {x} {pushable : Pushable ty} → (PUSH ty x) / tys ⇒ (ty ∷ tys)

data _//_⇒_ : List Instruction → Typing where
  []  : [] // tys ⇒ tys
  _∷_ : ∀ {ins inss} {tys₁ tys₂ tys₃}
    → ins / tys₁ ⇒ tys₂
    → inss // tys₂ ⇒ tys₃
    → (ins ∷ inss) // tys₁ ⇒ tys₃

prg₁ : List Instruction
prg₁ = PUSH nat (L-nat 40) ∷ PUSH nat (L-nat 2) ∷ ADD ∷ []

⊢prg₁ : prg₁ // tys ⇒ (nat ∷ tys)
⊢prg₁ = ⊢PUSH₁ ∷ (⊢PUSH₁ ∷ (⊢ADD₁ ∷ []))

prg₂ : List Instruction
prg₂ = PUSH nat (L-nat 40) ∷ PUSH nat (L-nat 2) ∷ COMPARE ∷ []

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
compare {address} comp v₁ v₂ = ⌊ Address.rep v₁ ≟S Address.rep v₂ ⌋
compare {bool} comp v₁ v₂ = ⌊ v₁ ≟ᴮ v₂ ⌋
compare {chain-id} comp v₁ v₂ = ⌊ ChainId.rep v₁ ≟ᴺ ChainId.rep v₂ ⌋
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
  ts₁ ts₂ : Timestamp

SingleStep : Set₁
SingleStep = List Typed → Typed → Set

data _/_↓_ : Instruction → SingleStep where
  ⊢ABS₁  : ABS / [_]   (int , z₁)           ↓ (nat , ∣ z₁ ∣)
  ⊢ADD₁  : ADD / [_,_] (nat , n₁) (nat , n₂) ↓ (nat , n₁ + n₂)
  ⊢ADD₂  : ADD / [_,_] (nat , n₁) (int , z₂) ↓ (int , (+ n₁) +ℤ z₂ )
  ⊢ADD₃  : ADD / [_,_] (int , z₁) (nat , n₂) ↓ (int , z₁ +ℤ (+ n₂))
  ⊢ADD₄  : ADD / [_,_] (int , z₁) (int , z₂) ↓ (int , z₁ +ℤ z₂)
  ⊢ADD₅  : ADD / [_,_] (timestamp , ts₁) (int , z₂) ↓ (timestamp , record { instant = Timestamp.instant ts₁ +ℤ z₂ })
  ⊢ADD₆  : ADD / [_,_] (int , z₁) (timestamp , ts₂) ↓ (timestamp , record { instant = z₁ +ℤ Timestamp.instant ts₂ })
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

  ⊢PUSH₁ : ∀ {l} {pushable : Pushable ty} → PUSH ty l / tyds ↝ ((ty , L⟦ l ⟧) ∷ tyds)
  
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
single-stepping-is-typed (⊢PUSH₁ {pushable = pushable}) = ⊢PUSH₁ {pushable = pushable}

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

record ContractInvocationState : Set where
  field
    self-address : Address
    amount : Mutez
    balance : Mutez
    chainId : ChainId
    active-contracts : List (Address × Type)
    level : ℕ
    now : Timestamp
    myty : Type
    self : Contract myty
    sender : Address
    source : Address
    total-voting-power : ℕ
    voting-power : KeyHash → ℕ

getContract  : ContractInvocationState → Address → (ty : Type) → Maybe (Contract ty)
getContract cs addr ty = lookup (ContractInvocationState.active-contracts cs)
  where
    lookup : List (Address × Type) → Maybe (Contract ty)
    lookup [] = nothing
    lookup ((my-addr , my-type) ∷ active)
      with my-addr ≟A addr
    ... | yes refl = just (record { rep = my-addr })
    ... | no addr≢ = lookup active

postulate
  freshAddress : ContractInvocationState → Type → Address × ContractInvocationState

CS-consistent : ContractInvocationState → Set
CS-consistent cs = getContract cs (ContractInvocationState.self-address cs) (ContractInvocationState.myty cs) ≡ just (record { rep = ContractInvocationState.self-address cs })

variable
  cs cs′ : ContractInvocationState
  a  : Address
  kh : KeyHash
  mkh : Maybe KeyHash
  m  : Mutez

data _/_↓_/_↝_ : Instruction → List Typed → List Typed → ContractInvocationState → ContractInvocationState → Set where
  ⊨SELF-ADDRESS    : SELF-ADDRESS / [] ↓ [(address , ContractInvocationState.self-address cs)] / cs ↝ cs
  ⊨AMOUNT          : AMOUNT       / [] ↓ [(mutez ,   ContractInvocationState.amount cs)] / cs ↝ cs
  ⊨BALANCE         : BALANCE      / [] ↓ [(mutez ,   ContractInvocationState.balance cs)] / cs ↝ cs
  ⊨CHAIN-ID        : CHAIN-ID     / [] ↓ [(chain-id , ContractInvocationState.chainId cs)] / cs ↝ cs
  ⊨CONTRACT        : CONTRACT ty  / [(address , a)] ↓ [(option (contract ty) , getContract cs a ty)] / cs ↝ cs
  ⊨LEVEL           : LEVEL        / [] ↓ [(nat , ContractInvocationState.level cs)] / cs ↝ cs
  ⊨SELF            : SELF         / [] ↓ [(contract (ContractInvocationState.myty cs) , ContractInvocationState.self cs)] / cs ↝ cs
  ⊨CREATE-CONTRACT : ∀ {pty sty inss v} → freshAddress cs pty ≡ (a , cs′) →
     CREATE-CONTRACT pty sty inss / [_,_,_] (option key-hash , mkh) (mutez , m) (sty , v) ↓ [_,_] (operation , CREATE-CONTRACT a pty sty inss) (address , a) / cs ↝ cs′
  ⊨SET-DELEGATE    : SET-DELEGATE / [(option key-hash , mkh)] ↓ [(operation , SET-DELEGATE (ContractInvocationState.self-address cs) mkh)] / cs ↝ cs
  ⊨TRANSFER-TOKENS : ∀ {v cty} → (passable-ty : Passable ty) →
                  TRANSFER-TOKENS / [_,_,_] (ty , v) (mutez , m) (contract ty , cty) ↓ [(operation , TRANSFER-TOKENS ty passable-ty v m cty)] / cs ↝ cs
  ⊨TOTAL-VOTING-POWER :
               TOTAL-VOTING-POWER / [] ↓ [(nat , ContractInvocationState.total-voting-power cs)] / cs ↝ cs
  ⊨VOTING-POWER    : VOTING-POWER / [(key-hash , kh)] ↓ [(nat , ContractInvocationState.voting-power cs kh)] / cs ↝ cs

module example-blockchain-instructions where

  contract-sender : Address
  contract-sender = record { rep = "yz9F023030" }

  contract-address : Address
  contract-address = record { rep = "tzBCx78efg" }

  contract-type : Type
  contract-type = mutez

  contract-state : ContractInvocationState
  contract-state = record
                     { amount = record { amount = 100 }
                     ; balance = record { amount = 1234 }
                     ; chainId = record { rep = 4711 }
                     ; active-contracts = [ (contract-address , contract-type) ]
                     ; level = 106371
                     ; now = record { instant = + 84600 }
                     ; myty = contract-type
                     ; self = record { rep = contract-address }
                     ; self-address = contract-address
                     ; sender = contract-sender
                     ; source = contract-sender
                     ; total-voting-power = 128000
                     ; voting-power = λ x → 128
                     }

  contract-state-consistent : CS-consistent contract-state
  contract-state-consistent = refl

-- global block chain stuff

record ContractState : Set where
  field
    balance : Mutez
    param-ty store-ty : Type
    {valid-store-ty} : Storable store-ty
    store : T⟦ store-ty ⟧
    instructions : List Instruction

record BlockchainState : Set where
  field
    contracts : List (Address × ContractState)
    delegates : Address → Maybe KeyHash

chain : {A B : Set} → ((x y : A) → Dec (x ≡ y)) → A → Maybe B → (A → Maybe B) → (A → Maybe B)
chain _≟_ a mb f x
  with x ≟ a
... | yes refl = mb
... | no  x≢a  = f a

variable
  bcs : BlockchainState
  ops : List Operation

getContractFromChain : BlockchainState → Address → (ty : Type) → Maybe ContractState
getContractFromChain bcs addr ty = lookup (BlockchainState.contracts bcs)
  where
    lookup : List (Address × ContractState) → Maybe ContractState
    lookup [] = nothing
    lookup ((my-addr , my-contract-state) ∷ active)
      with my-addr ≟A addr
    ... | yes refl = just my-contract-state
    ... | no addr≢ = lookup active

-- this may be better as a function
-- toplevel : Gas → List Operation → BlockchainState → Maybe BlockchainState

data _||_↝_ : List Operation → BlockchainState → BlockchainState → Set where
  [] : [] || bcs ↝ bcs
  ⊨CREATE-CONTRACT : ∀ {pty sty}
    → (CREATE-CONTRACT a pty sty inss ∷ ops) || bcs ↝ {!!}
  ⊨TRANSFER-TOKENS : ∀ {passable-ty : Passable ty}{v}{cty}{cstate}
    → getContractFromChain bcs (Contract.rep cty) ty ≡ just cstate
    → Mutez.amount m ≤ Mutez.amount (ContractState.balance cstate)
    → (TRANSFER-TOKENS ty passable-ty v m cty ∷ ops) || bcs ↝ record { contracts = {!!}
                                                                     ; delegates = BlockchainState.delegates bcs } 
  ⊨SET-DELEGATE : ∀ {mkh}
    → (SET-DELEGATE a mkh ∷ ops) || bcs ↝ record { contracts = BlockchainState.contracts bcs
                                                 ; delegates = chain _≟A_ a mkh (BlockchainState.delegates bcs) }
