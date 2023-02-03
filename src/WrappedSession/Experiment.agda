{-# OPTIONS --guardedness #-} {- required for IO -}
module WrappedSession.Experiment where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Unit using (⊤; tt)

open import Function.Base using (case_of_)

open import IO

data Type : Set where
  nat : Type

data Session : Set where
  select choice : Session → Session → Session
  send recv : Type → Session → Session
  end : Session

-- service protocol for a binary function
binaryp : Session
binaryp = (recv nat (recv nat (send nat end)))

-- service protocol for a unary function
unaryp : Session 
unaryp = (recv nat (send nat end))

-- service protocol for choosing between a binary and a unary function
arithp : Session
arithp = choice binaryp unaryp

variable
  A A′ A″ A₁ A₂ : Set
  t : Type
  s s₁ s₂ : Session

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ

data Commands (A : Set) : Session → Set₁ where
  END    : Commands A end
  SEND   : (A → T⟦ t ⟧ × A) → Commands A s → Commands A (send t s)
  RECV   : (T⟦ t ⟧ → A → A) → Commands A s → Commands A (recv t s)
  SELECT : (A → Bool × A) → Commands A s₁ → Commands A s₂ → Commands A (select s₁ s₂)
  CHOICE : (Bool → A → ⊤ × A) → Commands A s₁ → Commands A s₂ → Commands A (choice s₁ s₂)

record Accepting A s : Set₁ where
  constructor ACC
  field pgm : Commands A s

addp-command : Commands ℕ binaryp
addp-command = RECV (λ x z → x + z)
               (RECV (λ x z → x + z)
               (SEND (λ x → x , 0)
               END))

postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO ⊤
  primSend : A → Channel → IO ⊤
  primRecv : Channel → IO A

executor : {s : Session} → Commands A s → (init : A) → Channel → IO A
executor END state ch = do
  primClose ch
  return state
executor (SEND getx cmd) state ch = do
  let (x , state′) = getx state
  primSend x ch
  executor cmd state′ ch
executor (RECV putx cmd) state ch = do
  x ← primRecv ch
  let state′ = putx x state
  executor cmd state′ ch
executor (SELECT getx cmd₁ cmd₂) state ch = do
  let (x , state′) = getx state
  primSend x ch
  (case x of (λ{ false → executor cmd₁ state′ ch ; true → executor cmd₂ state′ ch}))
executor (CHOICE putx cmd₁ cmd₂) state ch = do
  x ← primRecv ch
  let (_ , state′) = putx x state
  (case x of (λ{ false → executor cmd₁ state′ ch ; true → executor cmd₂ state′ ch}))

acceptor : Accepting A s → A → IO A
acceptor (ACC pgm) a = primAccept >>= executor pgm a

----------------------------------------------------------------------
-- a Σ type isomorphic to A₁ ⊎ A₂

ifb : Set → Set → Bool → Set
ifb A₁ A₂ false = A₁
ifb A₁ A₂ true = A₂

zzfalse : Σ _ (ifb Bool ℕ)
zzfalse = false , false

zztrue :  Σ _ (ifb Bool ℕ)
zztrue =  true , 42

fffun  : (x : Bool) → ifb Bool ℕ x
fffun false = false
fffun true = 42

ΣB : Set → Set → Set
ΣB A₁ A₂ = Σ _ (ifb A₁ A₂)


data Commands′ (A : Set) : Set → Session → Set₁ where
  END    : Commands′ A A end
  SEND   : (A → T⟦ t ⟧ × A′) → Commands′ A′ A″ s → Commands′ A A″ (send t s)
  RECV   : (T⟦ t ⟧ → A → A′) → Commands′ A′ A″ s → Commands′ A A″ (recv t s)
  SELECT1 : (A → A₁ ⊎ A₂) → Commands′ A₁ A″ s₁ → Commands′ A₂ A″ s₂ → Commands′ A A″ (select s₁ s₂)
  CHOICE1 : ((x : Bool) → A → (case x of λ{false → A₁; true → A₂})) → Commands′ A₁ A″ s₁ → Commands′ A₂ A″ s₂ → Commands′ A A″ (choice s₁ s₂)

  SELECT2 : (A → ΣB A₁ A₂) → Commands′ A₁ A″ s₁ → Commands′ A₂ A″ s₂ → Commands′ A A″ (select s₁ s₂)

executor′ : {s : Session} → Commands′ A A″ s → (init : A) → Channel → IO A″
executor′ END state ch = do
  primClose ch
  return state
executor′ (SEND getx cmd) state ch = do
  let (x , state′) = getx state
  primSend x ch
  executor′ cmd state′ ch
executor′ (RECV putx cmd) state ch = do
  x ← primRecv ch
  let state′ = putx x state
  executor′ cmd state′ ch
executor′ (SELECT1 getx cmd₁ cmd₂) state ch
  with getx state
... | inj₁ state₁ = do
      primSend true ch
      executor′ cmd₁ state₁ ch
... | inj₂ state₂ = do
      primSend false ch
      executor′ cmd₂ state₂ ch
executor′ (CHOICE1 putx cmd₁ cmd₂) state ch = do
  false ← primRecv{A = Bool} ch
    where
      true → do
        let state′ = putx true state
        executor′ cmd₂ state′ ch
  let state′ = putx false state
  executor′ cmd₁ state′ ch
executor′ (SELECT2 getx cmd₁ cmd₂) state ch = do
  let bst = getx state
  primSend (proj₁ bst) ch
  (false , state₁) ← return bst
    where
      (true , state₂) → executor′ cmd₂ state₂ ch
  executor′ cmd₁ state₁ ch

