{-# OPTIONS --guardedness #-} {- required for IO -}
module WrappedSession.ContextFree where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Unit using (⊤; tt)

-- stdlib 2.0!
open import Effect.Monad.State using (State; RawMonadState)
open RawMonadState


open import Function.Base using (case_of_; _∘_; const; id)

open import IO

variable A : Set


postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO ⊤
  primSend : A → Channel → IO ⊤
  primRecv : Channel → IO A


data Type : Set where
  nat : Type

variable t : Type

infixr 30 _⨟_

data Session : Set where
  select choice _⨟_ : Session → Session → Session
  send recv : Type → Session
  skip : Session

variable s s₁ s₂ : Session

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ

data Cmd (A : Set) : Session → Set where
  SKIP    : Cmd A skip
  SEND   : (A → T⟦ t ⟧ × A) → Cmd A (send t)
  RECV   : (T⟦ t ⟧ → A → A) → Cmd A (recv t)
  SELECT : (A → Bool × A) → ((b : Bool) → if b then Cmd A s₁ else Cmd A s₂) → Cmd A (select s₁ s₂)
  CHOICE : ((b : Bool) → A → (if b then Cmd A s₁ else Cmd A s₂) × A) → Cmd A (choice s₁ s₂)
  _⨟_    : Cmd A s₁ → Cmd A s₂ → Cmd A (s₁ ⨟ s₂)

exec : {s : Session} → Cmd A s → A → Channel → IO A
exec SKIP a ch = pure a
exec (SEND getx) a ch = do
  let (v , a′) = getx a
  primSend v ch
  pure a′
exec (RECV putx) a ch = do
  v ← primRecv ch
  let a′ = putx v a
  pure a′
exec (SELECT f cont) a ch with f a 
... | false , a′ = exec (cont false) a′ ch
... | true , a′  = exec (cont true) a′ ch
exec (CHOICE cont) a ch = do
  false ← primRecv{Bool} ch
    where
      true → let (cmd , a′) = cont true a in exec cmd a′ ch
  let (cmd , a′) = cont false a in exec cmd a′ ch
exec (cmd₁ ⨟ cmd₂) a ch = do
  a′ ← exec cmd₁ a ch
  exec cmd₂ a′ ch

accept : Cmd A s → A → IO A
accept cmd a = do
  ch ← primAccept
  a′ ← exec cmd a ch
  primClose ch
  pure a′

----------------------------------------------------------------------

-- service protocol for a unary function
unaryp : Session 
unaryp = recv nat ⨟ send nat

unary-server : Cmd ℕ unaryp
unary-server = RECV const ⨟ SEND (λ x → x , x)
