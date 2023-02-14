{-# OPTIONS --guardedness #-} {- required for IO -}
open import Level using (Level) renaming (zero to lzero)

module WrappedSession.Monadic where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; _+_; 0ℤ; -_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- stdlib 2.0!
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Effect.Functor

open import Effect.Monad
open import Effect.Monad.State
open import Effect.Monad.Reader.Transformer as Reader
open import Effect.Monad.State.Transformer as State
open import Effect.Monad.IO

open import Effect.Monad.Reader.Instances
open import Effect.Monad.State.Instances
open import Effect.Monad.Identity.Instances
open import Effect.Monad.IO.Instances
open import IO.Instances

open RawMonad {{...}}
open RawMonadState {{...}}
open RawMonadReader {{...}}
open RawMonadIO {{...}}
open RawFunctor {{...}}

open import Function.Base using (case_of_; _∘_; _∘′_; const; id; _$_)

open import IO.Base using (IO)


postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO {lzero} ⊤
  primSend : ∀ {A : Set} → A → Channel → IO {lzero} ⊤
  primRecv : ∀ {A : Set} → Channel → IO A


data Type : Set where
  nat int bool : Type

data Session : Set where
  select chc : Session → Session → Session
  send recv : Type → Session → Session
  end : Session

-- service protocol for a binary function
binaryp : Session
binaryp = (recv int (recv int (send int end)))

-- service protocol for a unary function
unaryp : Session 
unaryp = (recv int (send int end))

-- service protocol for choosing between a binary and a unary function
arithp : Session
arithp = chc binaryp unaryp

variable
  a b : Level
  A A′ A″ A₁ A₂ : Set
  t : Type
  s s₁ s₂ : Session
  M : Set a → Set b

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ
T⟦ bool ⟧ = Bool
T⟦ int ⟧ = ℤ

M₀ = ReaderT Channel IO

data Command (A : Set) : Session → Set₁ where
  END    : Command A end
  SEND   : StateT A M₀ T⟦ t ⟧       → Command A s → Command A (send t s)
  RECV   : (T⟦ t ⟧ → StateT A M₀ ⊤) → Command A s → Command A (recv t s)
  SELECT : StateT A M₀ Bool         → Command A s₁ → Command A s₂ → Command A (select s₁ s₂)
  CHOICE : (Bool → StateT A M₀ ⊤)   → Command A s₁ → Command A s₂ → Command A (chc s₁ s₂)

  -- SENDM  : (∀ {M} → StateT A M T⟦ t ⟧) → Command A s → Command A (send t s)
  -- RECVM  : (T⟦ t ⟧ → ∀ {M} → StateT A M ⊤) → Command A s → Command A (recv t s)

record Accepting A s : Set₁ where
  constructor ACC
  field pgm : Command A s

addp-command : Command ℤ binaryp
addp-command = RECV put $ RECV (modify ∘′ _+_) $ SEND get $ END

negp-command : Command ℤ unaryp
negp-command = RECV (put ∘ -_) $ SEND get END

arithp-command : Command ℤ arithp
arithp-command = CHOICE (const (pure tt)) addp-command negp-command

exec : {s : Session} → Command A s → StateT A (ReaderT Channel IO) ⊤
exec END = ask >>= liftIO ∘ primClose
exec (SEND getx cmd) = getx >>= λ x → ask >>= liftIO ∘ primSend x >> exec cmd
exec (RECV putx cmd) = ask >>= liftIO ∘ primRecv >>= putx >> exec cmd
exec (SELECT getx cmd cmd₁) = getx >>= λ b → (ask >>= (liftIO ∘ primSend b)) >> (if b then (exec cmd) else (exec cmd₁))
exec (CHOICE putx cmd cmd₁) = ask >>= liftIO ∘ primRecv >>= λ b → putx b >> (if b then (exec cmd) else (exec cmd₁))

acceptor : Accepting A s → A → IO A
acceptor (ACC pgm) a = do
  ch ← primAccept
  final , _ ← runReaderT (runStateT (exec pgm) a) ch
  pure final
