{-# OPTIONS --guardedness #-} {- required for IO -}
module WrappedSession.Experiment where

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


data Session : Set
data Type : Set where
  nat : Type
  chan : Session → Type

data Session where
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
  A B A′ A″ A₁ A₂ : Set
  t : Type
  s s₁ s₂ : Session


postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO ⊤
  primSend : A → Channel → IO ⊤
  primRecv : Channel → IO A

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ
T⟦ chan s ⟧ = Channel

module composable-command where
  infixr 30 _⨟_

  data Fragment (A : Set) : (Session → Session) → Set where
    SEND : (A → T⟦ t ⟧ × A) → Fragment A (send t)
    RECV : (T⟦ t ⟧ → A → A) → Fragment A (recv t)
    _⨟_  : ∀ {f g} → Fragment A f → Fragment A g → Fragment A (f ∘ g)

  data Command A : Session → Set where
    CLOSE : ∀ {f} → Fragment A f → Command A (f end)

  addp-command : Command ℕ binaryp
  addp-command = CLOSE (RECV _+_ ⨟ RECV _+_ ⨟ SEND (λ x → x , 0))

  -- works, but not there is no help from the type checker when defining the command

  data Comp (A B : Set) : Set₁ where
    inject : (f : A → B) → Comp A B
    comp   : ∀ {C : Set} → (f : Comp C B) (g : Comp A C) → Comp A B

  compile : ∀{A B} → Comp A B → A → B
  compile (inject f) = f
  compile (comp f g) = compile f ∘ compile g

  data Frag1 (A : Set) : (Comp Session Session) → Set where
    SEND : (A → T⟦ t ⟧ × A) → Frag1 A (inject (send t))
    RECV : (T⟦ t ⟧ → A → A) → Frag1 A (inject (recv t))
    _⨟_  : ∀ {f g} → Frag1 A f → Frag1 A g → Frag1 A (comp f g)
  
  data Cmd1 A : Comp Session Session → Set₁ where
    CLOSE : ∀ {f} → Frag1 A f → Cmd1 A f

  tocomp : Session → Comp Session Session
  tocomp (send x s) = comp (inject (send x)) (tocomp s)
  tocomp (recv x s) = comp (inject (recv x)) (tocomp s)
  tocomp end = inject id
  tocomp (select s s₁) = {!!}
  tocomp (choice s s₁) = {!!}
  
  addp-cmd1 : Cmd1 ℕ (tocomp binaryp)
  addp-cmd1 = CLOSE ((RECV _+_) ⨟ ((RECV _+_) ⨟ ((SEND (λ x → x , 0)) ⨟ {!!})))






module even-more-alternative-branching where
  data Cmd (A B : Set) : Session → Set₁ where
    SELECT : ∀ {F} → (A → Σ Bool F)
      → ((p : Σ Bool F) → Cmd (F (proj₁ p)) B (if proj₁ p then s₁ else s₂))
      → Cmd A B (select s₁ s₂)
  
  exec : {s : Session} → Cmd A B s → A → Channel → IO B
  exec (SELECT getx cont) a ch = do
    let p = getx a
    exec (cont p) (proj₂ p) ch



module alternative-branching where
  data Commands (A : Set) : Session → Set where
    SELECT : (A → Bool × A) → ((b : Bool) → Commands A (if b then s₁ else s₂)) → Commands A (select s₁ s₂)
    CHOICE : ((b : Bool) → A → (Commands A (if b then s₁ else s₂)) × A) → Commands A (choice s₁ s₂)

  exec : {s : Session} → Commands A s → A → Channel → IO A
  exec (SELECT getx cont) st ch = do
    let (x , st′) = getx st
    exec (cont x) st′ ch
  exec (CHOICE cont) st ch = do
    x ← primRecv{Bool} ch
    let (cmdx , st′) = cont x st
    exec cmdx st′ ch





data Commands (A : Set) : Session → Set where
  END    : Commands A end
  SEND   : (A → T⟦ t ⟧ × A) → Commands A s → Commands A (send t s)
  RECV   : (T⟦ t ⟧ → A → A) → Commands A s → Commands A (recv t s)
  SELECT : (A → Bool × A) → Commands A s₁ → Commands A s₂ → Commands A (select s₁ s₂)
  CHOICE : (Bool → A → ⊤ × A) → Commands A s₁ → Commands A s₂ → Commands A (choice s₁ s₂)

record Accepting A s : Set where
  constructor ACC
  field pgm : Commands A s

addp-command : Commands ℕ binaryp
addp-command = RECV const
               (RECV _+_
               (SEND (λ x → x , 0)
               END))

executor : {s : Session} → Commands A s → (init : A) → Channel → IO A
executor END state ch = do
  primClose ch
  pure state
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
  pure state
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
  (false , state₁) ← pure bst
    where
      (true , state₂) → executor′ cmd₂ state₂ ch
  executor′ cmd₁ state₁ ch

