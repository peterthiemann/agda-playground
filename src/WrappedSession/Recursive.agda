{-# OPTIONS --guardedness #-} {- required for IO -}
module WrappedSession.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Unit using (⊤; tt)

open import Function.Base using (const; case_of_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)

open import IO

variable
  A A′ A″ A₁ A₂ : Set
  n : ℕ

data Type : Set where
  nat : Type

data Session n : Set where
  select choice : Session n → Session n → Session n
  send recv : Type → Session n → Session n
  end : Session n
  mu  : Session (suc n) → Session n
  var : Fin n → Session n

-- service protocol for a binary function
binaryp : Session n → Session n
binaryp s = (recv nat (recv nat (send nat s)))

-- service protocol for a unary function
unaryp : Session n → Session n
unaryp s = (recv nat (send nat s))

-- service protocol for choosing between a binary and a unary function
un-bin-p : Session n → Session n
un-bin-p s = choice (binaryp s) (unaryp s)

-- wanted: server that repeatedly executes arithp
arithp : Session 0
arithp = mu (choice (binaryp (var zero)) end)
-- in theory:
--     = choice (binaryp arithp) end

variable
  t : Type
  s s₁ s₂ : Session n

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ

data Commands n (A : Set) : Session n → Set where
  END    : Commands n A end
  SEND   : (A → T⟦ t ⟧ × A) → Commands n A s → Commands n A (send t s)
  RECV   : (T⟦ t ⟧ → A → A) → Commands n A s → Commands n A (recv t s)
  SELECT : (A → Bool × A) → Commands n A s₁ → Commands n A s₂ → Commands n A (select s₁ s₂)
  CHOICE : (Bool → A → A) → Commands n A s₁ → Commands n A s₂ → Commands n A (choice s₁ s₂)
  MU     : Commands (suc n) A s → Commands n A (mu s)
  CONTINUE : (i : Fin n) → Commands n A (var i)

record Accepting A s : Set where
  constructor ACC
  field pgm : Commands 0 A s

arithp-command : Commands 0 ℕ arithp
arithp-command = MU (CHOICE (λ b x → 0)
                            (RECV (λ _ x → x) (RECV _+_ (SEND (λ x → x , 0) (CONTINUE zero))))
                            END)

postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO ⊤
  primSend : A → Channel → IO ⊤
  primRecv : Channel → IO A

CommandStore : ∀ n → Set → Set
CommandStore n A = (i : Fin n) → ∃[ s ] (Commands (suc (toℕ (opposite i))) A s)

-- cms : CommandStore
-- cms A 0 = ( s : Session 1 , cmd)

Gas = ℕ

executor : Gas → Commands n A s → CommandStore n A → (init : A) → Channel → IO A
executor k END cms state ch = do
  primClose ch
  pure state
executor k (SEND getx cmd) cms state ch = do
  let (x , state′) = getx state
  primSend x ch
  executor k cmd cms state′ ch
executor k (RECV putx cmd) cms state ch = do
  x ← primRecv ch
  let state′ = putx x state
  executor k cmd cms state′ ch
executor k (SELECT getx cmd₁ cmd₂) cms state ch = do
  let (x , state′) = getx state
  primSend x ch
  (case x of (λ{ false → executor k cmd₁ cms state′ ch ; true → executor k cmd₂ cms state′ ch}))
executor k (CHOICE putx cmd₁ cmd₂) cms state ch = do
  x ← primRecv ch
  let state′ = putx x state
  (case x of (λ{ false → executor k cmd₁ cms state′ ch ; true → executor k cmd₂ cms state′ ch}))
executor {n} {A} {s = mu s} k (MU cmd) cms state ch = executor k cmd cms′ state ch
  where cms′ : CommandStore (suc n) A
        cms′ zero    rewrite toℕ-fromℕ n = s , cmd
        cms′ (suc i) rewrite toℕ-inject₁ (opposite i) = cms i
executor {suc n} {A} zero (CONTINUE i) cms state ch = pure state -- hack alert!
executor {suc n} {A} (suc k) (CONTINUE i) cms state ch
  with cms i
... | s-i , cmd-i = executor k cmd-i (pop cms i) state ch
  where
    pop1 : ∀{n} → CommandStore (suc n) A → CommandStore n A
    pop1 cms i with cms (suc i)
    ... | cms₁ rewrite toℕ-inject₁ (opposite i) = cms₁

    pop : ∀{n} → CommandStore (suc n) A → (i : Fin (suc n)) → CommandStore (suc (toℕ (opposite i))) A
    pop {n} cms zero rewrite toℕ-fromℕ n = cms
    pop {suc n} cms (suc i) = subst (λ H → CommandStore (suc H) A) (sym (toℕ-inject₁ (opposite i))) (pop (pop1 cms) i)

acceptor : Gas → Accepting A s → A → IO A
acceptor k (ACC pgm) a = primAccept >>= executor k pgm (λ()) a

-- ----------------------------------------------------------------------
-- -- a Σ type isomorphic to A₁ ⊎ A₂

-- ifb : Set → Set → Bool → Set
-- ifb A₁ A₂ false = A₁
-- ifb A₁ A₂ true = A₂

-- zzfalse : Σ _ (ifb Bool ℕ)
-- zzfalse = false , false

-- zztrue :  Σ _ (ifb Bool ℕ)
-- zztrue =  true , 42

-- fffun  : (x : Bool) → ifb Bool ℕ x
-- fffun false = false
-- fffun true = 42

-- ΣB : Set → Set → Set
-- ΣB A₁ A₂ = Σ _ (ifb A₁ A₂)


-- data Commands′ (A : Set) : Set → Session → Set₁ where
--   END    : Commands′ A A end
--   SEND   : (A → T⟦ t ⟧ × A′) → Commands′ A′ A″ s → Commands′ A A″ (send t s)
--   RECV   : (T⟦ t ⟧ → A → A′) → Commands′ A′ A″ s → Commands′ A A″ (recv t s)
--   SELECT1 : (A → A₁ ⊎ A₂) → Commands′ A₁ A″ s₁ → Commands′ A₂ A″ s₂ → Commands′ A A″ (select s₁ s₂)
--   CHOICE1 : ((x : Bool) → A → (case x of λ{false → A₁; true → A₂})) → Commands′ A₁ A″ s₁ → Commands′ A₂ A″ s₂ → Commands′ A A″ (choice s₁ s₂)

--   SELECT2 : (A → ΣB A₁ A₂) → Commands′ A₁ A″ s₁ → Commands′ A₂ A″ s₂ → Commands′ A A″ (select s₁ s₂)

-- executor′ : {s : Session} → Commands′ A A″ s → (init : A) → Channel → IO A″
-- executor′ END state ch = do
--   primClose ch
--   return state
-- executor′ (SEND getx cmd) state ch = do
--   let (x , state′) = getx state
--   primSend x ch
--   executor′ cmd state′ ch
-- executor′ (RECV putx cmd) state ch = do
--   x ← primRecv ch
--   let state′ = putx x state
--   executor′ cmd state′ ch
-- executor′ (SELECT1 getx cmd₁ cmd₂) state ch
--   with getx state
-- ... | inj₁ state₁ = do
--       primSend true ch
--       executor′ cmd₁ state₁ ch
-- ... | inj₂ state₂ = do
--       primSend false ch
--       executor′ cmd₂ state₂ ch
-- executor′ (CHOICE1 putx cmd₁ cmd₂) state ch = do
--   false ← primRecv{A = Bool} ch
--     where
--       true → do
--         let state′ = putx true state
--         executor′ cmd₂ state′ ch
--   let state′ = putx false state
--   executor′ cmd₁ state′ ch
-- executor′ (SELECT2 getx cmd₁ cmd₂) state ch = do
--   let bst = getx state
--   primSend (proj₁ bst) ch
--   (false , state₁) ← return bst
--     where
--       (true , state₂) → executor′ cmd₂ state₂ ch
--   executor′ cmd₁ state₁ ch

