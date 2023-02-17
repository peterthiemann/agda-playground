{-# OPTIONS --guardedness #-} {- for IO -}
module MultiSession where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Fin using (Fin; suc; zero; _≟_)
open import Data.Fin.Subset using (Subset)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; [] ; _∷_; lookup; updateAt)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Function.Base using (case_of_; const)

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

open import IO

variable
  m n : ℕ
  f : Fin (suc n)
  A : Set

-- splitting

data Split : ℕ → ℕ → Set where
  null : Split zero zero
  left : Split m n → Split (suc m) n
  right : Split m n → Split m (suc n)

apply-split : Split m n → Vec A (m + n) → Vec A m × Vec A n
apply-split null [] = [] , []
apply-split (left sp) (x ∷ v)
  with apply-split sp v
... | vl , vr = x ∷ vl , vr
apply-split{m}{suc n} (right sp) v
  rewrite +-suc m n
  with v
... | x ∷ v
  with apply-split sp v
... | vl , vr = vl , x ∷ vr

locate-split : Split m n → Fin (m + n) → Fin m ⊎ Fin n
locate-split (left sp) zero = inj₁ zero
locate-split (left sp) (suc f)
  with locate-split sp f
... | inj₁ x = inj₁ (suc x)
... | inj₂ y = inj₂ y
locate-split{m}{suc n} (right sp) f
  rewrite +-suc m n
  with f
... | zero = inj₂ zero
... | suc f
  with locate-split sp f
... | inj₁ x = inj₁ x
... | inj₂ y = inj₂ (suc y)

-- session types

data Direction : Set where
  INP OUT : Direction

data Session : ℕ → Set

data Type : Set where
  nat : Type

data SingleSession : Set where
  brn : (d : Direction) → SingleSession → SingleSession → SingleSession
  trm : (d : Direction) → Type          → SingleSession → SingleSession
  end : SingleSession

project : Fin n → Session n → SingleSession

data Session where
  fork : Split m n → Session (suc m) → Session (suc n) → Session (m + n)
  -- assume new channel has address zero in both threads
  brn : (d : Direction) → (i : Fin n) → (s₁ : Session n) → (s₂ : Session n)
    → (∀ (j : Fin n) → i ≢ j → project j s₁ ≡ project j s₂)
    → Session n
  -- higher-order?
  trm : (d : Direction) → Fin n → (t : Type) → Session n → Session n
  end : Fin (suc n) → Session n → Session (suc n)
  terminate : Session zero

  -- for higher-order...
  -- clever-send : Fin n → (t : Type) → Session n → Session (nchannels t + n)
  -- clever-recv : Fin n → (t : Type) → Session (nchannels t + n) → Session n

data MultiSession : {n : ℕ} → Vec SingleSession n → Set where
  brn : ∀ {ssn ssn₁ ssn₂ s₁ s₂} (d : Direction) (i : Fin n)
    → lookup ssn i ≡ brn d s₁ s₂
    → ssn₁ ≡ updateAt i (const s₁) ssn
    → ssn₂ ≡ updateAt i (const s₂) ssn
    → MultiSession ssn₁ → MultiSession ssn₂ → MultiSession ssn


pattern select x s₁ s₂ p = brn OUT x s₁ s₂ p
pattern choice x s₁ s₂ p = brn INP x s₁ s₂ p

pattern recv x t s = trm INP x t s
pattern send x t s = trm OUT x t s

-- adjust index f if index x is removed from set

adjust : (f : Fin (suc n)) (x : Fin (suc n)) → f ≢ x → Fin n
adjust zero zero f≢x = ⊥-elim (f≢x refl)
adjust{suc n} zero (suc x) f≢x = zero
adjust{suc n} (suc f) zero f≢x = f
adjust{suc n} (suc f) (suc x) f≢x
  with adjust f x (λ{ refl → f≢x refl})
... | r = suc r

-- duality

dual : SingleSession → SingleSession → Set
dual (brn INP s₁ s₂) (brn INP s₃ s₄) = ⊥
dual (brn INP s₁ s₂) (brn OUT s₃ s₄) = dual s₁ s₃ × dual s₂ s₄
dual (brn OUT s₁ s₂) (brn INP s₃ s₄) = dual s₁ s₃ × dual s₂ s₄
dual (brn OUT s₁ s₂) (brn OUT s₃ s₄) = ⊥
dual (brn x s₁ s₂) (trm x₁ x₂ s₃) = ⊥
dual (brn x s₁ s₂) end = ⊥
dual (trm x x₁ s₁) (brn x₂ s₂ s₃) = ⊥
dual (trm INP x₁ s₁) (trm INP x₃ s₂) = ⊥
dual (trm INP nat s₁) (trm OUT nat s₂) = dual s₁ s₂
dual (trm OUT nat s₁) (trm INP nat s₂) = dual s₁ s₂
dual (trm OUT nat s₁) (trm OUT nat s₂) = ⊥
dual (trm x x₁ s₁) end = ⊥
dual end (brn x s₂ s₃) = ⊥
dual end (trm x x₁ s₂) = ⊥
dual end end = ⊤

-- projection

-- project : Fin n → Session n → SingleSession
project f (fork sp-c s₁ s₂)
  with locate-split sp-c f
... | inj₁ x = project (suc x) s₁
... | inj₂ y = project (suc y) s₂
project f (brn d x s₁ s₂ _)
  with f ≟ x
... | no ¬p = project f s₁      -- must be equal to project n s₂
... | yes refl = brn d (project f s₁) (project f s₂)
project f (trm d x t s)
  with f ≟ x
... | no ¬p = project f s
... | yes refl = trm d t (project f s)
project {suc n} f (end x s)
  with f ≟ x
... | no f≢x = project (adjust f x f≢x) s
... | yes refl = end

-- well formedness

wft : Session n → Set
wft (fork sp-c s₁ s₂) = wft s₁ × wft s₂ × dual (project zero s₁) (project zero s₂)
wft (brn d x s₁ s₂ _)   = wft s₁ × wft s₂
wft (trm d x t s)    = wft s
wft (end x s)        = wft s
wft terminate        = ⊤

variable
  A′ A₁ A₂ : Set
  t : Type
  s s₁ s₂ : Session n

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ


data Commands (A : Set) :  {n : ℕ} → Session n → Set₁ where
  END    : ∀ f → (A → A) → Commands A s → Commands A (end f s)
  SEND   : ∀ f → (A → T⟦ t ⟧ × A) → Commands A s → Commands A (send f t s)
  RECV   : ∀ f → (T⟦ t ⟧ → A → ⊤ × A) → Commands A s → Commands A (recv f t s)
  SELECT : ∀ f → (A → Bool × A) → Commands A s₁ → Commands A s₂ → Commands A (select f s₁ s₂ _)
  CHOICE : ∀ f → (Bool → A → ⊤ × A) → Commands A s₁ → Commands A s₂ → Commands A (choice f s₁ s₂ _)

postulate
  Channel : Set
  primSend : Channel → A → IO ⊤
  primRecv : Channel → IO A
  primClose : Channel → IO ⊤
  forkIO   : IO A → IO ⊤
  newChan  : IO (Channel × Channel)

executor : {s : Session n} → Commands A s → (init : A)
  → Vec Channel (suc n) → IO (A × Vec Channel (suc n))
executor (END f gend s) state chns = pure (gend state , chns)
executor (SEND f getx cmds) state chns =
  let (x , state′) = getx state in
  primSend (lookup chns (suc f)) x >> executor cmds state′ chns
executor (RECV f putx cmds) state chns =
  primRecv (lookup chns (suc f)) >>= λ x →
  let (tt , state′) = putx x state in
  executor cmds state′ chns
executor (SELECT f x cmds cmds₁) state chns = {!!}
executor (CHOICE f x cmds cmds₁) state chns = {!!}
  
data Commands′ (A : Set) : (n : ℕ) → Session n → Set₁ where
  FORK   : ∀ {s₁ : Session (suc m)} {s₂ : Session (suc n)}
    → (A → A × A)
    → (sp : Split m n)
    → Commands′ A (suc m) s₁ → Commands′ A (suc n) s₂
    → Commands′ A (m + n) (fork sp s₁ s₂)

executor′ : {s : Session n} → Commands′ A n s → (state : A)
  → Vec Channel n → IO (A × Vec Channel n)
executor′ (FORK split-st split-ch cmds₁ cmds₂) state chns =
  let (state₁ , state₂) = split-st state in
  let (chns₁ , chns₂) = apply-split split-ch chns in
  newChan >>= λ (ch₁ , ch₂) →
  forkIO (executor′ cmds₁ state₁ (ch₁ ∷ chns₁)) >>
  forkIO (executor′ cmds₂ state₂ (ch₂ ∷ chns₂)) >>
  {!!} 

data Commands″ (A : Set) : (n o : ℕ) → Session n → Set₁ where
  FORK   : ∀ {s₁ : Session (suc m)} {s₂ : Session (suc n)}
    → (split : A → A × A)
    → (sp : Split m n)
    → Commands″ A (suc m) zero s₁ → Commands″ A (suc n) zero s₂
    → Commands″ A (m + n) zero (fork sp s₁ s₂)

executor″ : ∀ {o}{s : Session n} → Commands″ A n o s → (state : A)
  → Vec Channel n → IO (A × Vec Channel o)
executor″ (FORK split split-ch cmds₁ cmds₂) state chns =
  let (state₁ , state₂) = split state in
  let (chns₁ , chns₂) = apply-split split-ch chns in
  newChan >>= λ (ch₁ , ch₂) →
  forkIO (executor″ cmds₁ state₁ (ch₁ ∷ chns₁)) >>
  executor″ cmds₂ state₂ (ch₂ ∷ chns₂)
