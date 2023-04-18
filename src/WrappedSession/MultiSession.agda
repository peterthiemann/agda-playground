{-# OPTIONS --guardedness #-} {- for IO -}
module MultiSession where

open import Data.Bool using (Bool; true; false;if_then_else_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Fin using (Fin; suc; zero; _≟_)
open import Data.Fin.Subset using (Subset)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; [] ; _∷_; lookup; remove; updateAt)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Function.Base using (case_of_; const)

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

open import IO

variable
  m n o : ℕ
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

data MSession : ℕ → Set

data Type : Set where
  nat : Type

data Session : Set where
  brn : (d : Direction) → Session → Session → Session
  trm : (d : Direction) → Type    → Session → Session
  del : (d : Direction) → Session → Session → Session
  end : Session

project : Fin n → MSession n → Session

Check : Fin n → MSession n → MSession n → Set
Check {n} i s₁ s₂ = ∀ (j : Fin n) → i ≢ j → project j s₁ ≡ project j s₂

data MSession where
  fork : Split m n → MSession (suc m) → MSession (suc n) → MSession (m + n)
  -- assume new channel has address zero in both threads
  brn : (d : Direction) → (i : Fin n) → (s₁ : MSession n) → (s₂ : MSession n)
    → Check i s₁ s₂
    → MSession n
  -- higher-order: delegation
  delOUT : (i j : Fin (suc n)) → i ≢ j → Session → MSession n → MSession (suc n)
  delIN  : Fin n → Session → MSession (suc n) → MSession n
  -- received channel has address zero in continuation
  trm : (d : Direction) → Fin n → (t : Type) → MSession n → MSession n
  end : Fin (suc n) → MSession n → MSession (suc n)
  terminate : MSession zero

  -- for higher-order...
  -- clever-send : Fin n → (t : Type) → MSession n → MSession (nchannels t + n)
  -- clever-recv : Fin n → (t : Type) → MSession (nchannels t + n) → MSession n

data MultiSession : {n : ℕ} → Vec Session n → Set where
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

{-
is-dual : Session → Session → Set
is-dual (brn INP s₁ s₂) (brn INP s₃ s₄) = ⊥
is-dual (brn INP s₁ s₂) (brn OUT s₃ s₄) = is-dual s₁ s₃ × is-dual s₂ s₄
is-dual (brn OUT s₁ s₂) (brn INP s₃ s₄) = is-dual s₁ s₃ × is-dual s₂ s₄
is-dual (brn OUT s₁ s₂) (brn OUT s₃ s₄) = ⊥
is-dual (brn x s₁ s₂) (trm x₁ x₂ s₃) = ⊥
is-dual (brn x s₁ s₂) end = ⊥
is-dual (trm x x₁ s₁) (brn x₂ s₂ s₃) = ⊥
is-dual (trm INP x₁ s₁) (trm INP x₃ s₂) = ⊥
is-dual (trm INP nat s₁) (trm OUT nat s₂) = is-dual s₁ s₂
is-dual (trm OUT nat s₁) (trm INP nat s₂) = is-dual s₁ s₂
is-dual (trm OUT nat s₁) (trm OUT nat s₂) = ⊥
is-dual (trm x x₁ s₁) end = ⊥
is-dual end (brn x s₂ s₃) = ⊥
is-dual end (trm x x₁ s₂) = ⊥
is-dual end end = ⊤
-}

dual-dir : Direction → Direction
dual-dir INP = OUT
dual-dir OUT = INP

dual : Session → Session
dual (brn d s₁ s₂) = brn (dual-dir d) (dual s₁) (dual s₂)
dual (trm d t s) = trm (dual-dir d) t (dual s)
dual (del d s₀ s) = del (dual-dir d) s₀ (dual s)
dual end = end

{-
dual→is-dual : ∀ s₁ s₂ → dual s₁ ≡ s₂ → is-dual s₁ s₂
dual→is-dual (brn INP s₁ s₂) (brn .(dual-dir INP) .(dual s₁) .(dual s₂)) refl = dual→is-dual s₁ (dual s₁) refl , dual→is-dual s₂ (dual s₂) refl
dual→is-dual (brn OUT s₁ s₂) (brn .(dual-dir OUT) .(dual s₁) .(dual s₂)) refl = dual→is-dual s₁ (dual s₁) refl , dual→is-dual s₂ (dual s₂) refl
dual→is-dual (brn d s₁ s₂) (trm d₁ x s₃) ()
dual→is-dual (brn d s₁ s₂) end ()
dual→is-dual (trm d x s₁) (brn d₁ s₂ s₃) ()
dual→is-dual (trm INP nat s₁) (trm .(dual-dir INP) .nat .(dual s₁)) refl = dual→is-dual s₁ (dual s₁) refl
dual→is-dual (trm OUT nat s₁) (trm .(dual-dir OUT) .nat .(dual s₁)) refl = dual→is-dual s₁ (dual s₁) refl
dual→is-dual (trm d x s₁) end ()
dual→is-dual end (brn d s₂ s₃) ()
dual→is-dual end (trm d x s₂) ()
dual→is-dual end end refl = tt

is-dual→dual : ∀ s₁ s₂ → is-dual s₁ s₂ → dual s₁ ≡ s₂
is-dual→dual (brn INP s₁ s₂) (brn OUT s₃ s₄) (isd-s₁ , isd-s₂)
  rewrite is-dual→dual s₁ s₃ isd-s₁
  |  is-dual→dual s₂ s₄ isd-s₂ = refl
is-dual→dual (brn OUT s₁ s₂) (brn INP s₃ s₄) (isd-s₁ , isd-s₂)
  rewrite is-dual→dual s₁ s₃ isd-s₁
  |  is-dual→dual s₂ s₄ isd-s₂ = refl
is-dual→dual (brn INP s₁ s₂) (trm INP nat s₃) ()
is-dual→dual (brn INP s₁ s₂) (trm OUT nat s₃) ()
is-dual→dual (brn OUT s₁ s₂) (trm INP nat s₃) ()
is-dual→dual (brn OUT s₁ s₂) (trm OUT nat s₃) ()
is-dual→dual (brn INP s₁ s₂) end ()
is-dual→dual (brn OUT s₁ s₂) end ()
is-dual→dual (trm INP nat s₁) (trm OUT nat s₂) isd-s₁-s₂ rewrite is-dual→dual s₁ s₂ isd-s₁-s₂ = refl
is-dual→dual (trm OUT nat s₁) (trm INP nat s₂) isd-s₁-s₂ rewrite is-dual→dual s₁ s₂ isd-s₁-s₂ = refl
is-dual→dual end end isd-s₁-s₂ = refl
-}

-- projection

-- project : Fin n → MSession n → Session
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
project f (delOUT x j x≢j sj s)
  with f ≟ x
... | yes refl = del OUT sj (project (adjust f j x≢j) s)
... | no f≢x
  with f ≟ j
... | yes refl = sj
... | no f≢j = project (adjust f j f≢j) s
project f (delIN x s0 s)
  with f ≟ x
... | yes refl = del INP s0 (project (suc f) s)
... | no f≢x = project (suc f) s

-- well formedness

wft : MSession n → Set
wft (fork sp-c s₁ s₂) = wft s₁ × wft s₂ × dual (project zero s₁) ≡ project zero s₂
wft (brn d x s₁ s₂ _) = wft s₁ × wft s₂
wft (trm d x t s)    = wft s
wft (end x s)        = wft s
wft (delOUT i j i≢j sj s) = wft s
wft (delIN x s0 s)   = wft s
wft terminate        = ⊤

variable
  A′ A₁ A₂ : Set
  t : Type
  s s₁ s₂ : MSession n

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ


data Cmd (A : Set) : (n : ℕ) → MSession n → Set₁ where
  CLOSE  : ∀ f → (A → A) → Cmd A n s → Cmd A (suc n) (end f s)
  SEND   : ∀ f → (A → T⟦ t ⟧ × A) → Cmd A n s → Cmd A n (send f t s)
  RECV   : ∀ f → (T⟦ t ⟧ → A → ⊤ × A) → Cmd A n s → Cmd A n (recv f t s)
  SELECT : ∀ f → {check : Check f s₁ s₂} → (A → Bool × A) → Cmd A n s₁ → Cmd A n s₂ → Cmd A n (select f s₁ s₂ check)
  CHOICE : ∀ f → {check : Check f s₁ s₂} → Cmd A n s₁ → Cmd A n s₂ → Cmd A n (choice f s₁ s₂ check)
  FORK   : ∀ {s₁ : MSession (suc m)} {s₂ : MSession (suc n)}
    → (split : A → A × A)
    → (sp : Split m n)
    → Cmd A (suc m) s₁ → Cmd A (suc n) s₂
    → Cmd A (m + n) (fork sp s₁ s₂)
  SENDCH : ∀ {sj} → ∀ f j → (f≢j : f ≢ j) → Cmd A n s → Cmd A (suc n) (delOUT f j f≢j sj s)
  RECVCH : ∀ {sj} → ∀ f → Cmd A (suc n) s → Cmd A n (delIN f sj s)
  END    : Cmd A 0 terminate

postulate
  Channel : Set
  primSend : Channel → A → IO ⊤
  primRecv : Channel → IO A
  primClose : Channel → IO ⊤
  forkIO   : IO A → IO ⊤
  newChan  : IO (Channel × Channel)

exec : ∀{s : MSession n} → Cmd A n s → (state : A)
  → Vec Channel n → IO A
exec (SENDCH f j f≢j cmd) state chns = do
  primSend (lookup chns f) (lookup chns j)
  exec cmd state (remove chns j)
exec (RECVCH f cmd) state chns = do
  ch ← primRecv (lookup chns f)
  exec cmd state (ch ∷ chns)
exec (FORK split split-ch cmds₁ cmds₂) state chns =
  let (state₁ , state₂) = split state in
  let (chns₁ , chns₂) = apply-split split-ch chns in
  newChan >>= λ (ch₁ , ch₂) →
  forkIO (exec cmds₁ state₁ (ch₁ ∷ chns₁)) >>
  exec cmds₂ state₂ (ch₂ ∷ chns₂)
exec (CLOSE f gend s) state chns = do
  primClose (lookup chns f)
  exec s (gend state) (remove chns f)
exec (SEND f getx cmds) state chns =
  let (x , state′) = getx state in
  primSend (lookup chns f) x >> exec cmds state′ chns
exec (RECV f putx cmds) state chns =
  primRecv (lookup chns f) >>= λ x →
  let (tt , state′) = putx x state in
  exec cmds state′ chns
exec (SELECT f getx cmds₁ cmds₂) state chns = do
  let b , a = getx state
  primSend (lookup chns f) b
  if b then (exec cmds₁ a chns)
       else (exec cmds₂ a chns)
exec (CHOICE f cmd₁ cmd₂) state chns = do
  b ← primRecv (lookup chns f)
  if b then exec cmd₁ state chns
       else exec cmd₂ state chns
exec END state [] = do
  pure state


runCmd : Cmd A 0 s → A → IO A
runCmd cmd init = do
  exec cmd init []

