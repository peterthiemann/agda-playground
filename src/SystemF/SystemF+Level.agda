module SystemF+Level where

open import Level using (zero)
open import Data.Nat using ( ℕ; s≤s; z≤n; _<′_ ) renaming (_⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _<_ to _<ℕ_ )
open import Data.Nat.Properties using (+-identityʳ; +-suc; <-trans; <⇒<′; ⊔-idem; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m; <⇒≤)
open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; lookupAny)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function  using (id; _∘_)

open import Lib

coe-coe : ∀{a}{A B : Set a} (x≡y : A ≡ B) (y≡x : B ≡ A) {p : A}
  → (coe y≡x (coe x≡y p)) ≡ p
coe-coe refl refl = refl


import IRUniverse as IR

module _ where
  open IR.ℕ*ℕ-example public
  open IR.IR-Universe lvl

  import Data.Nat as N
  open import Data.Nat.Properties
  open import Data.Nat.Induction
  open Lexicographic N._<_ (λ _ → N._<_)

  _<ℕ*ℕ_ : ℕ × ℕ → ℕ × ℕ → Set
  _<ℕ*ℕ_ = Lexicographic._<_ _<ℕ_ (λ _ → _<ℕ_)

  postulate
    <-irrefl-ℕ*ℕ : Irreflexive _≡_ _<ℕ*ℕ_

  cmp-ℕ : (i j : ℕ) → i <ℕ j ⊎ j <ℕ i ⊎ i ≡ j
  cmp-ℕ ℕ.zero ℕ.zero = inj₂ (inj₂ refl)
  cmp-ℕ ℕ.zero (ℕ.suc j) = inj₁ (s≤s z≤n)
  cmp-ℕ (ℕ.suc i) ℕ.zero = inj₂ (inj₁ (s≤s z≤n))
  cmp-ℕ (ℕ.suc i) (ℕ.suc j)
    with cmp-ℕ i j
  ... | inj₁ x = inj₁ (s≤s x)
  ... | inj₂ (inj₁ x) = inj₂ (inj₁ (s≤s x))
  ... | inj₂ (inj₂ y) = inj₂ (inj₂ (ℕ.suc & y))

  cmp-ℕ*ℕ : (i j : ℕ × ℕ) →
      i <ℕ*ℕ j ⊎ j <ℕ*ℕ i ⊎ i ≡ j
  cmp-ℕ*ℕ i@(ifst , isnd) j@(jfst , jsnd)
    with cmp-ℕ ifst jfst
  ... | inj₁ x = inj₁ (left x)
  ... | inj₂ (inj₁ x) = inj₂ (inj₁ (left x))
  ... | inj₂ (inj₂ refl)
    with cmp-ℕ isnd jsnd
  ... | inj₁ x = inj₁ (right x)
  ... | inj₂ (inj₁ x) = inj₂ (inj₁ (right x))
  ... | inj₂ (inj₂ eq) = inj₂ (inj₂ (cong (λ j → (ifst , j)) eq))

  ≤-suc : ∀ {i j} → ℕ.suc i <ℕ ℕ.suc j → i <ℕ j
  ≤-suc (s≤s p) = p

  <-ext-ℕ : {i j : ℕ}
    → (∀ (k : ℕ) → (k <ℕ i → k <ℕ j) × (k <ℕ j → k <ℕ i))
    → i ≡ j
  <-ext-ℕ {i} {j} f
    with cmp-ℕ i j
  ... | inj₁ x = ⊥-elim (<-irrefl refl (Σ.proj₂ (f i) x))
  ... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl refl (Σ.proj₁ (f j) x))
  ... | inj₂ (inj₂ refl) = refl


  <-ext-ℕ*ℕ : ∀ {i j : ℕ × ℕ} →
      ((k : ℕ × ℕ) → (k <ℕ*ℕ i → k <ℕ*ℕ j) × (k <ℕ*ℕ j → k <ℕ*ℕ i)) →
      i ≡ j
  <-ext-ℕ*ℕ {i} {j} f
    with cmp-ℕ*ℕ i j
  ... | inj₁ x = ⊥-elim (<-irrefl-ℕ*ℕ refl (Σ.proj₂ (f i) x))
  ... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl-ℕ*ℕ refl (Σ.proj₁ (f j) x))
  ... | inj₂ (inj₂ refl) = refl

  <-trans-ℕ*ℕ : ∀ {x y z} → x <ℕ*ℕ y → y <ℕ*ℕ z → x <ℕ*ℕ z
  <-trans-ℕ*ℕ (Lexicographic.left x₁<x₂) (Lexicographic.left x₂<x₃) = left (<-trans x₁<x₂ x₂<x₃)
  <-trans-ℕ*ℕ (Lexicographic.left x₁<x₂) (Lexicographic.right y₁<y₂) = left x₁<x₂
  <-trans-ℕ*ℕ (Lexicographic.right y₁<y₂) (Lexicographic.left x₁<x₂) = left x₁<x₂
  <-trans-ℕ*ℕ (Lexicographic.right y₁<y₂) (Lexicographic.right y₂<y₃) = right (<-trans y₁<y₂ y₂<y₃)

  ordinal-ℕ*ℕ : IR.Ordinal lvl
  ordinal-ℕ*ℕ = record { cmp = cmp-ℕ*ℕ ; <-ext = <-ext-ℕ*ℕ }

  Lvl-suc : Lvl → Lvl
  Lvl-suc (fst , snd) = fst , ℕ.suc snd

open IR.IR-Univ-Ordinal ordinal-ℕ*ℕ

variable ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Lvl

--! TF >

≤-trans : ∀ {i} {j} {k} → i ≤ j → j ≤ k → i ≤ k
≤-trans (inj₁ i<j) (inj₁ j<k) = inj₁ (<-trans-ℕ*ℕ i<j j<k)
≤-trans (inj₁ i<j) (inj₂ refl) = inj₁ i<j
≤-trans (inj₂ refl) j≤k = j≤k

<≤-trans : ∀ {i} {j} {k} → i <ℕ*ℕ j → j ≤ k → i <ℕ*ℕ k
<≤-trans i<j (inj₁ j<k) = <-trans-ℕ*ℕ i<j j<k
<≤-trans i<j (inj₂ refl) = i<j

-- level variable environments

LvlEnv = List ⊤

variable
      δ δ′ δ₁ δ₂ δ₃ : LvlEnv


data FinLvl (δ : LvlEnv) : Set where
  `zero : FinLvl δ
  `suc  : FinLvl δ → FinLvl δ
  _`⊔_  : FinLvl δ → FinLvl δ → FinLvl δ
  `_    : tt ∈ δ → FinLvl δ

data LimLvl (δ : LvlEnv) : Set where
  `fin  : FinLvl δ → LimLvl δ
  `omg  : ℕ → LimLvl δ

_⊔ℓ_ : LimLvl δ → LimLvl δ → LimLvl δ
`fin x ⊔ℓ `fin y = `fin (x `⊔ y)
`fin x ⊔ℓ `omg y = `omg y
`omg x ⊔ℓ `fin y = `omg x
`omg x ⊔ℓ `omg y = `omg (x ⊔ℕ y)

sucℓ : LimLvl δ → LimLvl δ
sucℓ (`fin x) = `fin (`suc x)
sucℓ (`omg x) = `omg (ℕ.suc x)

wkₗ  : FinLvl δ → FinLvl (tt ∷ δ)
wkₗ `zero      = `zero
wkₗ (`suc l)   = `suc (wkₗ l)
wkₗ (` x)      = ` (there x)
wkₗ (l₁ `⊔ l₂) = wkₗ l₁ `⊔ wkₗ l₂

wkₗ′ : LimLvl δ → LimLvl (tt ∷ δ)
wkₗ′ (`fin x) = `fin (wkₗ x)
wkₗ′ (`omg x) = `omg x


DEnv : LvlEnv → Set
DEnv δ = tt ∈ δ → Lvl

⟦_⟧ℓ : FinLvl δ → DEnv δ → Lvl
⟦ `zero ⟧ℓ d = # ℕ.zero
⟦ `suc l ⟧ℓ d = Lvl-suc (⟦ l ⟧ℓ d)
⟦ l₁ `⊔ l₂ ⟧ℓ d = ⟦ l₁ ⟧ℓ d ⊔ ⟦ l₂ ⟧ℓ d
⟦ ` x ⟧ℓ d = d x

⟦_⟧ℓ′ : LimLvl δ → DEnv δ → Lvl
⟦ `fin x ⟧ℓ′ d = ⟦ x ⟧ℓ d
⟦ `omg x ⟧ℓ′ d = ω + (0 , x)

DEnv-ext : DEnv δ → Lvl → DEnv (tt ∷ δ)
DEnv-ext d ℓ (here refl) = ℓ
DEnv-ext d ℓ (there x) = d x

variable l l′ l″ l₁ l₂ l₃ : LimLvl δ

-- level environments

--! Env
Env : LvlEnv → Set
Env δ = List (LimLvl δ)

wkₗₑ : Env δ → Env (tt ∷ δ)
wkₗₑ []      = []
wkₗₑ (l ∷ Δ) = wkₗ′ l ∷ wkₗₑ Δ


variable Δ Δ₁ Δ₂ Δ₃ : Env δ


--! Type

data Type δ (Δ : Env δ) : LimLvl δ → Set where

  `ℕ      : Type δ Δ (`fin `zero)
  _`⇒_    : (T₁ : Type δ Δ l₁) (T₂ : Type δ Δ l₂) → Type δ Δ (l₁ ⊔ℓ l₂)
  `_      : (α : l ∈ Δ) → Type δ Δ l
  `∀α_,_  : (l : LimLvl δ) (T : Type δ (l ∷ Δ) l′) → Type δ Δ (sucℓ l ⊔ℓ l′)
  `∀ℓ_    : (T : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ′ l)) → Type δ Δ (`omg ℕ.zero ⊔ℓ l)

Lᵈ′ : DEnv δ → LimLvl δ → Lvl
Lᵈ′ d l = ⟦ l ⟧ℓ′ d

Uᵈ′ : DEnv δ → LimLvl δ → Set
Uᵈ′ d l = U (Lᵈ′ d l)

⟦⟧ℓ-⊔ : (d : DEnv δ) (l₁ : FinLvl δ) (l₂ : FinLvl δ) → ⟦ l₁ ⟧ℓ d ⊔ ⟦ l₂ ⟧ℓ d ≡ ⟦ l₁ `⊔ l₂ ⟧ℓ d
⟦⟧ℓ-⊔ d `zero `zero = refl
⟦⟧ℓ-⊔ d `zero (`suc l₂) = refl
⟦⟧ℓ-⊔ d `zero (l₂ `⊔ l₃) = refl
⟦⟧ℓ-⊔ d `zero (` x) = refl
⟦⟧ℓ-⊔ d (`suc l₁) `zero = refl
⟦⟧ℓ-⊔ d (`suc l₁) (`suc l₂) = refl
⟦⟧ℓ-⊔ d (`suc l₁) (l₂ `⊔ l₃) = refl
⟦⟧ℓ-⊔ d (`suc l₁) (` x) = refl
⟦⟧ℓ-⊔ d (l₁ `⊔ l₂) `zero = refl
⟦⟧ℓ-⊔ d (l₁ `⊔ l₂) (`suc l₃) = refl
⟦⟧ℓ-⊔ d (l₁ `⊔ l₂) (l₃ `⊔ l₄) = refl
⟦⟧ℓ-⊔ d (l₁ `⊔ l₂) (` x) = refl
⟦⟧ℓ-⊔ d (` x) `zero = refl
⟦⟧ℓ-⊔ d (` x) (`suc l₂) = refl
⟦⟧ℓ-⊔ d (` x) (l₂ `⊔ l₃) = refl
⟦⟧ℓ-⊔ d (` x) (` x₁) = refl

⟦⟧ℓ-fin : (d : DEnv δ) (l : FinLvl δ) → ∃[ k ] ⟦ l ⟧ℓ d ≡ (0 , k)
⟦⟧ℓ-fin d `zero = ℕ.zero , refl
⟦⟧ℓ-fin d (`suc l)
  with ⟦⟧ℓ-fin d l
... | k , p rewrite p = ℕ.suc k , refl
⟦⟧ℓ-fin d (l₁ `⊔ l₂)
  with ⟦⟧ℓ-fin d l₁ | ⟦⟧ℓ-fin d l₂
... | k₁ , p₁ | k₂ , p₂
  with cmp-ℕ k₁ k₂
... | inj₁ x = k₂ , {!!}
... | inj₂ r = {!!}
⟦⟧ℓ-fin d (` x) = {!!}

⟦⟧ℓ-⊔ℓ : (d : DEnv δ) (l₁ l₂ : LimLvl δ) → ⟦ l₁ ⊔ℓ l₂ ⟧ℓ′ d ≡ ⟦ l₁ ⟧ℓ′ d ⊔ ⟦ l₂ ⟧ℓ′ d
⟦⟧ℓ-⊔ℓ d (`fin x) (`fin y) = refl
⟦⟧ℓ-⊔ℓ d (`fin x) (`omg y)
  with ⟦⟧ℓ-fin d x
... | _ , eq rewrite eq = refl
⟦⟧ℓ-⊔ℓ d (`omg x) (`fin y)
  with ⟦⟧ℓ-fin d y
... | _ , eq rewrite eq = refl
⟦⟧ℓ-⊔ℓ d (`omg x) (`omg y)
  with cmp-ℕ x y
... | inj₁ x₁ rewrite m≤n⇒m⊔n≡n (<⇒≤ x₁) = refl
... | inj₂ (inj₁ x₁) rewrite m≥n⇒m⊔n≡m (<⇒≤ x₁) = refl
... | inj₂ (inj₂ refl) rewrite ⊔-idem x = refl

⟦⟧ℓ-suc : (d : DEnv δ) (l : LimLvl δ) → ⟦ sucℓ l ⟧ℓ′ d ≡ Lvl-suc (⟦ l ⟧ℓ′ d)
⟦⟧ℓ-suc d (`fin x) = refl
⟦⟧ℓ-suc d (`omg x) = refl

Lᵈ′-⊔ : (d : DEnv δ) (l₁ : LimLvl δ) (l₂ : LimLvl δ) → Lᵈ′ d l₁ ⊔ Lᵈ′ d l₂ ≡ Lᵈ′ d (l₁ ⊔ℓ l₂)
Lᵈ′-⊔ d (`fin x) (`fin y) = ⟦⟧ℓ-⊔ d x y
Lᵈ′-⊔ d (`fin x) (`omg y)
  with ⟦⟧ℓ-fin d x
... | k , p rewrite p = refl
Lᵈ′-⊔ d (`omg x) (`fin y)
  with ⟦⟧ℓ-fin d y
... | k , p rewrite p = refl
Lᵈ′-⊔ d (`omg x) (`omg y)
  with cmp-ℕ x y
... | inj₁ x<y = cong (1 ,_) (sym (m≤n⇒m⊔n≡n (<⇒≤ x<y)))
... | inj₂ (inj₁ y<x) = cong (1 ,_) (sym (m≥n⇒m⊔n≡m (<⇒≤ y<x)))
... | inj₂ (inj₂ refl) = cong (1 ,_) (sym (⊔-idem x))

coef :  (d : DEnv δ) (x : Lvl) (fl : FinLvl δ) → ⟦ fl ⟧ℓ d ≡ ⟦ wkₗ fl ⟧ℓ  (DEnv-ext d x)
coef d x `zero = refl
coef d x (`suc fl) = cong Lvl-suc (coef d x fl)
coef d x (fl₁ `⊔ fl₂) = cong₂ _⊔_ (coef d x fl₁) (coef d x fl₂)
coef d x (` z) = refl

coel :  (d : DEnv δ) (x : Lvl) (ll : LimLvl δ) → Uᵈ′ d ll ≡ Uᵈ′ (DEnv-ext d x) (wkₗ′ ll)
coel d x (`fin fl) = cong U (coef d x fl)
coel d x (`omg k) = refl

coel- :  (d : DEnv δ) (x : Lvl) (ll : LimLvl δ) → Lᵈ′ d ll ≡ Lᵈ′ (DEnv-ext d x) (wkₗ′ ll)
coel- d x (`fin fl) = coef d x fl
coel- d x (`omg k) = refl

-- coe1 :  (d : DEnv δ) (x : Lvl) (ll : LimLvl δ) → (u  : Uᵈ′ d ll) → Uᵈ′ (DEnv-ext d x) (wkₗ′ ll)
-- coe1 d x (`fin fl) u = subst U (coef d x fl) u
-- coe1 d x (`omg k) u = u

coe* : {Δ : Env δ} (d : DEnv δ) (x : Lvl) → All (Uᵈ′ d) Δ → All (Uᵈ′ (DEnv-ext d x)) (wkₗₑ Δ)
coe* d x [] = []
coe* {Δ = ll ∷ _} d x (u ∷ η) = coe (coel d x ll) u ∷ coe* d x η



Env* : DEnv δ → Env δ → Set
Env* d Δ = All (Uᵈ′ d) Δ


encode : (d : DEnv δ) (T : Type δ Δ l) (η : Env* d Δ) → Uᵈ′ d l
encode d `ℕ η = ℕ'
encode d (_`⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂) η
  = subst U (Lᵈ′-⊔ d l₁ l₂) (Lift≤ (⊔₁ (Lᵈ′ d l₁) (Lᵈ′ d l₂)) (encode d T₁ η))
    ⇒'
    subst U (Lᵈ′-⊔ d l₁ l₂) (Lift≤ (⊔₂ (Lᵈ′ d l₁) (Lᵈ′ d l₂)) (encode d T₂ η))
encode d (` α) η = lookup η α
encode d (`∀α_,_ {l′ = l′} l T) η
  with  ⊔₁ (⟦ sucℓ l ⟧ℓ′ d) (⟦ l′ ⟧ℓ′ d)
... | ≤-witness
  rewrite (⟦⟧ℓ-⊔ℓ d (sucℓ l) l′) =
  Π' (U' {j = ⟦ l ⟧ℓ′ d} (<≤-trans IR.ℕ*ℕ-example.<suc (≤-trans (inj₂ (sym (⟦⟧ℓ-suc d l))) ≤-witness)))
     λ u → let r = encode d T (coe  (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {⟦ l ⟧ℓ′ d} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) u ∷ η) in
         Lift≤ (⊔₂ (⟦ sucℓ l ⟧ℓ′ d) (⟦ l′ ⟧ℓ′ d)) r
encode d (`∀ℓ_ {l = l} T) η = Π' Lvl' (λ x → let r = coe (sym (coel d x l)) (encode (DEnv-ext d x) T (coe* d x η))
                                             in  Lift≤ (≤-trans (⊔₂ ω (Lᵈ′ d l)) (inj₂ (sym (⟦⟧ℓ-⊔ℓ d (`omg ℕ.zero) l)))) r)


⟦_⟧ᵀ : (T : Type δ Δ l) (d : DEnv δ) → (η : Env* d Δ) → Set
⟦ T ⟧ᵀ d η = El (encode d T η)


-- type environments
data Ctx : ∀ {δ} → Env δ → Set where
  ∅     : Ctx {δ} []
  _◁_   : Type δ Δ l → Ctx Δ → Ctx Δ          
  _◁*_  : (l : LimLvl δ) → Ctx Δ → Ctx (l ∷ Δ)
  ◁ℓ_   : Ctx Δ → Ctx (wkₗₑ Δ)

variable
  Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Ctx {δ} Δ
  T T′ : Type δ Δ l

postulate
  Twk : Type δ Δ l → Type δ (l′ ∷ Δ) l
  _[_]T : Type δ (l′ ∷ Δ) l → Type δ Δ l′ → Type δ Δ l
  _[_]ℓℓ : LimLvl (tt ∷ δ) → FinLvl δ → LimLvl δ
  _[_]ℓ : ∀ {l : LimLvl (tt ∷ δ)} → Type (tt ∷ δ) (wkₗₑ Δ) l → (newl : FinLvl δ) → Type δ Δ (l [ newl ]ℓℓ)

wkₗₜ : Type δ Δ l → Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ′ l)
wkₗₜ `ℕ = {!!}
wkₗₜ (T `⇒ T₁) = {!!}
wkₗₜ (` α) = {!!}
wkₗₜ (`∀α l , T) = {!`∀α_,_!}
wkₗₜ (`∀ℓ T) = {!`∀ℓ_!}

--! inn
data inn : Type δ Δ l → Ctx Δ → Set where
  here   : inn T (T ◁ Γ)
  there  : inn T Γ → inn T (T′ ◁ Γ)
  tskip  : inn T Γ → inn (Twk T) (l ◁* Γ)
  lskip  : inn T Γ → inn (wkₗₜ T) (◁ℓ Γ)


data Expr {δ} {Δ : Env δ} (Γ : Ctx Δ) : Type δ Δ l → Set where
  ##_    : (n : ℕ) → Expr Γ `ℕ
  `suc  : Expr Γ `ℕ → Expr Γ `ℕ
  `_    : ∀ {T : Type δ Δ l} → inn T Γ → Expr Γ T
  ƛ_    : ∀ {T : Type δ Δ l} {T′ : Type δ Δ l′} → Expr (T ◁ Γ) T′ → Expr Γ (T `⇒ T′)
  _·_   : ∀ {T : Type δ Δ l} {T′ : Type δ Δ l′} → Expr Γ (T `⇒ T′) → Expr Γ T → Expr Γ T′
  Λ_⇒_  : ∀ (l : LimLvl δ) → {T : Type δ (l ∷ Δ) l′} → Expr (l ◁* Γ) T → Expr Γ (`∀α l , T)
  _∙_    : ∀ {T : Type δ (l ∷ Δ) l′} → Expr Γ (`∀α l , T) → (T′ : Type δ Δ l) → Expr Γ (T [ T′ ]T)
  Λℓ_   : ∀ {T : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ′ l)} → Expr (◁ℓ Γ) T → Expr Γ (`∀ℓ T)
  _·ℓ_  : ∀ {T : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ′ l)} → Expr Γ (`∀ℓ T) → (newl : FinLvl δ) → Expr Γ (T [ newl ]ℓ)

variable e e₁ e₂ e₃ : Expr Γ T
variable n : ℕ

-- value environments

VEnv : {Δ : Env δ} → (d : DEnv δ) → Ctx Δ → Env* d Δ → Set
VEnv {δ} {Δ} d Γ η = ∀ l (T : Type δ Δ l) → (x : inn T Γ) → ⟦ T ⟧ᵀ d η

extend : ∀ {d : DEnv δ} {T : Type δ Δ l}{Γ : Ctx Δ}{η : Env* d Δ}
  → VEnv d Γ η → ⟦ T ⟧ᵀ d η → VEnv d (T ◁ Γ) η
extend γ v _ _ here = v
extend γ v _ _ (there x) = γ _ _ x

postulate
  extend-tskip : ∀ {d : DEnv δ} {Δ : Env δ} {Γ : Ctx Δ} {η : Env* d Δ} {⟦α⟧ : Uᵈ′ d l} →
    VEnv d Γ η → VEnv d (l ◁* Γ) (⟦α⟧ ∷ η)

  subst-env : ∀ {d : DEnv δ} (T : Type δ (l′ ∷ Δ) l) (T′ : Type δ Δ l′) (η : Env* d Δ) → ⟦ T ⟧ᵀ d (encode d T′ η ∷ η) ≡ ⟦ T [ T′ ]T ⟧ᵀ d η


E⟦_⟧ : ∀ {T : Type δ Δ l}{Γ : Ctx Δ} → (e : Expr Γ T) (d : DEnv δ) (η : Env* d Δ) → (γ : VEnv d Γ η) → ⟦ T ⟧ᵀ d η
E⟦ ## n ⟧ d η γ = n
E⟦ `suc x ⟧ d η γ = ℕ.suc (E⟦ x ⟧ d η γ)
E⟦ ` x ⟧ d η γ = γ _ _ x
E⟦ ƛ_ {l = l₁}{l′ = l₂}{T = T₁}{T′ = T₂} M ⟧ d η γ
  = λ x → let r = E⟦ M ⟧ d η (extend γ (coe (trans {!!} (ElLift≤ {Lᵈ′ d l₁} {Lᵈ′ d l₁ ⊔ Lᵈ′ d l₂} (⊔₁ (Lᵈ′ d l₁) (Lᵈ′ d l₂)) (encode d T₁ η))) x))
          in coe (sym (trans {!!} (ElLift≤ (⊔₂ (Lᵈ′ d l₁) (Lᵈ′ d l₂)) (encode d T₂ η)))) r
E⟦ _·_ {l = l}{l′ = l′}{T = T}{T′ = T′} M N ⟧ η γ =
  let f = E⟦ M ⟧ η γ ; a = E⟦ N ⟧ η γ in
  {!!}
--   coe (ElLift≤ (⊔₂ l l′) (encode T′ η)) (f (coe (sym (ElLift≤ (⊔₁ l l′) (encode T η))) a))
-- -- E⟦ M ⟧ η γ (E⟦ N ⟧ η γ)
-- E⟦ Λ_⇒_ {l′ = l′} l {T} M ⟧ η γ = λ α →
--   let η′ = coe (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) α ∷ η in
--   let r = E⟦ M ⟧ η′ (extend-tskip γ) in
--   coe (sym (ElLift≤ (⊔₂ (ℕ.suc l) l′) (encode T η′))) r
-- -- E⟦ M ⟧ (α ∷ η) (extend-tskip γ)
-- E⟦ _∙_ {l = l} {l′ = l′}{T = T} M T′ ⟧ η γ =
--   let F = E⟦ M ⟧ η γ in
--   let u′ = encode T′ η in
--   let eq1 = (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) in
--   let eq2 = Uⁱʳ & (ext (λ j → ext (λ p → trans (U<-compute {l} {wf} {j} {p}) (sym U<-compute)))) in
--   let r = F (coe eq2 u′) in
--   coe (trans (trans (cong (λ □ → Elⁱʳ (Lift≤ (⊔₂ (ℕ.suc l) l′) (encode T (□ ∷ η)))) (subst-subst' eq1 eq2 {u′}))
--                     (ElLift≤ (⊔₂ (ℕ.suc l) l′) (encode T (u′ ∷ η)))) (subst-env T T′ η)) r
