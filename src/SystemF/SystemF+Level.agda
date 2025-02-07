module SystemF+Level where

open import Level using (zero)
open import Data.Nat using ( ℕ; s≤s; z≤n; _<′_ ) renaming (_⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _<_ to _<ℕ_ )
open import Data.Nat.Properties using (+-identityʳ; +-suc; <-trans; <⇒<′)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; lookupAny)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function  using (id)

open import Lib
import IRUniverse as IR

module _ where
  open IR.ℕ*ℕ-example
  open IR.IR-Universe lvl

  import Data.Nat as N
  open import Data.Nat.Properties
  open import Data.Nat.Induction
  open Lexicographic N._<_ (λ _ → N._<_)

  postulate
    <-irrefl-ℕ*ℕ : Irreflexive _≡_ (Lexicographic._<_ _<ℕ_ (λ _ → _<ℕ_))

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
      (_<ℕ_ Lexicographic.< (λ _ → _<ℕ_)) i j ⊎
      (_<ℕ_ Lexicographic.< (λ _ → _<ℕ_)) j i ⊎ i ≡ j
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


  <-ext-ℕ*ℕ :  {i j : ℕ × ℕ} →
      ((k : ℕ × ℕ) →
       ((_<ℕ_ Lexicographic.< (λ _ → _<ℕ_)) k i →
        (_<ℕ_ Lexicographic.< (λ _ → _<ℕ_)) k j)
       ×
       ((_<ℕ_ Lexicographic.< (λ _ → _<ℕ_)) k j →
        (_<ℕ_ Lexicographic.< (λ _ → _<ℕ_)) k i)) →
      i ≡ j
  <-ext-ℕ*ℕ {i} {j} f
    with cmp-ℕ*ℕ i j
  ... | inj₁ x = ⊥-elim (<-irrefl-ℕ*ℕ refl (Σ.proj₂ (f i) x))
  ... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl-ℕ*ℕ refl (Σ.proj₁ (f j) x))
  ... | inj₂ (inj₂ refl) = refl

  ordinal-ℕ*ℕ : IR.Ordinal lvl
  ordinal-ℕ*ℕ = record { cmp = cmp-ℕ*ℕ ; <-ext = <-ext-ℕ*ℕ }

open IR.IR-Univ-Ordinal ordinal-ℕ*ℕ

-- variable l l′ l₁ l₂ l₃ : Lvl

--! TF >

-- ≤-trans : ∀ {i} {j} {k} → i ≤ j → j ≤ k → i ≤ k
-- ≤-trans (inj₁ i<j) (inj₁ j<k) = inj₁ (<-trans i<j j<k)
-- ≤-trans (inj₁ i<j) (inj₂ refl) = inj₁ i<j
-- ≤-trans (inj₂ refl) j≤k = j≤k

-- <≤-trans : ∀ {i} {j} {k} → i <ℕ j → j ≤ k → i <ℕ k
-- <≤-trans i<j (inj₁ j<k) = <-trans i<j j<k
-- <≤-trans i<j (inj₂ refl) = i<j

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


-- encode : (T : Type Δ l) → All U Δ → U l
-- encode `ℕ η = ℕ'
-- encode (_`⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂) η = (Lift≤ (⊔₁ l₁ l₂) (encode T₁ η)) ⇒' Lift≤ (⊔₂ l₁ l₂) (encode T₂ η)
-- encode (` α) η = lookup η α
-- encode (`∀α_,_ {l′ = l′} l T) η =
--   Π' (U' {j = l} (<≤-trans IR.ℕ-example.<suc (⊔₁ (ℕ.suc l) l′)))
--      λ u → Lift≤ (⊔₂ (ℕ.suc l) l′)
--         (encode T (coe  (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) u ∷ η))

-- Env* : LEnv → Set
-- Env* Δ = All U Δ

-- ⟦_⟧ᵀ : (T : Type Δ l) → (η : Env* Δ) → Set
-- ⟦ T ⟧ᵀ η = El (encode T η)


-- -- type environments
-- data Ctx : LEnv → Set where
--   ∅     : Ctx []
--   _◁_   : Type Δ l → Ctx Δ → Ctx Δ          
--   _◁*_  : (l : Lvl) → Ctx Δ → Ctx (l ∷ Δ) 

-- variable
--   Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Ctx Δ
--   T T′ : Type Δ l

-- postulate
--   Twk : Type Δ l → Type (l′ ∷ Δ) l
--   _[_]T : Type (l′ ∷ Δ) l → Type Δ l′ → Type Δ l

-- --! inn
-- data inn : Type Δ l → Ctx Δ → Set where
--   here   : inn T (T ◁ Γ)
--   there  : inn T Γ → inn T (T′ ◁ Γ)
--   tskip  : inn T Γ → inn (Twk T) (l ◁* Γ)


-- data Expr {Δ : LEnv} (Γ : Ctx Δ) : Type Δ l → Set where
--   #_    : (n : ℕ) → Expr Γ `ℕ
--   `suc  : Expr Γ `ℕ → Expr Γ `ℕ
--   `_    : ∀ {T : Type Δ l} → inn T Γ → Expr Γ T
--   ƛ_    : ∀ {T : Type Δ l} {T′ : Type Δ l′} → Expr (T ◁ Γ) T′ → Expr Γ (T `⇒ T′)
--   _·_   : ∀ {T : Type Δ l} {T′ : Type Δ l′} → Expr Γ (T `⇒ T′) → Expr Γ T → Expr Γ T′
--   Λ_⇒_  : ∀ (l : Lvl) → {T : Type (l ∷ Δ) l′} → Expr (l ◁* Γ) T → Expr Γ (`∀α l , T)
--   _∙_   : ∀ {T : Type (l ∷ Δ) l′} → Expr Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Γ (T [ T′ ]T)

-- variable e e₁ e₂ e₃ : Expr Γ T
-- variable n : ℕ

-- -- value environments

-- Env : {Δ : LEnv} → Ctx Δ → Env* Δ → Set
-- Env {Δ} Γ η = ∀ l (T : Type Δ l) → (x : inn T Γ) → ⟦ T ⟧ᵀ η

-- extend : ∀ {T : Type Δ l}{Γ : Ctx Δ}{η : Env* Δ}
--   → Env Γ η → ⟦ T ⟧ᵀ η → Env (T ◁ Γ) η
-- extend γ v _ _ here = v
-- extend γ v _ _ (there x) = γ _ _ x

-- postulate
--   extend-tskip : ∀ {Δ : LEnv} {Γ : Ctx Δ} {η : Env* Δ} {⟦α⟧ : U l} →
--     Env Γ η → Env (l ◁* Γ) (⟦α⟧ ∷ η)

--   subst-env : ∀ (T : Type (l′ ∷ Δ) l) (T′ : Type Δ l′) (η : Env* Δ) → ⟦ T ⟧ᵀ (encode T′ η ∷ η) ≡ ⟦ T [ T′ ]T ⟧ᵀ η


-- E⟦_⟧ : ∀ {T : Type Δ l}{Γ : Ctx Δ} → (e : Expr Γ T) → (η : Env* Δ) → (γ : Env Γ η) → ⟦ T ⟧ᵀ η
-- E⟦ # n ⟧ η γ = n
-- E⟦ `suc x ⟧ η γ = ℕ.suc (E⟦ x ⟧ η γ)
-- E⟦ ` x ⟧ η γ = γ _ _ x
-- E⟦ ƛ_ {l = l}{l′ = l′}{T = T}{T′ = T′} M ⟧ η γ =
--   λ x → let r = E⟦ M ⟧ η (extend γ (coe (ElLift≤ {l}{l ⊔ l′} (⊔₁ l l′) (encode T η)) x)) in
--         coe (sym (ElLift≤ (⊔₂ l l′) (encode T′ η))) r
-- -- λ x → E⟦ M ⟧ η (extend γ x)
-- E⟦ _·_ {l = l}{l′ = l′}{T = T}{T′ = T′} M N ⟧ η γ =
--   let f = E⟦ M ⟧ η γ ; a = E⟦ N ⟧ η γ in
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
