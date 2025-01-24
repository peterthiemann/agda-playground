module SystemF where

open import Level using (zero)
open import Data.Nat using ( ℕ; s≤s; z≤n; _<′_ ) renaming (_⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _<_ to _<ℕ_ )
open import Data.Nat.Properties using (+-identityʳ; +-suc; <-trans; <⇒<′)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; lookupAny)
open import Function  using (id)

open import Lib
import IRUniverse as IR

module _ where
  open IR.ℕ-example
  open IR.IR-Universe lvl

  cmp-ℕ : (i j : ℕ) → i <ℕ j ⊎ j <ℕ i ⊎ i ≡ j
  cmp-ℕ ℕ.zero ℕ.zero = inj₂ (inj₂ refl)
  cmp-ℕ ℕ.zero (ℕ.suc j) = inj₁ (s≤s z≤n)
  cmp-ℕ (ℕ.suc i) ℕ.zero = inj₂ (inj₁ (s≤s z≤n))
  cmp-ℕ (ℕ.suc i) (ℕ.suc j)
    with cmp-ℕ i j
  ... | inj₁ x = inj₁ (s≤s x)
  ... | inj₂ (inj₁ x) = inj₂ (inj₁ (s≤s x))
  ... | inj₂ (inj₂ y) = inj₂ (inj₂ (ℕ.suc & y))

  ≤-suc : ∀ {i j} → ℕ.suc i <ℕ ℕ.suc j → i <ℕ j
  ≤-suc (s≤s p) = p

  <-ext-ℕ : {i j : ℕ} → ((k : ℕ) → (k <ℕ i → k <ℕ j) × (k <ℕ j → k <ℕ i)) → i ≡ j
  <-ext-ℕ {ℕ.zero} {ℕ.zero} f = refl
  <-ext-ℕ {ℕ.zero} {ℕ.suc j} f
    with f ℕ.zero
  ... | x , y
    with y (s≤s z≤n)
  ... | ()
  <-ext-ℕ {ℕ.suc i} {ℕ.zero} f
    with f ℕ.zero
  ... | x , y
    with x (s≤s z≤n)
  ... | ()
  <-ext-ℕ {ℕ.suc i} {ℕ.suc j} f =
    ℕ.suc & (<-ext-ℕ {i} {j} (λ k → let x , y = f (ℕ.suc k) in
                                    (λ{ x₁ → ≤-suc (x (s≤s x₁))}) ,
                                    (λ x₁ → ≤-suc (y (s≤s x₁)))))

  ordinal-ℕ : IR.Ordinal lvl
  ordinal-ℕ = record { cmp = cmp-ℕ ; <-ext = <-ext-ℕ }

open IR.IR-Univ-Ordinal ordinal-ℕ

variable l l′ l₁ l₂ l₃ : Lvl

--! TF >

≤-trans : ∀ {i} {j} {k} → i ≤ j → j ≤ k → i ≤ k
≤-trans (inj₁ i<j) (inj₁ j<k) = inj₁ (<-trans i<j j<k)
≤-trans (inj₁ i<j) (inj₂ refl) = inj₁ i<j
≤-trans (inj₂ refl) j≤k = j≤k

<≤-trans : ∀ {i} {j} {k} → i <ℕ j → j ≤ k → i <ℕ k
<≤-trans i<j (inj₁ j<k) = <-trans i<j j<k
<≤-trans i<j (inj₂ refl) = i<j

-- level environments

--! LEnv
LEnv = List Lvl

variable Δ Δ₁ Δ₂ Δ₃ : LEnv

-- type variables

Δ-level : LEnv → Lvl
Δ-level [] = 0
Δ-level (x ∷ Δ) = ℕ.suc x ⊔ Δ-level Δ

-- types

--! Type
data Type Δ : Lvl → Set where
  `ℕ      : Type Δ ℕ.zero
  _`⇒_    : (T₁ : Type Δ l₁) (T₂ : Type Δ l₂) → Type Δ (l₁ ⊔ l₂)
  `_      : (α : l ∈ Δ) → Type Δ l
  `∀α_,_  : (l : Lvl) (T : Type (l ∷ Δ) l′) → Type Δ (ℕ.suc l ⊔ l′)

-- this encoding does not work
-- encode : Type Δ l → All (λ i → U i) Δ → U l
-- encode `ℕ η = ℕ'
-- encode (T₁ `⇒ T₂) η = Π'' (encode T₁ η) (λ _ → encode T₂ η)
-- encode (` α) η = lookup η α
-- encode {Δ = Δ} (`∀α i , T) η =
--   Π'' (U' {ℕ.suc i} IR.ℕ-example.<suc) λ α → encode {Δ = i ∷ Δ} T ({!!} ∷ η)

top-level-of : Type Δ l → Lvl
top-level-of `ℕ = 0
top-level-of (T `⇒ T₁) = 0
top-level-of (` α) = 0
top-level-of (`∀α l , T) = l

encode : (T : Type Δ l) → All U Δ → U l
encode `ℕ η = ℕ'
encode (_`⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂) η = (Lift≤ (⊔₁ l₁ l₂) (encode T₁ η)) ⇒' Lift≤ (⊔₂ l₁ l₂) (encode T₂ η)
encode (` α) η = lookup η α
encode (`∀α_,_ {l′ = l′} l T) η =
  Π' (U' {j = l} (<≤-trans IR.ℕ-example.<suc (⊔₁ (ℕ.suc l) l′)))
     λ u → Lift≤ (⊔₂ (ℕ.suc l) l′)
         (encode T (subst Uⁱʳ (ext (λ j → ext (λ p → cong (λ acc → (U< {l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) u ∷ η))
--         (encode T (coe {!U<-compute!} u ∷ η))

Env* : LEnv → Set
Env* Δ = All U Δ

⟦_⟧ᵀ : (T : Type Δ l) → (η : All U Δ) → Set
⟦ T ⟧ᵀ η = El (encode T η)

-- ⟦_⟧ᵀ : (T : Type Δ l) → (η : All U Δ) → Set
-- ⟦ `ℕ ⟧ᵀ η = ℕ
-- ⟦ T₁ `⇒ T₂ ⟧ᵀ η = ⟦ T₁ ⟧ᵀ η → ⟦ T₂ ⟧ᵀ η
-- ⟦ ` α ⟧ᵀ η = El (lookup η α)
-- ⟦ `∀α l , T ⟧ᵀ η = (α : U l) → ⟦ T ⟧ᵀ (α ∷ η)


-- type environments
data Ctx : LEnv → Set where
  ∅     : Ctx []
  _◁_   : Type Δ l → Ctx Δ → Ctx Δ          
  _◁*_  : (l : Lvl) → Ctx Δ → Ctx (l ∷ Δ) 

variable
  Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Ctx Δ
  T T′ : Type Δ l

postulate
  Twk : Type Δ l → Type (l′ ∷ Δ) l
  _[_]T : Type (l′ ∷ Δ) l → Type Δ l′ → Type Δ l

--! inn
data inn : Type Δ l → Ctx Δ → Set where
  here   : inn T (T ◁ Γ)
  there  : inn T Γ → inn T (T′ ◁ Γ)
  tskip  : inn T Γ → inn (Twk T) (l ◁* Γ)


data Expr {Δ : LEnv} (Γ : Ctx Δ) : Type Δ l → Set where
  #_    : (n : ℕ) → Expr Γ `ℕ
  `suc  : Expr Γ `ℕ → Expr Γ `ℕ
  `_    : ∀ {T : Type Δ l} → inn T Γ → Expr Γ T
  ƛ_    : ∀ {T : Type Δ l} {T′ : Type Δ l′} → Expr (T ◁ Γ) T′ → Expr Γ (T `⇒ T′)
  _·_   : ∀ {T : Type Δ l} {T′ : Type Δ l′} → Expr Γ (T `⇒ T′) → Expr Γ T → Expr Γ T′
  Λ_⇒_  : ∀ (l : Lvl) → {T : Type (l ∷ Δ) l′} → Expr (l ◁* Γ) T → Expr Γ (`∀α l , T)
  _∙_   : ∀ {T : Type (l ∷ Δ) l′} → Expr Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Γ (T [ T′ ]T)

variable e e₁ e₂ e₃ : Expr Γ T
variable n : ℕ

-- value environments

Env : {Δ : LEnv} → Ctx Δ → Env* Δ → Set
Env {Δ} Γ η = ∀ l (T : Type Δ l) → (x : inn T Γ) → ⟦ T ⟧ᵀ η

extend : ∀ {T : Type Δ l}{Γ : Ctx Δ}{η : Env* Δ}
  → Env Γ η → ⟦ T ⟧ᵀ η → Env (T ◁ Γ) η
extend γ v _ _ here = v
extend γ v _ _ (there x) = γ _ _ x

postulate
  extend-tskip : ∀ {Δ : LEnv} {Γ : Ctx Δ} {η : Env* Δ} {⟦α⟧ : U l} →
    Env Γ η → Env (l ◁* Γ) (⟦α⟧ ∷ η)


E⟦_⟧ : ∀ {T : Type Δ l}{Γ : Ctx Δ} → (e : Expr Γ T) → (η : Env* Δ) → (γ : Env Γ η) → ⟦ T ⟧ᵀ η
E⟦ # n ⟧ η γ = n
E⟦ `suc x ⟧ η γ = ℕ.suc (E⟦ x ⟧ η γ)
E⟦ ` x ⟧ η γ = γ _ _ x
E⟦ ƛ_ {l = l}{l′ = l′}{T = T}{T′ = T′} M ⟧ η γ =
  λ x → let r = E⟦ M ⟧ η (extend γ (coe (ElLift≤ {l}{l ⊔ l′} (⊔₁ l l′) (encode T η)) x)) in
        coe (sym (ElLift≤ (⊔₂ l l′) (encode T′ η))) r
-- λ x → E⟦ M ⟧ η (extend γ x)
E⟦ _·_ {l = l}{l′ = l′}{T = T}{T′ = T′} M N ⟧ η γ =
  let f = E⟦ M ⟧ η γ ; a = E⟦ N ⟧ η γ in
  coe (ElLift≤ (⊔₂ l l′) (encode T′ η)) (f (coe (sym (ElLift≤ (⊔₁ l l′) (encode T η))) a))
-- E⟦ M ⟧ η γ (E⟦ N ⟧ η γ)
E⟦ Λ_⇒_ {l′ = l′} l {T} M ⟧ η γ = λ α →
  let η′ = subst Uⁱʳ (ext (λ j → ext (λ p → cong (λ acc → (U< {l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) α ∷ η in
  let r = E⟦ M ⟧ η′ (extend-tskip γ) in
  coe (sym (ElLift≤ (⊔₂ (ℕ.suc l) l′) (encode T η′))) r
-- E⟦ M ⟧ (α ∷ η) (extend-tskip γ)
E⟦ _∙_ {l = l} M T′ ⟧ η γ =
  let F = E⟦ M ⟧ η γ ; u′ = encode T′ η in
  let r = F (coe (cong Uⁱʳ (ext (λ j → ext (λ p → {!!})))) u′) in
  {! !}
