module SimplyNumbered where

open import Level using (Level) renaming (zero to lzero)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_⊔_ to _⊔ℕ_; _⊓_ to _⊓ℕ_; _≤_ to _≤ℕ_; _*_ to _*ℕ_; _+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.List using (List; []; _∷_; length; map; concat; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)

-- intervals on natural numbers

record Mul : Set where
  constructor ⟪_,_⟫
  field
    lo : ℕ
    hi : Maybe ℕ

_∈∈_ : ℕ → Mul → Set
n ∈∈ ⟪ lo , just hi ⟫ = lo ≤ℕ n × n ≤ℕ hi
n ∈∈ ⟪ lo , nothing ⟫ = lo ≤ℕ n

_⊔M_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
just x ⊔M just x₁ = just (x ⊔ℕ x₁)
just x ⊔M nothing = just x
nothing ⊔M x₁ = x₁

_≤M_ : Maybe ℕ → Maybe ℕ → Set
x ≤M nothing = ⊤
just x ≤M just x₁ = x ≤ℕ x₁
nothing ≤M just x₁ = ⊥

_*M_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
just x *M just x₁ = just (x *ℕ x₁)
just zero *M nothing = just zero
just (suc x) *M nothing = nothing
nothing *M just zero = just zero
nothing *M just (suc x) = nothing
nothing *M nothing = nothing

_+M_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
just x +M just x₁ = just (x +ℕ x₁)
just x +M nothing = nothing
nothing +M x₁ = nothing


_⊔_ : Mul → Mul → Mul
⟪ lo , hi ⟫ ⊔ ⟪ lo₁ , hi₁ ⟫ = ⟪ lo ⊓ℕ lo₁ , hi ⊔M hi₁ ⟫

_≤_ : Mul → Mul → Set
⟪ lo , hi ⟫ ≤ ⟪ lo₁ , hi₁ ⟫ = lo₁ ≤ℕ lo × (hi ≤M hi₁)

_*_ : Mul → Mul → Mul
⟪ lo , hi ⟫ * ⟪ lo₁ , hi₁ ⟫ = ⟪ lo *ℕ lo₁ , hi *M hi₁ ⟫

_+_ : Mul → Mul → Mul
⟪ lo , hi ⟫ + ⟪ lo₁ , hi₁ ⟫ = ⟪ lo +ℕ lo₁ , hi +M hi₁ ⟫

-- numeri

data Num : Set where
  `- `! `? `* `+ : Num

𝓝⟦_⟧ : Num → Mul
𝓝⟦ `- ⟧ = ⟪ 0 , just 0 ⟫
𝓝⟦ `! ⟧ = ⟪ 1 , just 1 ⟫
𝓝⟦ `? ⟧ = ⟪ 0 , just 1 ⟫
𝓝⟦ `* ⟧ = ⟪ 0 , nothing ⟫
𝓝⟦ `+ ⟧ = ⟪ 1 , nothing ⟫

ADD : Num → Num → Num
ADD `- y = y
ADD `! `- = `!
ADD `! `! = `+
ADD `! `? = `+
ADD `! `* = `+
ADD `! `+ = `+
ADD `? `- = `?
ADD `? `! = `+
ADD `? `? = `*
ADD `? `* = `*
ADD `? `+ = `+
ADD `* `- = `*
ADD `* `! = `+
ADD `* `? = `*
ADD `* `* = `*
ADD `* `+ = `+
ADD `+ `- = `+
ADD `+ `! = `+
ADD `+ `? = `+
ADD `+ `* = `+
ADD `+ `+ = `+

ADD-sound : (η₁ η₂ : Num) → (𝓝⟦ η₁ ⟧ + 𝓝⟦ η₂ ⟧) ≤ 𝓝⟦ ADD η₁ η₂ ⟧
ADD-sound `- `- = z≤n , z≤n
ADD-sound `- `! = (s≤s z≤n) , (s≤s z≤n)
ADD-sound `- `? = z≤n , (s≤s z≤n)
ADD-sound `- `* = z≤n , tt
ADD-sound `- `+ = s≤s z≤n , tt
ADD-sound `! `- = s≤s z≤n , s≤s z≤n
ADD-sound `! `! = s≤s z≤n , tt
ADD-sound `! `? = s≤s z≤n , tt
ADD-sound `! `* = s≤s z≤n , tt
ADD-sound `! `+ = s≤s z≤n , tt
ADD-sound `? `- = z≤n , s≤s z≤n
ADD-sound `? `! = s≤s z≤n , tt
ADD-sound `? `? = z≤n , tt
ADD-sound `? `* = z≤n , tt
ADD-sound `? `+ = s≤s z≤n , tt
ADD-sound `* `- = z≤n , tt
ADD-sound `* `! = s≤s z≤n , tt
ADD-sound `* `? = z≤n , tt
ADD-sound `* `* = z≤n , tt
ADD-sound `* `+ = s≤s z≤n , tt
ADD-sound `+ `- = s≤s z≤n , tt
ADD-sound `+ `! = s≤s z≤n , tt
ADD-sound `+ `? = s≤s z≤n , tt
ADD-sound `+ `* = s≤s z≤n , tt
ADD-sound `+ `+ = s≤s z≤n , tt

data MUL : Num → Num → Num → Set where
  
MUL-sound : ∀ η₁ η₂ {η} → MUL η₁ η₂ η → (𝓝⟦ η₁ ⟧ * 𝓝⟦ η₂ ⟧) ≤ 𝓝⟦ η ⟧
MUL-sound η₁ η₂ {η} mul = {!!}

-- types

data Ty : Set

record NTy : Set where
  inductive
  constructor ⟨_,_⟩
  field
    num : Num
    ty  : Ty

data Ty where
  `⊥ : Ty
  □ : Ty
  _⇒_ : Ty → NTy → Ty
  _⇛_ : NTy → NTy → Ty

-- subtyping

data _<:ₙ_ : NTy → NTy → Set
data _<:ₜ_ : Ty → Ty → Set where
  <:ₜ-⊥ : ∀ {μ} → `⊥ <:ₜ μ
  <:ₜ-□ : □ <:ₜ □
  <:ₜ-⇒ : ∀ {μ₁ μ₂} {ημ₁ ημ₂} → μ₂ <:ₜ μ₁ → ημ₁ <:ₙ ημ₂ → (μ₁ ⇒ ημ₁) <:ₜ (μ₂ ⇒ ημ₂)
  <:ₜ-⇛ : ∀ {ημ₁ ημ₂ ημ₁′ ημ₂′} → ημ₁ <:ₙ ημ₁′ → ημ₂′ <:ₙ ημ₂ → (ημ₁′ ⇛ ημ₂′) <:ₜ (ημ₁ ⇛ ημ₂)

data _<:ₙ_ where
  <:ₙ-comb : ∀ {μ₁ μ₂} {η₁ η₂} → 𝓝⟦ η₁ ⟧ ≤ 𝓝⟦ η₂ ⟧ → μ₁ <:ₜ μ₂ →  ⟨ η₁ , μ₁ ⟩ <:ₙ ⟨ η₂ , μ₂ ⟩

--- expressions

module new-alternative where
  
  data Sort : Set where
    Si : Sort                    -- single
    Mu : Sort                    -- multiple

  data Expr (S : List Sort) : Sort → Set where
    []  : Expr S Mu
    _∷_ : Expr S Si → Expr S Mu → Expr S Mu
    var : Si ∈′ S → Expr S Si
    cst : ℕ → Expr S Si
    abs : Ty → Expr (Si ∷ S) Mu → Expr S Si
    mab : NTy → Expr (Si ∷ S) Mu → Expr S Si
    app : Expr S Mu → Expr S Mu → Expr S Si
    lst : Expr S Mu → Expr S Si

  data Value (S : List Sort) : ∀ {s} → Expr S s → Set where
    []  : Value S []
    _∷_ : ∀ {v}{w} → Value S v → Value S w → Value S (v ∷ w)
    cst : ∀ {k} → Value S (cst k)
    abs : ∀ {μ}{e*} → Value S (abs μ e*)
    mab : ∀ {ημ}{e*} → Value S (mab ημ e*)

  data AbsValue {S} : Expr S Si → Set where
    v-abs : ∀ μ e* → AbsValue (abs μ e*)

  data MabValue {S} : Expr S Si → Set where
    v-mab : ∀ ημ e* → MabValue (mab ημ e*)

  data ALL {S} (P : Expr S Si → Set) : Expr S Mu → Set where
    [] : ALL P []
    _∷_ : ∀ {e}{e*} → P e → ALL P e* → ALL P (e ∷ e*)

  absbody : ∀ {S}{e : Expr S Si} → AbsValue e → Expr (Si ∷ S) Mu
  absbody (v-abs μ s) = s

  mabbody : ∀ {S}{e : Expr S Si} → MabValue e → Expr (Si ∷ S) Mu
  mabbody (v-mab ημ s) = s

  mapALL : ∀ {S₁ S₂} {xs : Expr S₁ Mu} {P : Pred (Expr S₁ Si) lzero} → (∀ {x} → P x → Expr S₂ Mu) → ALL P xs → Expr S₂ Mu
  mapALL f [] = []
  mapALL f (px ∷ allx) = lst (f px) ∷ mapALL f allx

  Sub : List Sort → List Sort → Set
  Sub S₁ S₂ = Si ∈′ S₁ → Expr S₂ Si

  postulate
    sub  : ∀ {S₁ S₂} → Sub S₁ S₂ → Expr S₁ Si → Expr S₂ Si

  sub₁ : ∀ {S} → Expr S Si → Expr (Si ∷ S) Si → Expr S Si
  sub₁ {S} e₁ e₂ = sub σ e₂
    where
      σ : Sub (Si ∷ S) S
      σ (here refl) = e₁
      σ (there x) = var x

  -- small step operational semantics

  mapE : ∀ {S₁ S₂} → (Expr S₁ Si → Expr S₂ Si) → Expr S₁ Mu → Expr S₂ Mu
  mapE f [] = []
  mapE f (x ∷ xs) = f x ∷ mapE f xs

  _++E_ : ∀ {S} → Expr S Mu → Expr S Mu → Expr S Mu
  [] ++E e₂* = e₂*
  (e₁ ∷ e₁*) ++E e₂* = e₁ ∷ (e₁* ++E e₂*)

  data _⟶_ : ∀ {s} → Expr [] s → Expr [] s → Set where

    ξ-app₁ : ∀ {s₁}{s₁′}{s₂}
      → s₁ ⟶ s₁′
      → app s₁ s₂ ⟶ app s₁′ s₂

    ξ-app₂ : ∀ {s₁}{s₂}{s₂′}
      → Value [] s₁
      → s₂ ⟶ s₂′
      → app s₁ s₂ ⟶ app s₁ s₂′

    β₁ : ∀ {s}{w}
      → (abs₁ : ALL AbsValue s)
      → Value [] w
      → app s w ⟶ lst (mapE (λ v → lst (mapE (λ b → sub₁ v b) (mapALL absbody abs₁))) w)

    βₙ : ∀ {s}{w}
      → (mab₁ : ALL MabValue s)
      → Value [] w
      → app s w ⟶ lst (mapE (λ b → sub₁ (lst w) b) (mapALL mabbody mab₁))

    ξ-head : ∀ {e}{e′}{s}
      → e ⟶ e′
      → (e ∷ s) ⟶ (e′ ∷ s)

    ξ-flat : ∀ {s₁}{s₂}
      → (lst s₁ ∷ s₂) ⟶ (s₁ ++E s₂)

    ξ-tail : ∀ {e}{s}{s′}
      → Value [] e
      → s ⟶ s′
      → (e ∷ s) ⟶ (e ∷ s′)

  data _⟶*_ {s} : Expr [] s → Expr [] s → Set where
    ⟶-refl : ∀ {e*} → e* ⟶* e*
    ⟶-step : ∀ {e₁* e₂* e₃*} → e₁* ⟶ e₂* → e₂* ⟶* e₃* → e₁* ⟶* e₃*


data Expr : ℕ → Set where
  var : ∀ {n} → Fin n → Expr n
  cst : ∀ {n} → ℕ → Expr n
  abs : ∀ {n} → Ty → List (Expr (suc n)) → Expr n
  mab : ∀ {n} → NTy → List (Expr (suc n)) → Expr n
  app : ∀ {n} → List (Expr n) → List (Expr n) → Expr n
  lst : ∀ {n} → List (Expr n) → Expr n

  

data Value {n} : Expr n → Set where
  cst : ∀ {k} → Value (cst k)
  abs : ∀ {μ}{s} → Value (abs μ s)
  mab : ∀ {ημ}{s} → Value (mab ημ s)


data AbsValue {n} : Expr n → Set where
  v-abs : ∀ μ s → AbsValue (abs μ s)

data MabValue {n} : Expr n → Set where
  v-mab : ∀ ημ s → MabValue (mab ημ s)

absbody : ∀ {n}{e : Expr n} → AbsValue e → List (Expr (suc n))
absbody (v-abs μ s) = s

mabbody : ∀ {n}{e : Expr n} → MabValue e → List (Expr (suc n))
mabbody (v-mab ημ s) = s

mapAll : {A : Set}{B : Set} {xs : List A} {P : Pred A lzero} → (∀ {x} → P x → B) → All P xs → List B
mapAll f [] = []
mapAll f (px ∷ allx) = f px ∷ mapAll f allx

-- substitution

Sub : ℕ → ℕ → Set
Sub m n = Fin m → List (Expr n)

postulate
  sub  : ∀ {m}{n} → Sub m n → List (Expr m) → List (Expr n)
  sub₁ : ∀ {n} → Expr n → Expr (suc n) → Expr n
  subₙ : ∀ {n} → List (Expr n) → Expr (suc n) → Expr n

-- small step operational semantics

data _⟶_ {n} : List (Expr n) → List(Expr n) → Set
data _₁⟶₁_ {n} : Expr n → Expr n → Set where

  ξ-app₁ : ∀ {s₁}{s₁′}{s₂}
    → s₁ ⟶ s₁′
    → app s₁ s₂ ₁⟶₁ app s₁′ s₂

  ξ-app₂ : ∀ {s₁}{s₂}{s₂′}
    → All Value s₁
    → s₂ ⟶ s₂′
    → app s₁ s₂ ₁⟶₁ app s₁ s₂′

  β₁ : ∀ {s}{w}
    → (abs₁ : All AbsValue s)
    → All Value w
    → app s w ₁⟶₁ lst (map (λ v → lst (map (lst ∘ map (sub₁ v)) (mapAll absbody abs₁))) w)

  βₙ : ∀ {s}{w}
    → (mab₁ : All MabValue s)
    → All Value w
    → app s w ₁⟶₁ lst (map (λ f → lst (map (sub₁ (lst w)) f)) (mapAll mabbody mab₁))

data _⟶_ {n} where

  ξ-head : ∀ {e}{e′}{s}
    → e ₁⟶₁ e′
    → (e ∷ s) ⟶ (e′ ∷ s)

  ξ-flat : ∀ {s₁}{s₂}
    → (lst s₁ ∷ s₂) ⟶ (s₁ ++ s₂)

  ξ-tail : ∀ {e}{s}{s′}
    → Value e
    → s ⟶ s′
    → (e ∷ s) ⟶ (e ∷ s′)
  

data _⟶*_ {n} : List (Expr n) → List (Expr n) → Set where
  ⟶-refl : ∀ {e* : List (Expr n)} → e* ⟶* e*
  ⟶-step : ∀ {e₁* e₂* e₃* : List (Expr n)} → e₁* ⟶ e₂* → e₂* ⟶* e₃* → e₁* ⟶* e₃*

-- logical relation

𝓥⟦_⟧ : Ty → Pred (Expr zero) lzero
𝓦⟦_⟧ : NTy → Pred (List (Expr zero)) lzero
𝓔⟦_⟧ : NTy → Pred (List (Expr zero)) lzero

𝓥⟦ `⊥ ⟧ e          = ⊥
𝓥⟦ □ ⟧ e          = ∃[ n ] e ≡ cst n
𝓥⟦ μ₁ ⇒ ημ₂ ⟧ e   = ∃[ μ₀ ]  ∃[ s ] e ≡ abs μ₀ s    × μ₁ <:ₜ μ₀   ×  ∀ v → v ∈ 𝓥⟦ μ₁ ⟧   → map (sub₁ v) s ∈ 𝓔⟦ ημ₂ ⟧ 
𝓥⟦ ημ₁ ⇛ ημ₂ ⟧ e  = ∃[ ημ₀ ] ∃[ s ] e ≡ mab ημ₀ s   × ημ₁ <:ₙ ημ₀ ×  ∀ w → w ∈ 𝓦⟦ ημ₁ ⟧ → map (subₙ w) s ∈ 𝓔⟦ ημ₂ ⟧

𝓦⟦ ⟨ η , μ ⟩ ⟧ s  = All 𝓥⟦ μ ⟧ s × (length s ∈∈ 𝓝⟦ η ⟧)

𝓔⟦ ημ ⟧ s          = ∃[ w ] w ∈ 𝓦⟦ ημ ⟧ × (s ⟶* w) 

-- typing contexts

data Ctx : ℕ → Set where
  ∅ : Ctx zero
  _▻_ : ∀ {n} → NTy → Ctx n → Ctx (suc n)

lookup : ∀ {n} → Fin n → Ctx n → NTy
lookup Fin.zero (ημ ▻ _) = ημ
lookup (Fin.suc x) (_ ▻ Γ) = lookup x Γ

-- 𝓖⟦ Γ ⟧ characterizes substitutions σ: if x : ημ ∈ Γ then σ(x) ∈ 𝓦⟦ ημ ⟧

𝓖⟦_⟧ : ∀ {n} → Ctx n → Sub n zero → Set
𝓖⟦ ∅ ⟧ σ = ⊤
𝓖⟦ ημ ▻ Γ ⟧ σ = σ Fin.zero ∈ 𝓦⟦ ημ ⟧ × (σ ∘ Fin.suc) ∈ 𝓖⟦ Γ ⟧

-- semantic typing
-- Γ ⊨ s : ημ <=> ∀ σ ∈ 𝓖⟦ Γ ⟧ . σ s ∈ 𝓔⟦ ημ ⟧

_⊨_⦂_ : ∀ {n} → Ctx n → List (Expr n) → NTy → Set
Γ ⊨ s ⦂ ημ = ∀ σ → σ ∈ 𝓖⟦ Γ ⟧ → sub σ s ∈ 𝓔⟦ ημ ⟧

-- syntactic typing

data _⊢_⦂_  {n} : Ctx n → List (Expr n) → NTy → Set
data _⊢₁_⦂_  {n} : Ctx n → Expr n → NTy → Set where

  t-var : ∀ {Γ : Ctx n}{x} → Γ ⊢₁ var x ⦂ lookup x Γ

  t-abs : ∀ {Γ : Ctx n}{μ}{s}{ημ}
    → (⟨ `! , μ ⟩ ▻ Γ) ⊢ s ⦂ ημ
    → Γ ⊢₁ abs μ s  ⦂ ⟨ `! , (μ ⇒ ημ) ⟩

  t-mab : ∀ {Γ : Ctx n}{ημ}{s}{ημ′}
    → (ημ ▻ Γ) ⊢ s ⦂ ημ′
    → Γ ⊢₁ mab ημ s  ⦂ ⟨ `! , (ημ ⇛ ημ′) ⟩

  -- is this needed in presence of a general subsumption rule?
  -- t-app-e : ∀ {Γ : Ctx n}{s₁}{s₂}{ημ}
  --   → Γ ⊢ s₁ ⦂ ⟨ `- , `⊥ ⟩
  --   → Γ ⊢ s₂ ⦂ ημ
  --   → Γ ⊢₁ app s₁ s₂  ⦂ ⟨ `- , `⊥ ⟩

  t-app-s : ∀ {Γ : Ctx n}{s₁}{s₂}{η₁ μ₁ η₂ μ₂ η₃ η η′}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ⟨ η₃ , μ₁ ⟩
    → MUL η₁ η₂ η′ → MUL η′ η₃ η
    → Γ ⊢₁ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩

  t-app-p : ∀ {Γ : Ctx n}{s₁}{s₂}{η₁ ημ η₂ μ₂ η}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ημ
    → MUL η₁ η₂ η
    → Γ ⊢₁ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩

  t-sub : ∀ {Γ : Ctx n}{e}{ημ₁ ημ₂}
    → Γ ⊢₁ e ⦂ ημ₁
    → ημ₁ <:ₙ ημ₂
    → Γ ⊢₁ e  ⦂ ημ₂

  t-lst : ∀ {Γ : Ctx n}{s}{ημ}
    → Γ ⊢ s ⦂ ημ
    → Γ ⊢₁ lst s  ⦂ ημ
  
data _⊢_⦂_  {n} where

  t-empty : ∀ {Γ : Ctx n}{μ}
    → Γ ⊢ [] ⦂ ⟨ `- , μ ⟩

  t-head :  ∀ {Γ : Ctx n}{e}{s}{ηₑ ηₛ μ}
    → Γ ⊢₁ e ⦂ ⟨ ηₑ , μ ⟩
    → Γ ⊢ s ⦂ ⟨ ηₛ , μ ⟩
    → Γ ⊢ (e ∷ s) ⦂ ⟨ ADD ηₑ ηₛ , μ ⟩


-- Fundamental Theorem

-- Γ ⊢ s : ημ ⇒ Γ ⊨ s : ημ
