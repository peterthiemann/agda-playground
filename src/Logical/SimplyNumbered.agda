module SimplyNumbered where

open import Level using (Level) renaming (zero to lzero)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_⊔_ to _⊔ℕ_; _⊓_ to _⊓ℕ_; _≤_ to _≤ℕ_; _*_ to _*ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; *-zeroʳ; ≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.List using (List; []; _∷_; length; map; concat; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
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

≤M-refl : ∀ {x} → x ≤M x
≤M-refl {just x} = ≤-refl
≤M-refl {nothing} = tt

*M-zero-left : ∀ {x} → just 0 *M x ≡ just 0
*M-zero-left {just x} = refl
*M-zero-left {nothing} = refl

*M-zero-right : ∀ {x} → x *M just 0 ≡ just 0
*M-zero-right {just x} = cong just (*-zeroʳ x)
*M-zero-right {nothing} = refl

*M-identity-left : ∀ {x} → just 1 *M x ≡ x
*M-identity-left {just x} = cong just (+-identityʳ x)
*M-identity-left {nothing} = refl

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
  m0-left : ∀ {η} → MUL `- η `-
  m0-right : ∀ {η} → MUL η `- `-
  m1-left : ∀ {η} → MUL `! η η
  m1-right : ∀ {η} → MUL `! η η
  m2-diag : MUL `? `? `?
  m3-diag : MUL `+ `+ `+
  m4-diag : MUL `* `* `*
  m23     : MUL `? `+ `*
  m32     : MUL `+ `? `*
  m24     : MUL `? `* `*
  m42     : MUL `* `? `*
  m34     : MUL `+ `* `*
  m43     : MUL `* `+ `*
  
MUL-sound : ∀ η₁ η₂ {η} → MUL η₁ η₂ η → (𝓝⟦ η₁ ⟧ * 𝓝⟦ η₂ ⟧) ≤ 𝓝⟦ η ⟧
MUL-sound η₁ η₂ {η} m0-left rewrite *M-zero-left {𝓝⟦ η₂ ⟧ .Mul.hi} = z≤n , z≤n
MUL-sound η₁ η₂ {η} m0-right rewrite *M-zero-right {𝓝⟦ η₁ ⟧ .Mul.hi} = z≤n , z≤n
MUL-sound η₁ η₂ {η} m1-left rewrite +-identityʳ (𝓝⟦ η₂ ⟧ .Mul.lo) | *M-identity-left {𝓝⟦ η₂ ⟧ .Mul.hi} = ≤-refl , ≤M-refl
MUL-sound η₁ η₂ {η} m1-right rewrite +-identityʳ (𝓝⟦ η₂ ⟧ .Mul.lo) | *M-identity-left {𝓝⟦ η₂ ⟧ .Mul.hi} = ≤-refl , ≤M-refl
MUL-sound η₁ η₂ {η} m2-diag = z≤n , (s≤s z≤n)
MUL-sound η₁ η₂ {η} m3-diag = (s≤s z≤n) , tt
MUL-sound η₁ η₂ {η} m4-diag = z≤n , tt
MUL-sound η₁ η₂ {η} m23 = z≤n , tt
MUL-sound η₁ η₂ {η} m32 = z≤n , tt
MUL-sound η₁ η₂ {η} m24 = z≤n , tt
MUL-sound η₁ η₂ {η} m42 = z≤n , tt
MUL-sound η₁ η₂ {η} m34 = z≤n , tt
MUL-sound η₁ η₂ {η} m43 = z≤n , tt

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

lengthE : ∀ {S} → Expr S Mu → ℕ
lengthE [] = zero
lengthE (e ∷ e*) = suc (lengthE e*)

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

-- logical relation

𝓥⟦_⟧ : Ty → Pred (Expr [] Si) lzero
𝓦⟦_⟧ : NTy → Pred (Expr [] Mu) lzero
𝓔⟦_⟧ : NTy → Pred (Expr [] Mu) lzero

𝓥⟦ `⊥ ⟧ e = ⊥
𝓥⟦ □ ⟧ e = ∃[ n ] e ≡ cst n
𝓥⟦ μ ⇒ ημ ⟧ e = ∃[ μ₀ ]  ∃[ s ] e ≡ abs μ₀ s    × μ <:ₜ μ₀ × ∀ v → v ∈ 𝓥⟦ μ ⟧   → mapE (sub₁ v) s ∈ 𝓔⟦ ημ ⟧
𝓥⟦ ημ₁ ⇛ ημ₂ ⟧ e = ∃[ ημ₀ ] ∃[ s ] e ≡ mab ημ₀ s   × ημ₁ <:ₙ ημ₀ ×  ∀ w → w ∈ 𝓦⟦ ημ₁ ⟧ → mapE (sub₁ (lst w)) s ∈ 𝓔⟦ ημ₂ ⟧

𝓦⟦ ⟨ η , μ ⟩ ⟧ s  = ALL 𝓥⟦ μ ⟧ s × (lengthE s ∈∈ 𝓝⟦ η ⟧)

𝓔⟦ ημ ⟧ s          = ∃[ w ] w ∈ 𝓦⟦ ημ ⟧ × (s ⟶* w) 

-- typing contexts

data Ctx : List Sort → Set where
  ∅ : Ctx []
  _▻_ : ∀ {S} → NTy → Ctx S → Ctx (Si ∷ S)

lookup : ∀ {S} → Si ∈′ S → Ctx S → NTy
lookup (here refl) (ημ ▻ _) = ημ
lookup (there x) (_ ▻ Γ) = lookup x Γ

-- 𝓖⟦ Γ ⟧ characterizes substitutions σ: if x : ημ ∈ Γ then σ(x) ∈ 𝓦⟦ ημ ⟧

𝓖⟦_⟧ : ∀ {S} → Ctx S → Sub S [] → Set
𝓖⟦ ∅ ⟧ σ = ⊤
𝓖⟦ ημ ▻ Γ ⟧ σ = (∃[ w ] σ (here refl) ≡ lst w × w ∈ 𝓦⟦ ημ ⟧) × (σ ∘ there) ∈ 𝓖⟦ Γ ⟧

-- semantic typing
-- Γ ⊨ s : ημ <=> ∀ σ ∈ 𝓖⟦ Γ ⟧ . σ s ∈ 𝓔⟦ ημ ⟧

_⊨_⦂_ : ∀ {S} → Ctx S → Expr S Mu → NTy → Set
Γ ⊨ s ⦂ ημ = ∀ σ → σ ∈ 𝓖⟦ Γ ⟧ → {!sub σ (lst s)!} ∈ 𝓔⟦ ημ ⟧

-- syntactic typing

data _⊢_⦂_  {S} : ∀ {s} → Ctx S → Expr S s → NTy → Set where

  t-var : ∀ {Γ : Ctx S}{x} → Γ ⊢ var x ⦂ lookup x Γ

  t-abs : ∀ {Γ : Ctx S}{μ}{s}{ημ}
    → (⟨ `! , μ ⟩ ▻ Γ) ⊢ s ⦂ ημ
    → Γ ⊢ abs μ s  ⦂ ⟨ `! , (μ ⇒ ημ) ⟩

  t-mab : ∀ {Γ : Ctx S}{ημ}{s}{ημ′}
    → (ημ ▻ Γ) ⊢ s ⦂ ημ′
    → Γ ⊢ mab ημ s  ⦂ ⟨ `! , (ημ ⇛ ημ′) ⟩

  t-app-s : ∀ {Γ : Ctx S}{s₁}{s₂}{η₁ μ₁ η₂ μ₂ η₃ η η′}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ⟨ η₃ , μ₁ ⟩
    → MUL η₁ η₂ η′ → MUL η′ η₃ η
    → Γ ⊢ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩

  t-app-p : ∀ {Γ : Ctx S}{s₁}{s₂}{η₁ ημ η₂ μ₂ η}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ημ
    → MUL η₁ η₂ η
    → Γ ⊢ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩


  t-sub : ∀ {Γ : Ctx S}{e : Expr S Si}{ημ₁ ημ₂}
    → Γ ⊢ e ⦂ ημ₁
    → ημ₁ <:ₙ ημ₂
    → Γ ⊢ e  ⦂ ημ₂

  t-lst : ∀ {Γ : Ctx S}{s}{ημ}
    → Γ ⊢ s ⦂ ημ
    → Γ ⊢ lst s  ⦂ ημ

  t-empty : ∀ {Γ : Ctx S}{μ}
    → Γ ⊢ [] ⦂ ⟨ `- , μ ⟩

  t-head :  ∀ {Γ : Ctx S}{e}{s}{ηₑ ηₛ μ}
    → Γ ⊢ e ⦂ ⟨ ηₑ , μ ⟩
    → Γ ⊢ s ⦂ ⟨ ηₛ , μ ⟩
    → Γ ⊢ (e ∷ s) ⦂ ⟨ ADD ηₑ ηₛ , μ ⟩

-- Fundamental Theorem

-- Γ ⊢ s : ημ ⇒ Γ ⊨ s : ημ
