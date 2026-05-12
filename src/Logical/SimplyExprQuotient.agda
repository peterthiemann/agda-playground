module SimplyExprQuotient where

open import Level using (Level) renaming (zero to lzero)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Function using (_∘_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Interval

open import Numeri
open import Types

-- expressions

variable m n : ℕ

data Expr (n : ℕ) : Set where
  ε   : Expr n
  _·_ : Expr n → Expr n → Expr n
  var : Fin n → Expr n
  cst : ℕ → Expr n
  abs : Ty → Expr (suc n) → Expr n
  mab : NTy → Expr (suc n) → Expr n
  app : Expr n → Expr n → Expr n

-- renaming and substitution

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

extRen : Ren m n → Ren (suc m) (suc n)
extRen ρ Fin.zero = Fin.zero
extRen ρ (Fin.suc x) = Fin.suc (ρ x)

ren : Ren m n → Expr m → Expr n
ren ρ ε = ε
ren ρ (e₁ · e₂) = ren ρ e₁ · ren ρ e₂
ren ρ (var x) = var (ρ x)
ren ρ (cst k) = cst k
ren ρ (abs μ e) = abs μ (ren (extRen ρ) e)
ren ρ (mab ημ e) = mab ημ (ren (extRen ρ) e)
ren ρ (app e e₁) = app (ren ρ e) (ren ρ e₁)

weaken : Expr m → Expr (suc m)
weaken = ren Fin.suc

Sub : ℕ → ℕ → Set
Sub m n = Fin m → Expr n

extSub : Sub m n → Sub (suc m) (suc n)
extSub σ Fin.zero = var Fin.zero
extSub σ (Fin.suc x) = weaken (σ x)

sub : Sub m n → Expr m → Expr n
sub σ ε = ε
sub σ (e₁ · e₂) = sub σ e₁ · sub σ e₂
sub σ (var x) = σ x
sub σ (cst k) = cst k
sub σ (abs μ e) = abs μ (sub (extSub σ) e)
sub σ (mab ημ e) = mab ημ (sub (extSub σ) e)
sub σ (app e e₁) = app (sub σ e) (sub σ e₁)

sub₁σ : Expr n → Sub (suc n) n
sub₁σ e Fin.zero = e
sub₁σ e (Fin.suc x) = var x

sub₁ : Expr n → Expr (suc n) → Expr n
sub₁ e = sub (sub₁σ e)

-- utilities

mapE : (Expr m → Expr n) → Expr m → Expr n
mapE f ε = ε
mapE f (e₁ · e₂) = mapE f e₁ · mapE f e₂
mapE f (var x) = f (var x)
mapE f (cst x) = f (cst x)
mapE f (abs x e) = f (abs x e)
mapE f (mab x e) = f (mab x e)
mapE f (app e e₁) = f (app e e₁)

lengthE : Expr n → ℕ
lengthE ε = 0
lengthE (e₁ · e₂) = lengthE e₁ +ℕ lengthE e₂
lengthE (var x) = 1
lengthE (cst x) = 1
lengthE (abs x e) = 1
lengthE (mab x e) = 1
lengthE (app e e₁) = 1

-- values

data Value : Expr zero → Set where
  vε  : Value ε
  _v·_ : ∀ {v}{w}
    → Value v
    → Value w
    → {v≢ε : v ≡ ε → ⊥}
    → {w≢ε : w ≡ ε → ⊥}
    → {v≢· : ∀ {e₁ e₂} → v ≡ (e₁ · e₂) → ⊥}
    → Value (v · w)
  cst : ∀ {k} → Value (cst k)
  abs : ∀ {μ}{e*} → Value (abs μ e*)
  mab : ∀ {ημ}{e*} → Value (mab ημ e*)

data SingletonValue : Ty → Expr zero → Set where
  sv-cst : ∀ {k μ} → □ <:ₜ μ → SingletonValue μ (cst k)
  sv-abs : ∀ {μ μ₀ ημ e*} → (μ₀ ⇒ ημ) <:ₜ μ → SingletonValue μ (abs μ₀ e*)
  sv-mab : ∀ {μ ημ ημ′ e*} → (ημ ⇛ ημ′) <:ₜ μ → SingletonValue μ (mab ημ e*)

NonEmpty : Expr zero → Set
NonEmpty e = e ≡ ε → ⊥

data AbsValue : Expr zero → Set where
  v-abs : ∀ μ e* → AbsValue (abs μ e*)

data MabValue : Expr zero → Set where
  v-mab : ∀ ημ e* → MabValue (mab ημ e*)

data ALL (P : Expr zero → Set) : Expr zero → Set where
  Aε : ALL P ε
  _A·_ : ∀ {e₁}{e₂} → ALL P e₁ → ALL P e₂ → ALL P (e₁ · e₂)
  AP : ∀ {e} → P e → ALL P e

AllSingleton : Ty → Expr zero → Set
AllSingleton μ e = ALL (SingletonValue μ) e

data SequenceValue : NTy → Expr zero → Set where
  seq-zero : ∀ {μ} → SequenceValue ⟨ `- , μ ⟩ ε
  seq-one : ∀ {μ e}
    → SingletonValue μ e
    → SequenceValue ⟨ `! , μ ⟩ e
  seq-opt-zero : ∀ {μ} → SequenceValue ⟨ `? , μ ⟩ ε
  seq-opt-one : ∀ {μ e}
    → SingletonValue μ e
    → SequenceValue ⟨ `? , μ ⟩ e
  seq-star : ∀ {μ e}
    → AllSingleton μ e
    → SequenceValue ⟨ `* , μ ⟩ e
  seq-plus : ∀ {μ e}
    → AllSingleton μ e
    → NonEmpty e
    → SequenceValue ⟨ `+ , μ ⟩ e

absbody : ∀{e : Expr zero} → AbsValue e → Expr (suc zero)
absbody (v-abs μ s) = s

mabbody : ∀{e : Expr zero} → MabValue e → Expr (suc zero)
mabbody (v-mab ημ s) = s

mapALL : ∀ {n} {e : Expr zero} {P : Pred (Expr zero) lzero} → (∀ {x} → P x → Expr n) → ALL P e → Expr n
mapALL f Aε = ε
mapALL f (a A· a₁) = (mapALL f a) · (mapALL f a₁)
mapALL f (AP Pe) = f Pe

-- reduction

data _⟶_ : Expr zero → Expr zero → Set where

  ξ-app₁ : ∀ {s₁}{s₁′}{s₂}
    → s₁ ⟶ s₁′
    → app s₁ s₂ ⟶ app s₁′ s₂

  ξ-app₂ : ∀ {s₁}{s₂}{s₂′}
    → Value s₁
    → s₂ ⟶ s₂′
    → app s₁ s₂ ⟶ app s₁ s₂′

  ξ-head : ∀ {e}{e′}{s}
    → e ⟶ e′
    → (e · s) ⟶ (e′ · s)

  ξ-tail : ∀ {e}{s}{s′}
    → Value e
    → s ⟶ s′
    → (e · s) ⟶ (e · s′)

  mon-ε-unit-left : ∀ {e}
    → (ε · e) ⟶ e

  mon-ε-unit-right : ∀ {e}
    → (e · ε) ⟶ e

  mon-·-assoc : ∀ {e₁ e₂ e₃}
    → ((e₁ · e₂) · e₃) ⟶ (e₁ · (e₂ · e₃))

  β₁ : ∀ {s}{w}
    → Value s
    → (abs₁ : ALL AbsValue s)
    → Value w
    → app s w ⟶ mapE (λ v → mapE (λ b → sub₁ v b) (mapALL absbody abs₁)) w

  βₙ : ∀ {s}{w}
    → Value s
    → (mab₁ : ALL MabValue s)
    → Value w
    → app s w ⟶ mapE (λ b → sub₁ w b) (mapALL mabbody mab₁)


data _⟶*_ : Expr zero → Expr zero → Set where
  ⟶-refl : ∀ {e*} → e* ⟶* e*
  ⟶-step : ∀ {e₁* e₂* e₃*} → e₁* ⟶ e₂* → e₂* ⟶* e₃* → e₁* ⟶* e₃*


-- logical relation

𝓥⟦_⟧ : Ty → Pred (Expr zero) lzero
𝓦⟦_⟧ : NTy → Pred (Expr zero) lzero
𝓔⟦_⟧ : NTy → Pred (Expr zero) lzero

𝓥⟦ `⊥ ⟧ e = ⊥
𝓥⟦ □ ⟧ e = ∃[ n ] e ≡ cst n
𝓥⟦ μ ⇒ ημ ⟧ e = ∃[ μ₀ ]  ∃[ s ] e ≡ abs μ₀ s    × μ <:ₜ μ₀ × ∀ v → v ∈ 𝓥⟦ μ ⟧   → mapE (sub₁ v) s ∈ 𝓔⟦ ημ ⟧

𝓥⟦ ημ₁ ⇛ ημ₂ ⟧ e = ∃[ ημ₀ ] ∃[ s ] e ≡ mab ημ₀ s   × ημ₁ <:ₙ ημ₀ ×  ∀ w → w ∈ 𝓦⟦ ημ₁ ⟧ → mapE (sub₁ w) s ∈ 𝓔⟦ ημ₂ ⟧

𝓦⟦ ⟨ η , μ ⟩ ⟧ s  = ALL 𝓥⟦ μ ⟧ s × (lengthE s ∈∈ 𝓝⟦ η ⟧)

𝓔⟦ ημ ⟧ s          = ∃[ w ] w ∈ 𝓦⟦ ημ ⟧ × (s ⟶* w) 

-- typing contexts

data Ctx : ℕ → Set where
  ∅ : Ctx zero
  _▻_ : NTy → Ctx n → Ctx (suc n)

lookup : Fin n → Ctx n → NTy
lookup Fin.zero (ημ ▻ _) = ημ
lookup (Fin.suc x) (_ ▻ Γ) = lookup x Γ

-- 𝓖⟦ Γ ⟧ characterizes substitutions σ: if x : ημ ∈ Γ then σ(x) ∈ 𝓦⟦ ημ ⟧

𝓖⟦_⟧ : Ctx n → Sub n zero → Set
𝓖⟦ ∅ ⟧ σ = ⊤
𝓖⟦ ημ ▻ Γ ⟧ σ = (∃[ w ] σ Fin.zero ≡ w × w ∈ 𝓦⟦ ημ ⟧) × (σ ∘ Fin.suc) ∈ 𝓖⟦ Γ ⟧


-- semantic typing
-- Γ ⊨ s : ημ <=> ∀ σ ∈ 𝓖⟦ Γ ⟧ . σ s ∈ 𝓔⟦ ημ ⟧

_⊨_⦂_ : Ctx n → Expr n → NTy → Set
Γ ⊨ e ⦂ ημ = ∀ σ → σ ∈ 𝓖⟦ Γ ⟧ → sub σ e ∈ 𝓔⟦ ημ ⟧

-- syntactic typing

data _⊢_⦂_  {n} : Ctx n → Expr n → NTy → Set where

  t-var : ∀ {Γ : Ctx n}{x} → Γ ⊢ var x ⦂ lookup x Γ

  t-cst : ∀ {Γ : Ctx n}{k} → Γ ⊢ cst k ⦂ ⟨ `! , □ ⟩

  t-abs : ∀ {Γ : Ctx n}{μ}{s}{ημ}
    → (⟨ `! , μ ⟩ ▻ Γ) ⊢ s ⦂ ημ
    → Γ ⊢ abs μ s  ⦂ ⟨ `! , (μ ⇒ ημ) ⟩

  t-mab : ∀ {Γ : Ctx n}{ημ}{s}{ημ′}
    → (ημ ▻ Γ) ⊢ s ⦂ ημ′
    → Γ ⊢ mab ημ s  ⦂ ⟨ `! , (ημ ⇛ ημ′) ⟩

  t-app-s : ∀ {Γ : Ctx n}{s₁}{s₂}{η₁ μ₁ η₂ μ₂ η₃ η η′}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ⟨ η₃ , μ₁ ⟩
    → MUL η₁ η₂ η′ → MUL η′ η₃ η
    → Γ ⊢ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩

  t-app-p : ∀ {Γ : Ctx n}{s₁}{s₂}{η₁ ημ η₂ μ₂ η}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ημ
    → MUL η₁ η₂ η
    → Γ ⊢ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩

  t-sub : ∀ {Γ : Ctx n}{e : Expr n}{ημ₁ ημ₂}
    → Γ ⊢ e ⦂ ημ₁
    → ημ₁ <:ₙ ημ₂
    → Γ ⊢ e  ⦂ ημ₂

  t-empty : ∀ {Γ : Ctx n}{μ}
    → Γ ⊢ ε ⦂ ⟨ `- , μ ⟩

  t-head : ∀ {Γ : Ctx n}{e₁}{e₂}{η₁ η₂ η μ}
    → Γ ⊢ e₁ ⦂ ⟨ η₁ , μ ⟩
    → Γ ⊢ e₂ ⦂ ⟨ η₂ , μ ⟩
    → η ≡ ADD η₁ η₂
    → Γ ⊢ (e₁ · e₂) ⦂ ⟨ η , μ ⟩

-- typed renaming and substitution

infix 2 _⊢ₛ_∶_
_⊢ₛ_∶_ : Ctx n → Sub m n → Ctx m → Set
Δ ⊢ₛ σ ∶ Γ = ∀ x → Δ ⊢ σ x ⦂ lookup x Γ

infix 2 _⊢ᵣ_∶_
_⊢ᵣ_∶_ : Ctx n → Ren m n → Ctx m → Set
Δ ⊢ᵣ ρ ∶ Γ = ∀ x → lookup (ρ x) Δ ≡ lookup x Γ

ren-typed-ext : ∀ {Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n}{ημ}
  → Δ ⊢ᵣ ρ ∶ Γ
  → (ημ ▻ Δ) ⊢ᵣ extRen ρ ∶ (ημ ▻ Γ)
ren-typed-ext ρ⊢ Fin.zero = refl
ren-typed-ext ρ⊢ (Fin.suc x) = ρ⊢ x

ren-pres : ∀ {Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n}{e : Expr m}{ημ}
  → Γ ⊢ e ⦂ ημ
  → Δ ⊢ᵣ ρ ∶ Γ
  → Δ ⊢ ren ρ e ⦂ ημ
ren-pres (t-var {x = x}) ρ⊢
  with ρ⊢ x
... | eq rewrite sym eq = t-var
ren-pres t-cst ρ⊢ = t-cst
ren-pres (t-abs ⊢s) ρ⊢ = t-abs (ren-pres ⊢s (ren-typed-ext ρ⊢))
ren-pres (t-mab ⊢s) ρ⊢ = t-mab (ren-pres ⊢s (ren-typed-ext ρ⊢))
ren-pres (t-app-s ⊢s₁ ⊢s₂ x x₁) ρ⊢ = t-app-s (ren-pres ⊢s₁ ρ⊢) (ren-pres ⊢s₂ ρ⊢) x x₁
ren-pres (t-app-p ⊢s₁ ⊢s₂ x) ρ⊢ = t-app-p (ren-pres ⊢s₁ ρ⊢) (ren-pres ⊢s₂ ρ⊢) x
ren-pres (t-sub ⊢e ημ<:) ρ⊢ = t-sub (ren-pres ⊢e ρ⊢) ημ<:
ren-pres t-empty ρ⊢ = t-empty
ren-pres (t-head ⊢e₁ ⊢e₂ refl) ρ⊢ = t-head (ren-pres ⊢e₁ ρ⊢) (ren-pres ⊢e₂ ρ⊢) refl

weaken-typed : ∀ {Γ : Ctx m}{e : Expr m}{ημ}{ημ′}
  → Γ ⊢ e ⦂ ημ
  → (ημ′ ▻ Γ) ⊢ weaken e ⦂ ημ
weaken-typed {Γ = Γ} {ημ′ = ημ′} ⊢e = ren-pres ⊢e ρ⊢
  where
  ρ⊢ : (ημ′ ▻ Γ) ⊢ᵣ Fin.suc ∶ Γ
  ρ⊢ x = refl

sub-typed-ext : ∀ {Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n}{ημ}
  → Δ ⊢ₛ σ ∶ Γ
  → (ημ ▻ Δ) ⊢ₛ extSub σ ∶ (ημ ▻ Γ)
sub-typed-ext σ⊢ Fin.zero = t-var
sub-typed-ext σ⊢ (Fin.suc x) = weaken-typed (σ⊢ x)

sub-pres : ∀ {Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n}{e : Expr m}{ημ}
  → Δ ⊢ₛ σ ∶ Γ
  → Γ ⊢ e ⦂ ημ
  → Δ ⊢ sub σ e ⦂ ημ
sub-pres σ⊢ (t-var {x = x}) = σ⊢ x
sub-pres σ⊢ t-cst = t-cst
sub-pres σ⊢ (t-abs ⊢s) = t-abs (sub-pres (sub-typed-ext σ⊢) ⊢s)
sub-pres σ⊢ (t-mab ⊢s) = t-mab (sub-pres (sub-typed-ext σ⊢) ⊢s)
sub-pres σ⊢ (t-app-s ⊢s₁ ⊢s₂ x x₁) = t-app-s (sub-pres σ⊢ ⊢s₁) (sub-pres σ⊢ ⊢s₂) x x₁
sub-pres σ⊢ (t-app-p ⊢s₁ ⊢s₂ x) = t-app-p (sub-pres σ⊢ ⊢s₁) (sub-pres σ⊢ ⊢s₂) x
sub-pres σ⊢ (t-sub ⊢e ημ<:) = t-sub (sub-pres σ⊢ ⊢e) ημ<:
sub-pres σ⊢ t-empty = t-empty
sub-pres σ⊢ (t-head ⊢e₁ ⊢e₂ refl) = t-head (sub-pres σ⊢ ⊢e₁) (sub-pres σ⊢ ⊢e₂) refl

-- inversion lemmas

t-head-inversion : ∀ {e₁}{e₂}{η μ}
  → ∅ ⊢ (e₁ · e₂) ⦂ ⟨ η , μ ⟩
  → ∃[ η₀ ] ∃[ η₁ ] ∃[ η₂ ] ∃[ μ₀ ]
    ∅ ⊢ e₁ ⦂ ⟨ η₁ , μ₀ ⟩
  × ∅ ⊢ e₂ ⦂ ⟨ η₂ , μ₀ ⟩
  × η₀ <:₀ η
  × μ₀ <:ₜ μ
  × ADD η₁ η₂ ≡ η₀
t-head-inversion (t-sub ⊢e₁·e₂ (<:ₙ-comb η₁<:₀η μ₁<:ₜμ))
  with t-head-inversion ⊢e₁·e₂
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<: , μ₀<: , add-eq = η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ ,  (<:₀-trans η₀<: η₁<:₀η) , ((<:ₜ-trans μ₀<: μ₁<:ₜμ) , add-eq)
t-head-inversion {η = η} {μ = μ} (t-head {η₁ = η₁}{η₂} ⊢e₁ ⊢e₂ refl) = η , η₁ , η₂ , μ , ⊢e₁ , ⊢e₂ , <:₀-refl , <:ₜ-refl , refl

t-cst-inversion : ∀ {k}{ημ}
  → ∅ ⊢ cst k ⦂ ημ
  → ⟨ `! , □ ⟩ <:ₙ ημ

t-abs-inversion : ∀ {μ}{e}{ημ}
  → ∅ ⊢ abs μ e ⦂ ημ
  → ∃[ ημ₀ ]
    ⟨ `! , (μ ⇒ ημ₀) ⟩ <:ₙ ημ
  × (⟨ `! , μ ⟩ ▻ ∅) ⊢ e ⦂ ημ₀

t-mab-inversion : ∀ {ημ}{e}{ημ₁}
  → ∅ ⊢ mab ημ e ⦂ ημ₁
  → ∃[ ημ₀ ]
    ⟨ `! , (ημ ⇛ ημ₀) ⟩ <:ₙ ημ₁
  × (ημ ▻ ∅) ⊢ e ⦂ ημ₀

value-nonempty-one-lower : ∀ {e η μ}
  → Value e
  → NonEmpty e
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → `! <:₀ η

value-nonempty-plus : ∀ {e η μ}
  → Value e
  → NonEmpty e
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → ∅ ⊢ e ⦂ ⟨ `+ , μ ⟩
value-nonempty-plus vε e≢ε ⊢e
  with e≢ε refl
... | ()
value-nonempty-plus cst e≢ε ⊢e
  with t-cst-inversion ⊢e
... | <:ₙ-comb !<:η □<:μ = t-sub t-cst (<:ₙ-comb <:₀-!+ □<:μ)
value-nonempty-plus abs e≢ε ⊢e
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η abs<:μ , ⊢body = t-sub (t-abs ⊢body) (<:ₙ-comb <:₀-!+ abs<:μ)
value-nonempty-plus mab e≢ε ⊢e
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η mab<:μ , ⊢body = t-sub (t-mab ⊢body) (<:ₙ-comb <:₀-!+ mab<:μ)
value-nonempty-plus
  ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε}) e≢ε ⊢e
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢v , ⊢w , η₀<:η , μ₀<:μ , add-eq
  = t-sub
      (t-head
        (value-nonempty-plus vh v≢ε ⊢v)
        (value-nonempty-plus vw w≢ε ⊢w)
        refl)
      (<:ₙ-comb <:₀-refl μ₀<:μ)

value-atomic-one : ∀ {e η μ}
  → Value e
  → NonEmpty e
  → (∀ {e₁ e₂} → e ≡ (e₁ · e₂) → ⊥)
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → ∅ ⊢ e ⦂ ⟨ `! , μ ⟩
value-atomic-one vε e≢ε e≢· ⊢e
  with e≢ε refl
... | ()
value-atomic-one ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) e≢ε e≢· ⊢e
  with e≢· refl
... | ()
value-atomic-one cst e≢ε e≢· ⊢e
  with t-cst-inversion ⊢e
... | <:ₙ-comb !<:η □<:μ = t-sub t-cst (<:ₙ-comb <:₀-refl □<:μ)
value-atomic-one abs e≢ε e≢· ⊢e
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η abs<:μ , ⊢body = t-sub (t-abs ⊢body) (<:ₙ-comb <:₀-refl abs<:μ)
value-atomic-one mab e≢ε e≢· ⊢e
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η mab<:μ , ⊢body = t-sub (t-mab ⊢body) (<:ₙ-comb <:₀-refl mab<:μ)

t-head-inversion-value : ∀ {e₁}{e₂}{η μ}
  → ∅ ⊢ (e₁ · e₂) ⦂ ⟨ η , μ ⟩
  → Value (e₁ · e₂)
  → ∃[ μ₀ ]
    ∅ ⊢ e₁ ⦂ ⟨ `! , μ₀ ⟩
  × ∅ ⊢ e₂ ⦂ ⟨ `+ , μ₀ ⟩
  × `+ <:₀ η
  × μ₀ <:ₜ μ
t-head-inversion-value {η = η} {μ = μ} ⊢e
  ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:η , μ₀<:μ , add-eq
  = μ₀
  , value-atomic-one vh v≢ε v≢· ⊢e₁
  , value-nonempty-plus vw w≢ε ⊢e₂
  , <:₀-trans
      (subst (λ x → `+ <:₀ x) add-eq
        (ADD-both-one-super
          (value-nonempty-one-lower vh v≢ε ⊢e₁)
          (value-nonempty-one-lower vw w≢ε ⊢e₂)))
      η₀<:η
  , μ₀<:μ


t-cst-inversion t-cst = <:ₙ-refl
t-cst-inversion (t-sub ⊢e ημ<:)
  with t-cst-inversion ⊢e
... | !□<: = <:ₙ-trans !□<: ημ<:

t-abs-inversion (t-abs {ημ = ημ} ⊢e) = ημ , <:ₙ-refl , ⊢e
t-abs-inversion (t-sub ⊢e ημ₁<:)
  with t-abs-inversion ⊢e
... | ημ₀ , <:ημ , ⊢body = ημ₀ , (<:ₙ-trans <:ημ ημ₁<:) , ⊢body

t-mab-inversion (t-mab {ημ′ = ημ′} ⊢e) = ημ′ , <:ₙ-refl , ⊢e
t-mab-inversion (t-sub ⊢e x)
  with t-mab-inversion ⊢e
... | ημ₀ , <:ημ , ⊢body = ημ₀ , <:ₙ-trans <:ημ x , ⊢body

t-empty-inversion : ∀ {η μ}
  → ∅ ⊢ ε ⦂ ⟨ η , μ ⟩
  → `- <:₀ η
t-empty-inversion t-empty = <:₀-refl
t-empty-inversion (t-sub ⊢e (<:ₙ-comb η₁<:η _)) = <:₀-trans (t-empty-inversion ⊢e) η₁<:η

-- canonical forms

canonical-zero :  ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `- , μ ⟩ → Value e → e ≡ ε
canonical-zero ⊢e vε = refl
canonical-zero ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , <:₀-refl , μ₀<:μ , add-eq
  with ADD-zero η₁ η₂ (sym add-eq)
... | refl , refl
  with canonical-zero ⊢e₁ v-e
... | eq₁
  with v≢ε eq₁
... | ()
canonical-zero ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb () x₁
canonical-zero ⊢e abs
  with t-abs-inversion ⊢e
... | ημ , <:ₙ-comb () _ , _
canonical-zero ⊢e mab
  with t-mab-inversion ⊢e
... | _ , <:ₙ-comb () _ , _

value-nonempty-one-lower {η = `- } vw e≢ε ⊢e
  = ⊥-elim (e≢ε (canonical-zero ⊢e vw))
value-nonempty-one-lower {η = `! } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-refl
value-nonempty-one-lower {η = `? } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-!?
value-nonempty-one-lower {η = `* } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-!*
value-nonempty-one-lower {η = `+ } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-!+

canonical-one : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `! , μ ⟩ → Value e → SingletonValue μ e
canonical-one ⊢e vε
  with t-empty-inversion ⊢e
... | ()
canonical-one {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , <:₀-refl , μ₀<:μ , add-eq
  with ADD-one η₁ η₂ (sym add-eq)
... | add-one = impossible add-one
  where
  impossible : (`! ≡ η₁ × `- ≡ η₂) ⊎ (`- ≡ η₁ × `! ≡ η₂) → SingletonValue μ (v · w)
  impossible (inj₁ (refl , refl))
    with w≢ε (canonical-zero ⊢e₂ v-e₁)
  ... | ()
  impossible (inj₂ (refl , refl))
    with v≢ε (canonical-zero ⊢e₁ v-e)
  ... | ()
canonical-one ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb <:₀-refl □<:μ = sv-cst □<:μ
canonical-one ⊢e abs
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-refl abs<:μ , ⊢body = sv-abs abs<:μ
canonical-one ⊢e mab
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-refl mab<:μ , ⊢body = sv-mab mab<:μ

canonical-opt : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `? , μ ⟩ → Value e → (e ≡ ε) ⊎ SingletonValue μ e
canonical-opt ⊢e vε = inj₁ refl
canonical-opt {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:? , μ₀<:μ , add-eq = impossible η₀<:?
  where
  impossible : η₀ <:₀ `? → (v · w ≡ ε) ⊎ SingletonValue μ (v · w)
  impossible <:₀-refl
    with ADD-opt η₁ η₂ (sym add-eq)
  ... | add-opt = impossible-opt add-opt
    where
    impossible-opt : (`- ≡ η₁ × `? ≡ η₂) ⊎ (`? ≡ η₁ × `- ≡ η₂) → (v · w ≡ ε) ⊎ SingletonValue μ (v · w)
    impossible-opt (inj₁ (refl , refl))
      with v≢ε (canonical-zero ⊢e₁ v-e)
    ... | ()
    impossible-opt (inj₂ (refl , refl))
      with w≢ε (canonical-zero ⊢e₂ v-e₁)
    ... | ()
  impossible <:₀--?
    with ADD-zero η₁ η₂ (sym add-eq)
  ... | refl , refl
    with v≢ε (canonical-zero ⊢e₁ v-e)
  ... | ()
  impossible <:₀-!?
    with ADD-one η₁ η₂ (sym add-eq)
  ... | add-one = impossible-one add-one
    where
    impossible-one : (`! ≡ η₁ × `- ≡ η₂) ⊎ (`- ≡ η₁ × `! ≡ η₂) → (v · w ≡ ε) ⊎ SingletonValue μ (v · w)
    impossible-one (inj₁ (refl , refl))
      with w≢ε (canonical-zero ⊢e₂ v-e₁)
    ... | ()
    impossible-one (inj₂ (refl , refl))
      with v≢ε (canonical-zero ⊢e₁ v-e)
    ... | ()
canonical-opt ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb <:₀-!? □<:μ = inj₂ (sv-cst □<:μ)
canonical-opt ⊢e abs
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!? abs<:μ , ⊢body = inj₂ (sv-abs abs<:μ)
canonical-opt ⊢e mab
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!? mab<:μ , ⊢body = inj₂ (sv-mab mab<:μ)

canonical-star : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `* , μ ⟩ → Value e → AllSingleton μ e
canonical-star ⊢e vε = Aε
canonical-star {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:* , μ₀<:μ , add-eq
  = canonical-star (t-sub ⊢e₁ (<:ₙ-comb (num-to-star η₁) μ₀<:μ)) v-e
  A· canonical-star (t-sub ⊢e₂ (<:ₙ-comb (num-to-star η₂) μ₀<:μ)) v-e₁
canonical-star ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb <:₀-!* □<:μ = AP (sv-cst □<:μ)
canonical-star ⊢e abs
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!* abs<:μ , ⊢body = AP (sv-abs abs<:μ)
canonical-star ⊢e mab
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!* mab<:μ , ⊢body = AP (sv-mab mab<:μ)

canonical-plus : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `+ , μ ⟩ → Value e → AllSingleton μ e × NonEmpty e
canonical-plus ⊢e vε
  with t-empty-inversion ⊢e
... | ()
canonical-plus {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  , λ ()
canonical-plus {e = cst k} {μ = μ} ⊢e cst
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) cst
  , λ ()
canonical-plus {e = abs μ₀ e*} {μ = μ} ⊢e abs
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) abs
  , λ ()
canonical-plus {e = mab ημ e*} {μ = μ} ⊢e mab
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) mab
  , λ ()

canonical-sequence : ∀ {η μ} {e : Expr zero}
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → Value e
  → SequenceValue ⟨ η , μ ⟩ e
canonical-sequence {η = `- } {e = e} ⊢e ve
  with canonical-zero ⊢e ve
... | refl = seq-zero
canonical-sequence {η = `! } ⊢e ve = seq-one (canonical-one ⊢e ve)
canonical-sequence {η = `? } {e = e} ⊢e ve
  with canonical-opt ⊢e ve
... | inj₁ eq rewrite eq = seq-opt-zero
... | inj₂ sv = seq-opt-one sv
canonical-sequence {η = `* } ⊢e ve = seq-star (canonical-star ⊢e ve)
canonical-sequence {η = `+ } ⊢e ve
  with canonical-plus ⊢e ve
... | allsv , ne = seq-plus allsv ne

-- type preservation

mixed-mab-num-empty : ∀ {s η₁ μ₁ η₂ μ₂}
  → (mab₁ : ALL MabValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → `- <:₀ η₁
mixed-mab-num-empty Aε ⊢s = t-empty-inversion ⊢s
mixed-mab-num-empty (mab₁ A· mab₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = <:₀-trans (subst (λ x → `- <:₀ x) add-eq
      (ADD-empty-super
        (mixed-mab-num-empty mab₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
        (mixed-mab-num-empty mab₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))))
      η₀<:
mixed-mab-num-empty (AP (v-mab ημ e*)) ⊢s
  with t-mab-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mixed-abs-num-empty : ∀ {s η₁ ημ η₂ μ₂}
  → (abs₁ : ALL AbsValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → `- <:₀ η₁
mixed-abs-num-empty Aε ⊢s = t-empty-inversion ⊢s
mixed-abs-num-empty (abs₁ A· abs₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = <:₀-trans (subst (λ x → `- <:₀ x) add-eq
      (ADD-empty-super
        (mixed-abs-num-empty abs₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
        (mixed-abs-num-empty abs₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))))
      η₀<:
mixed-abs-num-empty (AP (v-abs μ e*)) ⊢s
  with t-abs-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mixed-mab-minus : ∀ {s w η₁ μ₁ η₂ μ₂}
  → (mab₁ : ALL MabValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ mapE (λ b → sub₁ w b) (mapALL mabbody mab₁) ⦂ ⟨ `- , μ₂ ⟩
mixed-mab-minus Aε ⊢s = t-empty
mixed-mab-minus (mab₁ A· mab₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = t-head
      (mixed-mab-minus mab₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
      (mixed-mab-minus mab₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))
      refl
mixed-mab-minus (AP (v-mab ημ e*)) ⊢s
  with t-mab-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mixed-abs-minus : ∀ {s v η₁ ημ η₂ μ₂}
  → (abs₁ : ALL AbsValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ mapE (λ b → sub₁ v b) (mapALL absbody abs₁) ⦂ ⟨ `- , μ₂ ⟩
mixed-abs-minus Aε ⊢s = t-empty
mixed-abs-minus (abs₁ A· abs₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = t-head
      (mixed-abs-minus abs₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
      (mixed-abs-minus abs₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))
      refl
mixed-abs-minus (AP (v-abs μ e*)) ⊢s
  with t-abs-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mapE-minus : ∀ {e : Expr zero}{μ}
  → (f : Expr zero → Expr zero)
  → (∀ {x} → ∅ ⊢ f x ⦂ ⟨ `- , μ ⟩)
  → ∅ ⊢ mapE f e ⦂ ⟨ `- , μ ⟩
mapE-minus {e = ε} f f⊢ = t-empty
mapE-minus {e = e₁ · e₂} f f⊢ = t-head (mapE-minus {e = e₁} f f⊢) (mapE-minus {e = e₂} f f⊢) refl
mapE-minus {e = var ()} f f⊢
mapE-minus {e = cst k} f f⊢ = f⊢
mapE-minus {e = abs μ e} f f⊢ = f⊢
mapE-minus {e = mab ημ e} f f⊢ = f⊢
mapE-minus {e = app e₁ e₂} f f⊢ = f⊢

mapE-sub₁ : ∀ {w : Expr zero}{e : Expr (suc zero)}
  → mapE (λ b′ → sub₁ w b′) e ≡ sub₁ w e
mapE-sub₁ {e = ε} = refl
mapE-sub₁ {w = w} {e = e₁ · e₂}
  rewrite mapE-sub₁ {w = w} {e = e₁} | mapE-sub₁ {w = w} {e = e₂} = refl
mapE-sub₁ {e = var x} = refl
mapE-sub₁ {e = cst x} = refl
mapE-sub₁ {e = abs x e} = refl
mapE-sub₁ {e = mab x e} = refl
mapE-sub₁ {e = app e e₁} = refl


β₁-pres-s-A· : ∀ {s₁ s₂ w η₁ μ₁ η₂ μ₂ η₃ η η′}
  → Value (s₁ · s₂)
  → (abs₁ : ALL AbsValue s₁)
  → (abs₂ : ALL AbsValue s₂)
  → Value w
  → ∅ ⊢ (s₁ · s₂) ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ v → mapE (λ b → sub₁ v b) (mapALL absbody (abs₁ A· abs₂))) w ⦂ ⟨ η , μ₂ ⟩


β₁-pres-s-AP-concat : ∀ {v w μ₁ μ₂ η₃ η η′ b}
  → (vh : Value v)
  → (vw : Value w)
  → (v≢ε : v ≡ ε → ⊥)
  → (w≢ε : w ≡ ε → ⊥)
  → (v≢· : ∀ {e₁ e₂} → v ≡ (e₁ · e₂) → ⊥)
  → ∅ ⊢ (v · w) ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ x → mapE (λ b′ → sub₁ x b′) b) v ⦂ ⟨ η , μ₂ ⟩
  → ∅ ⊢ mapE (λ x → mapE (λ b′ → sub₁ x b′) b) w ⦂ ⟨ η , μ₂ ⟩
  → ∅ ⊢ mapE (λ x → mapE (λ b′ → sub₁ x b′) b) (v · w) ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s-AP-concat vh vw v≢ε w≢ε v≢· ⊢vw m₂ ⊢v ⊢w
  with t-head-inversion-value ⊢vw ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = t-sub
      (t-head ⊢v ⊢w refl)
      (<:ₙ-comb (ADD-self-super-plus +<:η₃ m₂) <:ₜ-refl)

β₁-pres-s-AP : ∀ {w η₁ μ₁ η₂ μ₂ η₃ η η′ μ ημ₀ b}
  → Value w
  → ∅ ⊢ abs μ b ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → (ημ₀<:η₂μ₂ : ημ₀ <:ₙ ⟨ η₂ , μ₂ ⟩)
  → (⟨ `! , μ ⟩ ▻ ∅) ⊢ b ⦂ ημ₀
  → ∅ ⊢ mapE (λ v → mapE (λ b′ → sub₁ v b′) b) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s-AP {μ₂ = μ₂} vε ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-empty-inversion ⊢w
... | η₃-empty = t-sub t-empty (<:ₙ-comb (MUL-right-empty η₃-empty m₂) <:ₜ-refl)
β₁-pres-s-AP {w = (v · w)} ((vε v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with v≢ε refl
... | ()
β₁-pres-s-AP {w = (v · w)} (((v-v₁ v· v-v₂) v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with v≢· refl
... | ()
β₁-pres-s-AP {w = (v · w)} {b = b} ((cst v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-head-inversion-value ⊢w ((cst v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-AP cst ⊢s ⊢v₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
      tail-pres = β₁-pres-s-AP w-v ⊢s ⊢w₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
    in β₁-pres-s-AP-concat {b = b} cst w-v v≢ε w≢ε (λ ()) ⊢w m₂ head-pres tail-pres
β₁-pres-s-AP {w = (v · w)} {b = b} ((abs v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-head-inversion-value ⊢w ((abs v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-AP abs ⊢s ⊢v₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
      tail-pres = β₁-pres-s-AP w-v ⊢s ⊢w₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
    in β₁-pres-s-AP-concat {b = b} abs w-v v≢ε w≢ε (λ ()) ⊢w m₂ head-pres tail-pres
β₁-pres-s-AP {w = (v · w)} {b = b} ((mab v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-head-inversion-value ⊢w ((mab v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-AP mab ⊢s ⊢v₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
      tail-pres = β₁-pres-s-AP w-v ⊢s ⊢w₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
    in β₁-pres-s-AP-concat {b = b} mab w-v v≢ε w≢ε (λ ()) ⊢w m₂ head-pres tail-pres
β₁-pres-s-AP {w = cst k} {b = b} cst ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-abs-inversion ⊢s
... | ημs , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημs<:η₂μ₂) , ⊢sbody
  with t-cst-inversion ⊢w
... | <:ₙ-comb !<:η₃ □<:μ₁
  rewrite mapE-sub₁ {w = cst k} {e = b}
  = let
      η₂<:η′ = MUL-left-one-super !<:η₁ m₁
      η′<:η = MUL-right-one-super !<:η₃ m₂
      η₂<:η = <:₀-trans η₂<:η′ η′<:η
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub t-cst (<:ₙ-comb <:₀-refl (<:ₜ-trans □<:μ₁ μ₁<:μ))
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)
β₁-pres-s-AP {w = abs μw bw} {b = b} abs ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-abs-inversion ⊢s
... | ημs , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημs<:η₂μ₂) , ⊢sbody
  with t-abs-inversion ⊢w
... | ημw , <:ₙ-comb !<:η₃ abs<:μ₁ , ⊢wbody
  rewrite mapE-sub₁ {w = abs μw bw} {e = b}
  = let
      η₂<:η′ = MUL-left-one-super !<:η₁ m₁
      η′<:η = MUL-right-one-super !<:η₃ m₂
      η₂<:η = <:₀-trans η₂<:η′ η′<:η
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub (t-abs ⊢wbody) (<:ₙ-comb <:₀-refl (<:ₜ-trans abs<:μ₁ μ₁<:μ))
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)
β₁-pres-s-AP {w = mab ημw bw} {b = b} mab ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-abs-inversion ⊢s
... | ημs , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημs<:η₂μ₂) , ⊢sbody
  with t-mab-inversion ⊢w
... | ημw′ , <:ₙ-comb !<:η₃ mab<:μ₁ , ⊢wbody
  rewrite mapE-sub₁ {w = mab ημw bw} {e = b}
  = let
      η₂<:η′ = MUL-left-one-super !<:η₁ m₁
      η′<:η = MUL-right-one-super !<:η₃ m₂
      η₂<:η = <:₀-trans η₂<:η′ η′<:η
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub (t-mab ⊢wbody) (<:ₙ-comb <:₀-refl (<:ₜ-trans mab<:μ₁ μ₁<:μ))
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)

β₁-pres-s-AP-single : ∀ {w η₁ μ₁ η₂ μ₂ η₃ η η′ μ ημ₀ b}
  → Value w
  → ∅ ⊢ abs μ b ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → (ημ₀<:η₂μ₂ : ημ₀ <:ₙ ⟨ η₂ , μ₂ ⟩)
  → (⟨ `! , μ ⟩ ▻ ∅) ⊢ b ⦂ ημ₀
  → ∅ ⊢ mapE (λ v → mapE (λ b′ → sub₁ v b′) b) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s-AP-single vw ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  = β₁-pres-s-AP vw ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b

β₁-pres-s : ∀ {s w η₁ μ₁ η₂ μ₂ η₃ η η′}
  → Value s
  → (abs₁ : ALL AbsValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ v → mapE (λ b → sub₁ v b) (mapALL absbody abs₁)) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s {w = w} {μ₂ = μ₂} vs Aε vw ⊢s ⊢w m₁ m₂
  = t-sub
      (mapE-minus {e = w}
        (λ _ → ε)
        (λ {x} → t-empty {μ = μ₂}))
      (<:ₙ-comb (MUL-left-empty (MUL-left-empty (t-empty-inversion ⊢s) m₁) m₂) <:ₜ-refl)
β₁-pres-s vs (abs₁ A· abs₂) vw ⊢s ⊢w m₁ m₂ = β₁-pres-s-A· vs abs₁ abs₂ vw ⊢s ⊢w m₁ m₂
β₁-pres-s vs (AP (v-abs μ b)) vw ⊢s ⊢w m₁ m₂
  with t-abs-inversion ⊢s
... | ημ₀ , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημ₀<:η₂μ₂) , ⊢b = β₁-pres-s-AP vw ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b

β₁-pres-s-A· {μ₂ = μ₂}
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ vε ⊢s ⊢w m₁ m₂
  with t-empty-inversion ⊢w
... | η₃-empty = t-sub t-empty (<:ₙ-comb (MUL-right-empty η₃-empty m₂) <:ₜ-refl)
β₁-pres-s-A·
  {w = (v · w)}
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂
  ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  ⊢s ⊢vw m₁ m₂
  with t-head-inversion-value ⊢vw ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-A· ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·}) abs₁ abs₂ vh ⊢s ⊢v₃ m₁ m₂
      tail-pres = β₁-pres-s-A· ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·}) abs₁ abs₂ vw ⊢s ⊢w₃ m₁ m₂
    in β₁-pres-s-AP-concat {b = mapALL absbody (abs₁ A· abs₂)} vh vw v≢ε w≢ε v≢· ⊢vw m₂ head-pres tail-pres
β₁-pres-s-A·
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ cst ⊢s ⊢w m₁ m₂
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μ₀ , ⊢s₁! , ⊢s₂+ , +<:η₁ , μ₀<:μ₁⇒η₂μ₂
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μ₀<:μ₁⇒η₂μ₂)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μ₀<:μ₁⇒η₂μ₂)
      head-pres = β₁-pres-s vs₁ abs₁ cst ⊢s₁η₁ ⊢w m₁ m₂
      tail-pres = β₁-pres-s vs₂ abs₂ cst ⊢s₂η₁ ⊢w m₁ m₂
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul +<:η₁ m₁ m₂) <:ₜ-refl)
β₁-pres-s-A·
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ abs ⊢s ⊢w m₁ m₂
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μ₀ , ⊢s₁! , ⊢s₂+ , +<:η₁ , μ₀<:μ₁⇒η₂μ₂
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μ₀<:μ₁⇒η₂μ₂)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μ₀<:μ₁⇒η₂μ₂)
      head-pres = β₁-pres-s vs₁ abs₁ abs ⊢s₁η₁ ⊢w m₁ m₂
      tail-pres = β₁-pres-s vs₂ abs₂ abs ⊢s₂η₁ ⊢w m₁ m₂
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul +<:η₁ m₁ m₂) <:ₜ-refl)
β₁-pres-s-A·
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ mab ⊢s ⊢w m₁ m₂
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μ₀ , ⊢s₁! , ⊢s₂+ , +<:η₁ , μ₀<:μ₁⇒η₂μ₂
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μ₀<:μ₁⇒η₂μ₂)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μ₀<:μ₁⇒η₂μ₂)
      head-pres = β₁-pres-s vs₁ abs₁ mab ⊢s₁η₁ ⊢w m₁ m₂
      tail-pres = β₁-pres-s vs₂ abs₂ mab ⊢s₂η₁ ⊢w m₁ m₂
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul +<:η₁ m₁ m₂) <:ₜ-refl)

βₙ-pres-s : ∀ {s w η₁ μ₁ η₂ μ₂ η₃ η η′}
  → (mab₁ : ALL MabValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ b → sub₁ w b) (mapALL mabbody mab₁) ⦂ ⟨ η , μ₂ ⟩
βₙ-pres-s mab₁ vw ⊢s ⊢w m₁ m₂
  = t-sub
      (mixed-mab-minus mab₁ ⊢s)
      (<:ₙ-comb (MUL-left-empty (MUL-left-empty (mixed-mab-num-empty mab₁ ⊢s) m₁) m₂) <:ₜ-refl)

β₁-pres-p : ∀ {s w η₁ ημ η₂ μ₂ η}
  → (abs₁ : ALL AbsValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ημ
  → MUL η₁ η₂ η
  → ∅ ⊢ mapE (λ v → mapE (λ b → sub₁ v b) (mapALL absbody abs₁)) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-p {w = w} abs₁ vw ⊢s ⊢w m
  = t-sub
      (mapE-minus {e = w}
        (λ v → mapE (λ b → sub₁ v b) (mapALL absbody abs₁))
        (λ {x} → mixed-abs-minus abs₁ ⊢s))
      (<:ₙ-comb (MUL-left-empty (mixed-abs-num-empty abs₁ ⊢s) m) <:ₜ-refl)


βₙ-pres-p : ∀ {s w η₁ ημ η₂ μ₂ η}
  → Value s
  → (mab₁ : ALL MabValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ημ
  → MUL η₁ η₂ η
  → ∅ ⊢ mapE (λ b → sub₁ w b) (mapALL mabbody mab₁) ⦂ ⟨ η , μ₂ ⟩
βₙ-pres-p vε Aε vw ⊢s ⊢w m
  = t-sub
      t-empty
      (<:ₙ-comb (MUL-left-empty (t-empty-inversion ⊢s) m) <:ₜ-refl)
βₙ-pres-p
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  (mab₁ A· mab₂)
  vw
  ⊢s
  ⊢w
  m
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μv , ⊢s₁! , ⊢s₂+ , +<:η₁ , μv<:μ
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μv<:μ)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μv<:μ)
      head-pres = βₙ-pres-p vs₁ mab₁ vw ⊢s₁η₁ ⊢w m
      tail-pres = βₙ-pres-p vs₂ mab₂ vw ⊢s₂η₁ ⊢w m
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul-left +<:η₁ m) <:ₜ-refl)
βₙ-pres-p {w = w} mab (AP (v-mab ημw b)) vw ⊢s ⊢w m
  with t-mab-inversion ⊢s
... | ημ₀ , <:ₙ-comb !<:η₁ (<:ₜ-⇛ ημ<:ημw ημ₀<:η₂μ₂) , ⊢b
  rewrite mapE-sub₁ {w = w} {e = b}
  = let
      η₂<:η = MUL-left-one-super !<:η₁ m
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub ⊢w ημ<:ημw
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)

preserve : ∀ {e e′ ημ}
  → ∅ ⊢ e ⦂ ημ
  → e ⟶ e′
  → ∅ ⊢ e′ ⦂ ημ
preserve (t-var {x = ()}) red
preserve t-cst ()
preserve (t-abs ⊢e) ()
preserve (t-mab ⊢e) ()
preserve (t-app-s ⊢s₁ ⊢s₂ m₁ m₂) (ξ-app₁ red) = t-app-s (preserve ⊢s₁ red) ⊢s₂ m₁ m₂
preserve (t-app-s ⊢s₁ ⊢s₂ m₁ m₂) (ξ-app₂ v₁ red) = t-app-s ⊢s₁ (preserve ⊢s₂ red) m₁ m₂
preserve (t-app-s ⊢s₁ ⊢s₂ m₁ m₂) (β₁ vs abs₁ v) = β₁-pres-s vs abs₁ v ⊢s₁ ⊢s₂ m₁ m₂
preserve (t-app-s ⊢s₁ ⊢s₂ m₁ m₂) (βₙ vs mab₁ v) = βₙ-pres-s mab₁ v ⊢s₁ ⊢s₂ m₁ m₂
preserve (t-app-p ⊢s₁ ⊢s₂ m) (ξ-app₁ red) = t-app-p (preserve ⊢s₁ red) ⊢s₂ m
preserve (t-app-p ⊢s₁ ⊢s₂ m) (ξ-app₂ v₁ red) = t-app-p ⊢s₁ (preserve ⊢s₂ red) m
preserve (t-app-p ⊢s₁ ⊢s₂ m) (β₁ vs abs₁ v) = β₁-pres-p abs₁ v ⊢s₁ ⊢s₂ m
preserve (t-app-p ⊢s₁ ⊢s₂ m) (βₙ vs mab₁ v) = βₙ-pres-p vs mab₁ v ⊢s₁ ⊢s₂ m
preserve (t-sub ⊢e ημ<:) red = t-sub (preserve ⊢e red) ημ<:
preserve t-empty ()
preserve (t-head ⊢e₁ ⊢e₂ refl) (ξ-head red) = t-head (preserve ⊢e₁ red) ⊢e₂ refl
preserve (t-head ⊢e₁ ⊢e₂ refl) (ξ-tail v red) = t-head ⊢e₁ (preserve ⊢e₂ red) refl
preserve (t-head {η₁ = η₁} ⊢e₁ ⊢e₂ refl) mon-ε-unit-left
  = t-sub ⊢e₂ (<:ₙ-comb (ADD-left-empty-super (t-empty-inversion ⊢e₁)) <:ₜ-refl)
preserve (t-head {η₁ = η₁} {η₂ = η₂} ⊢e₁ ⊢e₂ refl) mon-ε-unit-right
  = t-sub ⊢e₁ (<:ₙ-comb (ADD-right-empty-super (t-empty-inversion ⊢e₂)) <:ₜ-refl)
preserve (t-head {η₁ = η₁₂} {η₂ = η₃} ⊢e₁₂ ⊢e₃ refl) mon-·-assoc
  with t-head-inversion ⊢e₁₂
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:η₁₂ , μ₀<:μ , add-eq
  = t-sub
      (t-head
        (t-sub ⊢e₁ (<:ₙ-comb <:₀-refl μ₀<:μ))
        (t-head (t-sub ⊢e₂ (<:ₙ-comb <:₀-refl μ₀<:μ)) ⊢e₃ refl)
        refl)
      (<:ₙ-comb η<: <:ₜ-refl)
  where
  η-assoc : ADD η₁ (ADD η₂ η₃) <:₀ ADD (ADD η₁ η₂) η₃
  η-assoc rewrite ADD-assoc η₁ η₂ η₃ = <:₀-refl

  η-step : ADD (ADD η₁ η₂) η₃ <:₀ ADD η₁₂ η₃
  η-step = subst
    (λ x → ADD x η₃ <:₀ ADD η₁₂ η₃)
    (sym add-eq)
    (ADD-monotone-left η₀<:η₁₂)

  η<: : ADD η₁ (ADD η₂ η₃) <:₀ ADD η₁₂ η₃
  η<: = <:₀-trans η-assoc η-step

-- progress

all-single-absvalue : ∀ {μ}{ημ}{s} → (v   : Value s) (x   : AllSingleton (μ ⇒ ημ) s) → ALL AbsValue s
all-single-absvalue vε Aε = Aε
all-single-absvalue (v v· v₁) (x A· x₁) = (all-single-absvalue v x) A· (all-single-absvalue v₁ x₁)
all-single-absvalue cst (AP (sv-cst ()))
all-single-absvalue abs (AP (sv-abs (<:ₜ-⇒ x x₁))) = AP (v-abs _ _)
all-single-absvalue mab (AP (sv-mab ()))

all-single-mabvalue : ∀ {ημ}{ημ₁}{s} → (v   : Value s) (x   : AllSingleton (ημ ⇛ ημ₁) s) → ALL MabValue s
all-single-mabvalue vε Aε = Aε
all-single-mabvalue (v v· v₁) (x A· x₁) = (all-single-mabvalue v x) A· (all-single-mabvalue v₁ x₁)
all-single-mabvalue cst (AP (sv-cst ()))
all-single-mabvalue abs (AP (sv-abs ()))
all-single-mabvalue mab (AP (sv-mab x)) = AP (v-mab _ _)


data Progress (e : Expr zero) : Set where

  step : ∀ {e′} → e ⟶ e′ → Progress e
  done : Value e → Progress e

progress : ∀ {e}{ημ} → ∅ ⊢ e ⦂ ημ → Progress e
progress t-cst = done cst
progress (t-abs ⊢e) = done abs
progress (t-mab ⊢e) = done mab
progress (t-app-s ⊢e ⊢e₁ m m₁)
  with progress ⊢e
... | step e⟶ = step (ξ-app₁ e⟶)
... | done v
  with progress ⊢e₁
... | step e⟶ = step (ξ-app₂ v e⟶)
... | done w
  with canonical-sequence ⊢e v
... | seq-zero = step (β₁ v Aε w)
... | seq-one (sv-abs x) = step (β₁ v (AP (v-abs _ _)) w)
... | seq-opt-zero = step (β₁ v Aε w)
... | seq-opt-one (sv-abs x) = step (β₁ v (AP (v-abs _ _)) w)
... | seq-star x = step (β₁ v (all-single-absvalue v x) w)
... | seq-plus x x₁ = step (β₁ v (all-single-absvalue v x) w)
progress (t-app-p ⊢e ⊢e₁ m)
  with progress ⊢e
... | step e⟶ = step (ξ-app₁ e⟶)
... | done v
  with progress ⊢e₁
... | step e⟶ = step (ξ-app₂ v e⟶)
... | done w
  with canonical-sequence ⊢e v
... | seq-zero = step (β₁ v Aε w)
... | seq-one (sv-mab x) = step (βₙ v (AP (v-mab _ _)) w)
... | seq-opt-zero = step (β₁ v Aε w)
... | seq-opt-one (sv-mab x) = step (βₙ v (AP (v-mab _ _)) w)
... | seq-star all = step (βₙ v (all-single-mabvalue v all) w)
... | seq-plus all x₁ = step (βₙ v (all-single-mabvalue v all) w)
progress (t-sub ⊢e x) = progress ⊢e
progress t-empty = done vε
progress (t-head ⊢e ⊢e₁ add-eq)
  with progress ⊢e
... | step e⟶ = step (ξ-head e⟶)
... | done v
  with progress ⊢e₁
... | step e⟶ = step (ξ-tail v e⟶)
progress (t-head ⊢e ⊢e₁ add-eq) | done vε | done w = step mon-ε-unit-left
progress (t-head ⊢e ⊢e₁ add-eq) | done (v v· v₁) | done w = step mon-·-assoc
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done vε = step mon-ε-unit-right
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done ww@(w v· w₁) = done ((cst v· ww) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done cst = done ((cst v· cst) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done abs
  with t-cst-inversion ⊢e | t-abs-inversion ⊢e₁
... | <:ₙ-comb _ <:ₜ-□ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done mab
  with t-cst-inversion ⊢e | t-mab-inversion ⊢e₁
... | <:ₙ-comb _ <:ₜ-□ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done vε = step mon-ε-unit-right
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done ww@(w v· w₁) = done ((abs v· ww) {λ ()}{λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done cst
  with t-abs-inversion ⊢e | t-cst-inversion ⊢e₁
... | _ , <:ₙ-comb _ () , _ | <:ₙ-comb _ <:ₜ-□
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done abs = done ((abs v· abs) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done mab
  with t-abs-inversion ⊢e | t-mab-inversion ⊢e₁
... | _ , <:ₙ-comb _ (<:ₜ-⇒ _ _) , _ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done vε = step mon-ε-unit-right
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done ww@(w v· w₁) = done ((mab v· ww) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done cst
  with t-mab-inversion ⊢e | t-cst-inversion ⊢e₁
... | _ , <:ₙ-comb _ () , _ | <:ₙ-comb _ <:ₜ-□
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done abs
  with t-mab-inversion ⊢e | t-abs-inversion ⊢e₁
... | _ , <:ₙ-comb _ (<:ₜ-⇛ _ _) , _ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done mab = done ((mab v· mab) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
