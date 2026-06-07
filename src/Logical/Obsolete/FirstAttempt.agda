module SimplyNumbered where

open import Level using (Level) renaming (zero to lzero)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_⊔_ to _⊔ℕ_; _⊓_ to _⊓ℕ_; _≤_ to _≤ℕ_; _*_ to _*ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; *-zeroʳ; ≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.List using (List; []; _∷_; length; map; concat; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Function using (_∘_)

open import Interval
open import Numeri
open import Types

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

sub  : ∀ {S₁ S₂}{s} → Sub S₁ S₂ → Expr S₁ s → Expr S₂ s
sub σ [] = []
sub σ (e ∷ e*) = (sub σ e) ∷ (sub σ e*)
sub σ (var x) = σ x
sub σ (cst k) = cst k
sub σ (abs μ e) = abs μ {!!}
sub σ (mab ημ e) = mab ημ {!!}
sub σ (app e e₁) = app (sub σ e) (sub σ e₁)
sub σ (lst e) = lst (sub σ e)

sub₁ : ∀ {S} → Expr S Si → Expr (Si ∷ S) Si → Expr S Si
sub₁ {S} e₁ e₂ = sub σ e₂
  where
    σ : Sub (Si ∷ S) S
    σ (here refl) = e₁
    σ (there x) = var x

-- small step operational semantics

lengthE : Expr [] Mu → ℕ
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

down : ∀ {S}{s} → Expr S s → Expr S Si
down {S} {Si} e = e
down {S} {Mu} e = lst e

_⊨_⦂_ : ∀ {S}{s} → Ctx S → Expr S s → NTy → Set
Γ ⊨ e ⦂ ημ = ∀ σ → σ ∈ 𝓖⟦ Γ ⟧ → sub σ (down e) ∷ [] ∈ 𝓔⟦ ημ ⟧

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

  t-head :  ∀ {Γ : Ctx S}{e}{s}{ηₑ ηₛ η μ}
    → Γ ⊢ e ⦂ ⟨ ηₑ , μ ⟩
    → Γ ⊢ s ⦂ ⟨ ηₛ , μ ⟩
    → η ≡ ADD ηₑ ηₛ
    → Γ ⊢ (e ∷ s) ⦂ ⟨ η , μ ⟩

-- Typing Preservation

canonical-- : ∀ {s}{e : Expr [] s} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `- , μ ⟩ → Value [] e → Σ (s ≡ Mu) λ {refl → e ≡ []}
canonical-- t-empty [] = refl , refl
canonical-- (t-head {ηₑ = ηₑ} {ηₛ} ⊢e ⊢e₁ eq) (v ∷ v*)
  with ADD-zero ηₑ ηₛ eq
canonical-- (t-head {ηₑ = ηₑ} {ηₛ} ⊢e ⊢e₁ eq) (cst ∷ v*) | refl , refl = {!⊢e!}
canonical-- (t-head {ηₑ = ηₑ} {ηₛ} ⊢e ⊢e₁ eq) (abs ∷ v*) | refl , refl = {!!}
canonical-- (t-head {ηₑ = ηₑ} {ηₛ} ⊢e ⊢e₁ eq) (mab ∷ v*) | refl , refl = {!!}
canonical-- ⊢e cst = {!!}
canonical-- ⊢e abs = {!!}
canonical-- ⊢e mab = {!!}

preserves-⊢ :  ∀{s} → {e* e*′ : Expr [] s} → {ημ : NTy}
  → ∅ ⊢ e* ⦂ ημ
  → e* ⟶ e*′
  → ∅ ⊢ e*′ ⦂ ημ
preserves-⊢ (t-app-s ⊢e* ⊢e*₁ m₁ m₂) (ξ-app₁ e*⟶) = t-app-s (preserves-⊢ ⊢e* e*⟶) ⊢e*₁ m₁ m₂
preserves-⊢ (t-app-s ⊢e* ⊢e*₁ m₁ m₂) (ξ-app₂ val-e* e*⟶) = t-app-s ⊢e* (preserves-⊢ ⊢e*₁ e*⟶) m₁ m₂
preserves-⊢ (t-app-s ⊢e* ⊢e*₁ m₁ m₂) (β₁ abs₁ val-e*₁) = {!!}
preserves-⊢ (t-app-s ⊢e* ⊢e*₁ m₁ m₂) (βₙ mab₁ x) = {!!}
preserves-⊢ (t-app-p ⊢e* ⊢e*₁ m) e*⟶ = {!!}
preserves-⊢ (t-sub {ημ₁ = ημ₁} ⊢e* ημ₁<:ημ) e*⟶ = t-sub (preserves-⊢ ⊢e* e*⟶) ημ₁<:ημ
preserves-⊢ (t-head ⊢e ⊢e* eq) (ξ-head e⟶) = t-head (preserves-⊢ ⊢e e⟶) ⊢e* eq
preserves-⊢ (t-head (t-sub ⊢e x) ⊢e* eq) ξ-flat = {!!} -- need an inversion lemma here
preserves-⊢ (t-head (t-lst ⊢e) ⊢e* eq) ξ-flat = {!!}   -- need a lemma about ++E and ADD
preserves-⊢ (t-head ⊢e ⊢e* eq) (ξ-tail val-e e*⟶) = t-head ⊢e (preserves-⊢ ⊢e* e*⟶) eq

-- Fundamental Theorem
-- Γ ⊢ s : ημ ⇒ Γ ⊨ s : ημ

fundamental-theorem : ∀ {S}{s} → (Γ : Ctx S) → (e* : Expr S s) → (ημ : NTy)
  → Γ ⊢ e* ⦂ ημ
  → Γ ⊨ e* ⦂ ημ
fundamental-theorem Γ [] ημ t-empty σ σ⊨ = [] , (([] , z≤n , z≤n) , ⟶-step ξ-flat ⟶-refl)
fundamental-theorem Γ (e ∷ e*) ⟨ η , μ ⟩ (t-head {ηₑ = ηₑ} {ηₛ} ⊢e ⊢e* eq) σ σ⊨
  with fundamental-theorem Γ e ⟨ ηₑ , μ ⟩ ⊢e σ σ⊨
... | ihe
  with fundamental-theorem Γ e* ⟨ ηₛ , μ ⟩ ⊢e* σ σ⊨
... | ihe*
  = {!!}
fundamental-theorem Γ (var x) ημ t-var σ σ⊨ = {!!}
fundamental-theorem Γ (var x) ημ (t-sub ⊢e* ημ₁<:ημ) σ σ⊨ = {!!}
fundamental-theorem Γ (cst x) ημ (t-sub ⊢e* ημ₁<:ημ) σ σ⊨ = {!!}
fundamental-theorem Γ (abs x e*) ημ ⊢e* σ σ⊨ = {!!}
fundamental-theorem Γ (mab x e*) ημ ⊢e* σ σ⊨ = {!!}
fundamental-theorem Γ (app e* e*₁) ημ ⊢e* σ σ⊨ = {!!}
fundamental-theorem Γ (lst e*) ημ (t-sub ⊢e* ημ₁<:ημ) σ σ⊨ = {!!}
fundamental-theorem Γ (lst e*) ημ (t-lst ⊢e*) σ σ⊨ = {!!}
