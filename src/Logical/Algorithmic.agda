module Algorithmic where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤)

open import Numeri
open import Types
open import Expressions
open import Values using (Value)
open import SimplyNumbered using (Ctx; ∅; lookup; _▻_; _⊢_⦂_)

variable
  n : ℕ
  Γ : Ctx n

-- A small completion of multiplicities with an artificial bottom.
-- The declarative system still speaks in terms of Num; Num⊥ is useful
-- for principal implementations that want to record "no possible
-- multiplicity" without perturbing the existing development over Num.

data Num⊥ : Set where
  `⊘ : Num⊥
  ↑₀  : Num → Num⊥

infix 4 _<:₀⊥_
_<:₀⊥_ : Num⊥ → Num⊥ → Set
`⊘    <:₀⊥ η      = ⊤
↑₀ η₁ <:₀⊥ `⊘    = ⊥
↑₀ η₁ <:₀⊥ ↑₀ η₂ = η₁ <:₀ η₂

ADD⊥ : Num⊥ → Num⊥ → Num⊥
ADD⊥ `⊘      _       = `⊘
ADD⊥ _       `⊘      = `⊘
ADD⊥ (↑₀ η₁) (↑₀ η₂) = ↑₀ (ADD η₁ η₂)

-- The syntax-directed judgement.  It has no final subsumption rule.
-- Places where syntax naturally needs an expected type (application
-- domains, common sequence element types) carry local subtype premises.

infix 2 _⊢ᵃ_⦂_
infix 2 _⊢ᶜ_⦂_
mutual
  data _⊢ᵃ_⦂_ {n : ℕ} : Ctx n → Expr n → NTy → Set where

    a-var : ∀ {x}
      → Γ ⊢ᵃ var x ⦂ lookup x Γ

    a-cst : ∀ {k}
      → Γ ⊢ᵃ cst k ⦂ ⟨ `! , □ ⟩

    a-abs : ∀ {μ s ημ}
      → (⟨ `! , μ ⟩ ▻ Γ) ⊢ᵃ s ⦂ ημ
      → Γ ⊢ᵃ abs μ s ⦂ ⟨ `! , μ ⇒ ημ ⟩

    a-mab : ∀ {ημ s ημ′}
      → (ημ ▻ Γ) ⊢ᵃ s ⦂ ημ′
      → Γ ⊢ᵃ mab ημ s ⦂ ⟨ `! , ημ ⇛ ημ′ ⟩

    a-app-s : ∀ {s₁ s₂ η₁ μ₁ η₂ μ₂ ηa μa η₃ η η′}
      → Γ ⊢ᶜ s₁ ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
      → Γ ⊢ᵃ s₂ ⦂ ⟨ ηa , μa ⟩
      → ηa <:₀ η₃
      → μa <:ₜ μ₁
      → MUL η₁ η₂ η′
      → MUL η′ η₃ η
      → Γ ⊢ᵃ app s₁ s₂ ⦂ ⟨ η , μ₂ ⟩

    a-app-p : ∀ {s₁ s₂ η₁ ημ ηarg η₂ μ₂ η}
      → Γ ⊢ᶜ s₁ ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
      → Γ ⊢ᵃ s₂ ⦂ ηarg
      → ηarg <:ₙ ημ
      → MUL η₁ η₂ η
      → Γ ⊢ᵃ app s₁ s₂ ⦂ ⟨ η , μ₂ ⟩

    a-empty :
      Γ ⊢ᵃ ε ⦂ ⟨ `- , `⊥ ⟩

    a-head : ∀ {e₁ e₂ η₁ μ₁ η₂ μ₂ μ}
      → Γ ⊢ᵃ e₁ ⦂ ⟨ η₁ , μ₁ ⟩
      → Γ ⊢ᵃ e₂ ⦂ ⟨ η₂ , μ₂ ⟩
      → μ₁ <:ₜ μ
      → μ₂ <:ₜ μ
      → Γ ⊢ᵃ (e₁ · e₂) ⦂ ⟨ ADD η₁ η₂ , μ ⟩

    a-mtc : ∀ {v e s ημ η μ}
      → ∅ ⊢ᶜ v ⦂ ημ
      → Value v
      → Γ ⊢ᶜ e ⦂ ημ
      → Γ ⊢ᵃ s ⦂ ⟨ η , μ ⟩
      → Γ ⊢ᵃ mtc v e s ⦂ ⟨ EXT0 η , μ ⟩

-- Checking against a declarative type is synthesis plus one explicit
-- subtype comparison.  This is the form used by completeness.

  _⊢ᶜ_⦂_ : Ctx n → Expr n → NTy → Set
  Γ ⊢ᶜ e ⦂ ημ = Σ NTy λ ημ₀ → (Γ ⊢ᵃ e ⦂ ημ₀) × (ημ₀ <:ₙ ημ)
