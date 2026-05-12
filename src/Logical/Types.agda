module Types where

open import Numeri

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
  <:ₙ-comb : ∀ {μ₁ μ₂} {η₁ η₂} → η₁ <:₀ η₂ → μ₁ <:ₜ μ₂ → ⟨ η₁ , μ₁ ⟩ <:ₙ ⟨ η₂ , μ₂ ⟩

<:ₜ-refl : ∀ {μ} → μ <:ₜ μ
<:ₙ-refl : ∀ {ημ} → ημ <:ₙ ημ

<:ₜ-refl {`⊥} = <:ₜ-⊥
<:ₜ-refl {□} = <:ₜ-□
<:ₜ-refl {μ ⇒ ημ} = <:ₜ-⇒ <:ₜ-refl <:ₙ-refl
<:ₜ-refl {ημ ⇛ ημ₁} = <:ₜ-⇛ <:ₙ-refl <:ₙ-refl

<:ₙ-refl {⟨ num , ty ⟩} = <:ₙ-comb <:₀-refl <:ₜ-refl

<:ₜ-trans : ∀ {μ₁ μ₂ μ₃} → μ₁ <:ₜ μ₂ → μ₂ <:ₜ μ₃ → μ₁ <:ₜ μ₃
<:ₙ-trans : ∀ {ημ₁ ημ₂ ημ₃} → ημ₁ <:ₙ ημ₂ → ημ₂ <:ₙ ημ₃ → ημ₁ <:ₙ ημ₃

<:ₜ-trans <:ₜ-⊥ <:ₜ-⊥ = <:ₜ-⊥
<:ₜ-trans <:ₜ-⊥ <:ₜ-□ = <:ₜ-⊥
<:ₜ-trans <:ₜ-⊥ (<:ₜ-⇒ μ₂<: x) = <:ₜ-⊥
<:ₜ-trans <:ₜ-⊥ (<:ₜ-⇛ x x₁) = <:ₜ-⊥
<:ₜ-trans <:ₜ-□ <:ₜ-□ = <:ₜ-□
<:ₜ-trans (<:ₜ-⇒ μ₁<: ημ₁<:) (<:ₜ-⇒ μ₂<: ημ₂<:) = <:ₜ-⇒ (<:ₜ-trans μ₂<: μ₁<:) (<:ₙ-trans ημ₁<: ημ₂<:)
<:ₜ-trans (<:ₜ-⇛ ημ₁<: ημ₂<:) (<:ₜ-⇛ ημ₃<: ημ₄<:) = <:ₜ-⇛ (<:ₙ-trans ημ₃<: ημ₁<:) (<:ₙ-trans ημ₂<: ημ₄<:)

<:ₙ-trans (<:ₙ-comb x μ₁<:) (<:ₙ-comb x₂ μ₂<:) = <:ₙ-comb (<:₀-trans x x₂) (<:ₜ-trans μ₁<: μ₂<:)
