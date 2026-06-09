module AlgorithmicSoundnessCompleteness where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Numeri
open import Types
open import Expressions
open import SimplyNumbered hiding (m; n; Γ)
open import Algorithmic hiding (n; Γ)

variable
  n : ℕ
  Γ : Ctx n

ADD-monotone-right : ∀ {η₁ η₂ η₃}
  → η₂ <:₀ η₃
  → ADD η₁ η₂ <:₀ ADD η₁ η₃
ADD-monotone-right {η₁} {η₂} {η₃} η₂<:η₃
  rewrite ADD-comm {η₁} {η₂}
        | ADD-comm {η₁} {η₃}
  = ADD-monotone-left η₂<:η₃

ADD-monotone-both : ∀ {η₁ η₂ η₁′ η₂′}
  → η₁ <:₀ η₁′
  → η₂ <:₀ η₂′
  → ADD η₁ η₂ <:₀ ADD η₁′ η₂′
ADD-monotone-both η₁<:η₁′ η₂<:η₂′ =
  <:₀-trans (ADD-monotone-left η₁<:η₁′) (ADD-monotone-right η₂<:η₂′)

EXT0-monotone : ∀ {η₁ η₂}
  → η₁ <:₀ η₂
  → EXT0 η₁ <:₀ EXT0 η₂
EXT0-monotone <:₀-refl = <:₀-refl
EXT0-monotone <:₀--? = <:₀--?
EXT0-monotone <:₀--* = <:₀--*
EXT0-monotone <:₀-!? = <:₀-refl
EXT0-monotone <:₀-!* = <:₀-?*
EXT0-monotone <:₀-!+ = <:₀-?*
EXT0-monotone <:₀-?* = <:₀-?*
EXT0-monotone <:₀-+* = <:₀-refl

mutual
  sound : ∀ {e : Expr n} {ημ}
    → Γ ⊢ᵃ e ⦂ ημ
    → Γ ⊢ e ⦂ ημ
  sound a-var = t-var
  sound a-cst = t-cst
  sound (a-abs ⊢s) = t-abs (sound ⊢s)
  sound (a-mab ⊢s) = t-mab (sound ⊢s)
  sound (a-app-s ⊢s₁ ⊢s₂ ηa<:η₃ μa<:μ₁ m₁ m₂) =
    t-app-s
      (check-sound ⊢s₁)
      (t-sub (sound ⊢s₂) (<:ₙ-comb ηa<:η₃ μa<:μ₁))
      m₁
      m₂
  sound (a-app-p ⊢s₁ ⊢s₂ ηarg<:ημ m) =
    t-app-p
      (check-sound ⊢s₁)
      (t-sub (sound ⊢s₂) ηarg<:ημ)
      m
  sound a-empty = t-empty
  sound (a-head ⊢e₁ ⊢e₂ μ₁<:μ μ₂<:μ) =
    t-head
      (t-sub (sound ⊢e₁) (<:ₙ-comb <:₀-refl μ₁<:μ))
      (t-sub (sound ⊢e₂) (<:ₙ-comb <:₀-refl μ₂<:μ))
      refl
  sound (a-mtc ⊢v val-v ⊢e ⊢s) =
    t-mtc (check-sound ⊢v) val-v (check-sound ⊢e) (sound ⊢s)

  check-sound : ∀ {e : Expr n} {ημ}
    → Γ ⊢ᶜ e ⦂ ημ
    → Γ ⊢ e ⦂ ημ
  check-sound (_ , ⊢e , ημ₀<:ημ) = t-sub (sound ⊢e) ημ₀<:ημ

complete : ∀ {e : Expr n} {ημ}
  → Γ ⊢ e ⦂ ημ
  → Γ ⊢ᶜ e ⦂ ημ
complete t-var = _ , a-var , <:ₙ-refl
complete t-cst = _ , a-cst , <:ₙ-refl
complete (t-abs {μ = μ} ⊢s)
  with complete ⊢s
... | ημ₀ , ⊢sᵃ , ημ₀<:ημ =
  _
  , a-abs ⊢sᵃ
  , <:ₙ-comb <:₀-refl (<:ₜ-⇒ <:ₜ-refl ημ₀<:ημ)
complete (t-mab {ημ = ημ} ⊢s)
  with complete ⊢s
... | ημ₀ , ⊢sᵃ , ημ₀<:ημ′ =
  _
  , a-mab ⊢sᵃ
  , <:ₙ-comb <:₀-refl (<:ₜ-⇛ <:ₙ-refl ημ₀<:ημ′)
complete (t-app-s {η₁ = η₁} {μ₁ = μ₁} {η₂ = η₂} {μ₂ = μ₂} {η₃ = η₃} {η = η} {η′ = η′} ⊢s₁ ⊢s₂ m₁ m₂)
  with complete ⊢s₁ | complete ⊢s₂
... | ⊢s₁ᶜ
    | ⟨ ηa , μa ⟩ , ⊢s₂ᵃ , <:ₙ-comb ηa<:η₃ μa<:μ₁ =
  ⟨ η , μ₂ ⟩
  , a-app-s ⊢s₁ᶜ ⊢s₂ᵃ ηa<:η₃ μa<:μ₁ m₁ m₂
  , <:ₙ-refl
complete (t-app-p {η₁ = η₁} {ημ = ημ} {η₂ = η₂} {μ₂ = μ₂} {η = η} ⊢s₁ ⊢s₂ m)
  with complete ⊢s₁ | complete ⊢s₂
... | ⊢s₁ᶜ
    | ηarg , ⊢s₂ᵃ , ηarg<:ημ =
  ⟨ η , μ₂ ⟩
  , a-app-p ⊢s₁ᶜ ⊢s₂ᵃ ηarg<:ημ m
  , <:ₙ-refl
complete (t-sub ⊢e ημ₁<:ημ₂)
  with complete ⊢e
... | ημ₀ , ⊢eᵃ , ημ₀<:ημ₁ =
  ημ₀ , ⊢eᵃ , <:ₙ-trans ημ₀<:ημ₁ ημ₁<:ημ₂
complete t-empty =
  ⟨ `- , `⊥ ⟩
  , a-empty
  , <:ₙ-comb <:₀-refl <:ₜ-⊥
complete (t-head {η₁ = η₁} {η₂ = η₂} {μ = μ} ⊢e₁ ⊢e₂ refl)
  with complete ⊢e₁ | complete ⊢e₂
... | ⟨ η₁ᵃ , μ₁ᵃ ⟩ , ⊢e₁ᵃ , <:ₙ-comb η₁ᵃ<:η₁ μ₁ᵃ<:μ
    | ⟨ η₂ᵃ , μ₂ᵃ ⟩ , ⊢e₂ᵃ , <:ₙ-comb η₂ᵃ<:η₂ μ₂ᵃ<:μ =
  ⟨ ADD η₁ᵃ η₂ᵃ , μ ⟩
  , a-head ⊢e₁ᵃ ⊢e₂ᵃ μ₁ᵃ<:μ μ₂ᵃ<:μ
  , <:ₙ-comb (ADD-monotone-both η₁ᵃ<:η₁ η₂ᵃ<:η₂) <:ₜ-refl
complete (t-mtc {v = v} {e = e} {s = s} {ημ = ημ} {η = η} {μ = μ} ⊢v val-v ⊢e ⊢s)
  with complete ⊢v | complete ⊢e | complete ⊢s
... | ⊢vᶜ | ⊢eᶜ | ⟨ ηᵃ , μᵃ ⟩ , ⊢sᵃ , <:ₙ-comb ηᵃ<:η μᵃ<:μ =
  ⟨ EXT0 ηᵃ , μᵃ ⟩
  , a-mtc ⊢vᶜ val-v ⊢eᶜ ⊢sᵃ
  , <:ₙ-comb (EXT0-monotone ηᵃ<:η) μᵃ<:μ
