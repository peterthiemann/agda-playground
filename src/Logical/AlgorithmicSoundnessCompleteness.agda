module AlgorithmicSoundnessCompleteness where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Numeri
open import Types
open import AlgorithmicOps
open import Expressions
open import SimplyNumbered hiding (m; n; Γ)
open import Algorithmic hiding (n; Γ)

variable
  n : ℕ
  Γ : Ctx n

mutual
  sound : ∀ {e : Expr n} {ημ}
    → Γ ⊢ᵃ e ⦂ ημ
    → Γ ⊢ e ⦂ ημ
  sound a-var = t-var
  sound a-cst = t-cst
  sound (a-abs ⊢s) = t-abs (sound ⊢s)
  sound (a-mab ⊢s) = t-mab (sound ⊢s)
  sound (a-app-s ⊢s₁ ⊢s₂ μa<:μ₁ m₁ m₂) =
    t-app-s
      (sound ⊢s₁)
      (t-sub (sound ⊢s₂) (<:ₙ-comb <:₀-refl μa<:μ₁))
      m₁
      m₂
  sound (a-app-p ⊢s₁ ⊢s₂ m) =
    t-app-p (sound ⊢s₁) (check-sound ⊢s₂) m
  sound (a-app-⊥-s {μa = μa} ⊢s₁ ηf<:η₁ ⊢s₂ ηa<:η₃ m₁ m₂) =
    t-app-s
      (t-sub (sound ⊢s₁) (<:ₙ-comb ηf<:η₁ <:ₜ-⊥))
      (t-sub (sound ⊢s₂) (<:ₙ-comb ηa<:η₃ <:ₜ-refl))
      m₁
      m₂
  sound (a-app-⊥-p ⊢s₁ ⊢s₂) =
    t-app-p
      (t-sub (sound ⊢s₁) (<:ₙ-comb <:₀-refl <:ₜ-⊥))
      (sound ⊢s₂)
      m0-right
  sound a-empty = t-empty
  sound (a-head {μ₁ = μ₁} {μ₂ = μ₂} ⊢e₁ ⊢e₂) =
    t-head
      (t-sub (sound ⊢e₁) (<:ₙ-comb <:₀-refl (⊔-upper-left μ₁ μ₂)))
      (t-sub (sound ⊢e₂) (<:ₙ-comb <:₀-refl (⊔-upper-right μ₁ μ₂)))
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
... | ⟨ ηf , `⊥ ⟩ , ⊢s₁ᵃ , <:ₙ-comb ηf<:η₁ <:ₜ-⊥
    | ⟨ ηa , μa ⟩ , ⊢s₂ᵃ , <:ₙ-comb ηa<:η₃ μa<:μ₁ =
  ⟨ η , `⊥ ⟩
  , a-app-⊥-s ⊢s₁ᵃ ηf<:η₁ ⊢s₂ᵃ ηa<:η₃ m₁ m₂
  , <:ₙ-comb <:₀-refl <:ₜ-⊥
... | ⟨ ηf , μf ⇒ ⟨ η₂f , μ₂f ⟩ ⟩ , ⊢s₁ᵃ , <:ₙ-comb ηf<:η₁ (<:ₜ-⇒ μ₁<:μf (<:ₙ-comb η₂f<:η₂ μ₂f<:μ₂))
    | ⟨ ηa , μa ⟩ , ⊢s₂ᵃ , <:ₙ-comb ηa<:η₃ μa<:μ₁ =
  ⟨ MUL₀ (MUL₀ ηf η₂f) ηa , μ₂f ⟩
  , a-app-s
      ⊢s₁ᵃ
      ⊢s₂ᵃ
      (<:ₜ-trans μa<:μ₁ μ₁<:μf)
      (MUL₀-sound ηf η₂f)
      (MUL₀-sound (MUL₀ ηf η₂f) ηa)
  , <:ₙ-comb
      (<:₀-trans
        (MUL₀-monotone
          (<:₀-trans (MUL₀-monotone ηf<:η₁ η₂f<:η₂) (MUL₀-complete m₁))
          ηa<:η₃)
        (MUL₀-complete m₂))
      μ₂f<:μ₂
complete (t-app-p {η₁ = η₁} {ημ = ημ} {η₂ = η₂} {μ₂ = μ₂} {η = η} ⊢s₁ ⊢s₂ m)
  with complete ⊢s₁ | complete ⊢s₂
... | ⟨ ηf , `⊥ ⟩ , ⊢s₁ᵃ , <:ₙ-comb ηf<:η₁ <:ₜ-⊥
    | ηarg , ⊢s₂ᵃ , ηarg<:ημ =
  ⟨ η , `⊥ ⟩
  , a-app-⊥-p ⊢s₁ᵃ ⊢s₂ᵃ
  , <:ₙ-comb <:₀-refl <:ₜ-⊥
... | ⟨ ηf , ημf ⇛ ⟨ η₂f , μ₂f ⟩ ⟩ , ⊢s₁ᵃ , <:ₙ-comb ηf<:η₁ (<:ₜ-⇛ ημ<:ημf (<:ₙ-comb η₂f<:η₂ μ₂f<:μ₂))
    | ηarg , ⊢s₂ᵃ , ηarg<:ημ =
  ⟨ MUL₀ ηf η₂f , μ₂f ⟩
  , a-app-p
      ⊢s₁ᵃ
      (ηarg , ⊢s₂ᵃ , <:ₙ-trans ηarg<:ημ ημ<:ημf)
      (MUL₀-sound ηf η₂f)
  , <:ₙ-comb
      (<:₀-trans (MUL₀-monotone ηf<:η₁ η₂f<:η₂) (MUL₀-complete m))
      μ₂f<:μ₂
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
  , a-head ⊢e₁ᵃ ⊢e₂ᵃ
  , <:ₙ-comb
      (ADD-monotone-both η₁ᵃ<:η₁ η₂ᵃ<:η₂)
      (⊔-least μ₁ᵃ<:μ μ₂ᵃ<:μ)
complete (t-mtc {v = v} {e = e} {s = s} {ημ = ημ} {η = η} {μ = μ} ⊢v val-v ⊢e ⊢s)
  with complete ⊢v | complete ⊢e | complete ⊢s
... | ⊢vᶜ | ⊢eᶜ | ⟨ ηᵃ , μᵃ ⟩ , ⊢sᵃ , <:ₙ-comb ηᵃ<:η μᵃ<:μ =
  ⟨ EXT0 ηᵃ , μᵃ ⟩
  , a-mtc ⊢vᶜ val-v ⊢eᶜ ⊢sᵃ
  , <:ₙ-comb (EXT0-monotone ηᵃ<:η) μᵃ<:μ
