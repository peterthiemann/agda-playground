module Substitution where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃-syntax; _,_; Σ)
open import Function using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)

open import Syntax

{-
Ren : Context → Context → Set
Ren Γ₁ Γ₂ = ∀ T → Γ₁ ∋ T → Γ₂ ∋ T

ren : Ren Γ₁ Γ₂ → Expr Γ₁ T ε → Expr Γ₂ T ε
ren ρ (var ≅Γ) = {!!}
ren ρ (lam d M) = {!!}
ren ρ (app d x x₁ M M₁) = {!!}
ren ρ unit = {!!}
ren ρ ((M ⨾ M₁) x) = {!!}
ren ρ (let1 M M₁ x) = {!!}
ren ρ (prod d x x₁ M M₁) = {!!}
ren ρ (case-⊗ d M M₁ x) = {!!}
ren ρ (inj i M) = {!!}
ren ρ (case-ΣΣ M x x₁) = {!!}
ren ρ (sub-ctx x x₁ M) = {!!}
-}

≅-↓ : Γ₁ ≅ Γ₂ → Γ₁ ≡ (𝓖 ↓ Γ) → ∃[ 𝓖′ ] ∃[ Γ′ ] Γ₂ ≡ 𝓖′ ↓ Γ′ × 𝓖 ↓ ∅ ≅ 𝓖′ ↓ ∅ × Γ ≅ Γ′
≅-↓ Γ₁≅Γ₂ = {!!}

≅₃-singleton-↓ : 𝓖 ↓ $[ T ] ≅₃ Γ → is-null-pattern 𝓖 → ∃[ 𝓖′ ] is-null-pattern 𝓖′ × Γ ≡ 𝓖′ ↓ $[ T ]
≅₃-singleton-↓ {⟪⟫} Γ≅ 𝓖0 = {!!}
≅₃-singleton-↓ {𝓖 ⨾ˡ Γ} Γ≅ 𝓖0 = {!!}
≅₃-singleton-↓ {Γ ⨾ʳ 𝓖} Γ≅ 𝓖0 = {!!}
≅₃-singleton-↓ {𝓖 ∥ˡ Γ} Γ≅ 𝓖0 = {!!}
≅₃-singleton-↓ {Γ ∥ʳ 𝓖} Γ≅ 𝓖0 = {!!}

≅-singleton-↓ : 𝓖 ↓ $[ T ] ≅ Γ → is-null-pattern 𝓖 → ∃[ 𝓖′ ] is-null-pattern 𝓖′ × Γ ≡ 𝓖′ ↓ $[ T ]
≅-singleton-↓ {𝓖} ≅-refl 𝓖0 = 𝓖 , 𝓖0 , refl
≅-singleton-↓ (≅-step eqv₃ Γ≅) 𝓖0
  with 𝓖₁ , 𝓖₁0 , refl ← ≅₃-singleton-↓ eqv₃ 𝓖0 = ≅-singleton-↓ Γ≅ 𝓖₁0

≅-singleton-≡ : $[ T₁ ] ≅ $[ T₂ ] → T₁ ≡ T₂
≅-singleton-≡ ≅-refl = refl
≅-singleton-≡ (≅-step x eqv) = {!!}



Ren : Γ₁ ≅ Γ₂ → Set
Ren {Γ₁}{Γ₂} Γ₁≅Γ₂ = ∀ T → Γ₁ ∋ T → Γ₂ ∋ T

ren-↓ : ∀ {Γ₁}{Γ₂} {Γ₁≅Γ₂ : Γ₁ ≅ Γ₂} → Ren Γ₁≅Γ₂ → Γ₁ ≡ 𝓖 ↓ Γ → Γ₂ ≡ 𝓖′ ↓ Γ′ → (𝓖≅ : 𝓖 ↓ ∅ ≅ 𝓖′ ↓ ∅) → (Γ≅ : Γ ≅ Γ′) → Ren 𝓖≅ × Ren Γ≅
ren-↓ = {!!}

ren-ext :  ∀ {Γ₁}{Γ₂} {Γ₁≅Γ₂ : Γ₁ ≅ Γ₂}{T₁} → ∀ d → Ren Γ₁≅Γ₂ → Ren (≅-ctx-extend{T = T₁} d Γ₁≅Γ₂)
ren-ext Left ρ T (left-⨾ here) = left-⨾ here
ren-ext Left ρ T (right-⨾ x) = right-⨾ (ρ T x)
ren-ext Right ρ T (left-⨾ x) = left-⨾ (ρ T x)
ren-ext Right ρ T (right-⨾ here) = right-⨾ here
ren-ext Unord ρ T (left-∥ here) = left-∥ here
ren-ext Unord ρ T (right-∥ x) = right-∥ (ρ T x)

ren : ∀ {Γ₁}{Γ₂} {Γ₁≅Γ₂ : Γ₁ ≅ Γ₂} → Ren Γ₁≅Γ₂ → Expr Γ₁ T ε → Expr Γ₂ T ε
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (var ≡Γ) = sub-ctx (≼-≅ (≅-sym Γ₁≅Γ₂)) ⊑-refl (var ≡Γ) -- var (≅-trans (≅-sym Γ₁≅Γ₂) ≅Γ) --sub-ctx (≼-≅ (≅-sym Γ₁≅Γ₂)) ⊑-refl var 
-- ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (var' isn) = {!var'!}
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (lam d M) = lam d (ren{Γ₁≅Γ₂ = ≅-ctx-extend d Γ₁≅Γ₂} (ren-ext{Γ₁≅Γ₂ = Γ₁≅Γ₂} d ρ) M)
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (app d cs es L M) = app d {!!} {!!} {!!} {!!}
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ unit = sub-ctx (≼-≅ (≅-sym Γ₁≅Γ₂)) ⊑-refl unit
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (_⨾_ {Γ = Γ}{𝓖 = 𝓖} L M cond gg)
  with ≅-↓{𝓖 = 𝓖}{Γ = Γ} Γ₁≅Γ₂ gg
... | 𝓖′ , Γ′ , Γ₂≡𝓖′↓Γ′ , 𝓖∅≅ , Γ≅Γ′
  with ρ𝓖 , ρΓ ← ren-↓ {Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ gg Γ₂≡𝓖′↓Γ′ 𝓖∅≅ Γ≅Γ′
    = (ren{Γ₁≅Γ₂ = Γ≅Γ′} ρΓ L ⨾ ren{Γ₁≅Γ₂ = 𝓖∅≅} ρ𝓖 M) {!cond!} Γ₂≡𝓖′↓Γ′
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (let1 L M cond gg) = {!!}
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (prod d cs es L M) = {!!}
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (case-⊗ d L M cond gg) = {!!}
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (inj i M) = {!!}
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (case-ΣΣ M x cond gg) = {!!}
ren{Γ₁≅Γ₂ = Γ₁≅Γ₂} ρ (sub-ctx x x₁ M) = {!!}

-- substitution

pat-extend : (d : Dir) → Pattern → Type → Pattern
pat-extend Left 𝓖 T = $[ T ] ⨾ʳ 𝓖
pat-extend Right 𝓖 T = 𝓖 ⨾ˡ $[ T ]
pat-extend Unord 𝓖 T = $[ T ] ∥ʳ 𝓖

ctx-pat-extend : (d : Dir) → ctx-extend d (ctx-pattern-fill 𝓖 Γ) T ≡ (pat-extend d 𝓖 T ↓ Γ)
ctx-pat-extend Left = refl
ctx-pat-extend Right = refl
ctx-pat-extend Unord = refl

pat-split : 𝓖′ ↓ $[ T ] ≡ 𝓖 ↓ Γ → ∃[ 𝓖₁ ] Γ ≡ 𝓖₁ ↓ $[ T ] × 𝓖′ ≡ pat-∘ 𝓖 𝓖₁
                                ⊎ ∃[ 𝓖₂ ] 𝓖 ↓ ∅ ≡ 𝓖₂ ↓ $[ T ]
pat-split = {!!}

⨾-injective : Γ₁ ⨾ Γ₂ ≡ Γ₃ ⨾ Γ₄ → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
⨾-injective refl = refl , refl

∥-injective : Γ₁ ∥ Γ₂ ≡ Γ₃ ∥ Γ₄ → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
∥-injective refl = refl , refl

pat-split' : ∀ Γ′ → 𝓖′ ↓ Γ′ ≡ 𝓖 ↓ Γ → ∃[ 𝓖₁ ] Γ ≡ 𝓖₁ ↓ Γ′ × 𝓖′ ≡ pat-∘ 𝓖 𝓖₁
                                    ⊎ ∃[ 𝓖₂ ] 𝓖 ↓ ∅ ≡ 𝓖₂ ↓ Γ′
                                    ⊎ Γ′ ≡ 𝓖 ↓ Γ
pat-split' {⟪⟫} {𝓖} Γ′ eq = inj₂ (inj₂ eq)
pat-split' {𝓖′} {⟪⟫} Γ′ eq = inj₁ (𝓖′ , sym eq , refl)
pat-split' {𝓖′ ⨾ˡ Γ} {𝓖 ⨾ˡ Γ₁} Γ′ eq
  with eq1 , refl ← ⨾-injective eq
  with pat-split'{𝓖′}{𝓖} Γ′ eq1
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , (iheq1 , cong₂ _⨾ˡ_ iheq2 refl))
... | inj₂ (inj₁ (𝓖₂ , iheq)) = inj₂ (inj₁ (𝓖₂ ⨾ˡ Γ , cong₂ _⨾_ iheq refl))
... | inj₂ (inj₂ y) = {!!}
pat-split' {𝓖′ ⨾ˡ Γ} {Γ₁ ⨾ʳ 𝓖} Γ′ eq = {!!}
pat-split' {Γ ⨾ʳ 𝓖′} {𝓖} Γ′ eq = {!!}
pat-split' {𝓖′ ∥ˡ Γ} {𝓖} Γ′ eq = {!!}
pat-split' {Γ ∥ʳ 𝓖′} {𝓖} Γ′ eq = {!!}

pat-split'' : ∀ 𝓖 𝓖′ {Γ}{Γ′} → 𝓖 ↓ Γ ≡ 𝓖′ ↓ Γ′
  → ∃[ 𝓖₁ ] Γ′ ≡ 𝓖₁ ↓ Γ × 𝓖 ≡ pat-∘ 𝓖′ 𝓖₁
  ⊎ ∃[ 𝓖₂ ] Γ ≡ 𝓖₂ ↓ Γ′ × 𝓖′ ≡ pat-∘ 𝓖 𝓖₂
  ⊎ {!!}
pat-split'' 𝓖 ⟪⟫ eq = inj₁ (𝓖 , sym eq , refl)
pat-split'' ⟪⟫ 𝓖′ eq = inj₂ (inj₁ (𝓖′ , eq , refl))
pat-split'' (𝓖 ⨾ˡ Γ) (𝓖′ ⨾ˡ Γ′) eq
  with eq1 , refl ← ⨾-injective eq
  with pat-split'' 𝓖 𝓖′ eq1
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , iheq1 , (cong₂ _⨾ˡ_ iheq2 refl))
... | inj₂ (inj₁ (𝓖₁ , iheq1 , iheq2)) = inj₂ (inj₁ (𝓖₁ , iheq1 , cong₂ _⨾ˡ_ iheq2 refl))
... | inj₂ (inj₂ y) = {!!}
pat-split'' (𝓖 ⨾ˡ Γ) (Γ′ ⨾ʳ 𝓖′) eq
  with eq1 , refl ← ⨾-injective eq
  = {!!}
pat-split'' (Γ ⨾ʳ 𝓖) (𝓖′ ⨾ˡ Γ₁) eq = {!!}
pat-split'' (Γ ⨾ʳ 𝓖) (Γ₁ ⨾ʳ 𝓖′) eq
  with refl , eq1 ← ⨾-injective eq
  with pat-split'' 𝓖 𝓖′ eq1
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , iheq1 , cong₂ _⨾ʳ_ refl iheq2)
... | inj₂ (inj₁ (𝓖₁ , iheq1 , iheq2)) = inj₂ (inj₁ (𝓖₁ , iheq1 , cong₂ _⨾ʳ_ refl iheq2))
... | inj₂ (inj₂ y) = {!!}
pat-split'' (𝓖 ∥ˡ Γ) (𝓖′ ∥ˡ Γ₁) eq
  with eq1 , refl ← ∥-injective eq
  with pat-split'' 𝓖 𝓖′ eq1
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , iheq1 , (cong₂ _∥ˡ_ iheq2 refl))
... | inj₂ (inj₁ (𝓖₁ , iheq1 , iheq2)) = inj₂ (inj₁ (𝓖₁ , iheq1 , cong₂ _∥ˡ_ iheq2 refl))
... | inj₂ (inj₂ y) = {!!}
pat-split'' (𝓖 ∥ˡ Γ) (Γ₁ ∥ʳ 𝓖′) eq = {!!}
pat-split'' (Γ ∥ʳ 𝓖) (𝓖′ ∥ˡ Γ₁) eq = {!!}
pat-split'' (Γ ∥ʳ 𝓖) (Γ₁ ∥ʳ 𝓖′) eq
  with refl , eq1 ← ∥-injective eq
  with pat-split'' 𝓖 𝓖′ eq1
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , iheq1 , cong₂ _∥ʳ_ refl iheq2)
... | inj₂ (inj₁ (𝓖₁ , iheq1 , iheq2)) = inj₂ (inj₁ (𝓖₁ , iheq1 , cong₂ _∥ʳ_ refl iheq2))
... | inj₂ (inj₂ y) = {!!}

---- substitution (maybe renaming is not needed)

sub : (𝓖 ↓ $[ T₁ ]) ≡ Γ → Expr Γ T ε → Expr Γ₁ T₁ Pure → Expr (𝓖 ↓ Γ₁) T ε
sub {𝓖 = ⟪⟫} {T₁} refl (var refl) V = V
sub {𝓖 = 𝓖} {T₁} {Γ} refl (lam{T₁ = Tₓ} d M) V = {!!}
  -- the following type checks, but upsets the termination checker
  -- let ih = sub {𝓖 = pat-extend d 𝓖 Tₓ} refl (subst (λ Γ → Expr Γ _ _) (ctx-pat-extend d) M) V in
  --                                                          lam d (subst (λ Γ → Expr Γ _ _) (sym (ctx-pat-extend d)) ih)
sub {𝓖 = 𝓖} {T₁} {Γ} eq (app d ctx-split-unord eff-split-unord L M) V
  with 𝓖
... | 𝓖′ ∥ˡ Γ with refl ← eq = app d ctx-split-unord eff-split-unord (sub {𝓖 = 𝓖′} {T₁} refl L V) M
... | Γ ∥ʳ 𝓖′ with refl ← eq = app d ctx-split-unord eff-split-unord L (sub {𝓖 = 𝓖′} {T₁} refl M V )
sub {𝓖 = 𝓖} {T₁} {Γ} eq (app d ctx-split-left eff-split-left L M) V
  with 𝓖
... | 𝓖′ ⨾ˡ Γ with refl ← eq = app d ctx-split-left eff-split-left L (sub refl M V)
... | Γ ⨾ʳ 𝓖′ with refl ← eq = app d ctx-split-left eff-split-left (sub refl L V) M
sub {𝓖 = 𝓖} {T₁} {Γ} eq (app d ctx-split-right eff-split-right L M) V
  with 𝓖
... | 𝓖′ ⨾ˡ Γ with refl ← eq = app d ctx-split-right eff-split-right (sub refl L V) M
... | Γ ⨾ʳ 𝓖′ with refl ← eq = app d ctx-split-right eff-split-right L (sub refl M V)
sub {𝓖 = ⟪⟫} {T₁} {Γ} () unit V
sub {𝓖 = 𝓖′} {T₁} {Γ} eq (_⨾_ {𝓖 = 𝓖} L M cond gg) V with refl ← eq
  with pat-split{𝓖′ = 𝓖′}{𝓖 = 𝓖} gg in eq
... | inj₁ (𝓖₁ , refl , refl) = (sub refl L V ⨾ M) cond (sym (pat-∘-↓{𝓖}{𝓖₁}))
... | inj₂ (𝓖₂ , eq2) = (L ⨾ (sub {!!} M V)) {!!} {!!}
sub {𝓖 = 𝓖} {T₁} {Γ} eq (let1 L M cond gg) V = {!!}
sub {𝓖 = 𝓖 ∥ˡ Γ₁} {T₁} {Γ} eq (prod d ctx-split-unord eff-split-unord L M) V with refl ← eq = prod d ctx-split-unord eff-split-unord (sub refl L V) M
sub {𝓖 = Γ₁ ∥ʳ 𝓖} {T₁} {Γ} eq (prod d ctx-split-unord eff-split-unord L M) V with refl ← eq = prod d ctx-split-unord eff-split-unord L (sub refl M V)
sub {𝓖 = 𝓖 ⨾ˡ Γ₁} {T₁} {Γ} eq (prod d ctx-split-left eff-split-left L M) V with refl ← eq = prod d ctx-split-left eff-split-left L (sub refl M V)
sub {𝓖 = Γ₁ ⨾ʳ 𝓖} {T₁} {Γ} eq (prod d ctx-split-left eff-split-left L M) V with refl ← eq = prod d ctx-split-left eff-split-left (sub refl L V) M
sub {𝓖 = 𝓖 ⨾ˡ Γ₁} {T₁} {Γ} eq (prod d ctx-split-right eff-split-right L M) V with refl ← eq = prod d ctx-split-right eff-split-right (sub refl L V) M
sub {𝓖 = Γ₁ ⨾ʳ 𝓖} {T₁} {Γ} eq (prod d ctx-split-right eff-split-right L M) V with refl ← eq = prod d ctx-split-right eff-split-right L (sub refl M V)
sub {𝓖 = 𝓖} {T₁} {Γ} eq (case-⊗ d L M cond gg) V = {!𝓖!}
sub {𝓖 = 𝓖} {T₁} {Γ} eq (inj i M) V with refl ← eq = inj i (sub refl M V)
sub {𝓖 = 𝓖} {T₁} {Γ} eq (case-ΣΣ M x cond gg) V = {!!}
sub {𝓖 = 𝓖} {T₁} {Γ} eq (sub-ctx Γ₁≼Γ₂ ε₁⊑ε₂ M) V with refl ← eq = let r = sub {!!} M V in sub-ctx {!!} ε₁⊑ε₂ {!!}
