module Substitution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃-syntax; _,_; Σ; proj₁; proj₂)
open import Function using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst)

open import Syntax


-- substitution

pat-extend : (d : Dir) → Pattern → Type → Pattern
pat-extend Left 𝓖 T = $[ T ] ⨾ʳ 𝓖
pat-extend Right 𝓖 T = 𝓖 ⨾ˡ $[ T ]
pat-extend Unord 𝓖 T = $[ T ] ∥ʳ 𝓖

ctx-pat-extend : (d : Dir) → ctx-extend d (𝓖 ↓ Γ) T ≡ (pat-extend d 𝓖 T ↓ Γ)
ctx-pat-extend Left = refl
ctx-pat-extend Right = refl
ctx-pat-extend Unord = refl

⨾-injective : Γ₁ ⨾ Γ₂ ≡ Γ₃ ⨾ Γ₄ → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
⨾-injective refl = refl , refl

∥-injective : Γ₁ ∥ Γ₂ ≡ Γ₃ ∥ Γ₄ → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
∥-injective refl = refl , refl

pat-split : 𝓖′ ↓ $[ T ] ≡ 𝓖 ↓ Γ → ∃[ 𝓖₁ ] Γ ≡ 𝓖₁ ↓ $[ T ] × 𝓖′ ≡ pat-∘ 𝓖 𝓖₁
                                ⊎ ∃[ 𝓖₂ ] 𝓖 ↓ ∅ ≡ 𝓖₂ ↓ $[ T ] ×  ∀ Γ′ → ∃[ 𝓖₃ ] 𝓖₃ ↓ ∅ ≡ 𝓖₂ ↓ Γ′
pat-split {⟪⟫} {T} {⟪⟫} {Γ} refl = inj₁ (⟪⟫ , refl , refl)
pat-split {𝓖′ ⨾ˡ Γ₁} {T} {⟪⟫} {Γ} refl = inj₁ ((𝓖′ ⨾ˡ Γ₁) , refl , refl)
pat-split {𝓖′ ⨾ˡ Γ₁} {T} {𝓖 ⨾ˡ Γ₂} {Γ} eq
  with eq , refl ← ⨾-injective eq
  with pat-split {𝓖′} {T} {𝓖} {Γ} eq
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , iheq1 , (cong₂ _⨾ˡ_ iheq2 refl))
... | inj₂ (𝓖₂ , iheq1 , feq) = inj₂ (𝓖₂ ⨾ˡ _ , cong₂ _⨾_ iheq1 refl , (λ Γ′ → let 𝓖₃ , geq = feq Γ′ in (𝓖₃ ⨾ˡ Γ₁) , cong₂ _⨾_ geq refl))
pat-split {𝓖′ ⨾ˡ Γ₁} {T} {Γ₂ ⨾ʳ 𝓖} {Γ} eq 
  with refl , refl ← ⨾-injective eq
  = inj₂ ((𝓖′ ⨾ˡ (𝓖 ↓ ∅)) , refl , λ Γ′ → ((𝓖′ ↓ Γ′) ⨾ʳ 𝓖) , refl)
pat-split {Γ₁ ⨾ʳ 𝓖′} {T} {⟪⟫} {Γ} refl = inj₁ ((Γ₁ ⨾ʳ 𝓖′) , (refl , refl))
pat-split {Γ₁ ⨾ʳ 𝓖′} {T} {𝓖 ⨾ˡ Γ₂} {Γ} eq
  with refl , refl ← ⨾-injective eq
  = inj₂ (((𝓖 ↓ ∅) ⨾ʳ 𝓖′) , refl , λ Γ′ → (𝓖 ⨾ˡ (𝓖′ ↓ Γ′)) , refl)
pat-split {Γ₁ ⨾ʳ 𝓖′} {T} {Γ₂ ⨾ʳ 𝓖} {Γ} eq
  with refl , eq ← ⨾-injective eq
  with pat-split {𝓖′} {T} {𝓖} {Γ} eq
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , (iheq1 , (cong₂ _⨾ʳ_ refl iheq2)))
... | inj₂ (𝓖₂ , iheq , feq) = inj₂ ((Γ₁ ⨾ʳ 𝓖₂) , cong₂ _⨾_ refl iheq , λ Γ′ → let 𝓖₃ , geq = feq Γ′ in (Γ₁ ⨾ʳ 𝓖₃) , cong₂ _⨾_ refl geq)
pat-split {𝓖′ ∥ˡ Γ₁} {T} {⟪⟫} {Γ} refl = inj₁ ((𝓖′ ∥ˡ Γ₁) , refl , refl)
pat-split {𝓖′ ∥ˡ Γ₁} {T} {𝓖 ∥ˡ Γ₂} {Γ} eq
  with eq , refl ← ∥-injective eq
  with pat-split {𝓖′} {T} {𝓖} {Γ} eq
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , iheq1 , (cong₂ _∥ˡ_ iheq2 refl))
... | inj₂ (𝓖₂ , iheq , feq) = inj₂ (𝓖₂ ∥ˡ _ , cong₂ _∥_ iheq refl , λ Γ′ → let 𝓖₃ , geq = feq Γ′ in (𝓖₃ ∥ˡ Γ₁) , cong₂ _∥_ geq refl)
pat-split {𝓖′ ∥ˡ Γ₁} {T} {Γ₂ ∥ʳ 𝓖} {Γ} eq
  with refl , refl ← ∥-injective eq
  = inj₂ ((𝓖′ ∥ˡ (𝓖 ↓ ∅)) , refl , λ Γ′ → ((𝓖′ ↓ Γ′) ∥ʳ 𝓖) , refl)
pat-split {Γ₁ ∥ʳ 𝓖′} {T} {⟪⟫} {Γ} refl = inj₁ ((Γ₁ ∥ʳ 𝓖′) , refl , refl)
pat-split {Γ₁ ∥ʳ 𝓖′} {T} {𝓖 ∥ˡ Γ₂} {Γ} eq
  with refl , refl ← ∥-injective eq
  = inj₂ (((𝓖 ↓ ∅) ∥ʳ 𝓖′) , refl , λ Γ′ → (𝓖 ∥ˡ (𝓖′ ↓ Γ′)) , refl)
pat-split {Γ₁ ∥ʳ 𝓖′} {T} {Γ₂ ∥ʳ 𝓖} {Γ} eq
  with refl , eq ← ∥-injective eq
  with pat-split {𝓖′} {T} {𝓖} {Γ} eq
... | inj₁ (𝓖₁ , iheq1 , iheq2) = inj₁ (𝓖₁ , (iheq1 , (cong₂ _∥ʳ_ refl iheq2)))
... | inj₂ (𝓖₂ , iheq , feq) = inj₂ ((Γ₁ ∥ʳ 𝓖₂) , cong₂ _∥_ refl iheq , λ Γ′ → let 𝓖₃ , geq = feq Γ′ in (Γ₁ ∥ʳ 𝓖₃) , cong₂ _∥_ refl geq)


-- lemma01 : (𝓖 ↓ ∅) ≡ (𝓖₂ ↓ $[ T₁ ]) → ∃[ 𝓖₂′ ] 𝓖 ↓ $[ T₂ ] ≡ 𝓖₂′ ↓ $[ T₁ ]
-- lemma02 : (𝓖 ↓ ∅) ≡ (𝓖₂ ↓ $[ T₁ ]) → ∀ Γ′ → ∃[ 𝓖₂′ ] 𝓖 ↓ $[ T₂ ] ≡ 𝓖₂′ ↓ $[ T₁ ]

lemma1 : (𝓖 ↓ ∅) ≡ (𝓖₂ ↓ $[ T₁ ]) → ∀ Γ → ∃[ 𝓖₂′ ] 𝓖 ↓ Γ ≡ 𝓖₂′ ↓ $[ T₁ ]
lemma1 {⟪⟫} {⟪⟫} ()
lemma1 {⟪⟫} {𝓖₂ ⨾ˡ Γ} ()
lemma1 {⟪⟫} {Γ ⨾ʳ 𝓖₂} ()
lemma1 {⟪⟫} {𝓖₂ ∥ˡ Γ} ()
lemma1 {⟪⟫} {Γ ∥ʳ 𝓖₂} ()
lemma1 {𝓖 ⨾ˡ Γ} {𝓖₂ ⨾ˡ Γ₁}{T₁} eq Γ′
  with eq1 , refl ← ⨾-injective eq
  with lemma1 {𝓖}{𝓖₂}{T₁} eq1 Γ′
... | 𝓖₂′ , ih = (𝓖₂′ ⨾ˡ Γ) , cong₂ _⨾_ ih refl
lemma1 {𝓖 ⨾ˡ Γ} {Γ₁ ⨾ʳ 𝓖₂}{T₁} refl Γ′ = ((𝓖 ↓ Γ′) ⨾ʳ 𝓖₂) , refl
lemma1 {Γ ⨾ʳ 𝓖} {𝓖₂ ⨾ˡ Γ₁}{T₁} refl Γ′ = (𝓖₂ ⨾ˡ (𝓖 ↓ Γ′)) , refl
lemma1 {Γ ⨾ʳ 𝓖} {Γ₁ ⨾ʳ 𝓖₂}{T₁} eq Γ′
  with refl , eq1 ← ⨾-injective eq
  with lemma1 {𝓖}{𝓖₂}{T₁} eq1 Γ′
... | 𝓖₂′ , ih = (Γ ⨾ʳ 𝓖₂′) , cong₂ _⨾_ refl ih
lemma1 {𝓖 ∥ˡ Γ} {𝓖₂ ∥ˡ Γ₁}{T₁} eq Γ′
  with eq1 , refl ← ∥-injective eq
  with lemma1 {𝓖}{𝓖₂}{T₁} eq1 Γ′
... | 𝓖₂′ , ih = (𝓖₂′ ∥ˡ Γ) , cong₂ _∥_ ih refl
lemma1 {𝓖 ∥ˡ Γ} {Γ₁ ∥ʳ 𝓖₂} {T₁} refl Γ′ = ((𝓖 ↓ Γ′) ∥ʳ 𝓖₂) , refl
lemma1 {Γ ∥ʳ 𝓖} {𝓖₂ ∥ˡ Γ₁} {T₁} refl Γ′ = (𝓖₂ ∥ˡ (𝓖 ↓ Γ′)) , refl
lemma1 {Γ ∥ʳ 𝓖} {Γ₁ ∥ʳ 𝓖₂}{T₁} eq Γ′
  with refl , eq1 ← ∥-injective eq
  with lemma1 {𝓖}{𝓖₂}{T₁} eq1 Γ′
... | 𝓖₂′ , ih = (Γ ∥ʳ 𝓖₂′) , cong₂ _∥_ refl ih

lemma2 : (𝓖₂ ↓ $[ T₂ ]) ≡ (𝓖₁ ↓ $[ T₁ ]) → 𝓖₁ ≢ 𝓖₂ → ∀ Γ → ∃[ 𝓖 ] 𝓖₁ ↓ Γ ≡ 𝓖 ↓ $[ T₂ ]
lemma2 {⟪⟫} {T₂} {⟪⟫} {T₁} eq neq Γ = ⊥-elim (neq refl)
lemma2 {𝓖₂ ⨾ˡ Γ₁} {T₂} {𝓖₁ ⨾ˡ Γ₂} {T₁} eq neq Γ
  with eq1 , refl ← ⨾-injective eq
  with lemma2 {𝓖₂}{T₂}{𝓖₁}{T₁} eq1 (λ x → neq (cong₂ _⨾ˡ_ x refl)) Γ
... | 𝓖 , ih-eq  = (𝓖 ⨾ˡ Γ₁) , cong₂ _⨾_ ih-eq refl
lemma2 {𝓖₂ ⨾ˡ Γ₁} {T₂} {Γ₂ ⨾ʳ 𝓖₁} {T₁} refl neq Γ = (𝓖₂ ⨾ˡ (𝓖₁ ↓ Γ)) , refl
lemma2 {Γ₁ ⨾ʳ 𝓖₂} {T₂} {𝓖₁ ⨾ˡ Γ₂} {T₁} refl neq Γ = ((𝓖₁ ↓ Γ) ⨾ʳ 𝓖₂) , refl
lemma2 {Γ₁ ⨾ʳ 𝓖₂} {T₂} {Γ₂ ⨾ʳ 𝓖₁} {T₁} eq neq Γ
  with refl , eq1 ← ⨾-injective eq
  with lemma2 {𝓖₂}{T₂}{𝓖₁}{T₁} eq1 (λ x → neq (cong₂ _⨾ʳ_ refl x)) Γ
... | 𝓖 , ih-eq  = (Γ₁ ⨾ʳ 𝓖) , cong₂ _⨾_ refl ih-eq
lemma2 {𝓖₂ ∥ˡ Γ₁} {T₂} {𝓖₁ ∥ˡ Γ₂} {T₁} eq neq Γ
  with eq1 , refl ← ∥-injective eq
  with lemma2 {𝓖₂}{T₂}{𝓖₁}{T₁} eq1 (λ x → neq (cong₂ _∥ˡ_ x refl)) Γ
... | 𝓖 , ih-eq  = (𝓖 ∥ˡ Γ₁) , cong₂ _∥_ ih-eq refl
lemma2 {𝓖₂ ∥ˡ Γ₁} {T₂} {Γ₂ ∥ʳ 𝓖₁} {T₁} refl neq Γ = (𝓖₂ ∥ˡ (𝓖₁ ↓ Γ)) , refl
lemma2 {Γ₁ ∥ʳ 𝓖₂} {T₂} {𝓖₁ ∥ˡ Γ₂} {T₁} refl neq Γ = ((𝓖₁ ↓ Γ) ∥ʳ 𝓖₂) , refl
lemma2 {Γ₁ ∥ʳ 𝓖₂} {T₂} {Γ₂ ∥ʳ 𝓖₁} {T₁} eq neq Γ
  with refl , eq1 ← ∥-injective eq
  with lemma2 {𝓖₂}{T₂}{𝓖₁}{T₁} eq1 (λ x → neq (cong₂ _∥ʳ_ refl x)) Γ
... | 𝓖 , ih-eq  = (Γ₁ ∥ʳ 𝓖) , cong₂ _∥_ refl ih-eq

---- substitution (maybe renaming is not needed)

sub : (𝓖 ↓ $[ T₁ ]) ≡ Γ → Expr Γ T ε → Expr Γ₁ T₁ Pure → Expr (𝓖 ↓ Γ₁) T ε
sub {𝓖 = 𝓖} {T₁} eq0 (var refl) V
  with 𝓖
... | ⟪⟫ with refl ← eq0 = V
sub {𝓖 = ⟪⟫} {T₁} {Γ} () unit V
sub {𝓖 = 𝓖} {T₁} {Γ} eq0 (lam{T₁ = Tₓ} d M) V  with refl ← eq0 =
  let ih = sub {𝓖 = pat-extend d 𝓖 Tₓ} (sym (ctx-pat-extend d)) M V in
  lam d (subst (λ Γ → Expr Γ _ _) (sym (ctx-pat-extend d)) ih)
sub {𝓖 = 𝓖} {T₁} {Γ} eq (app d ctx-split-unord eff-split-unord L M) V
  with 𝓖
... | 𝓖′ ∥ˡ Γ with refl ← eq = app d ctx-split-unord eff-split-unord (sub {𝓖 = 𝓖′} {T₁} refl L V) M
... | Γ ∥ʳ 𝓖′ with refl ← eq = app d ctx-split-unord eff-split-unord L (sub {𝓖 = 𝓖′} {T₁} refl M V )
sub {𝓖 = 𝓖} {T₁} {Γ} eq (app d ctx-split-left eff-split-left L M) V
  with 𝓖
... | 𝓖′ ⨾ˡ Γ with refl ← eq = app d ctx-split-left eff-split-left L (sub  refl M V)
... | Γ ⨾ʳ 𝓖′ with refl ← eq = app d ctx-split-left eff-split-left (sub  refl L V) M
sub {𝓖 = 𝓖} {T₁} {Γ} eq (app d ctx-split-right eff-split-right L M) V
  with 𝓖
... | 𝓖′ ⨾ˡ Γ with refl ← eq = app d ctx-split-right eff-split-right (sub  refl L V) M
... | Γ ⨾ʳ 𝓖′ with refl ← eq = app d ctx-split-right eff-split-right L (sub  refl M V)
sub {𝓖 = 𝓖′} {T₁} {Γ} {Γ₁ = Γ₁} eq (_⨾_ {𝓖 = 𝓖} L M cond gg) V with refl ← eq
  with pat-split{𝓖′ = 𝓖′}{𝓖 = 𝓖} gg in eq
... | inj₁ (𝓖₁ , refl , refl) = (sub refl L V ⨾ M) cond (sym (pat-∘-↓{𝓖}{𝓖₁}))
... | inj₂ (𝓖₂ , eq2 , feq) = let ih = sub (sym eq2) M V in let 𝓖₃ , geq = feq Γ₁ in (L ⨾ subst (λ Γ′ → Expr Γ′ _ _) (sym geq) ih) (λ ε₁≡Impure → {!cond ε₁≡Impure!}) {!!}
-- V    : Expr Γ₁ T₁ Pure
-- L    : Expr Γ₂ T₂ ε₁
-- M    : Expr (𝓖 ↓ $[ T₂ ]) T ε₂
-- L ⨾ M : Expr (𝓖 ↓ Γ₂) T (ε₁ ⊔ ε₂)
-- eq2  : (𝓖 ↓ ∅) ≡ (𝓖₂ ↓ $[ T₁ ])
-- gg   : (𝓖′ ↓ $[ T₁ ]) ≡ (𝓖 ↓ Γ₂)
-- lemma : (𝓖 ↓ ∅) ≡ (𝓖₂ ↓ $[ T₁ ]) → ∃[ 𝓖₂′ ] 𝓖 ↓ $[ T₂ ] ≡ 𝓖₂′ ↓ $[ T₁ ]
sub {𝓖 = 𝓖′} {T₁} {Γ} {Γ₁ = Γ₁} eq0 (let1 {T₁ = T₂}{𝓖 = 𝓖} L M cond gg) V
  with refl ← eq0
  with pat-split{𝓖′ = 𝓖′}{𝓖 = 𝓖} gg in eq
... | inj₁ (𝓖₁ , refl , refl) = let1 (sub  refl L V) M cond (sym (pat-∘-↓{𝓖}{𝓖₁}))
... | inj₂ (𝓖₂ , eq2 , feq)
  = let feq2 = lemma1 {T₁ = T₁} eq2 in
    let 𝓖₂′ , geq-1 = feq2 $[ T₂ ] in
    let ih = sub (sym geq-1) M V in
    let 𝓖₂″ , geq-2 = lemma2 geq-1 {!!} Γ₁ in
    let1 {𝓖 = 𝓖₂″} L (subst (λ Γ → Expr Γ _ _) geq-2 ih) {!!} {!!}
-- geq-1 : (𝓖 ↓ $[ T₂ ]) ≡ (𝓖₂′ ↓ $[ T₁ ])
-- needed : ∀ Γ₁ → ∃[ 𝓖‴ ] (𝓖₂′ ↓ Γ₁) ≡ 𝓖‴ ↓ $[ T₂ ]
-- lemma2 : (𝓖₂ ↓ $[ T₂ ]) ≡ (𝓖₁ ↓ $[ T₁ ]) → ∀ Γ → ∃[ 𝓖 ] 𝓖₁ ↓ Γ ≡ 𝓖 ↓ $[ T₂ ]
sub {𝓖 = 𝓖 ∥ˡ Γ₁} {T₁} {Γ} eq (prod d ctx-split-unord eff-split-unord L M) V with refl ← eq = prod d ctx-split-unord eff-split-unord (sub  refl L V) M
sub {𝓖 = Γ₁ ∥ʳ 𝓖} {T₁} {Γ} eq (prod d ctx-split-unord eff-split-unord L M) V with refl ← eq = prod d ctx-split-unord eff-split-unord L (sub  refl M V)
sub {𝓖 = 𝓖 ⨾ˡ Γ₁} {T₁} {Γ} eq (prod d ctx-split-left eff-split-left L M) V with refl ← eq = prod d ctx-split-left eff-split-left L (sub refl M V)
sub {𝓖 = Γ₁ ⨾ʳ 𝓖} {T₁} {Γ} eq (prod d ctx-split-left eff-split-left L M) V with refl ← eq = prod d ctx-split-left eff-split-left (sub refl L V) M
sub {𝓖 = 𝓖 ⨾ˡ Γ₁} {T₁} {Γ} eq (prod d ctx-split-right eff-split-right L M) V with refl ← eq = prod d ctx-split-right eff-split-right (sub  refl L V) M
sub {𝓖 = Γ₁ ⨾ʳ 𝓖} {T₁} {Γ} eq (prod d ctx-split-right eff-split-right L M) V with refl ← eq = prod d ctx-split-right eff-split-right L (sub  refl M V)
sub {𝓖 = 𝓖} {T₁} {Γ} eq (case-⊗ d L M cond gg) V = {!𝓖!}
sub {𝓖 = 𝓖} {T₁} {Γ} eq (inj i M) V with refl ← eq = inj i (sub  refl M V)
sub {𝓖 = 𝓖} {T₁} {Γ} eq (case-ΣΣ M x cond gg) V = {!!}
sub {𝓖 = 𝓖} {T₁} {Γ} eq (sub-ctx Γ₁≼Γ₂ ε₁⊑ε₂ M) V with refl ← eq = let r = sub  {!!} M V in sub-ctx {!!} ε₁⊑ε₂ {!!}

{-  renaming is most likely unneeded

≅-↓ : Γ₁ ≅ Γ₂ → Γ₁ ≡ (𝓖 ↓ Γ) → ∃[ 𝓖′ ] ∃[ Γ′ ] Γ₂ ≡ 𝓖′ ↓ Γ′ × 𝓖 ↓ ∅ ≅ 𝓖′ ↓ ∅ × Γ ≅ Γ′
≅-↓ Γ₁≅Γ₂ = {!!}

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
-}
