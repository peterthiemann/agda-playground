module Soundness where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; -,_; proj₁ ; proj₂; ∃-syntax)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import StackBasedBigStep



-- properties


eval-soundness : wfΓ Γ
  → Γ ⊢ e ⦂ S
  → Γ ⊨ 𝓔 / (𝓢 , σ)
  → q-of S ≤ q
  → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → ∃[ S′ ] S′ <⦂ S × [ v ⦂ S′ ]
eval-soundness wfg TUnit ⊨𝓔 ≤q EUnit = -, <⦂-refl wf-Unit , TVUnit
eval-soundness {S = T ^ 𝟙} {𝓢 = 𝓢} {σ} {𝟙} wfg (TVar x) ⊨𝓔 ≤q (EVarH x₂) = -, <⦂-refl (wfg _ _ x) , access-soundness {𝓢σ = 𝓢 , σ} ⊨𝓔 x x₂
eval-soundness {S = T ^ 𝟙} {𝓢 = 𝓢} {σ} {𝟚} wfg (TVar x) ⊨𝓔 ≤q (EVarS x₂) = -, <⦂-refl (wfg _ _ x) , genaccess-soundness ⊨𝓔 x x₂
eval-soundness {S = T ^ 𝟚} {q = 𝟚} wfg (TVar x) ⊨𝓔 ≤-refl (EVarS x₂) = -, <⦂-refl (wfg _ _ x) , genaccess-soundness ⊨𝓔 x x₂
eval-soundness wfg (TAbs{Γ = Γ} wf-arg ⊢e refl) ⊨𝓔 ≤-refl EAbsH = -, <⦂-refl (wf-Fun wf-arg (wf-typing (wf-ext (wf-bounded wfg) wf-arg) ⊢e)) , let ⊨𝓔′ = restrict ⊨𝓔 refl in TVClos ⊨𝓔′ (q-bounded-idem{Γ = Γ} refl) ⊢e refl
eval-soundness wfg (TAbs{Γ = Γ} wf-arg ⊢e refl) ⊨𝓔 ≤-refl EAbsS = -, <⦂-refl (wf-Fun wf-arg (wf-typing (wf-ext (wf-bounded wfg) wf-arg) ⊢e)) , TVClos (restrict ⊨𝓔 refl) (q-bounded-idem{Γ = Γ} refl) ⊢e refl
eval-soundness wfg (TAbs{Γ = Γ} wf-arg ⊢e refl) ⊨𝓔 ≤-bottop EAbsS = -, <⦂-refl (wf-Fun wf-arg (wf-typing (wf-ext (wf-bounded wfg) wf-arg) ⊢e)) , TVClos (restrict ⊨𝓔 refl) (q-bounded-idem{Γ = Γ} refl) ⊢e {!!}
eval-soundness wfg (TApp ⊢e₁ ⊢e₂) ⊨𝓔 ≤q (EAppH ⇓₁ ⇓₂ ⇓)
  with eval-soundness {q = 𝟚} wfg ⊢e₁ ⊨𝓔 ≤-refl ⇓₁
... | - , sub , TVClos ⊨𝓔′ q-bd ⊢e σ?≡ = {!!}
eval-soundness wfg (TApp ⊢e₁ ⊢e₂) ⊨𝓔 ≤q (EAppS ⇓ ⇓₁ ⇓₂) = {!!}
eval-soundness wfg (TSub ⊢e S₁<⦂S) ⊨𝓔 ≤q ⇓
  with eval-soundness wfg ⊢e ⊨𝓔 (≤-trans (q-of-mono S₁<⦂S) ≤q) ⇓
... | S₂ , S₂<⦂S₁ , v⦂S₂ = S₂ , (<⦂-trans S₂<⦂S₁ S₁<⦂S , v⦂S₂)
eval-soundness wfg (TSeq q₁≤q₂ ⊢e₁ ⊢e₂ qS≤) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness wfg (TRef qS≤ ⊢e Γ≡) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness wfg (TDeref ⊢e) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness wfg (TSetref ⊢e₁ ⊢e₂ S′<⦂S) ⊨𝓔 ≤q ⇓ = {!!}
