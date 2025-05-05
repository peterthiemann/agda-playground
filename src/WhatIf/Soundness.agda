module Soundness where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; proj₁ ; proj₂)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import StackBasedBigStep



-- properties

eval-soundness :
  Γ ⊢ e ⦂ S
  → Γ ⊨ 𝓔 / (𝓢 , σ)
  → q-of S ≤ q
  → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → [ v ⦂ S ]
eval-soundness TUnit ⊨𝓔 ≤q EUnit = TVUnit
eval-soundness {S = T ^ 𝟙} {𝓢 = 𝓢} {σ} {𝟙} (TVar x) ⊨𝓔 ≤q (EVarH x₂) = access-soundness {𝓢σ = 𝓢 , σ} ⊨𝓔 x x₂
eval-soundness {S = T ^ 𝟙} {𝓢 = 𝓢} {σ} {𝟚} (TVar x) ⊨𝓔 ≤q (EVarS x₂) = genaccess-soundness ⊨𝓔 x x₂
eval-soundness {S = T ^ 𝟚} {q = 𝟚} (TVar x) ⊨𝓔 ≤-refl (EVarS x₂) = genaccess-soundness ⊨𝓔 x x₂
eval-soundness (TAbs{Γ = Γ} ⊢e q-bd) ⊨𝓔 ≤-refl EAbsH = let ⊨𝓔′ = restrict ⊨𝓔 q-bd in TVClos ⊨𝓔′ (q-bounded-idem{Γ = Γ} q-bd) ⊢e refl
eval-soundness (TAbs{Γ = Γ} ⊢e q-bd) ⊨𝓔 ≤-refl EAbsS = TVClos (restrict ⊨𝓔 q-bd) (q-bounded-idem{Γ = Γ} q-bd) ⊢e refl
eval-soundness (TAbs{Γ = Γ} ⊢e q-bd) ⊨𝓔 ≤-bottop EAbsS = TVClos (restrict ⊨𝓔 q-bd) (q-bounded-idem{Γ = Γ} q-bd) ⊢e {!!}
eval-soundness (TApp ⊢e ⊢e₁) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness (TSub ⊢e S<⦂S₁) ⊨𝓔 ≤q ⇓ = TVSub S<⦂S₁ (eval-soundness ⊢e ⊨𝓔 (≤-trans (q-of-mono S<⦂S₁) ≤q) ⇓)
eval-soundness (TSeq x ⊢e ⊢e₁ x₁) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness (TRef ⊢e x) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness (TDeref ⊢e) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness (TSetref ⊢e ⊢e₁ x) ⊨𝓔 ≤q ⇓ = {!!}
