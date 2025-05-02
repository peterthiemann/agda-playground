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


-- heap & stack typing

-- data _⊨_/_ : Context → Env → Stack × StackMap → Set where
--   start : ∅ ⊨ 𝓔 / 𝓢σ

_⊨_/_ : (Γ : Context) → (𝓔 : Env) → Stack × StackMap → Set
Γ ⊨ 𝓔 / (𝓢 , σ) = ∀ {s}{T}{v} → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) →  Access 𝓔 s v → [ v ⦂ (T ^ 𝟙) ]

access-soundness : Γ ⊨ 𝓔 / 𝓢σ → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) → Access 𝓔 s v → [ v ⦂ (T ^ 𝟙) ]
access-soundness Γ⊨ x∈ access = Γ⊨ x∈ access

genaccess-soundness : Γ ⊨ 𝓔 / (𝓢 , σ) → Γ ∋ x ⦂ (T ^ 𝟙) → GenAccess 𝓔 𝓢 σ x v → [ v ⦂ (T ^ 𝟙) ]
genaccess-soundness Γ⊨ x∈ genaccess = {!!}

-- properties

eval-soundness :
  Γ ⊢ e ⦂ S
  → Γ ⊨ 𝓔 / (𝓢 , σ)
  → let q = q-of S
  in  𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → [ v ⦂ S ]
eval-soundness TUnit ⊨𝓔 EUnit = TVUnit
eval-soundness {S = T ^ 𝟙} {𝓢 = 𝓢} {σ} (TVar x) ⊨𝓔 (EVarH x₂) = access-soundness {𝓢σ = 𝓢 , σ} ⊨𝓔 x x₂
eval-soundness {S = T ^ 𝟚} (TVar x) ⊨𝓔 (EVarS x₂) = {!genaccess-soundness ⊨𝓔 !}
eval-soundness (TAbs ⊢e x) ⊨𝓔 ⇓ = {!!}
eval-soundness (TApp ⊢e ⊢e₁) ⊨𝓔 ⇓ = {!!}
eval-soundness (TSub ⊢e S₁<⦂S) ⊨𝓔 ⇓ = {!!}
eval-soundness (TSeq x ⊢e ⊢e₁ x₁) ⊨𝓔 ⇓ = {!!}
eval-soundness (TRef ⊢e x) ⊨𝓔 ⇓ = {!!}
eval-soundness (TDeref ⊢e) ⊨𝓔 ⇓ = {!!}
eval-soundness (TSetref ⊢e ⊢e₁ x) ⊨𝓔 ⇓ = {!!}
