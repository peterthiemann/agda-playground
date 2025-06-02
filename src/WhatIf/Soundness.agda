module Soundness where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; -,_; proj₁ ; proj₂; ∃-syntax; Σ)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)

open import Qualifiers
open import StackBasedBigStep



-- if Access 𝓔 s v before and s ∉ Γ, then Access 𝓔 s v afterwards

eval-preservation :
  Γ ⊢ e ⦂ S
  → Γ ⊨ 𝓔 / (𝓢 , σ)
  → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → Γ ⊨ 𝓔 / (𝓢′ , σ)
eval-preservation (TSub ⊢e x) ⊨𝓔 ⇓ = eval-preservation ⊢e ⊨𝓔 ⇓
eval-preservation ⊢e ⊨𝓔 EUnit = ⊨𝓔
eval-preservation ⊢e ⊨𝓔 (EVarH x) = ⊨𝓔
eval-preservation ⊢e ⊨𝓔 (EVarS x) = ⊨𝓔
eval-preservation ⊢e ⊨𝓔 EAbsH = ⊨𝓔
eval-preservation ⊢e ⊨𝓔 EAbsS = ⊨𝓔
eval-preservation ⊢e ⊨𝓔 (EAppH ⇓ ⇓₁ ⇓₂) = ⊨𝓔
eval-preservation (TApp ⊢e ⊢e₁) ⊨𝓔 (EAppS ⇓ ⇓₁ ⇓₂)
  using ⊨𝓔′ ← eval-preservation ⊢e ⊨𝓔 ⇓
  using ⊨𝓔″ ← eval-preservation ⊢e₁ ⊨𝓔′ ⇓₁
 = {!eval-preservation ? ? ⇓₂!}
eval-preservation (TRef ⊢e x) ⊨𝓔 (ERefH ⇓) = let ⊨𝓔′ = eval-preservation ⊢e (restrict  ⊨𝓔 x) ⇓ in {!!}
eval-preservation {Γ = Γ} (TRef ⊢e x) ⊨𝓔 (ERefS {q = q} ⇓ q=1 q=2)
  with q 
... | 𝟙
  with refl , refl , refl ← q=1 refl
    = let ⊨𝓔′ = eval-preservation ⊢e (restrict ⊨𝓔 x) ⇓ in {!!}
... | 𝟚
  with refl , refl ← q=2 refl
  rewrite sym (𝟚-bounded Γ)
  with refl ← x
    = let ⊨𝓔′ = eval-preservation ⊢e ⊨𝓔 ⇓ in mk-⊨ (⊨-heap ⊨𝓔′) {!!}
eval-preservation (TDeref ⊢e) ⊨𝓔 (EDerefH ⇓ x) = eval-preservation ⊢e ⊨𝓔 ⇓
eval-preservation (TDeref ⊢e) ⊨𝓔 (EDerefS ⇓ x x₁) = eval-preservation ⊢e ⊨𝓔 ⇓
eval-preservation (TSetref ⊢e ⊢e₁ x) ⊨𝓔 (ESetrefH ⇓ ⇓₁)
  using ⊨𝓔′ ← eval-preservation ⊢e ⊨𝓔 ⇓
  = eval-preservation ⊢e₁ ⊨𝓔′ ⇓₁
eval-preservation (TSetref ⊢e ⊢e₁ x₂) ⊨𝓔 (ESetrefS {q = q} ⇓ ⇓₁ q=1 q=2)
  using ⊨𝓔′ ← eval-preservation ⊢e ⊨𝓔 ⇓
  using ⊨𝓔″ ← eval-preservation ⊢e₁ ⊨𝓔′ ⇓₁
  with q
... | 𝟙
  with refl , refl ← q=1 refl = ⊨𝓔″
... | 𝟚
  with refl , wr ← q=2 refl = {!!}
eval-preservation (TSeq x ⊢e ⊢e₁ x₁) ⊨𝓔 (ESeq ⇓ ⇓₁)
  using ⊨𝓔′ ← eval-preservation ⊢e ⊨𝓔 ⇓
  = eval-preservation ⊢e₁ ⊨𝓔′ ⇓₁

-- properties


eval-soundness :
  Γ ⊢ e ⦂ S
  → Γ ⊨ 𝓔 / (𝓢 , σ)
  → q-of S ≤ q
  → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → ∃[ S′ ] S′ <⦂ S × [ v ⦂ S′ ]
eval-soundness TUnit ⊨𝓔 ≤q EUnit = -, <⦂-refl , TVUnit
eval-soundness {S = 𝟙 ^ T} {𝓢 = 𝓢} {σ} {𝟙} (TVar x) ⊨𝓔 ≤q (EVarH x₂) = -, <⦂-refl , access-soundness {𝓢σ = 𝓢 , σ} ⊨𝓔 x x₂
eval-soundness {S = 𝟙 ^ T} {𝓢 = 𝓢} {σ} {𝟚} (TVar x) ⊨𝓔 ≤q (EVarS x₂) = -, <⦂-refl , genaccess-soundness ⊨𝓔 x x₂
eval-soundness {S = 𝟚 ^ T} {q = 𝟚} (TVar x) ⊨𝓔 ≤-refl (EVarS x₂) = -, <⦂-refl , genaccess-soundness ⊨𝓔 x x₂
eval-soundness (TAbs{Γ = Γ} ⊢e refl) ⊨𝓔 ≤-refl EAbsH = -, <⦂-refl , let ⊨𝓔′ = restrict ⊨𝓔 refl in TVClos ⊨𝓔′ (q-bounded-idem{Γ = Γ} refl) ⊢e refl
eval-soundness (TAbs{Γ = Γ} ⊢e refl) ⊨𝓔 ≤-refl EAbsS = -, <⦂-refl , TVClos (restrict ⊨𝓔 refl) (q-bounded-idem{Γ = Γ} refl) ⊢e refl
eval-soundness (TAbs{Γ = Γ} ⊢e refl) ⊨𝓔 ≤-bottop EAbsS = -, <⦂-refl , TVClos (restrict ⊨𝓔 refl) (q-bounded-idem{Γ = Γ} refl) ⊢e {!!}
eval-soundness (TApp {S₁ = S₁}{S₂ = S₂} ⊢e₁ ⊢e₂) ⊨𝓔 ≤q (EAppH ⇓₁ ⇓₂ ⇓)
  with eval-soundness {q = 𝟚} ⊢e₁ ⊨𝓔 ≤-refl ⇓₁
... | S₁′ , SFun q≤𝟚 S₁<⦂Sc₁ sub₁ , TVClos {S₁ = Sc₁} {S₂ = Sc₂} ⊨𝓔′ q-bd ⊢e σ?≡
  with eval-soundness ⊢e₂ (eval-preservation ⊢e₁ ⊨𝓔 ⇓₁) (q-of-mono S₁<⦂Sc₁) ⇓₂
... | S₂′ , sub₂ , ⊢v₂
  with eval-soundness ⊢e {!!} ≤-refl ⇓
... | S′ , sub , ⊢v = S′ , {!!} , ⊢v
eval-soundness (TApp ⊢e₁ ⊢e₂) ⊨𝓔 ≤q (EAppS ⇓ ⇓₁ ⇓₂) = {!!}
eval-soundness (TSub ⊢e S₁<⦂S) ⊨𝓔 ≤q ⇓
  with eval-soundness ⊢e ⊨𝓔 (≤-trans (q-of-mono S₁<⦂S) ≤q) ⇓
... | S₂ , S₂<⦂S₁ , v⦂S₂ = S₂ , (<⦂-trans S₂<⦂S₁ S₁<⦂S , v⦂S₂)
eval-soundness (TSeq q₁≤q₂ ⊢e₁ ⊢e₂ qS≤) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness (TRef ⊢e Γ≡) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness (TDeref ⊢e) ⊨𝓔 ≤q ⇓ = {!!}
eval-soundness (TSetref ⊢e₁ ⊢e₂ S′<⦂S) ⊨𝓔 ≤q ⇓ = {!!}
