module Simple.Soundness where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; foldr)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; [] ; _∷_; ++⁺)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; fromℕ<; inject≤)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using () renaming (≤-trans to ≤ℕ-trans)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; -,_; proj₁ ; proj₂; ∃-syntax; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

open import Qualifiers
open import Auxiliary
open import Simple.StackBasedBigStep
-- open import Simple.Extends


--

⊨-extend : Σₕₛ ≼ₕₛ Σₕₛ′ → 𝓢 ≼ₛ 𝓢′ → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢 → ⟨ Σₕₛ′ , Γ ⟩⊨ 𝓔 / 𝓢′
⊢ᵥ-extend : Σₕₛ ≼ₕₛ Σₕₛ′ → 𝓢 ≼ₛ 𝓢′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ] → ⟨ Σₕₛ′ ⟩⊢[ v ⦂ S ]

⊨-extend {𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼Σ ≼𝓢 ⊨𝓔 = mk-⊨ (λ x → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x in v , acc , ⊢ᵥ-extend {𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼Σ ≼𝓢 ⊢v)
                         (λ x → let a , sacc , v , jv≡ , ⊢v = ⊨-stack ⊨𝓔 x in a , sacc , v , ↓ᵥ-mono{𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼𝓢 jv≡ , ⊢ᵥ-extend {𝓢 = 𝓢}{𝓢′ = 𝓢′} ≼Σ ≼𝓢 ⊢v)
⊢ᵥ-extend ≼Σ ≼𝓢 TVUnit = TVUnit
⊢ᵥ-extend ≼Σ ≼𝓢 TVCst = TVCst
⊢ᵥ-extend ≼Σ ≼𝓢 (TVClos {𝓢′ = 𝓢ᶜ} {q = 𝟙} ⊨𝓔 𝓢≼ refl qbd ⊢e wf₁ wf₂ <⦂S)
  = TVClos {𝓢′ = 𝓢ᶜ} (⊨-extend ≼Σ (≼ₛ-refl {𝓢ᶜ}) ⊨𝓔) 𝓢≼ refl qbd ⊢e wf₁ wf₂ <⦂S
⊢ᵥ-extend ≼Σ ≼𝓢 (TVClos {𝓢′ = 𝓢ᶜ} {q = 𝟚} ⊨𝓔 𝓢≼ 𝓢≡ qbd ⊢e wf₁ wf₂ <⦂S)
  = TVClos {𝓢′ = 𝓢ᶜ} (⊨-extend ≼Σ (≼ₛ-refl {𝓢ᶜ}) ⊨𝓔) 𝓢≼ 𝓢≡ qbd ⊢e wf₁ wf₂ <⦂S
⊢ᵥ-extend {Σₕₛ = Σₕₛ} ≼Σ ≼𝓢 (TVRef {q = q} ℓ< lkup≡ <⦂S)
  with ≼Σ q in eq
... | qts , eq1 = TVRef (≤ℕ-trans ℓ< (≼ₕₛ⇒length ≼Σ q)) (trans (lookup-from-i′ (Σₕₛ q) ℓ< eq1) lkup≡) <⦂S

-- properties

postulate
  eval-preservation :
    Γ ⊢ e ⦂ S
    → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢
    → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
    → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢′


variable
  HSs SSs : List QType
  

record Soundness (Σₕₛ : HSType) (v : Val) (S : QType) (𝓗′ : Heap) (𝓢 𝓢′ : Stack) : Set where
  field
    sound-Σₕₛ′ : HSType
    sound-Σ≼   : Σₕₛ ≼ₕₛ Σₕₛ′
    sound-⊢v   : ⟨ Σₕₛ′ ⟩⊢[ v ⦂ S ]
    sound-⊢𝓗  : Σₕₛ′ ⊢ₕ 𝓗′
    sound-⊢𝓢   : Σₕₛ′ ⊢ₛ 𝓢′
    sound-𝓢≼   : 𝓢 ≼ₛ 𝓢′


eval-soundness :
  Σₕₛ ⊢ₕ 𝓗
  → Σₕₛ ⊢ₛ 𝓢
  → Γ ⊢ e ⦂ S
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → q-of S ≤ q
  → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → ∃[ Σₕₛ′ ] Σₕₛ ≼ₕₛ Σₕₛ′ × ⟨ Σₕₛ′ ⟩⊢[ v ⦂ S ] × Σₕₛ′ ⊢ₕ 𝓗′ × Σₕₛ′ ⊢ₛ 𝓢′ × 𝓢 ≼ₛ 𝓢′
-- → Soundness Σₕₛ v S 𝓗′ 𝓢 𝓢′ 

----- subtyping

eval-soundness ⊢𝓗 ⊢𝓢 (TSub ⊢e S<⦂) ⊨𝓔 ≤-q ⇓
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 (≤-trans (q-of-mono S<⦂) ≤-q) ⇓
... | _ , Σ≼ , ⊢v , ⊢𝓗′ , ⊢𝓢′ , 𝓢≼𝓢′
  = -, Σ≼ , <⦂-val-lift ⊢v S<⦂ , ⊢𝓗′ , ⊢𝓢′ , 𝓢≼𝓢′
eval-soundness {𝓢 = 𝓢} ⊢𝓗 ⊢𝓢 TUnit ⊨𝓔 ≤-q EUnit = -, ≼ₕₛ-refl , TVUnit , ⊢𝓗 , ⊢𝓢 , ≼ₛ-refl{𝓢}

----- variables

eval-soundness {𝓢 = 𝓢} ⊢𝓗 ⊢𝓢 (TVar x) ⊨𝓔 ≤-refl (EVarH acc)
  = -, ≼ₕₛ-refl , access-soundness ⊨𝓔 x acc , ⊢𝓗 , ⊢𝓢 , ≼ₛ-refl{𝓢}
eval-soundness {𝓢 = 𝓢} {S = mkQ 𝟙 T} ⊢𝓗 ⊢𝓢 (TVar {x = X s 𝟚} x∈) ⊨𝓔 ≤-q (EVarS (on-stack sacc) dec≡)
  = -, ≼ₕₛ-refl , genaccess-soundness-𝟚 ⊨𝓔 x∈ (on-stack sacc) _ dec≡ , ⊢𝓗 , ⊢𝓢 , ≼ₛ-refl{𝓢}
eval-soundness {𝓢 = 𝓢} {S = mkQ 𝟚 T} ⊢𝓗 ⊢𝓢 (TVar {x = X s 𝟙} x∈) ⊨𝓔 ≤-q (EVarS (on-heap hacc) refl)
  = -, ≼ₕₛ-refl , genaccess-soundness ⊨𝓔 x∈ (on-heap hacc) , ⊢𝓗 , ⊢𝓢 , ≼ₛ-refl{𝓢}

----- abstraction

eval-soundness {𝓢 = 𝓢} {q = 𝟙} ⊢𝓗 ⊢𝓢 (TAbs ⊢e qbdd {wf₁} {wf₂}) ⊨𝓔 ≤-refl (EAbs {q₁ = 𝟙} ≤-refl ≤-refl refl)
  = -, ≼ₕₛ-refl , TVClos (restrict′ ⊨𝓔 qbdd) (≼ₛ-refl {mkS [] []}) refl (is-bounded qbdd) ⊢e wf₁ wf₂ <⦂-refl , ⊢𝓗 , ⊢𝓢 , ≼ₛ-refl{𝓢}
eval-soundness {𝓢 = 𝓢} {q = 𝟚} ⊢𝓗 ⊢𝓢 (TAbs ⊢e qbdd {wf₁} {wf₂}) ⊨𝓔 ≤-refl (EAbs {q₁ = 𝟚} ≤-refl ≤-top refl)
  = -, ≼ₕₛ-refl , TVClos (restrict′ ⊨𝓔 qbdd) (≼ₛ-refl {𝓢}) refl (is-bounded qbdd) ⊢e wf₁ wf₂ <⦂-refl , ⊢𝓗 , ⊢𝓢 , ≼ₛ-refl{𝓢}

----- application

eval-soundness {q = 𝟙} ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-refl (EApp {𝓢 = 𝓢}{q = 𝟙} {q₁ = 𝟙}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″} ≤-refl ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVClos {q = 𝟙} {x = X s _} ⊨𝓔′ 𝓢≼ refl qbd ⊢e₀ wf₁ ≤-refl (SQual qsub (SFun{S₁ = S₁@ (T₁ ^ 𝟙)} S₁<⦂S₂ S₃<⦂S₄)) , ⊢𝓗′ , ⊢𝓢′ , 𝓢≼𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (⊨-extend ≼Σ′ 𝓢≼𝓢′ ⊨𝓔) (≤-trans (q-of-mono S₁<⦂S₂) wf₁) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″ , 𝓢′≼𝓢″
  using ⊨𝓔″ ← ⊨-extend-𝟙 s T₁ (⊢ᵥ-adjust (<⦂-val-lift ⊢varg S₁<⦂S₂)) (⊨-adjust {Σₛ = []} (⊨-extend-Σ ≼Σ″ ⊨𝓔′) (𝟙-bound⇒∀𝟚∉ qbd))
  with eval-soundness (⊢ₕ-adjust [] [] ⊢𝓗″) [] ⊢e₀ ⊨𝓔″ (≤-trans (q-of-mono S₃<⦂S₄) ≤-refl) ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴ , ≼𝓢‴
  using ≼Σ₁₂ ← ≼ₕₛ-trans ≼Σ′ ≼Σ″
  = adjust-stack Σₕₛ‴ (Σₕₛ″ 𝟚)
  , ≼ₕₛ-trans ≼Σ₁₂ (≼ₕₛ-adjust-[] ≼Σ‴)
  , ⊢ᵥ-adjust (<⦂-val-lift ⊢vres S₃<⦂S₄)
  , ⊢ₕ-adjust (Σₕₛ″ 𝟚) (⊢ₛ-adjust-[] {𝓢 = 𝓢″} ≼Σ‴ ⊢𝓢″) ⊢𝓗‴
  , ⊢ₛ-adjust-[] {𝓢 = 𝓢″} ≼Σ‴ ⊢𝓢″
  , ≼ₛ-trans{𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢″} 𝓢≼𝓢′ 𝓢′≼𝓢″

eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-q (EApp {q = 𝟙}{q₁ = 𝟚} q2< ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVClos {S₁≤x = ()} ⊨𝓔₁ 𝓢≼ 𝓢≡ qbd ⊢e₂ ≤-refl ≤-refl (SQual qsub (SFun S₁<⦂S₂ S₃<⦂S₄)) , ⊢𝓗′ , ⊢𝓢′ , 𝓢≼𝓢′

eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-q (EApp {q₀ = 𝟙}{𝓢 = 𝓢}{q = 𝟚}{q₁ = 𝟙}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″}{𝓢‴ = 𝓢‴} ≤-refl ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVClos {x = X s _} {S₁≤x = refl} ⊨𝓔₁ 𝓢≼ 𝓢≡ qbd ⊢e₂ wf₁ wf₂ (SQual qsub (SFun{S₁ = S₁@ (T₁ ^ 𝟙)} S₁<⦂S₂ S₃<⦂S₄)) , ⊢𝓗′ , ⊢𝓢′ , 𝓢≼𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (⊨-extend ≼Σ′ 𝓢≼𝓢′ ⊨𝓔) (q-of-mono S₁<⦂S₂) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″ , 𝓢′≼𝓢″
  using ⊨𝓔″ ← ⊨-extend ≼Σ″
  with eval-soundness ⊢𝓗″ ⊢𝓢″ ⊢e₂ {! ⊨𝓔₁!} (≤-trans (q-of-mono S₃<⦂S₄) ≤-q) ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴ , ≼𝓢‴
  = Σₕₛ‴ , (≼ₕₛ-trans ≼Σ′ (≼ₕₛ-trans ≼Σ″ ≼Σ‴)) , <⦂-val-lift ⊢vres S₃<⦂S₄ , ⊢𝓗‴ , ⊢𝓢‴ , (≼ₛ-trans{𝓢₁ = 𝓢}{𝓢₂ = 𝓢′}{𝓢₃ = 𝓢‴} 𝓢≼𝓢′ (≼ₛ-trans{𝓢₁ = 𝓢′}{𝓢₂ = 𝓢″}{𝓢₃ = 𝓢‴} 𝓢′≼𝓢″ ≼𝓢‴))

eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-q (EApp {q₀ = 𝟚}{q = 𝟚}{q₁ = 𝟙} q2< ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVClos {x = X s _} {S₁≤x = refl} ⊨𝓔₁ 𝓢≼ 𝓢≡ qbd ⊢e₂ wf₁ wf₂ (SQual qsub (SFun{S₁ = S₁@ (T₁ ^ 𝟙)} S₁<⦂S₂ S₃<⦂S₄)) , ⊢𝓗′ , ⊢𝓢′ , 𝓢≼𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (⊨-extend ≼Σ′ 𝓢≼𝓢′ ⊨𝓔) (q-of-mono S₁<⦂S₂) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″ , 𝓢′≼𝓢″
  with eval-soundness ⊢𝓗″ ⊢𝓢″ ⊢e₂ {!⊨𝓔₁!} {!!} ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴ , ≼𝓢‴
  = {!!}

eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-q (EApp {q = 𝟚}{q₁ = 𝟚} q2< ⇓ ⇓₁ ⇓₂ refl)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVClos {S₁≤x = refl} ⊨𝓔₁ 𝓢≼ 𝓢≡ qbd ⊢e₂ wf₁ wf₂ (SQual qsub (SFun S₁<⦂S₂ S₃<⦂S₄)) , ⊢𝓗′ , ⊢𝓢′ , 𝓢≼𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (⊨-extend ≼Σ′ 𝓢≼𝓢′ ⊨𝓔) (q-of-mono S₁<⦂S₂) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″ , 𝓢′≼𝓢″
  with eval-soundness ⊢𝓗″ ⊢𝓢″ ⊢e₂ {!⊨𝓔₁!} {!!} ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴ , ≼𝓢‴
  = {!!}

{-
-- varying q and q₂ (as in X s q₂)

eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-q (EApp q2< ⇓ ⇓₁ ⇓₂ 𝓢≡)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓

-- q = 𝟙, 𝟙 → 𝟙 <⦂ 𝟙 → 𝟙
eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-refl (EApp {𝓢″ = 𝓢″} ⇓ ⇓₁ ⇓₂ refl)
  | Σₕₛ′ , ≼Σ′ , TVClos {q = 𝟙} {x = X s q₁′} {S₁≤x = refl} ⊨𝓔′ 𝓢≡ qbd ⊢e₂ ≤-refl ≤-refl (SQual q1<=q2 (SFun {S₃ = S₃@ (T₃ ^ 𝟙)}{S₁ = S₁@ (T₁ ^ 𝟙)}{S₂ = S₂}{S₄ = S₄} <⦂Sarg <⦂Sres)) , ⊢𝓗′ , ⊢𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) (q-of-mono <⦂Sarg) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″
  using foo ← ⊨-extend-𝟙 s T₁ (⊢ᵥ-adjust (<⦂-val-lift ⊢varg <⦂Sarg)) (⊨-adjust {Σₛ = []} (⊨-extend-Σ ≼Σ″ ⊨𝓔′) (𝟙-bound⇒∀𝟚∉ qbd))
  with eval-soundness (⊢ₕ-adjust [] [] ⊢𝓗″) [] ⊢e₂ foo (q-of-mono <⦂Sres) ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴
  using ≼Σ₁₂ ← ≼ₕₛ-trans ≼Σ′ ≼Σ″
  = adjust-stack Σₕₛ‴ (Σₕₛ″ 𝟚)
  , ≼ₕₛ-trans ≼Σ₁₂ (≼-adjust-[] ≼Σ‴)
  , ⊢ᵥ-adjust (<⦂-val-lift ⊢vres <⦂Sres)
  , ⊢ₕ-adjust (Σₕₛ″ 𝟚) (⊢ₛ-adjust-[] {𝓢 = 𝓢″} ≼Σ‴ ⊢𝓢″) ⊢𝓗‴
  , ⊢ₛ-adjust-[] {𝓢 = 𝓢″} ≼Σ‴ ⊢𝓢″

-- q = 𝟙, 𝟚 → 𝟙 <⦂ 𝟙 → 𝟙
eval-soundness ⊢𝓗 ⊢𝓢 (TApp {S₁ = S₁@ (T₁ ^ 𝟚)}{S₂ = S₂} ⊢e ⊢e₁) ⊨𝓔 ≤-refl (EApp {𝓢″ = 𝓢″} ⇓ ⇓₁ ⇓₂ refl)
  | Σₕₛ′ , ≼Σ′ , TVClos {q = 𝟙} {x = X s q₁′} {S₁≤x = refl} ⊨𝓔′ 𝓢≡ qbd ⊢e₂ ≤-refl ≤-refl (SQual ≤-bottop (SFun{S₃ = S₃@ (T₃ ^ 𝟚)}{S₁ = S₁′@ (T₁′ ^ 𝟙)}{S₄ = S₄} <⦂Sarg <⦂Sres)) , ⊢𝓗′ , ⊢𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) (q-of-mono <⦂Sarg) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″
  using foo ← ⊨-extend-𝟙 s T₁′ (⊢ᵥ-adjust (<⦂-val-lift ⊢varg <⦂Sarg)) (⊨-adjust {Σₛ = []} (⊨-extend-Σ ≼Σ″ ⊨𝓔′) (𝟙-bound⇒∀𝟚∉ qbd))
  with eval-soundness (⊢ₕ-adjust [] [] ⊢𝓗″) [] ⊢e₂ foo (q-of-mono <⦂Sres) ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴
  using ≼Σ₁₂ ← ≼ₕₛ-trans ≼Σ′ ≼Σ″
  = adjust-stack Σₕₛ‴ (Σₕₛ″ 𝟚)
  , ≼ₕₛ-trans ≼Σ₁₂ (≼-adjust-[] ≼Σ‴)
  , ⊢ᵥ-adjust (<⦂-val-lift ⊢vres <⦂Sres)
  , ⊢ₕ-adjust (Σₕₛ″ 𝟚) (⊢ₛ-adjust-[] {𝓢 = 𝓢″} ≼Σ‴ ⊢𝓢″) ⊢𝓗‴
  , ⊢ₛ-adjust-[] {𝓢 = 𝓢″} ≼Σ‴ ⊢𝓢″

-- q = 𝟚, ? → ? <⦂ 𝟙 → 𝟙
eval-soundness ⊢𝓗 ⊢𝓢 (TApp {S₁ = S₁@ (T₁ ^ 𝟙)} {S₂ = S₂} ⊢e ⊢e₁) ⊨𝓔 ≤-refl (EApp {𝓢 = 𝓢}{𝓢′ = 𝓢′}{𝓢″ = 𝓢″} ⇓ ⇓₁ ⇓₂ refl)
  | Σₕₛ′ , ≼Σ′ , TVClos {𝓢 = 𝓢₁} {q = 𝟚} {x = X s q₂} {S₁≤x = refl} ⊨𝓔′ 𝓢≡ qbd ⊢e₂ wf₁ wf₂ (SQual ≤-refl (SFun{S₃ = S₃}{S₁ = S₁′@ (T₁′ ^ 𝟙)}{S₂ = _}{S₄ = S₄@ (T₄ ^ 𝟙)} <⦂Sarg <⦂Sres)) , ⊢𝓗′ , ⊢𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) (q-of-mono <⦂Sarg) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″
  with eval-soundness ⊢𝓗″ ⊢𝓢″ ⊢e₂ (⊨-extend-𝟙 s T₁′ (<⦂-val-lift ⊢varg <⦂Sarg) (⊨-adjust-≼ₛ {!≼ₛ-trans{𝓢₁}{𝓢′}{𝓢″}!} (⊨-extend-Σ ≼Σ″ ⊨𝓔′))) (q-of-mono <⦂Sres) ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴
  = Σₕₛ‴ , ≼ₕₛ-trans ≼Σ′ (≼ₕₛ-trans ≼Σ″ ≼Σ‴) , <⦂-val-lift ⊢vres <⦂Sres , ⊢𝓗‴ , ⊢𝓢‴

-- q = 𝟚, ? → ? <⦂ 𝟚 → 𝟙
eval-soundness ⊢𝓗 ⊢𝓢 (TApp {S₁ = S₁@ (T₁ ^ 𝟙)} {S₂ = S₂} ⊢e ⊢e₁) ⊨𝓔 ≤-refl (EApp {v₂ = v₂} {𝓢″ = 𝓢″} ⇓ ⇓₁ ⇓₂ refl)
  | Σₕₛ′ , ≼Σ′ , TVClos {q = 𝟚} {x = X s q₂} {S₁≤x = refl} ⊨𝓔′ 𝓢≡ qbd ⊢e₂ wf₁ wf₂ (SQual ≤-refl (SFun{S₃ = S₃}{S₁ = S₁′@ (T₁′ ^ 𝟚)}{S₂ = _}{S₄ = S₄@ (T₄ ^ 𝟙)} <⦂Sarg <⦂Sres)) , ⊢𝓗′ , ⊢𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) (q-of-mono <⦂Sarg) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″
  using ≼-ext ← ≼ₕₛ-extend-Σ 𝟚 S₁′
  -- (⊨-extend-𝟙 s T₁′ (<⦂-val-lift ⊢varg <⦂Sarg) (⊨-adjust-≼ₛ {!!} (⊨-extend-Σ ≼Σ″ ⊨𝓔′)))
  using ⊨𝓔-after-push ← ⊨-adjust-push-update s (<⦂-val-lift ⊢varg <⦂Sarg) (⊨-extend-Σ ≼Σ″ ⊨𝓔′)
  with eval-soundness (⊢ₕ-adjust _ (⊢ₛ-adjust-push ⊢varg ⊢𝓢″) ⊢𝓗″) (⊢ₛ-adjust-push ⊢varg ⊢𝓢″) ⊢e₂ {!⊨𝓔-after-push!} (q-of-mono <⦂Sres) {!!} -- ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢vres , ⊢𝓗‴ , ⊢𝓢‴
  = {!!}

-- -- q = 𝟚, 𝟚 → ? ...
-- eval-soundness ⊢𝓗 ⊢𝓢 (TApp {S₁ = S₁@ (T₁ ^ 𝟚)} {S₂ = S₂} ⊢e ⊢e₁) ⊨𝓔 ≤-q (EAppH {𝓢″ = 𝓢″} ⇓ ⇓₁ ⇓₂ refl)
--   | Σₕₛ′ , ≼Σ′ , TVClos {q = 𝟚} {x = X s q₂} {S₁≤x = refl} ⊨𝓔′ qbd ⊢e₂ σ?≡ wf₂ (SQual q1<=q2 (SFun <⦂Sarg <⦂Sres)) , ⊢𝓗′ , ⊢𝓢′ = {!!}

-- eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-q (EAppS ⇓ ⇓₁ ⇓₂ refl)
--   = {!!}

-}

-------- EVERYTHING'S FINE FROM HERE ON 

-- ----- sequence

-- eval-soundness ⊢𝓗 ⊢𝓢 (TSeq ⊢e ⊢e₁) ⊨𝓔 ≤-q (ESeq ⇓ ⇓₁)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-top ⇓
-- ... | Σₕₛ′ , ≼Σ′ , TVClos x x₁ x₂ x₃ wf₂ (SQual qsub ()) , ⊢𝓗′ , ⊢𝓢′
-- ... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< x (SQual qsub ()) , ⊢𝓗′ , ⊢𝓢′
-- ... | Σₕₛ′ , ≼Σ′ , TVUnit , ⊢𝓗′ , ⊢𝓢′
--   with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) ≤-q ⇓₁
-- ... | Σₕₛ″ , ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″
--   = Σₕₛ″ , ≼ₕₛ-trans ≼Σ′ ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″

-- ----- ref

-- -- Ref (T ^ 𝟙) ^ 𝟙 / ERefH
-- eval-soundness ⊢𝓗 ⊢𝓢 (TRef {S = S@(T ^ 𝟙)} {wf = ≤-refl} ⊢e) ⊨𝓔 ≤-refl (ERefH {𝓢′ = 𝓢′} ⇓)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
-- ... | Σₕₛ′ , ≼Σ′ , ⊢v , ⊢𝓗′ , ⊢𝓢′
--   rewrite sym (⊢ₕ-length ⊢𝓗′)
--   = extend-Σ Σₕₛ′ 𝟙 T , ≼ₕₛ-trans ≼Σ′ (≼ₕₛ-extend-Σ 𝟙 T) , TVRef (length-< T (Σₕₛ′ 𝟙) []) (lookup-last T (Σₕₛ′ 𝟙)) <⦂-refl , ⊢𝓗-extend-𝟙 _ ⊢v ⊢𝓗′ , ⊢𝓢-extend-𝟙 {𝓢 = 𝓢′} T ⊢𝓢′
-- -- Ref (T ^ 𝟙) ^ 𝟙 / ERefS
-- eval-soundness ⊢𝓗 ⊢𝓢 (TRef {S = S@ (T ^ 𝟙)} {q = 𝟙} {wf = ≤-refl} ⊢e) ⊨𝓔 ≤-top (ERefS {q = q} {𝓢′ = 𝓢′} ⇓ q=1 q=2)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
-- ... | Σₕₛ′ , ≼Σ′ , ⊢v , ⊢𝓗′ , ⊢𝓢′
--   with refl , refl , refl ← q=1 refl
--   rewrite sym (⊢ₕ-length ⊢𝓗′)
--  = extend-Σ Σₕₛ′ 𝟙 T , ≼ₕₛ-trans ≼Σ′ (≼ₕₛ-extend-Σ 𝟙 T) , TVRef (length-< T (Σₕₛ′ 𝟙) []) (lookup-last T (Σₕₛ′ 𝟙)) <⦂-refl , ⊢𝓗-extend-𝟙 _ ⊢v ⊢𝓗′ , ⊢𝓢-extend-𝟙 {𝓢 = 𝓢′} T ⊢𝓢′
-- -- Ref (T ^ 𝟚) ^ 𝟚 / ERefS
-- eval-soundness ⊢𝓗 ⊢𝓢 (TRef {S = S@(T ^ 𝟚)} {q = 𝟚} {wf = ≤-refl} ⊢e) ⊨𝓔 ≤-top (ERefS {q = q} {𝓢′ = 𝓢′} ⇓ q=1 q=2)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
-- ... | Σₕₛ′ , ≼Σ′ , ⊢v , ⊢𝓗′ , ⊢𝓢′
--   with refl , refl ← q=2 refl
--   rewrite sym (⊢ₛ-length {𝓢 = 𝓢′} ⊢𝓢′)
--  = extend-Σ Σₕₛ′ 𝟚 S , ≼ₕₛ-trans ≼Σ′ (≼ₕₛ-extend-Σ 𝟚 S) , TVRef (length-< S (Σₕₛ′ 𝟚) []) (lookup-last S (Σₕₛ′ 𝟚)) <⦂-refl , ⊢𝓗-extend-𝟚 S ⊢𝓗′ , ⊢𝓢-extend-𝟚 {𝓢 = 𝓢′} S ⊢v ⊢𝓢′
-- -- Ref (T ^ 𝟙) ^ 𝟚 / ERefS
-- eval-soundness ⊢𝓗 ⊢𝓢 (TRef {S = S@ (T ^ 𝟙)} {q = 𝟚} {wf = ≤-bottop} ⊢e) ⊨𝓔 ≤-refl (ERefS {𝓢′ = 𝓢′} ⇓ q=1 q=2)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-bottop ⇓
-- ... | Σₕₛ′ , ≼Σ′ , ⊢v , ⊢𝓗′ , ⊢𝓢′
--   with refl , refl ← q=2 refl
--   rewrite sym (⊢ₛ-length {𝓢 = 𝓢′} ⊢𝓢′)
--   = (extend-Σ Σₕₛ′ 𝟚 S) , (≼ₕₛ-trans ≼Σ′ (≼ₕₛ-extend-Σ 𝟚 S)) , TVRef (length-< S (Σₕₛ′ 𝟚) []) (lookup-last S (Σₕₛ′ 𝟚)) <⦂-refl , (⊢𝓗-extend-𝟚 S ⊢𝓗′) , (⊢𝓢-extend-𝟚 {𝓢 = 𝓢′} S ⊢v ⊢𝓢′)


-- ----- deref

-- eval-soundness ⊢𝓗 ⊢𝓢 (TDeref ⊢e) ⊨𝓔 ≤-refl (EDerefH ⇓ xread)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
-- ... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SQual ≤-refl (SRef S<⦂ <⦂S)) , ⊢𝓗′ , ⊢𝓢′
--   with refl ← <⦂-antisym S<⦂ <⦂S
--   = Σₕₛ′ , ≼Σ′ , typed-read ⊢𝓗′ ℓ< lkup≡ xread , ⊢𝓗′ , ⊢𝓢′
-- eval-soundness ⊢𝓗 ⊢𝓢 (TDeref {q = 𝟚} ⊢e) ⊨𝓔 ≤-q (EDerefS ⇓ q=1 q=2)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
-- ... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SQual ≤-bottop (SRef S<⦂ <⦂S)) , ⊢𝓗′ , ⊢𝓢′
--   with xread ← q=1 refl
--   with refl ← <⦂-antisym  S<⦂ <⦂S
--   = Σₕₛ′ , ≼Σ′ , typed-read ⊢𝓗′ ℓ< lkup≡ xread , ⊢𝓗′ , ⊢𝓢′
-- ... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SQual ≤-refl (SRef S<⦂ <⦂S)) , ⊢𝓗′ , ⊢𝓢′
--   with xsread ← q=2 refl
--   with refl ← <⦂-antisym  S<⦂ <⦂S
--   = Σₕₛ′ , ≼Σ′ , typed-sread ⊢𝓢′ ℓ< lkup≡ xsread , ⊢𝓗′ , ⊢𝓢′

-- ----- setref

-- eval-soundness ⊢𝓗 ⊢𝓢 (TSetref ⊢e ⊢e₁) ⊨𝓔 ≤-q (ESetrefS {q = 𝟙} ⇓ ⇓₁ q=1 q=2)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-top ⇓
-- ... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SQual _ (SRef {wf₁ = wf₁} <⦂S S<⦂)) , ⊢𝓗′ , ⊢𝓢′
--   with refl ← <⦂-antisym  S<⦂ <⦂S
--   with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) wf₁ ⇓₁
-- ... | Σₕₛ″ , ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″
--   with xwrite , refl ← q=1 refl
--   = Σₕₛ″ , (≼ₕₛ-trans ≼Σ′ ≼Σ″) , TVUnit , typed-write ⊢𝓗″ (≤ℕ-trans ℓ< (≼ₕₛ⇒length ≼Σ″ 𝟙)) (trans (trans (cong (lookup (Σₕₛ″ 𝟙)) (fromℕ-inject≤ (≼ₕₛ⇒length ≼Σ″ 𝟙) ℓ<)) (sym (≼ₕₛ-lookup ≼Σ″ 𝟙 (fromℕ< ℓ<)))) lkup≡) ⊢v xwrite , ⊢𝓢″
-- eval-soundness ⊢𝓗 ⊢𝓢 (TSetref ⊢e ⊢e₁) ⊨𝓔 ≤-q (ESetrefS {q = 𝟚} ⇓ ⇓₁ q=1 q=2)
--   with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-top ⇓
-- ... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SQual _ (SRef {wf₁ = wf₁} <⦂S S<⦂)) , ⊢𝓗′ , ⊢𝓢′
--   with refl ← <⦂-antisym  S<⦂ <⦂S
--   with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) wf₁ ⇓₁
-- ... | Σₕₛ″ , ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″
--   with refl , xswrite ← q=2 refl
--   = Σₕₛ″ , (≼ₕₛ-trans ≼Σ′ ≼Σ″) , TVUnit , ⊢𝓗″ , typed-swrite ⊢𝓢″ (≤ℕ-trans ℓ< (≼ₕₛ⇒length ≼Σ″ 𝟚)) (trans (trans (cong (lookup (Σₕₛ″ 𝟚)) (fromℕ-inject≤ (≼ₕₛ⇒length ≼Σ″ 𝟚) ℓ<)) (sym (≼ₕₛ-lookup ≼Σ″ 𝟚 (fromℕ< ℓ<)))) lkup≡) ⊢v xswrite
