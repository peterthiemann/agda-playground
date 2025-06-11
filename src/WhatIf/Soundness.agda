module Soundness where

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
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

open import Qualifiers
open import StackBasedBigStep



-- properties

postulate
  eval-preservation :
    Γ ⊢ e ⦂ S
    → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / (𝓢 , σ)
    → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
    → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / (𝓢′ , σ)


variable
  HSs SSs : List QType
  

eval-soundness :
  Σₕₛ ⊢ₕ 𝓗
  → Σₕₛ ⊢ₛ 𝓢
  → Γ ⊢ e ⦂ S
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / (𝓢 , σ)
  → q-of S ≤ q
  → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
  → ∃[ Σₕₛ′ ] Σₕₛ ≼ Σₕₛ′ × ⟨ Σₕₛ′ ⟩⊢[ v ⦂ S ] × Σₕₛ′ ⊢ₕ 𝓗′ × Σₕₛ′ ⊢ₛ 𝓢′
eval-soundness ⊢𝓗 ⊢𝓢 (TSub ⊢e S<⦂) ⊨𝓔 ≤-q ⇓
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 (≤-trans (q-of-mono S<⦂) ≤-q) ⇓
... | _ , Σ≼ , ⊢v , ⊢𝓗′ , ⊢𝓢′
  = -, Σ≼ , <⦂-val-lift ⊢v S<⦂ , ⊢𝓗′ , ⊢𝓢′
eval-soundness ⊢𝓗 ⊢𝓢 TUnit ⊨𝓔 ≤-q EUnit
  = -, ≼-refl , TVUnit , ⊢𝓗 , ⊢𝓢
eval-soundness ⊢𝓗 ⊢𝓢 (TVar x) ⊨𝓔 ≤-refl (EVarH acc)
  = -, ≼-refl , access-soundness ⊨𝓔 x acc , ⊢𝓗 , ⊢𝓢
eval-soundness {S = mkQ 𝟙 T} ⊢𝓗 ⊢𝓢 (TVar x) ⊨𝓔 ≤-q (EVarS acc)
  = -, ≼-refl , genaccess-soundness ⊨𝓔 x acc , ⊢𝓗 , ⊢𝓢
eval-soundness {S = mkQ 𝟚 T} ⊢𝓗 ⊢𝓢 (TVar x) ⊨𝓔 ≤-q (EVarS acc)
  = -, ≼-refl , genaccess-soundness ⊨𝓔 x acc , ⊢𝓗 , ⊢𝓢

----- abstraction

eval-soundness ⊢𝓗 ⊢𝓢 (TAbs {q = 𝟙} ⊢e qbdd refl {wf₁}{wf₂}) ⊨𝓔 ≤-refl EAbsH
  = -, ≼-refl , TVClos (restrict′ ⊨𝓔 qbdd) (is-bounded qbdd) ⊢e refl wf₁ wf₂ <⦂-refl , ⊢𝓗 , ⊢𝓢
-- why is the following case legal?
eval-soundness ⊢𝓗 ⊢𝓢 (TAbs {q = 𝟙} {S≤x = refl} ⊢e qbdd refl {≤-refl}{≤-refl}) ⊨𝓔 ≤-bottop EAbsS
  = -, ≼-refl , TVClos (restrict′ ⊨𝓔 qbdd) (is-bounded qbdd) ⊢e refl ≤-refl ≤-refl <⦂-refl , ⊢𝓗 , ⊢𝓢
eval-soundness ⊢𝓗 ⊢𝓢 (TAbs {q = 𝟚} ⊢e qbdd refl {wf₁}{wf₂}) ⊨𝓔 ≤-refl EAbsS
  = -, ≼-refl , TVClos (restrict′ ⊨𝓔 qbdd) (is-bounded qbdd) ⊢e refl wf₁ wf₂ <⦂-refl , ⊢𝓗 , ⊢𝓢

----- application

eval-soundness ⊢𝓗 ⊢𝓢 (TApp {S₁ = S₁}{S₂ = S₂} ⊢e ⊢e₁) ⊨𝓔 ≤-refl (EAppH ⇓ ⇓₁ ⇓₂)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVClos {q = q}{x = X s q₂}{σ? = σ?}{S₁≤x = refl} ⊨𝓔′ qbd ⊢e₂ σ?≡ wf₁ wf₂ (SFun q1<=q2 <⦂Sarg <⦂Sres) , ⊢𝓗′ , ⊢𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) (q-of-mono <⦂Sarg) ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″
  with q , q₂
... | 𝟚 , 𝟙 -- why do we have this case?
  with refl ← σ?≡
  with ≤-refl ← wf₁
  with ≤-refl ← wf₂
  with eval-soundness ⊢𝓗″ {!!} ⊢e₂ {!!} (q-of-mono <⦂Sres) ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢v , ⊢𝓗‴ , ⊢𝓢‴
  = Σₕₛ‴ , (≼-trans ≼Σ′ (≼-trans ≼Σ″ ≼Σ‴)) , {!⊢v!} , {!⊢𝓗‴!} , {!!}

eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-refl (EAppH ⇓ ⇓₁ ⇓₂)
    | Σₕₛ′ , ≼Σ′ , TVClos {q = q}{x = X s q₂}{σ? = σ?}{S₁≤x = refl} ⊨𝓔′ qbd ⊢e₂ σ?≡ wf₁ wf₂ (SFun q1<=q2 <⦂Sarg <⦂Sres) , ⊢𝓗′ , ⊢𝓢′
    | Σₕₛ″ , ≼Σ″ , ⊢varg , ⊢𝓗″ , ⊢𝓢″
    | 𝟙 , 𝟙
  with refl ← σ?≡
  with ≤-refl ← wf₁
  with ≤-refl ← wf₂
  with eval-soundness (⊢ₕ-adjust [] [] ⊢𝓗″) [] ⊢e₂ (⊨-adjust [] {!!}) (q-of-mono <⦂Sres) {!!} -- ⇓₂
... | Σₕₛ‴ , ≼Σ‴ , ⊢v , ⊢𝓗‴ , ⊢𝓢‴
   = {!!} , {!!} , {!!} , {!!} , {!!}

eval-soundness ⊢𝓗 ⊢𝓢 (TApp ⊢e ⊢e₁) ⊨𝓔 ≤-q (EAppS ⇓ ⇓₁ ⇓₂) = {!!}

----- sequence

eval-soundness ⊢𝓗 ⊢𝓢 (TSeq q1≤q2 ⊢e ⊢e₁ q₁≤S) ⊨𝓔 ≤-q (ESeq ⇓ ⇓₁)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-top ⇓
... | Σₕₛ′ , ≼Σ′ , TVUnit , ⊢𝓗′ , ⊢𝓢′
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) ≤-q ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″
  = Σₕₛ″ , ≼-trans ≼Σ′ ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″

----- ref

eval-soundness ⊢𝓗 ⊢𝓢 (TRef {S = S@(T ^ 𝟙)} ⊢e qbdd {≤-refl}) ⊨𝓔 ≤-refl (ERefH {𝓢′ = 𝓢′} ⇓)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e (restrict′ ⊨𝓔 qbdd) ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , ⊢v , ⊢𝓗′ , ⊢𝓢′
  rewrite sym (⊢ₕ-length ⊢𝓗′)
  = extend-Σ Σₕₛ′ 𝟙 T , ≼-trans ≼Σ′ (≼-extend-Σ 𝟙 T) , TVRef (length-< T (Σₕₛ′ 𝟙) []) (lookup-last T (Σₕₛ′ 𝟙)) <⦂-refl , ⊢𝓗-extend-𝟙 _ ⊢v ⊢𝓗′ , ⊢𝓢-extend-𝟙 {𝓢 = 𝓢′} T ⊢𝓢′
eval-soundness ⊢𝓗 ⊢𝓢 (TRef {S = S@ (T ^ 𝟙)} {q = 𝟙} ⊢e qbdd {≤-refl}) ⊨𝓔 ≤-top (ERefS {q = q} {𝓢′ = 𝓢′} ⇓ q=1 q=2)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e (restrict′ ⊨𝓔 qbdd) ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , ⊢v , ⊢𝓗′ , ⊢𝓢′
  with refl , refl , refl ← q=1 refl
  rewrite sym (⊢ₕ-length ⊢𝓗′)
 = extend-Σ Σₕₛ′ 𝟙 T , ≼-trans ≼Σ′ (≼-extend-Σ 𝟙 T) , TVRef (length-< T (Σₕₛ′ 𝟙) []) (lookup-last T (Σₕₛ′ 𝟙)) <⦂-refl , ⊢𝓗-extend-𝟙 _ ⊢v ⊢𝓗′ , ⊢𝓢-extend-𝟙 {𝓢 = 𝓢′} T ⊢𝓢′
eval-soundness ⊢𝓗 ⊢𝓢 (TRef {S = S@(T ^ 𝟚)} {q = 𝟚} ⊢e qbdd {≤-refl}) ⊨𝓔 ≤-top (ERefS {q = q} {𝓢′ = 𝓢′} ⇓ q=1 q=2)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e (restrict′ ⊨𝓔 qbdd) ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , ⊢v , ⊢𝓗′ , ⊢𝓢′
  with refl , refl ← q=2 refl
  rewrite sym (⊢ₛ-length {𝓢 = 𝓢′} ⊢𝓢′)
 = extend-Σ Σₕₛ′ 𝟚 T , ≼-trans ≼Σ′ (≼-extend-Σ 𝟚 T) , TVRef (length-< T (Σₕₛ′ 𝟚) []) (lookup-last T (Σₕₛ′ 𝟚)) <⦂-refl , ⊢𝓗-extend-𝟚 T ⊢𝓗′ , ⊢𝓢-extend-𝟚 {𝓢 = 𝓢′} T ⊢v ⊢𝓢′

----- deref

eval-soundness ⊢𝓗 ⊢𝓢 (TDeref ⊢e) ⊨𝓔 ≤-refl (EDerefH ⇓ xread)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SRef ≤-refl S<⦂ <⦂S) , ⊢𝓗′ , ⊢𝓢′
  with refl ← <⦂-antisym S<⦂ <⦂S
  = Σₕₛ′ , ≼Σ′ , typed-read ⊢𝓗′ ℓ< lkup≡ xread , ⊢𝓗′ , ⊢𝓢′
eval-soundness ⊢𝓗 ⊢𝓢 (TDeref {q = 𝟚} ⊢e) ⊨𝓔 ≤-q (EDerefS ⇓ q=1 q=2)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SRef ≤-bottop S<⦂ <⦂S) , ⊢𝓗′ , ⊢𝓢′
  with xread ← q=1 refl
  with refl ← <⦂-antisym  S<⦂ <⦂S
  = Σₕₛ′ , ≼Σ′ , typed-read ⊢𝓗′ ℓ< lkup≡ xread , ⊢𝓗′ , ⊢𝓢′
... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SRef ≤-refl S<⦂ <⦂S) , ⊢𝓗′ , ⊢𝓢′
  with xsread ← q=2 refl
  with refl ← <⦂-antisym  S<⦂ <⦂S
  = Σₕₛ′ , ≼Σ′ , typed-sread ⊢𝓢′ ℓ< lkup≡ xsread , ⊢𝓗′ , ⊢𝓢′

----- setref

eval-soundness ⊢𝓗 ⊢𝓢 (TSetref ⊢e ⊢e₁) ⊨𝓔 ≤-refl (ESetrefH ⇓ ⇓₁ xwrite)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-refl ⇓
... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SRef ≤-refl S<⦂ <⦂S {wf₁}) , ⊢𝓗′ , ⊢𝓢′
  with refl ← <⦂-antisym S<⦂ <⦂S
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) wf₁ ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″
  = Σₕₛ″ , (≼-trans ≼Σ′ ≼Σ″) , TVUnit , typed-write ⊢𝓗″ (≤ℕ-trans ℓ< (≼⇒length ≼Σ″ 𝟙)) (trans (trans (cong (lookup (Σₕₛ″ 𝟙)) (fromℕ-inject≤ (≼⇒length ≼Σ″ 𝟙) ℓ<)) (sym (≼-lookup ≼Σ″ 𝟙 (fromℕ< ℓ<)))) lkup≡) ⊢v xwrite , ⊢𝓢″
eval-soundness ⊢𝓗 ⊢𝓢 (TSetref ⊢e ⊢e₁) ⊨𝓔 ≤-q (ESetrefS {q = 𝟙} ⇓ ⇓₁ q=1 q=2)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-top ⇓
... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SRef _ <⦂S S<⦂ {wf₁}) , ⊢𝓗′ , ⊢𝓢′
  with refl ← <⦂-antisym  S<⦂ <⦂S
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) wf₁ ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″
  with xwrite , refl ← q=1 refl
  = Σₕₛ″ , (≼-trans ≼Σ′ ≼Σ″) , TVUnit , typed-write ⊢𝓗″ (≤ℕ-trans ℓ< (≼⇒length ≼Σ″ 𝟙)) (trans (trans (cong (lookup (Σₕₛ″ 𝟙)) (fromℕ-inject≤ (≼⇒length ≼Σ″ 𝟙) ℓ<)) (sym (≼-lookup ≼Σ″ 𝟙 (fromℕ< ℓ<)))) lkup≡) ⊢v xwrite , ⊢𝓢″
eval-soundness ⊢𝓗 ⊢𝓢 (TSetref ⊢e ⊢e₁) ⊨𝓔 ≤-q (ESetrefS {q = 𝟚} ⇓ ⇓₁ q=1 q=2)
  with eval-soundness ⊢𝓗 ⊢𝓢 ⊢e ⊨𝓔 ≤-top ⇓
... | Σₕₛ′ , ≼Σ′ , TVRef ℓ< lkup≡ (SRef _ <⦂S S<⦂ {wf₁}) , ⊢𝓗′ , ⊢𝓢′
  with refl ← <⦂-antisym  S<⦂ <⦂S
  with eval-soundness ⊢𝓗′ ⊢𝓢′ ⊢e₁ (eval-preservation ⊢e (⊨-extend-Σ ≼Σ′ ⊨𝓔) ⇓) wf₁ ⇓₁
... | Σₕₛ″ , ≼Σ″ , ⊢v , ⊢𝓗″ , ⊢𝓢″
  with refl , xswrite ← q=2 refl
  = Σₕₛ″ , (≼-trans ≼Σ′ ≼Σ″) , TVUnit , ⊢𝓗″ , typed-swrite ⊢𝓢″ (≤ℕ-trans ℓ< (≼⇒length ≼Σ″ 𝟚)) (trans (trans (cong (lookup (Σₕₛ″ 𝟚)) (fromℕ-inject≤ (≼⇒length ≼Σ″ 𝟚) ℓ<)) (sym (≼-lookup ≼Σ″ 𝟚 (fromℕ< ℓ<)))) lkup≡) ⊢v xswrite
