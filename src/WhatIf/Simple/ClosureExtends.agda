module Simple.ClosureExtends where

open import Data.Unit using (⊤; tt)
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
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Function using (case_of_)

open import Qualifiers
open import Simple.StackBasedBigStep

read-heap-closure : Heap → Set
read-heap-closure 𝓗 = ∀ ℓ {v} → read 𝓗 ℓ v → q-val v ≡ 𝟙

rhc-drop : read-heap-closure (v ∷ 𝓗) → read-heap-closure 𝓗
rhc-drop rhc ℓ x = rhc (suc ℓ) (read1 x)

rhc-ext : read-heap-closure 𝓗 → q-val v ≡ 𝟙 → read-heap-closure (𝓗 ++ [ v ])
rhc-ext {𝓗 = []} rhc qv=𝟙 ℓ read0 = qv=𝟙
rhc-ext {𝓗 = x₁ ∷ 𝓗} rhc qv=𝟙 ℓ read0 = rhc ℓ read0
rhc-ext {𝓗 = x₁ ∷ 𝓗} rhc qv=𝟙 (suc ℓ) (read1 x) = rhc-ext (rhc-drop rhc) qv=𝟙 ℓ x

rhc-write : read-heap-closure 𝓗 → q-val v ≡ 𝟙 → write 𝓗 ℓ v 𝓗′ → read-heap-closure 𝓗′
rhc-write rhc qv=𝟙 write0 ℓr read0 = qv=𝟙
rhc-write rhc qv=𝟙 write0 ℓr (read1 rd) = rhc ℓr (read1 rd)
rhc-write rhc qv=𝟙 (write1 wr) ℓr read0 = rhc ℓr read0
rhc-write rhc qv=𝟙 (write1 wr) (suc ℓr) (read1 rd) = rhc-write (rhc-drop rhc) qv=𝟙 wr ℓr rd

read-heap-env : Env → Set
read-heap-env 𝓔 = ∀ {s} {v} → Access 𝓔 (X s 𝟙) v → q-val v ≡ 𝟙

rhe-ext : read-heap-env 𝓔 → q-val v ≡ 𝟙 → read-heap-env ⟨ s ≔ v , 𝓔 ⟩
rhe-ext rhe qv=𝟙 here = qv=𝟙
rhe-ext rhe qv=𝟙 (there x _) = rhe x

clos-condition : Val → Stack → Set
clos-condition v 𝓢′ = case v of λ{ (clos q₁ 𝓔′ 𝓢ᶜ x e′ q₂) → 𝓢ᶜ ≼ₛ 𝓢′ ; _ → ⊤ }

eval-heap-inv :
      read-heap-closure 𝓗
    → read-heap-env 𝓔
    → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
    → read-heap-closure 𝓗′
    × q-val v ≤ q
    × clos-condition v 𝓢′

eval-heap-inv rhc rhe EUnit = rhc , ≤-bot , tt
eval-heap-inv rhc rhe (EVarH x) rewrite rhe x = rhc , ≤-refl , {!!}
eval-heap-inv rhc rhe (EVarS x x₁) = rhc , ≤-top , {!!}
eval-heap-inv {q = 𝟙} rhc rhe (EAbs {𝓢 = 𝓢} ≤-refl x₁ refl) = rhc , ≤-refl , ≼ₛ-bot 𝓢
eval-heap-inv {q = 𝟚} rhc rhe (EAbs {𝟙}{𝓢 = 𝓢} x x₁ refl) = rhc , x , ≼ₛ-bot 𝓢
eval-heap-inv {q = 𝟚} rhc rhe (EAbs {𝟚}{𝓢 = 𝓢} x x₁ refl) = rhc , x , (≼ₛ-refl{𝓢})

eval-heap-inv rhc rhe (EApp q≤ ⇓ ⇓₁ ⇓₂ x)
  with eval-heap-inv rhc rhe ⇓
... | rhc₁ , qv≤₁ , casev₁
  with eval-heap-inv rhc₁ rhe ⇓₁
eval-heap-inv {q = 𝟙} rhc rhe (EApp {q₀ = 𝟙} {q = 𝟙}{q₁ = 𝟙} q≤ ⇓ ⇓₁ ⇓₂ x)
  | rhc₁ , qv≤₁ , casev₁
  | rhc₂ , qv≤₂ , casev₂
  -- here we need typing to obtain `read-heap-env 𝓔′` from `clos 𝟙 𝓔′ 𝓢ᶜ (X s 𝟙) e q₂`
    with eval-heap-inv rhc₂ {!rhe-ext rhe (≤⇒≡ qv≤₂)!} ⇓₂
... | r = {!!}
eval-heap-inv {q = 𝟙} rhc rhe (EApp {q₀ = 𝟙} {q = 𝟚}{q₁ = 𝟙} q≤ ⇓ ⇓₁ ⇓₂ x)
  | rhc₁ , qv≤₁ , casev₁
  | rhc₂ , qv≤₂ , casev₂ = {!!}
eval-heap-inv {q = 𝟙} rhc rhe (EApp {q₀ = 𝟙} {q = q′}{q₁ = 𝟚} q≤ ⇓ ⇓₁ ⇓₂ x)
  | rhc₁ , qv≤₁ , casev₁
  | rhc₂ , qv≤₂ , casev₂ = {!!}
eval-heap-inv {q = 𝟚} rhc rhe (EApp {q₀ = 𝟚} {q = q′}{q₁ = 𝟙} q≤ ⇓ ⇓₁ ⇓₂ x)
  | rhc₁ , qv≤₁ , casev₁
  | rhc₂ , qv≤₂ , casev₂ = {!!}
eval-heap-inv {q = 𝟚} rhc rhe (EApp {q₀ = 𝟚} {q = q′}{q₁ = 𝟚} q≤ ⇓ ⇓₁ ⇓₂ x)
  | rhc₁ , qv≤₁ , casev₁
  | rhc₂ , qv≤₂ , casev₂ = {!!}

eval-heap-inv rhc rhe (ERef {q = 𝟙} ≤-refl ⇓ (refl , refl , refl))
  with eval-heap-inv rhc rhe ⇓
... | rhc′ , qv≤ , casev = rhc-ext rhc′ (≤⇒≡ qv≤) , ≤-refl , tt
eval-heap-inv rhc rhe (ERef {q = 𝟚} q≤ ⇓ (refl , refl))
  with eval-heap-inv rhc rhe ⇓
... | rhc′ , qv≤ , casev = rhc′ , q≤ , tt
eval-heap-inv {q = 𝟙} rhc rhe (EDeref {ℓ = ℓ} x ⇓ rd)
  with eval-heap-inv rhc rhe ⇓
... | rhc′ , qv≤ , casev
  with rhc′ ℓ
... | qv
  rewrite qv rd = rhc′ , ≤-refl , {!!}
eval-heap-inv {q = 𝟚} rhc rhe (EDeref x ⇓ x₁)
  with eval-heap-inv rhc rhe ⇓
... | rhc′ , qv≤ , casev = rhc′ , ≤-top , {!!}
eval-heap-inv rhc rhe (ESetref {q₁ = 𝟙} ⇓ ⇓₁ (wr , refl))
  with eval-heap-inv rhc rhe ⇓
... | rhc₁ , qv≤₁ , casev₁
  with eval-heap-inv rhc₁ rhe ⇓₁
... | rhc₂ , qv≤₂ , casev₂ = rhc-write rhc₂ (≤⇒≡ qv≤₂) wr , ≤-bot , tt
eval-heap-inv rhc rhe (ESetref {q₁ = 𝟚} ⇓ ⇓₁ (refl , wr))
  with eval-heap-inv rhc rhe ⇓
... | rhc₁ , qv≤₁ , casev₁
  with eval-heap-inv rhc₁ rhe ⇓₁
... | rhc₂ , qv≤₂ , casev₂  = rhc₂ , ≤-bot , tt
eval-heap-inv rhc rhe (ESeq ⇓ ⇓₁)
  with eval-heap-inv rhc rhe ⇓
... | rhc′ , ih′ , casev′
  with eval-heap-inv rhc′ rhe ⇓₁
... | rhc″ , ih″ , casev″ = rhc″ , ih″ , casev″


{-
eval-clos-≼ₛ :
    read-heap-closure 𝓗
    → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q ] clos q₁ 𝓔′ 𝓢ᶜ x e′ q₂  ⊣ 𝓗′ , 𝓢′
    → 𝓢ᶜ ≼ₛ 𝓢′ × read-heap-closure 𝓗′
-}
