module AlgorithmicOps where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; z≤n; s≤s)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Interval as I
open import Numeri
open import Types

infixl 6 _⊔₀_ _⊔ₙ_ _⊔_
infixl 7 _⊓_ _⊓ₙ?_

_⊔₀_ : Num → Num → Num
`- ⊔₀ `- = `-
`- ⊔₀ `! = `?
`- ⊔₀ `? = `?
`- ⊔₀ `* = `*
`- ⊔₀ `+ = `*
`! ⊔₀ `- = `?
`! ⊔₀ `! = `!
`! ⊔₀ `? = `?
`! ⊔₀ `* = `*
`! ⊔₀ `+ = `+
`? ⊔₀ `- = `?
`? ⊔₀ `! = `?
`? ⊔₀ `? = `?
`? ⊔₀ `* = `*
`? ⊔₀ `+ = `*
`* ⊔₀ η₂ = `*
`+ ⊔₀ `- = `*
`+ ⊔₀ `! = `+
`+ ⊔₀ `? = `*
`+ ⊔₀ `* = `*
`+ ⊔₀ `+ = `+

_⊓₀?_ : Num → Num → Maybe Num
`- ⊓₀? `- = just `-
`- ⊓₀? `! = nothing
`- ⊓₀? `? = just `-
`- ⊓₀? `* = just `-
`- ⊓₀? `+ = nothing
`! ⊓₀? `- = nothing
`! ⊓₀? `! = just `!
`! ⊓₀? `? = just `!
`! ⊓₀? `* = just `!
`! ⊓₀? `+ = just `!
`? ⊓₀? `- = just `-
`? ⊓₀? `! = just `!
`? ⊓₀? `? = just `?
`? ⊓₀? `* = just `?
`? ⊓₀? `+ = just `!
`* ⊓₀? η₂ = just η₂
`+ ⊓₀? `- = nothing
`+ ⊓₀? `! = just `!
`+ ⊓₀? `? = just `!
`+ ⊓₀? `* = just `+
`+ ⊓₀? `+ = just `+

mutual
  _⊔_ : Ty → Ty → Ty
  `⊥ ⊔ μ₂ = μ₂
  `⊤ ⊔ μ₂ = `⊤
  □ ⊔ `⊥ = □
  □ ⊔ `⊤ = `⊤
  □ ⊔ □ = □
  □ ⊔ (_ ⇒ _) = `⊤
  □ ⊔ (_ ⇛ _) = `⊤
  (μ₁ ⇒ ημ₁) ⊔ `⊥ = μ₁ ⇒ ημ₁
  (μ₁ ⇒ ημ₁) ⊔ `⊤ = `⊤
  (μ₁ ⇒ ημ₁) ⊔ □ = `⊤
  (μ₁ ⇒ ημ₁) ⊔ (μ₂ ⇒ ημ₂) = (μ₁ ⊓ μ₂) ⇒ (ημ₁ ⊔ₙ ημ₂)
  (μ₁ ⇒ ημ₁) ⊔ (_ ⇛ _) = `⊤
  (ημ₁ ⇛ ημ₁′) ⊔ `⊥ = ημ₁ ⇛ ημ₁′
  (ημ₁ ⇛ ημ₁′) ⊔ `⊤ = `⊤
  (ημ₁ ⇛ ημ₁′) ⊔ □ = `⊤
  (ημ₁ ⇛ ημ₁′) ⊔ (_ ⇒ _) = `⊤
  (ημ₁ ⇛ ημ₁′) ⊔ (ημ₂ ⇛ ημ₂′) with ημ₁ ⊓ₙ? ημ₂
  ... | just ημ = ημ ⇛ (ημ₁′ ⊔ₙ ημ₂′)
  ... | nothing = `⊤

  _⊔ₙ_ : NTy → NTy → NTy
  ⟨ η₁ , μ₁ ⟩ ⊔ₙ ⟨ η₂ , μ₂ ⟩ = ⟨ η₁ ⊔₀ η₂ , μ₁ ⊔ μ₂ ⟩

  _⊓_ : Ty → Ty → Ty
  `⊥ ⊓ μ₂ = `⊥
  `⊤ ⊓ μ₂ = μ₂
  □ ⊓ `⊥ = `⊥
  □ ⊓ `⊤ = □
  □ ⊓ □ = □
  □ ⊓ (_ ⇒ _) = `⊥
  □ ⊓ (_ ⇛ _) = `⊥
  (μ₁ ⇒ ημ₁) ⊓ `⊥ = `⊥
  (μ₁ ⇒ ημ₁) ⊓ `⊤ = μ₁ ⇒ ημ₁
  (μ₁ ⇒ ημ₁) ⊓ □ = `⊥
  (μ₁ ⇒ ημ₁) ⊓ (μ₂ ⇒ ημ₂) with ημ₁ ⊓ₙ? ημ₂
  ... | just ημ = (μ₁ ⊔ μ₂) ⇒ ημ
  ... | nothing = `⊥
  (μ₁ ⇒ ημ₁) ⊓ (_ ⇛ _) = `⊥
  (ημ₁ ⇛ ημ₁′) ⊓ `⊥ = `⊥
  (ημ₁ ⇛ ημ₁′) ⊓ `⊤ = ημ₁ ⇛ ημ₁′
  (ημ₁ ⇛ ημ₁′) ⊓ □ = `⊥
  (ημ₁ ⇛ ημ₁′) ⊓ (_ ⇒ _) = `⊥
  (ημ₁ ⇛ ημ₁′) ⊓ (ημ₂ ⇛ ημ₂′) with ημ₁′ ⊓ₙ? ημ₂′
  ... | just ημ′ = (ημ₁ ⊔ₙ ημ₂) ⇛ ημ′
  ... | nothing = `⊥

  _⊓ₙ?_ : NTy → NTy → Maybe NTy
  ⟨ η₁ , μ₁ ⟩ ⊓ₙ? ⟨ η₂ , μ₂ ⟩ with η₁ ⊓₀? η₂
  ... | just η = just ⟨ η , μ₁ ⊓ μ₂ ⟩
  ... | nothing = nothing


⊔₀-comm : ∀ η₁ η₂ → η₁ ⊔₀ η₂ ≡ η₂ ⊔₀ η₁
⊔₀-comm `- `- = refl
⊔₀-comm `- `! = refl
⊔₀-comm `- `? = refl
⊔₀-comm `- `* = refl
⊔₀-comm `- `+ = refl
⊔₀-comm `! `- = refl
⊔₀-comm `! `! = refl
⊔₀-comm `! `? = refl
⊔₀-comm `! `* = refl
⊔₀-comm `! `+ = refl
⊔₀-comm `? `- = refl
⊔₀-comm `? `! = refl
⊔₀-comm `? `? = refl
⊔₀-comm `? `* = refl
⊔₀-comm `? `+ = refl
⊔₀-comm `* `- = refl
⊔₀-comm `* `! = refl
⊔₀-comm `* `? = refl
⊔₀-comm `* `* = refl
⊔₀-comm `* `+ = refl
⊔₀-comm `+ `- = refl
⊔₀-comm `+ `! = refl
⊔₀-comm `+ `? = refl
⊔₀-comm `+ `* = refl
⊔₀-comm `+ `+ = refl

⊔₀-upper-left : ∀ η₁ η₂ → η₁ <:₀ (η₁ ⊔₀ η₂)
⊔₀-upper-left `- `- = <:₀-refl
⊔₀-upper-left `- `! = <:₀--?
⊔₀-upper-left `- `? = <:₀--?
⊔₀-upper-left `- `* = <:₀--*
⊔₀-upper-left `- `+ = <:₀--*
⊔₀-upper-left `! `- = <:₀-!?
⊔₀-upper-left `! `! = <:₀-refl
⊔₀-upper-left `! `? = <:₀-!?
⊔₀-upper-left `! `* = <:₀-!*
⊔₀-upper-left `! `+ = <:₀-!+
⊔₀-upper-left `? `- = <:₀-refl
⊔₀-upper-left `? `! = <:₀-refl
⊔₀-upper-left `? `? = <:₀-refl
⊔₀-upper-left `? `* = <:₀-?*
⊔₀-upper-left `? `+ = <:₀-?*
⊔₀-upper-left `* η₂ = <:₀-refl
⊔₀-upper-left `+ `- = <:₀-+*
⊔₀-upper-left `+ `! = <:₀-refl
⊔₀-upper-left `+ `? = <:₀-+*
⊔₀-upper-left `+ `* = <:₀-+*
⊔₀-upper-left `+ `+ = <:₀-refl

⊔₀-upper-right : ∀ η₁ η₂ → η₂ <:₀ (η₁ ⊔₀ η₂)
⊔₀-upper-right η₁ η₂ rewrite ⊔₀-comm η₁ η₂ = ⊔₀-upper-left η₂ η₁

⊔₀-least : ∀ {η₁ η₂ η}
  → η₁ <:₀ η
  → η₂ <:₀ η
  → (η₁ ⊔₀ η₂) <:₀ η
⊔₀-least {η₁} {η₂} {`* } η₁<:η η₂<:η = num-to-star (η₁ ⊔₀ η₂)
⊔₀-least {η = `- } <:₀-refl <:₀-refl = <:₀-refl
⊔₀-least {η = `! } <:₀-refl <:₀-refl = <:₀-refl
⊔₀-least {η = `? } <:₀-refl <:₀-refl = <:₀-refl
⊔₀-least {η = `? } <:₀-refl <:₀--? = <:₀-refl
⊔₀-least {η = `? } <:₀-refl <:₀-!? = <:₀-refl
⊔₀-least {η = `? } <:₀--? <:₀-refl = <:₀-refl
⊔₀-least {η = `? } <:₀--? <:₀--? = <:₀--?
⊔₀-least {η = `? } <:₀--? <:₀-!? = <:₀-refl
⊔₀-least {η = `? } <:₀-!? <:₀-refl = <:₀-refl
⊔₀-least {η = `? } <:₀-!? <:₀--? = <:₀-refl
⊔₀-least {η = `? } <:₀-!? <:₀-!? = <:₀-!?
⊔₀-least {η = `+ } <:₀-refl <:₀-refl = <:₀-refl
⊔₀-least {η = `+ } <:₀-refl <:₀-!+ = <:₀-refl
⊔₀-least {η = `+ } <:₀-!+ <:₀-refl = <:₀-refl
⊔₀-least {η = `+ } <:₀-!+ <:₀-!+ = <:₀-!+

⊓₀?-comm : ∀ η₁ η₂ → η₁ ⊓₀? η₂ ≡ η₂ ⊓₀? η₁
⊓₀?-comm `- `- = refl
⊓₀?-comm `- `! = refl
⊓₀?-comm `- `? = refl
⊓₀?-comm `- `* = refl
⊓₀?-comm `- `+ = refl
⊓₀?-comm `! `- = refl
⊓₀?-comm `! `! = refl
⊓₀?-comm `! `? = refl
⊓₀?-comm `! `* = refl
⊓₀?-comm `! `+ = refl
⊓₀?-comm `? `- = refl
⊓₀?-comm `? `! = refl
⊓₀?-comm `? `? = refl
⊓₀?-comm `? `* = refl
⊓₀?-comm `? `+ = refl
⊓₀?-comm `* `- = refl
⊓₀?-comm `* `! = refl
⊓₀?-comm `* `? = refl
⊓₀?-comm `* `* = refl
⊓₀?-comm `* `+ = refl
⊓₀?-comm `+ `- = refl
⊓₀?-comm `+ `! = refl
⊓₀?-comm `+ `? = refl
⊓₀?-comm `+ `* = refl
⊓₀?-comm `+ `+ = refl

⊓₀?-defined : ∀ {η η₁ η₂}
  → η <:₀ η₁
  → η <:₀ η₂
  → Σ Num (λ η₁₂ → η₁ ⊓₀? η₂ ≡ just η₁₂)
⊓₀?-defined {η₁ = `- } {η₂ = `- } η<:η₁ η<:η₂ = `- , refl
⊓₀?-defined {η₁ = `- } {η₂ = `! } <:₀-refl ()
⊓₀?-defined {η₁ = `- } {η₂ = `? } η<:η₁ η<:η₂ = `- , refl
⊓₀?-defined {η₁ = `- } {η₂ = `* } η<:η₁ η<:η₂ = `- , refl
⊓₀?-defined {η₁ = `- } {η₂ = `+ } <:₀-refl ()
⊓₀?-defined {η₁ = `! } {η₂ = `- } <:₀-refl ()
⊓₀?-defined {η₁ = `! } {η₂ = `! } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `! } {η₂ = `? } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `! } {η₂ = `* } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `! } {η₂ = `+ } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `? } {η₂ = `- } η<:η₁ η<:η₂ = `- , refl
⊓₀?-defined {η₁ = `? } {η₂ = `! } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `? } {η₂ = `? } η<:η₁ η<:η₂ = `? , refl
⊓₀?-defined {η₁ = `? } {η₂ = `* } η<:η₁ η<:η₂ = `? , refl
⊓₀?-defined {η₁ = `? } {η₂ = `+ } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `* } {η₂ = η₂} η<:η₁ η<:η₂ = η₂ , refl
⊓₀?-defined {η₁ = `+ } {η₂ = `- } () <:₀-refl
⊓₀?-defined {η₁ = `+ } {η₂ = `! } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `+ } {η₂ = `? } η<:η₁ η<:η₂ = `! , refl
⊓₀?-defined {η₁ = `+ } {η₂ = `* } η<:η₁ η<:η₂ = `+ , refl
⊓₀?-defined {η₁ = `+ } {η₂ = `+ } η<:η₁ η<:η₂ = `+ , refl

⊓₀?-lower-left : ∀ η₁ η₂ {η}
  → η₁ ⊓₀? η₂ ≡ just η
  → η <:₀ η₁
⊓₀?-lower-left `- `- refl = <:₀-refl
⊓₀?-lower-left `- `! ()
⊓₀?-lower-left `- `? refl = <:₀-refl
⊓₀?-lower-left `- `* refl = <:₀-refl
⊓₀?-lower-left `- `+ ()
⊓₀?-lower-left `! `- ()
⊓₀?-lower-left `! `! refl = <:₀-refl
⊓₀?-lower-left `! `? refl = <:₀-refl
⊓₀?-lower-left `! `* refl = <:₀-refl
⊓₀?-lower-left `! `+ refl = <:₀-refl
⊓₀?-lower-left `? `- refl = <:₀--?
⊓₀?-lower-left `? `! refl = <:₀-!?
⊓₀?-lower-left `? `? refl = <:₀-refl
⊓₀?-lower-left `? `* refl = <:₀-refl
⊓₀?-lower-left `? `+ refl = <:₀-!?
⊓₀?-lower-left `* η₂ refl = num-to-star η₂
⊓₀?-lower-left `+ `- ()
⊓₀?-lower-left `+ `! refl = <:₀-!+
⊓₀?-lower-left `+ `? refl = <:₀-!+
⊓₀?-lower-left `+ `* refl = <:₀-refl
⊓₀?-lower-left `+ `+ refl = <:₀-refl

⊓₀?-lower-right : ∀ η₁ η₂ {η}
  → η₁ ⊓₀? η₂ ≡ just η
  → η <:₀ η₂
⊓₀?-lower-right η₁ η₂ eq rewrite ⊓₀?-comm η₁ η₂ = ⊓₀?-lower-left η₂ η₁ eq

⊓₀?-greatest : ∀ {η η₁ η₂ η₁₂}
  → η <:₀ η₁
  → η <:₀ η₂
  → η₁ ⊓₀? η₂ ≡ just η₁₂
  → η <:₀ η₁₂
⊓₀?-greatest {η₁ = `- } {η₂ = `- } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `- } {η₂ = `! } η<:η₁ η<:η₂ ()
⊓₀?-greatest {η₁ = `- } {η₂ = `? } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `- } {η₂ = `* } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `- } {η₂ = `+ } η<:η₁ η<:η₂ ()
⊓₀?-greatest {η₁ = `! } {η₂ = `- } η<:η₁ η<:η₂ ()
⊓₀?-greatest {η₁ = `! } {η₂ = `! } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `! } {η₂ = `? } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `! } {η₂ = `* } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `! } {η₂ = `+ } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `? } {η₂ = `- } η<:η₁ η<:η₂ refl = η<:η₂
⊓₀?-greatest {η₁ = `? } {η₂ = `! } η<:η₁ η<:η₂ refl = η<:η₂
⊓₀?-greatest {η₁ = `? } {η₂ = `? } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `? } {η₂ = `* } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `? } {η₂ = `+ } <:₀-!? <:₀-!+ refl = <:₀-refl
⊓₀?-greatest {η₁ = `* } {η₂ = η₂} η<:η₁ η<:η₂ refl = η<:η₂
⊓₀?-greatest {η₁ = `+ } {η₂ = `- } η<:η₁ η<:η₂ ()
⊓₀?-greatest {η₁ = `+ } {η₂ = `! } η<:η₁ η<:η₂ refl = η<:η₂
⊓₀?-greatest {η₁ = `+ } {η₂ = `? } <:₀-!+ <:₀-!? refl = <:₀-refl
⊓₀?-greatest {η₁ = `+ } {η₂ = `* } η<:η₁ η<:η₂ refl = η<:η₁
⊓₀?-greatest {η₁ = `+ } {η₂ = `+ } η<:η₁ η<:η₂ refl = η<:η₁

⊔₀-interval-sound : ∀ η₁ η₂
  → I._≤_ (I._⊔_ 𝓝⟦ η₁ ⟧ 𝓝⟦ η₂ ⟧) 𝓝⟦ η₁ ⊔₀ η₂ ⟧
⊔₀-interval-sound `- `- = z≤n , z≤n
⊔₀-interval-sound `- `! = z≤n , s≤s z≤n
⊔₀-interval-sound `- `? = z≤n , s≤s z≤n
⊔₀-interval-sound `- `* = z≤n , tt
⊔₀-interval-sound `- `+ = z≤n , tt
⊔₀-interval-sound `! `- = z≤n , s≤s z≤n
⊔₀-interval-sound `! `! = s≤s z≤n , s≤s z≤n
⊔₀-interval-sound `! `? = z≤n , s≤s z≤n
⊔₀-interval-sound `! `* = z≤n , tt
⊔₀-interval-sound `! `+ = s≤s z≤n , tt
⊔₀-interval-sound `? `- = z≤n , s≤s z≤n
⊔₀-interval-sound `? `! = z≤n , s≤s z≤n
⊔₀-interval-sound `? `? = z≤n , s≤s z≤n
⊔₀-interval-sound `? `* = z≤n , tt
⊔₀-interval-sound `? `+ = z≤n , tt
⊔₀-interval-sound `* `- = z≤n , tt
⊔₀-interval-sound `* `! = z≤n , tt
⊔₀-interval-sound `* `? = z≤n , tt
⊔₀-interval-sound `* `* = z≤n , tt
⊔₀-interval-sound `* `+ = z≤n , tt
⊔₀-interval-sound `+ `- = z≤n , tt
⊔₀-interval-sound `+ `! = s≤s z≤n , tt
⊔₀-interval-sound `+ `? = z≤n , tt
⊔₀-interval-sound `+ `* = z≤n , tt
⊔₀-interval-sound `+ `+ = s≤s z≤n , tt

⊓₀-interval-sound : ∀ η₁ η₂ {η}
  → η₁ ⊓₀? η₂ ≡ just η
  → I._≤_ (I._⊓_ 𝓝⟦ η₁ ⟧ 𝓝⟦ η₂ ⟧) 𝓝⟦ η ⟧
⊓₀-interval-sound `- `- refl = z≤n , z≤n
⊓₀-interval-sound `- `! ()
⊓₀-interval-sound `- `? refl = z≤n , z≤n
⊓₀-interval-sound `- `* refl = z≤n , z≤n
⊓₀-interval-sound `- `+ ()
⊓₀-interval-sound `! `- ()
⊓₀-interval-sound `! `! refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `! `? refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `! `* refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `! `+ refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `? `- refl = z≤n , z≤n
⊓₀-interval-sound `? `! refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `? `? refl = z≤n , s≤s z≤n
⊓₀-interval-sound `? `* refl = z≤n , s≤s z≤n
⊓₀-interval-sound `? `+ refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `* `- refl = z≤n , z≤n
⊓₀-interval-sound `* `! refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `* `? refl = z≤n , s≤s z≤n
⊓₀-interval-sound `* `* refl = z≤n , tt
⊓₀-interval-sound `* `+ refl = s≤s z≤n , tt
⊓₀-interval-sound `+ `- ()
⊓₀-interval-sound `+ `! refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `+ `? refl = s≤s z≤n , s≤s z≤n
⊓₀-interval-sound `+ `* refl = s≤s z≤n , tt
⊓₀-interval-sound `+ `+ refl = s≤s z≤n , tt

⊓₀-interval-empty : ∀ η₁ η₂
  → η₁ ⊓₀? η₂ ≡ nothing
  → ∀ {k} → I._∈∈_ k (I._⊓_ 𝓝⟦ η₁ ⟧ 𝓝⟦ η₂ ⟧) → ⊥
⊓₀-interval-empty `- `- ()
⊓₀-interval-empty `- `! refl {zero} (() , k≤0)
⊓₀-interval-empty `- `! refl {suc k} (lo≤k , ())
⊓₀-interval-empty `- `? ()
⊓₀-interval-empty `- `* ()
⊓₀-interval-empty `- `+ refl {zero} (() , k≤0)
⊓₀-interval-empty `- `+ refl {suc k} (lo≤k , ())
⊓₀-interval-empty `! `- refl {zero} (() , k≤0)
⊓₀-interval-empty `! `- refl {suc k} (lo≤k , ())
⊓₀-interval-empty `! `! ()
⊓₀-interval-empty `! `? ()
⊓₀-interval-empty `! `* ()
⊓₀-interval-empty `! `+ ()
⊓₀-interval-empty `? `- ()
⊓₀-interval-empty `? `! ()
⊓₀-interval-empty `? `? ()
⊓₀-interval-empty `? `* ()
⊓₀-interval-empty `? `+ ()
⊓₀-interval-empty `* `- ()
⊓₀-interval-empty `* `! ()
⊓₀-interval-empty `* `? ()
⊓₀-interval-empty `* `* ()
⊓₀-interval-empty `* `+ ()
⊓₀-interval-empty `+ `- refl {zero} (() , k≤0)
⊓₀-interval-empty `+ `- refl {suc k} (lo≤k , ())
⊓₀-interval-empty `+ `! ()
⊓₀-interval-empty `+ `? ()
⊓₀-interval-empty `+ `* ()
⊓₀-interval-empty `+ `+ ()

⊓ₙ?-defined : ∀ {ημ ημ₁ ημ₂}
  → ημ <:ₙ ημ₁
  → ημ <:ₙ ημ₂
  → Σ NTy (λ ημ₁₂ → ημ₁ ⊓ₙ? ημ₂ ≡ just ημ₁₂)
⊓ₙ?-defined
  {ημ₁ = ⟨ η₁ , μ₁ ⟩}
  {ημ₂ = ⟨ η₂ , μ₂ ⟩}
  (<:ₙ-comb η<:η₁ μ<:μ₁)
  (<:ₙ-comb η<:η₂ μ<:μ₂)
  with ⊓₀?-defined η<:η₁ η<:η₂
... | η₁₂ , eq rewrite eq = ⟨ η₁₂ , μ₁ ⊓ μ₂ ⟩ , refl

mutual
  ⊔-upper-left : ∀ μ₁ μ₂ → μ₁ <:ₜ (μ₁ ⊔ μ₂)
  ⊔-upper-left `⊥ μ₂ = <:ₜ-⊥
  ⊔-upper-left `⊤ μ₂ = <:ₜ-⊤
  ⊔-upper-left □ `⊥ = <:ₜ-refl
  ⊔-upper-left □ `⊤ = <:ₜ-⊤
  ⊔-upper-left □ □ = <:ₜ-refl
  ⊔-upper-left □ (_ ⇒ _) = <:ₜ-⊤
  ⊔-upper-left □ (_ ⇛ _) = <:ₜ-⊤
  ⊔-upper-left (μ₁ ⇒ ημ₁) `⊥ = <:ₜ-refl
  ⊔-upper-left (μ₁ ⇒ ημ₁) `⊤ = <:ₜ-⊤
  ⊔-upper-left (μ₁ ⇒ ημ₁) □ = <:ₜ-⊤
  ⊔-upper-left (μ₁ ⇒ ημ₁) (μ₂ ⇒ ημ₂) =
    <:ₜ-⇒ (⊓-lower-left μ₁ μ₂) (⊔ₙ-upper-left ημ₁ ημ₂)
  ⊔-upper-left (μ₁ ⇒ ημ₁) (_ ⇛ _) = <:ₜ-⊤
  ⊔-upper-left (ημ₁ ⇛ ημ₁′) `⊥ = <:ₜ-refl
  ⊔-upper-left (ημ₁ ⇛ ημ₁′) `⊤ = <:ₜ-⊤
  ⊔-upper-left (ημ₁ ⇛ ημ₁′) □ = <:ₜ-⊤
  ⊔-upper-left (ημ₁ ⇛ ημ₁′) (_ ⇒ _) = <:ₜ-⊤
  ⊔-upper-left (⟨ η₁ , μ₁ ⟩ ⇛ ημ₁′) (⟨ η₂ , μ₂ ⟩ ⇛ ημ₂′) with η₁ ⊓₀? η₂ in eq
  ... | just η = <:ₜ-⇛
    (<:ₙ-comb (⊓₀?-lower-left η₁ η₂ eq) (⊓-lower-left μ₁ μ₂))
    (⊔ₙ-upper-left ημ₁′ ημ₂′)
  ... | nothing = <:ₜ-⊤

  ⊔-upper-right : ∀ μ₁ μ₂ → μ₂ <:ₜ (μ₁ ⊔ μ₂)
  ⊔-upper-right `⊥ μ₂ = <:ₜ-refl
  ⊔-upper-right `⊤ μ₂ = <:ₜ-⊤
  ⊔-upper-right □ `⊥ = <:ₜ-⊥
  ⊔-upper-right □ `⊤ = <:ₜ-⊤
  ⊔-upper-right □ □ = <:ₜ-refl
  ⊔-upper-right □ (_ ⇒ _) = <:ₜ-⊤
  ⊔-upper-right □ (_ ⇛ _) = <:ₜ-⊤
  ⊔-upper-right (μ₁ ⇒ ημ₁) `⊥ = <:ₜ-⊥
  ⊔-upper-right (μ₁ ⇒ ημ₁) `⊤ = <:ₜ-⊤
  ⊔-upper-right (μ₁ ⇒ ημ₁) □ = <:ₜ-⊤
  ⊔-upper-right (μ₁ ⇒ ημ₁) (μ₂ ⇒ ημ₂) =
    <:ₜ-⇒ (⊓-lower-right μ₁ μ₂) (⊔ₙ-upper-right ημ₁ ημ₂)
  ⊔-upper-right (μ₁ ⇒ ημ₁) (_ ⇛ _) = <:ₜ-⊤
  ⊔-upper-right (ημ₁ ⇛ ημ₁′) `⊥ = <:ₜ-⊥
  ⊔-upper-right (ημ₁ ⇛ ημ₁′) `⊤ = <:ₜ-⊤
  ⊔-upper-right (ημ₁ ⇛ ημ₁′) □ = <:ₜ-⊤
  ⊔-upper-right (ημ₁ ⇛ ημ₁′) (_ ⇒ _) = <:ₜ-⊤
  ⊔-upper-right (⟨ η₁ , μ₁ ⟩ ⇛ ημ₁′) (⟨ η₂ , μ₂ ⟩ ⇛ ημ₂′) with η₁ ⊓₀? η₂ in eq
  ... | just η = <:ₜ-⇛
    (<:ₙ-comb (⊓₀?-lower-right η₁ η₂ eq) (⊓-lower-right μ₁ μ₂))
    (⊔ₙ-upper-right ημ₁′ ημ₂′)
  ... | nothing = <:ₜ-⊤

  ⊔ₙ-upper-left : ∀ ημ₁ ημ₂ → ημ₁ <:ₙ (ημ₁ ⊔ₙ ημ₂)
  ⊔ₙ-upper-left ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ =
    <:ₙ-comb (⊔₀-upper-left η₁ η₂) (⊔-upper-left μ₁ μ₂)

  ⊔ₙ-upper-right : ∀ ημ₁ ημ₂ → ημ₂ <:ₙ (ημ₁ ⊔ₙ ημ₂)
  ⊔ₙ-upper-right ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ =
    <:ₙ-comb (⊔₀-upper-right η₁ η₂) (⊔-upper-right μ₁ μ₂)

  ⊔-least : ∀ {μ₁ μ₂ μ}
    → μ₁ <:ₜ μ
    → μ₂ <:ₜ μ
    → (μ₁ ⊔ μ₂) <:ₜ μ
  ⊔-least {μ₁ = `⊥} μ₁<:μ μ₂<:μ = μ₂<:μ
  ⊔-least {μ₁ = `⊤} μ₁<:μ μ₂<:μ = μ₁<:μ
  ⊔-least {μ₁ = □} {μ₂ = `⊥} μ₁<:μ μ₂<:μ = μ₁<:μ
  ⊔-least {μ₁ = _ ⇒ _} {μ₂ = `⊥} μ₁<:μ μ₂<:μ = μ₁<:μ
  ⊔-least {μ₁ = _ ⇛ _} {μ₂ = `⊥} μ₁<:μ μ₂<:μ = μ₁<:μ
  ⊔-least {μ₁ = □} {μ₂ = `⊤} μ₁<:μ μ₂<:μ = μ₂<:μ
  ⊔-least {μ₁ = _ ⇒ _} {μ₂ = `⊤} μ₁<:μ μ₂<:μ = μ₂<:μ
  ⊔-least {μ₁ = _ ⇛ _} {μ₂ = `⊤} μ₁<:μ μ₂<:μ = μ₂<:μ
  ⊔-least {μ₁ = □} {μ₂ = □} μ₁<:μ μ₂<:μ = μ₁<:μ
  ⊔-least {μ₁ = □} {μ₂ = _ ⇒ _} <:ₜ-⊤ μ₂<:μ = <:ₜ-⊤
  ⊔-least {μ₁ = □} {μ₂ = _ ⇛ _} <:ₜ-⊤ μ₂<:μ = <:ₜ-⊤
  ⊔-least {μ₁ = _ ⇒ _} {μ₂ = □} μ₁<:μ <:ₜ-⊤ = <:ₜ-⊤
  ⊔-least {μ₁ = _ ⇛ _} {μ₂ = □} μ₁<:μ <:ₜ-⊤ = <:ₜ-⊤
  ⊔-least {μ₁ = μ₁ ⇒ ημ₁} {μ₂ = μ₂ ⇒ ημ₂} <:ₜ-⊤ μ₂<:μ = <:ₜ-⊤
  ⊔-least {μ₁ = μ₁ ⇒ ημ₁} {μ₂ = μ₂ ⇒ ημ₂}
    (<:ₜ-⇒ μ<:μ₁ ημ₁<:ημ)
    (<:ₜ-⇒ μ<:μ₂ ημ₂<:ημ) =
    <:ₜ-⇒ (⊓-greatest μ<:μ₁ μ<:μ₂) (⊔ₙ-least ημ₁<:ημ ημ₂<:ημ)
  ⊔-least {μ₁ = _ ⇒ _} {μ₂ = _ ⇛ _} <:ₜ-⊤ μ₂<:μ = <:ₜ-⊤
  ⊔-least {μ₁ = _ ⇛ _} {μ₂ = _ ⇒ _} μ₁<:μ <:ₜ-⊤ = <:ₜ-⊤
  ⊔-least {μ₁ = ημ₁ ⇛ ημ₁′} {μ₂ = ημ₂ ⇛ ημ₂′} <:ₜ-⊤ μ₂<:μ = <:ₜ-⊤
  ⊔-least {μ₁ = ημ₁ ⇛ ημ₁′} {μ₂ = ημ₂ ⇛ ημ₂′}
    (<:ₜ-⇛ ημ<:ημ₁ ημ₁′<:ημ′)
    (<:ₜ-⇛ ημ<:ημ₂ ημ₂′<:ημ′)
    with ⊓ₙ?-defined ημ<:ημ₁ ημ<:ημ₂
  ... | ημ , eq rewrite eq =
    <:ₜ-⇛ (⊓ₙ?-greatest ημ<:ημ₁ ημ<:ημ₂ eq) (⊔ₙ-least ημ₁′<:ημ′ ημ₂′<:ημ′)

  ⊔ₙ-least : ∀ {ημ₁ ημ₂ ημ}
    → ημ₁ <:ₙ ημ
    → ημ₂ <:ₙ ημ
    → (ημ₁ ⊔ₙ ημ₂) <:ₙ ημ
  ⊔ₙ-least
    (<:ₙ-comb η₁<:η μ₁<:μ)
    (<:ₙ-comb η₂<:η μ₂<:μ) =
    <:ₙ-comb (⊔₀-least η₁<:η η₂<:η) (⊔-least μ₁<:μ μ₂<:μ)

  ⊓-lower-left : ∀ μ₁ μ₂ → (μ₁ ⊓ μ₂) <:ₜ μ₁
  ⊓-lower-left `⊥ μ₂ = <:ₜ-⊥
  ⊓-lower-left `⊤ μ₂ = <:ₜ-⊤
  ⊓-lower-left □ `⊥ = <:ₜ-⊥
  ⊓-lower-left □ `⊤ = <:ₜ-refl
  ⊓-lower-left □ □ = <:ₜ-refl
  ⊓-lower-left □ (_ ⇒ _) = <:ₜ-⊥
  ⊓-lower-left □ (_ ⇛ _) = <:ₜ-⊥
  ⊓-lower-left (μ₁ ⇒ ημ₁) `⊥ = <:ₜ-⊥
  ⊓-lower-left (μ₁ ⇒ ημ₁) `⊤ = <:ₜ-refl
  ⊓-lower-left (μ₁ ⇒ ημ₁) □ = <:ₜ-⊥
  ⊓-lower-left (μ₁ ⇒ ⟨ η₁ , μ₁′ ⟩) (μ₂ ⇒ ⟨ η₂ , μ₂′ ⟩) with η₁ ⊓₀? η₂ in eq
  ... | just η = <:ₜ-⇒
    (⊔-upper-left μ₁ μ₂)
    (<:ₙ-comb (⊓₀?-lower-left η₁ η₂ eq) (⊓-lower-left μ₁′ μ₂′))
  ... | nothing = <:ₜ-⊥
  ⊓-lower-left (μ₁ ⇒ ημ₁) (_ ⇛ _) = <:ₜ-⊥
  ⊓-lower-left (ημ₁ ⇛ ημ₁′) `⊥ = <:ₜ-⊥
  ⊓-lower-left (ημ₁ ⇛ ημ₁′) `⊤ = <:ₜ-refl
  ⊓-lower-left (ημ₁ ⇛ ημ₁′) □ = <:ₜ-⊥
  ⊓-lower-left (ημ₁ ⇛ ημ₁′) (_ ⇒ _) = <:ₜ-⊥
  ⊓-lower-left (ημ₁ ⇛ ⟨ η₁′ , μ₁′ ⟩) (ημ₂ ⇛ ⟨ η₂′ , μ₂′ ⟩) with η₁′ ⊓₀? η₂′ in eq
  ... | just η′ = <:ₜ-⇛
    (⊔ₙ-upper-left ημ₁ ημ₂)
    (<:ₙ-comb (⊓₀?-lower-left η₁′ η₂′ eq) (⊓-lower-left μ₁′ μ₂′))
  ... | nothing = <:ₜ-⊥

  ⊓-lower-right : ∀ μ₁ μ₂ → (μ₁ ⊓ μ₂) <:ₜ μ₂
  ⊓-lower-right `⊥ μ₂ = <:ₜ-⊥
  ⊓-lower-right `⊤ μ₂ = <:ₜ-refl
  ⊓-lower-right □ `⊥ = <:ₜ-⊥
  ⊓-lower-right □ `⊤ = <:ₜ-⊤
  ⊓-lower-right □ □ = <:ₜ-refl
  ⊓-lower-right □ (_ ⇒ _) = <:ₜ-⊥
  ⊓-lower-right □ (_ ⇛ _) = <:ₜ-⊥
  ⊓-lower-right (μ₁ ⇒ ημ₁) `⊥ = <:ₜ-⊥
  ⊓-lower-right (μ₁ ⇒ ημ₁) `⊤ = <:ₜ-⊤
  ⊓-lower-right (μ₁ ⇒ ημ₁) □ = <:ₜ-⊥
  ⊓-lower-right (μ₁ ⇒ ⟨ η₁ , μ₁′ ⟩) (μ₂ ⇒ ⟨ η₂ , μ₂′ ⟩) with η₁ ⊓₀? η₂ in eq
  ... | just η = <:ₜ-⇒
    (⊔-upper-right μ₁ μ₂)
    (<:ₙ-comb (⊓₀?-lower-right η₁ η₂ eq) (⊓-lower-right μ₁′ μ₂′))
  ... | nothing = <:ₜ-⊥
  ⊓-lower-right (μ₁ ⇒ ημ₁) (_ ⇛ _) = <:ₜ-⊥
  ⊓-lower-right (ημ₁ ⇛ ημ₁′) `⊥ = <:ₜ-⊥
  ⊓-lower-right (ημ₁ ⇛ ημ₁′) `⊤ = <:ₜ-⊤
  ⊓-lower-right (ημ₁ ⇛ ημ₁′) □ = <:ₜ-⊥
  ⊓-lower-right (ημ₁ ⇛ ημ₁′) (_ ⇒ _) = <:ₜ-⊥
  ⊓-lower-right (ημ₁ ⇛ ⟨ η₁′ , μ₁′ ⟩) (ημ₂ ⇛ ⟨ η₂′ , μ₂′ ⟩) with η₁′ ⊓₀? η₂′ in eq
  ... | just η′ = <:ₜ-⇛
    (⊔ₙ-upper-right ημ₁ ημ₂)
    (<:ₙ-comb (⊓₀?-lower-right η₁′ η₂′ eq) (⊓-lower-right μ₁′ μ₂′))
  ... | nothing = <:ₜ-⊥

  ⊓ₙ?-lower-left : ∀ ημ₁ ημ₂ {ημ}
    → ημ₁ ⊓ₙ? ημ₂ ≡ just ημ
    → ημ <:ₙ ημ₁
  ⊓ₙ?-lower-left ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ eq with η₁ ⊓₀? η₂ in eq₀
  ⊓ₙ?-lower-left ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ refl | just η =
    <:ₙ-comb (⊓₀?-lower-left η₁ η₂ eq₀) (⊓-lower-left μ₁ μ₂)
  ⊓ₙ?-lower-left ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ () | nothing

  ⊓ₙ?-lower-right : ∀ ημ₁ ημ₂ {ημ}
    → ημ₁ ⊓ₙ? ημ₂ ≡ just ημ
    → ημ <:ₙ ημ₂
  ⊓ₙ?-lower-right ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ eq with η₁ ⊓₀? η₂ in eq₀
  ⊓ₙ?-lower-right ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ refl | just η =
    <:ₙ-comb (⊓₀?-lower-right η₁ η₂ eq₀) (⊓-lower-right μ₁ μ₂)
  ⊓ₙ?-lower-right ⟨ η₁ , μ₁ ⟩ ⟨ η₂ , μ₂ ⟩ () | nothing

  ⊓-greatest : ∀ {μ μ₁ μ₂}
    → μ <:ₜ μ₁
    → μ <:ₜ μ₂
    → μ <:ₜ (μ₁ ⊓ μ₂)
  ⊓-greatest {μ = `⊥} μ<:μ₁ μ<:μ₂ = <:ₜ-⊥
  ⊓-greatest {μ₁ = `⊥} μ<:μ₁ μ<:μ₂ = μ<:μ₁
  ⊓-greatest {μ₁ = `⊤} μ<:μ₁ μ<:μ₂ = μ<:μ₂
  ⊓-greatest {μ₁ = □} {μ₂ = `⊥} μ<:μ₁ μ<:μ₂ = μ<:μ₂
  ⊓-greatest {μ₁ = _ ⇒ _} {μ₂ = `⊥} μ<:μ₁ μ<:μ₂ = μ<:μ₂
  ⊓-greatest {μ₁ = _ ⇛ _} {μ₂ = `⊥} μ<:μ₁ μ<:μ₂ = μ<:μ₂
  ⊓-greatest {μ₁ = □} {μ₂ = `⊤} μ<:μ₁ μ<:μ₂ = μ<:μ₁
  ⊓-greatest {μ₁ = _ ⇒ _} {μ₂ = `⊤} μ<:μ₁ μ<:μ₂ = μ<:μ₁
  ⊓-greatest {μ₁ = _ ⇛ _} {μ₂ = `⊤} μ<:μ₁ μ<:μ₂ = μ<:μ₁
  ⊓-greatest {μ = □} {μ₁ = □} {μ₂ = □} <:ₜ-□ <:ₜ-□ = <:ₜ-□
  ⊓-greatest {μ = μ ⇒ ημ} {μ₁ = μ₁ ⇒ ημ₁} {μ₂ = μ₂ ⇒ ημ₂}
    (<:ₜ-⇒ μ₁<:μ ημ<:ημ₁)
    (<:ₜ-⇒ μ₂<:μ ημ<:ημ₂)
    with ⊓ₙ?-defined ημ<:ημ₁ ημ<:ημ₂
  ... | ημ₁₂ , eq rewrite eq =
    <:ₜ-⇒ (⊔-least μ₁<:μ μ₂<:μ) (⊓ₙ?-greatest ημ<:ημ₁ ημ<:ημ₂ eq)
  ⊓-greatest {μ = ημ ⇛ ημ′} {μ₁ = ημ₁ ⇛ ημ₁′} {μ₂ = ημ₂ ⇛ ημ₂′}
    (<:ₜ-⇛ ημ₁<:ημ ημ′<:ημ₁′)
    (<:ₜ-⇛ ημ₂<:ημ ημ′<:ημ₂′)
    with ⊓ₙ?-defined ημ′<:ημ₁′ ημ′<:ημ₂′
  ... | ημ′₁₂ , eq rewrite eq =
    <:ₜ-⇛ (⊔ₙ-least ημ₁<:ημ ημ₂<:ημ) (⊓ₙ?-greatest ημ′<:ημ₁′ ημ′<:ημ₂′ eq)

  ⊓ₙ?-greatest : ∀ {ημ ημ₁ ημ₂ ημ₁₂}
    → ημ <:ₙ ημ₁
    → ημ <:ₙ ημ₂
    → ημ₁ ⊓ₙ? ημ₂ ≡ just ημ₁₂
    → ημ <:ₙ ημ₁₂
  ⊓ₙ?-greatest
    {ημ = ⟨ η , μ ⟩}
    {ημ₁ = ⟨ η₁ , μ₁ ⟩}
    {ημ₂ = ⟨ η₂ , μ₂ ⟩}
    (<:ₙ-comb η<:η₁ μ<:μ₁)
    (<:ₙ-comb η<:η₂ μ<:μ₂)
    eq with η₁ ⊓₀? η₂ in eq₀
  ⊓ₙ?-greatest
    {ημ = ⟨ η , μ ⟩}
    {ημ₁ = ⟨ η₁ , μ₁ ⟩}
    {ημ₂ = ⟨ η₂ , μ₂ ⟩}
    (<:ₙ-comb η<:η₁ μ<:μ₁)
    (<:ₙ-comb η<:η₂ μ<:μ₂)
    refl | just η₁₂ =
    <:ₙ-comb (⊓₀?-greatest η<:η₁ η<:η₂ eq₀) (⊓-greatest μ<:μ₁ μ<:μ₂)
  ⊓ₙ?-greatest
    {ημ = ⟨ η , μ ⟩}
    {ημ₁ = ⟨ η₁ , μ₁ ⟩}
    {ημ₂ = ⟨ η₂ , μ₂ ⟩}
    (<:ₙ-comb η<:η₁ μ<:μ₁)
    (<:ₙ-comb η<:η₂ μ<:μ₂)
    () | nothing
