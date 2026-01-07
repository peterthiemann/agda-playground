import Level

open import Relation.Binary using (Rel; StrictTotalOrder; IsStrictTotalOrder; IsStrictPartialOrder; IsEquivalence; Trichotomous; tri<; tri≈; tri>; Monotonic₁; Reflexive; Symmetric; Transitive)


open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Binary.Connected using (Connected; just; just-nothing; nothing-just; nothing)
open import Data.Product

open import Relation.Nullary using (¬_)

module IntrinsicSet {ℓ} (so : StrictTotalOrder ℓ ℓ ℓ) where

open StrictTotalOrder so using (Carrier; _<_; _≈_; isStrictTotalOrder)

open IsStrictTotalOrder
open IsStrictPartialOrder

-- Connected R is not transitive: composing just-nothing and nothing-just defies R
-- Connected does not preserve Trichotomous

data ISet : Maybe Carrier → Set (Level.suc ℓ) where
  [] : ISet nothing
  _∷_ : {mx₂ : Maybe Carrier} (x₁ : Carrier) → (xs : ISet mx₂) → {x₁<<xs : Connected _<_ (just x₁) mx₂}
      → ISet (just x₁)

_<<_ = Connected _<_

glb : Carrier → Maybe Carrier → Carrier
glb x (just y)
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = x
... | tri≈ ¬a b ¬c = x
... | tri> ¬a ¬b c = y
glb x nothing = x

_⊓_ : Maybe Carrier → Maybe Carrier → Maybe Carrier
just x ⊓ my = just (glb x my)
nothing ⊓ my = my

{- 
just x ⊓ just y
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = just x
... | tri≈ ¬a b ¬c = just x
... | tri> ¬a ¬b c = just y
just x ⊓ nothing = just x
nothing ⊓ just x = just x
nothing ⊓ nothing = nothing
-}

conn-glb : ∀ {x}{y}{mz} → y < x → just y << mz → y < glb x mz
conn-glb {x}{y} y<x (just {y = z} z<)
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c
  with  compare isStrictTotalOrder x z
... | tri< a₁ ¬b₁ ¬c₁ = y<x
... | tri≈ ¬a b ¬c₁ = y<x
... | tri> ¬a ¬b₁ c = z<
conn-glb {x}{y} y<x (just {y = z} z<) | tri≈ ¬a b ¬c
  with  compare isStrictTotalOrder x z
... | tri< a ¬b ¬c₁ = y<x
... | tri≈ ¬a₁ b₁ ¬c₁ = y<x
... | tri> ¬a₁ ¬b c = z<
conn-glb {x}{y} y<x (just {y = z} z<) | tri> ¬a ¬b c
  with compare isStrictTotalOrder x z
... | tri< a ¬b₁ ¬c = c
... | tri≈ ¬a₁ b ¬c = c
... | tri> ¬a₁ ¬b₁ c₁ = z<
conn-glb y<x just-nothing = y<x

Connected-resp-≈ : ∀ {x}{y}{mz} → x ≈ y → just y << mz → just x << mz
Connected-resp-≈ x≈y (just x) = just (<-resp-≈ (isStrictPartialOrder isStrictTotalOrder) .proj₂
                                        (IsEquivalence.sym
                                         (isEquivalence (isStrictPartialOrder isStrictTotalOrder)) x≈y)
                                        x)
Connected-resp-≈ x≈y just-nothing = just-nothing

insert : ∀ x {my} (xs : ISet my) → ISet (just x ⊓ my)
insert x {just _} xs′@(y ∷ xs)
  with compare isStrictTotalOrder x y
... | tri< x<y ¬b ¬c = _∷_ x xs′ {just x<y}
insert x {just _} ((y ∷ xs) {x₁<<xs}) | tri≈ ¬a x≈y ¬c = _∷_ x xs {Connected-resp-≈ x≈y x₁<<xs}
insert x {just _} ((y ∷ xs) {x₁<<xs}) | tri> ¬a ¬b y<x = _∷_ y (insert x xs) {just (conn-glb y<x x₁<<xs)}
insert x {nothing} [] = _∷_ x [] {just-nothing}
