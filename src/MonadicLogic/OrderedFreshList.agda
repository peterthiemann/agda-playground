open import Level using (_⊔_)
import Agda.Builtin.Unit
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Binary
open import Relation.Unary using (Pred)
open import Data.Fin using (Fin; zero; suc)

open import Data.List using (List; []; _∷_; [_]; map; length)
open import Data.List.Relation.Unary.Linked as Linked using (Linked; _∷_)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_; _∉_ to _∉′_)

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary using (¬_; contradiction)

open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂; map)

open import Function using (_∘_; id)

module OrderedFreshList {ℓ₀}{ℓ₁}{ℓ₂}(so : StrictTotalOrder ℓ₀ ℓ₁ ℓ₂) where

open StrictTotalOrder so using (Carrier; _<_; _≈_; isStrictTotalOrder)

open IsStrictTotalOrder

--
postulate
  ext : ∀ {a}{b} {A : Set a}{B : A → Set b} (f g : (x : A) → B x) → 
    (∀ x → f x ≡ g x) → f ≡ g

-- inspired by Data.List.Relation.Unary.Sorted.TotalOrder

FreshOrderedList : Pred (List Carrier) _
FreshOrderedList = Linked _<_

------------------------------------------------------------------------
-- Operations

module _ {x y xs} where

  head : FreshOrderedList (x ∷ y ∷ xs) → x < y
  head = Linked.head

  tail : FreshOrderedList (x ∷ xs) → FreshOrderedList xs
  tail = Linked.tail

-- elements of a FOL

_∈_  _∉_ : (x : Carrier) {xs : List Carrier} → FreshOrderedList xs → Set ℓ₀
_∈_ x {xs′} xs = x ∈′ xs′
x ∉ xs = ¬ (x ∈ xs)

-- index

index : ∀ {x : Carrier}{xs} → x ∈′ xs → Fin (length xs)
index (here px) = zero
index (there x) = suc (index x)

-- irrelevance of _∈_

<-irreflexive : ∀ {x}{y} → x < y → ¬ (x ≈ y)
<-irreflexive {x}{y} x<y x≈y
   with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = ¬b x≈y
... | tri≈ ¬a b ¬c = ¬a x<y
... | tri> ¬a ¬b c = ¬b x≈y

¬x<x : ∀ {x} → ¬ (x < x)
¬x<x {x} x<x
   with compare isStrictTotalOrder x x
... | tri< a ¬b ¬c = ¬c x<x
... | tri≈ ¬a b ¬c = ¬c x<x
... | tri> ¬a ¬b c = ¬a x<x

x<y-y≈z⇒x<z : ∀ {x}{y}{z} → x < y → y ≈ z → x < z
x<y-y≈z⇒x<z x<y y≈z
  with IsStrictPartialOrder.<-resp-≈ (isStrictPartialOrder isStrictTotalOrder)
... | ≈-<-l , ≈-<-r = ≈-<-l y≈z x<y

x≈z-x<y⇒z<y : ∀ {x}{y}{z} → x ≈ z → x < y → z < y
x≈z-x<y⇒z<y x≈z x<y
  with IsStrictPartialOrder.<-resp-≈ (isStrictPartialOrder isStrictTotalOrder)
... | ≈-<-l , ≈-<-r = ≈-<-r x≈z x<y

≈-∷ : ∀ {xs′ : List Carrier} {x′} {y′} → y′ ≈ x′ → FreshOrderedList (x′ ∷ xs′) → FreshOrderedList (y′ ∷ xs′)
≈-∷ y′≈x′ Linked.[-] = Linked.[-]
≈-∷ y′≈x′ (x ∷ xs) = proj₂
                      (IsStrictPartialOrder.<-resp-≈
                       (isStrictPartialOrder isStrictTotalOrder))
                      (IsEquivalence.sym
                       (IsStrictPartialOrder.isEquivalence
                        (isStrictPartialOrder isStrictTotalOrder))
                       y′≈x′)
                      x
                      ∷ xs

head-is-min : (x : Carrier) {xs′ : List Carrier} (xs : FreshOrderedList (x ∷ xs′)) → ∀ {y} → y ∈ Linked.tail xs → x < y
head-is-min x {(y ∷ _)} xs (here refl) = head xs
head-is-min x {y ∷ _} (x<y ∷ xs) (there y∈tail) = IsStrictTotalOrder.trans isStrictTotalOrder x<y (head-is-min y xs y∈tail)  
fresh-ordered⇒¬in : (x : Carrier) {xs′ : List Carrier} (xs : FreshOrderedList (x ∷ xs′)) → x ∉ Linked.tail xs
fresh-ordered⇒¬in x xs x∈tail = ¬x<x (head-is-min x xs x∈tail)

∈-irrelevant : (x : Carrier) {xs′ : List Carrier} (xs : FreshOrderedList xs′) → (p q : x ∈ xs) → p ≡ q
∈-irrelevant x {.(x ∷ _)} xs (here refl) (here refl) = refl
∈-irrelevant x {.(x ∷ _)} xs (here refl) (there q) = contradiction q (fresh-ordered⇒¬in x xs)
∈-irrelevant x {.(x ∷ _)} xs (there p) (here refl) = contradiction p (fresh-ordered⇒¬in x xs)
∈-irrelevant x {.(_ ∷ _ ∷ _)} (x₁ ∷ xs) (there p) (there q) = cong there (∈-irrelevant x xs p q)

-- subset and irrelevance

_⊆_ : ∀ {xs}{ys} → FreshOrderedList xs → FreshOrderedList ys → Set ℓ₀
xs ⊆ ys = ∀ x → x ∈ xs → x ∈ ys

⊆-irrelevant : ∀ {xs′}{ys′}
  → (xs : FreshOrderedList xs′) (ys : FreshOrderedList ys′)
  → (p q : xs ⊆ ys) → p ≡ q
⊆-irrelevant xs ys p q = ext p q (λ x → ext (p x) (q x) (λ x₁ → ∈-irrelevant x ys (p x x₁) (q x x₁)))

-- monotone functions preserve the structure
-- check against Data.List.Linked.Properties.map⁺

Monotone : (f : Carrier → Carrier) → Set _
Monotone f = ∀ {x y} → x < y →  f x < f y

monotone-preserves : ∀ f {xs′} → Monotone f → FreshOrderedList xs′ → FreshOrderedList (Data.List.map f xs′)
monotone-preserves f mon-f Linked.[] = Linked.[]
monotone-preserves f mon-f Linked.[-] = Linked.[-]
monotone-preserves f mon-f (x<y ∷ ps) = mon-f x<y ∷ monotone-preserves f mon-f ps

-- this can be generalized from Monotone to Preserves R f
-- defined as
-- Preserves : ∀ {a} → Rel Carrier a → (f : Carrier → Carrier) → Set a
-- Preserves R f = ∀ {x y} → {!Rel Carrier _!} → {!!}
-- R x y → R (f x) (f y)
-- and then
-- preserves* : ∀ f {xs′} → Preserves R f → Linked R xs′ → Linked R (Data.List.map f xs′)


-- FOL operations

----------------------------------------------------------------------
-- singleton

⁅_⁆ : (x : Carrier) → FreshOrderedList [ x ]
⁅ x ⁆ = Linked.[-]

----------------------------------------------------------------------
-- insert

insert₀ : (x : Carrier) (xs : List Carrier) → List Carrier
insert₀ x [] = [ x ]
insert₀ x (y ∷ xs)
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = x ∷ y ∷ xs
... | tri≈ ¬a b ¬c = y ∷ xs
... | tri> ¬a ¬b c = y ∷ insert₀ x xs

lemma-insert₀ : ∀ {x y xs} → y < x → insert₀ x (y ∷ xs) ≡ y ∷ insert₀ x xs
lemma-insert₀ {x}{y} y<x
  with compare isStrictTotalOrder x y
... | tri< x<y ¬b ¬y<x = contradiction y<x ¬y<x
... | tri≈ ¬a b ¬y<x = contradiction y<x ¬y<x
... | tri> ¬a ¬b y<x = refl

insert : (x : Carrier) {xs′ : List Carrier} → FreshOrderedList xs′ → FreshOrderedList (insert₀ x xs′)
insert x Linked.[] = Linked.[-]
insert x { x₁ ∷ [] } Linked.[-]
  with compare isStrictTotalOrder x x₁
... | tri< x<x₁ ¬b ¬c = x<x₁ ∷ Linked.[-]
... | tri≈ ¬a b ¬c = Linked.[-]
... | tri> ¬a ¬b x₁<x = x₁<x ∷ Linked.[-]
insert x {x₁ ∷ x₂ ∷ xs′} (x₁<x₂ ∷ xs)
  with compare isStrictTotalOrder x x₁
... | tri< x<x₁ ¬b ¬c = x<x₁ ∷ x₁<x₂ ∷ xs
... | tri≈ ¬a x≈x₁ ¬c = x₁<x₂ ∷ xs
... | tri> ¬a ¬b x₁<x
  with compare isStrictTotalOrder x x₂
... | tri< x<x₂ ¬b₁ ¬c = x₁<x ∷ x<x₂ ∷ xs
... | tri≈ ¬a₁ x≈x₂ ¬c = x₁<x₂ ∷ xs
... | tri> ¬a₁ ¬b₁ x₂<x
  with ih ← insert x xs
  rewrite lemma-insert₀ {xs = xs′} x₂<x
  = x₁<x₂ ∷ ih

----------------------------------------------------------------------
-- delete

delete₀ : (x : Carrier) (xs : List Carrier) → List Carrier
delete₀ x [] = []
delete₀ x (y ∷ xs)
  with compare isStrictTotalOrder x y
... | tri< x<y ¬b ¬c = y ∷ xs
... | tri≈ ¬a x≈y ¬c = xs
... | tri> ¬a ¬b y<x = y ∷ delete₀ x xs

lemma-delete₀ : ∀ {x y xs} → y < x → delete₀ x (y ∷ xs) ≡ y ∷ delete₀ x xs
lemma-delete₀ {x}{y} y<x
  with compare isStrictTotalOrder x y
... | tri< x<y ¬b ¬y<x = contradiction y<x ¬y<x
... | tri≈ ¬a y≈x ¬y<x = contradiction y<x ¬y<x
... | tri> ¬a ¬b y<x = refl

delete : (x : Carrier) {xs′ : List Carrier} → FreshOrderedList xs′ → FreshOrderedList (delete₀ x xs′)
delete x {[]} Linked.[] = Linked.[]
delete x {x₁ ∷ .[]} Linked.[-]
  with compare isStrictTotalOrder x x₁
... | tri< x<x₁ ¬b ¬c = Linked.[-]
... | tri≈ ¬a x≈x₁ ¬c = Linked.[]
... | tri> ¬a ¬b x₁<x = Linked.[-]
delete x {x₁ ∷ (x₂ ∷ xs′)} (x₁<x₂ ∷ xs)
  with compare isStrictTotalOrder x x₁
... | tri< x<x₁ ¬b ¬c = x₁<x₂ ∷ xs
... | tri≈ ¬a x≈x₁ ¬c = xs
... | tri> ¬a ¬b x₁<x 
  with compare isStrictTotalOrder x x₂
... | tri< x<x₂ ¬b₁ ¬c = x₁<x₂ ∷ xs
delete x {x₁ ∷ x₂ ∷ .[]} (x₁<x₂ ∷ Linked.[-]) | tri> ¬a ¬b x₁<x | tri≈ ¬a₁ x≈x₂ ¬c = Linked.[-]
delete x {x₁ ∷ x₂ ∷ xs′@(_ ∷ _)} (x₁<x₂ ∷ x₂<y ∷ xs) | tri> ¬a ¬b x₁<x | tri≈ ¬a₁ x≈x₂ ¬c = (IsStrictTotalOrder.trans isStrictTotalOrder x₁<x₂ x₂<y) ∷ xs
... | tri> ¬a₁ ¬b₁ x₂<x
  with ih ← delete x xs
  rewrite lemma-delete₀ {xs = xs′} x₂<x = x₁<x₂ ∷ ih

----------------------------------------------------------------------
_─′_ : {x₀ : Carrier} {xs′ : List Carrier} → (xs : FreshOrderedList xs′) → (x∈ : x₀ ∈ xs) → FreshOrderedList (xs′ Data.List.─ index x∈)
Linked.[-] ─′ here px = Linked.[]
(x ∷ Linked.[-]) ─′ here px = Linked.[-]
(x ∷ x₁ ∷ xs) ─′ here px = x₁ ∷ xs
(x ∷ Linked.[-]) ─′ there (here px) = Linked.[-]
(x₁<x₂ ∷ x₂<x₃ ∷ xs<) ─′ there (here px) = (IsStrictPartialOrder.trans
                                              (isStrictPartialOrder isStrictTotalOrder) x₁<x₂ x₂<x₃) ∷ xs<
(x₁<x₂ ∷ x₂<x₃ ∷ xs<) ─′ there (there x∈) = x₁<x₂ ∷ ((x₂<x₃ ∷ xs<) ─′ there x∈)

----------------------------------------------------------------------
-- union

{-# TERMINATING #-}
union₀ : List Carrier → List Carrier → List Carrier
union₀ [] ys = ys
union₀ (x ∷ xs) [] = x ∷ xs
union₀ xs₀@(x ∷ xs) ys₀@(y ∷ ys)
  with compare isStrictTotalOrder x y
... | tri< x<y ¬b ¬c = x ∷ union₀ xs ys₀
... | tri≈ ¬a x≈y ¬c = x ∷ union₀ xs ys
... | tri> ¬a ¬b y<x = y ∷ union₀ xs₀ ys

lemma-union₀-r : ∀ {x}{y}{xs}{ys} → y < x → union₀ (x ∷ xs) (y ∷ ys) ≡ y ∷ union₀ (x ∷ xs) ys
lemma-union₀-r{x}{y} y<x
  with compare isStrictTotalOrder x y
... | tri< x<y ¬b ¬y<x = contradiction y<x ¬y<x
... | tri≈ ¬a y≈x ¬y<x = contradiction y<x ¬y<x
... | tri> ¬a ¬b c = refl

lemma-union₀-l : ∀ {x}{y}{xs}{ys} → x < y → union₀ (x ∷ xs) (y ∷ ys) ≡ x ∷ union₀ xs (y ∷ ys)
lemma-union₀-l{x}{y} x<y
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = refl
... | tri≈ ¬x<y x≈y ¬c = contradiction x<y ¬x<y
... | tri> ¬x<y ¬b y<x = contradiction x<y ¬x<y

lemma-union₀-≈ : ∀ {x}{y}{xs}{ys} → x ≈ y → union₀ (x ∷ xs) (y ∷ ys) ≡ x ∷ union₀ xs ys
lemma-union₀-≈{x}{y} x≈y
  with compare isStrictTotalOrder x y
... | tri< a ¬x≈y ¬c = contradiction x≈y ¬x≈y
... | tri≈ ¬a b ¬c = refl
... | tri> ¬a ¬x≈y c = contradiction x≈y ¬x≈y

lemma-union₀-[] : ∀{xs} → union₀ xs [] ≡ xs
lemma-union₀-[] {[]} = refl
lemma-union₀-[] {x ∷ xs} = refl

{-# TERMINATING #-}
union : {xs′ ys′ : List Carrier} → FreshOrderedList xs′ → FreshOrderedList ys′ → FreshOrderedList (union₀ xs′ ys′)
union {.[]} {ys′} Linked.[] ys = ys
union {.(_ ∷ [])} {.[]} Linked.[-] Linked.[] = Linked.[-]
union {(x ∷ [])} {(y ∷ [])} Linked.[-] Linked.[-]
  with compare isStrictTotalOrder x y
... | tri< x<y ¬b ¬c = x<y ∷ Linked.[-]
... | tri≈ ¬a x≈y ¬c = Linked.[-]
... | tri> ¬a ¬b y<x = y<x ∷ Linked.[-]
union {(x ∷ [])} {(y₁ ∷ y₂ ∷ ys′)} Linked.[-] (y₁<y₂ ∷ ys)
  with compare isStrictTotalOrder x y₁
... | tri< x<y₁ ¬b ¬c = x<y₁ ∷ y₁<y₂ ∷ ys
... | tri≈ ¬a x≈y₁ ¬c = x≈z-x<y⇒z<y (IsEquivalence.sym (isEquivalence isStrictTotalOrder) x≈y₁) y₁<y₂ ∷ ys
... | tri> ¬a ¬b y₁<x
  with compare isStrictTotalOrder x y₂
... | tri< x<y₂ ¬b₁ ¬c = y₁<x ∷ x<y₂ ∷ ys
... | tri≈ ¬a₁ x≈y₂ ¬c = y₁<x ∷ ≈-∷ x≈y₂ ys
... | tri> ¬a₁ ¬b₁ y₂<x
  with ih ← union {[ x ]}{y₂ ∷ ys′} Linked.[-] ys
  rewrite lemma-union₀-r {xs = []} {ys = ys′} y₂<x
  = y₁<y₂ ∷ ih 
union {.(_ ∷ _ ∷ _)} {.[]} (x₁<x₂ ∷ xs) Linked.[] = x₁<x₂ ∷ xs
union {(x₁ ∷ x₂ ∷ xs′)} {(y ∷ [])} (x₁<x₂ ∷ xs) Linked.[-]
  with compare isStrictTotalOrder x₁ y
... | tri≈ ¬a b ¬c = x₁<x₂ ∷ xs
... | tri> ¬a ¬b y<x₁ = y<x₁ ∷ x₁<x₂ ∷ xs
... | tri< x₁<y ¬b ¬c
  with compare isStrictTotalOrder x₂ y
... | tri< x₂<y ¬b₁ ¬c₁
  with ih ← union {x₂ ∷ xs′}{[ y ]} xs Linked.[-]
  rewrite lemma-union₀-l {xs = xs′} {ys = []} x₂<y
  = x₁<x₂ ∷ ih
... | tri≈ ¬a x₂≈y ¬c₁ rewrite  lemma-union₀-[] {xs = xs′} = x₁<x₂ ∷ xs
... | tri> ¬a ¬b₁ y<x₂ = x₁<y ∷ y<x₂ ∷ xs

union {(x₁ ∷ x₂ ∷ xs′)} {(y₁ ∷ y₂ ∷ ys′)} (x₁<x₂ ∷ xs) (y₁<y₂ ∷ ys)
  with compare isStrictTotalOrder x₁ y₁
... | tri< x₁<y₁ ¬b ¬c
  with compare isStrictTotalOrder x₂ y₁
... | tri< x₂<y₁ ¬b₁ ¬c₁
  with ih ← union xs (y₁<y₂ ∷ ys)
  rewrite lemma-union₀-l {xs = xs′}{ys = y₂ ∷ ys′}x₂<y₁
  = x₁<x₂ ∷ ih
... | tri≈ ¬a x₂≈y₁ ¬c₁
  with ih ← union xs ys
  rewrite lemma-union₀-l {xs = xs′}{ys = ys′} (x≈z-x<y⇒z<y (IsEquivalence.sym
                       (IsStrictPartialOrder.isEquivalence
                        (isStrictPartialOrder isStrictTotalOrder))
                       x₂≈y₁) y₁<y₂) = x₁<x₂ ∷ ih
... | tri> ¬a ¬b₁ y₁<x₂
  with ih ← union xs (y₁<y₂ ∷ ys)
  rewrite lemma-union₀-r {xs = xs′}{ys = y₂ ∷ ys′} y₁<x₂
  = x₁<y₁ ∷ ih

union {(x₁ ∷ x₂ ∷ xs′)} {(y₁ ∷ y₂ ∷ ys′)} xs₀@(x₁<x₂ ∷ xs) ys₀@(y₁<y₂ ∷ ys) | tri> ¬a ¬b y₁<x₁
  with ih ← union xs₀ ys
  with compare isStrictTotalOrder x₁ y₂
... | tri< x₁<y₂ ¬b₁ ¬c
  = y₁<x₁ ∷ ih
... | tri≈ ¬a₁ x₁≈y₂ ¬c
  = y₁<x₁ ∷ ih
... | tri> ¬a₁ ¬b₁ y₂<x₁
  = y₁<y₂ ∷ ih

union {(x₁ ∷ x₂ ∷ xs′)} {(y₁ ∷ y₂ ∷ ys′)} (x₁<x₂ ∷ xs) (y₁<y₂ ∷ ys) | tri≈ ¬a x₁≈y₁ ¬c
  with ih ← union xs ys
  with compare isStrictTotalOrder x₂ y₂
... | tri< x₂<y₂ ¬b ¬c₁
  = x₁<x₂ ∷ ih
... | tri≈ ¬a₁ x₂≈y₂ ¬c₁
  = x₁<x₂ ∷ ih
... | tri> ¬a₁ ¬b y₂<x₂
  = x≈z-x<y⇒z<y (IsEquivalence.sym (IsStrictPartialOrder.isEquivalence
                        (isStrictPartialOrder isStrictTotalOrder)) x₁≈y₁) y₁<y₂ ∷ ih

--

union-elim : ∀ {xs′ ys′ : List Carrier} {x₀} → (xs : FreshOrderedList xs′) (ys : FreshOrderedList ys′)
  →  x₀ ∈ union xs ys → x₀ ∈ xs ⊎ x₀ ∈ ys
union-elim Linked.[] ys x∈ = inj₂ x∈
union-elim Linked.[-] Linked.[] x∈ = inj₁ x∈
union-elim {x ∷ []} {y ∷ []} Linked.[-] Linked.[-] x∈
  with compare isStrictTotalOrder x y
union-elim {x ∷ []} {y ∷ []} Linked.[-] Linked.[-] (here refl) | tri< a ¬b ¬c = inj₁ (here refl)
union-elim {x ∷ []} {y ∷ []} Linked.[-] Linked.[-] (there x∈) | tri< a ¬b ¬c = inj₂ x∈
union-elim {x ∷ []} {y ∷ []} Linked.[-] Linked.[-] (here refl) | tri≈ ¬a b ¬c = inj₁ (here refl)
union-elim {x ∷ []} {y ∷ []} Linked.[-] Linked.[-] (here refl) | tri> ¬a ¬b c = inj₂ (here refl)
union-elim {x ∷ []} {y ∷ []} Linked.[-] Linked.[-] (there x∈) | tri> ¬a ¬b c = inj₁ x∈
union-elim {x ∷ []} {y ∷ ys′} Linked.[-] (y< ∷ ys) x∈
  with compare isStrictTotalOrder x y
union-elim {x ∷ []} {y ∷ .(_ ∷ _)} Linked.[-] (y< ∷ ys) (here refl) | tri< a ¬b ¬c = inj₁ (here refl)
union-elim {x ∷ []} {y ∷ .(_ ∷ _)} Linked.[-] (y< ∷ ys) (there x∈) | tri< a ¬b ¬c = inj₂ x∈
union-elim {x ∷ []} {y ∷ .(_ ∷ _)} Linked.[-] (y< ∷ ys) (here refl) | tri≈ ¬a b ¬c = inj₁ (here refl)
union-elim {x ∷ []} {y ∷ .(_ ∷ _)} Linked.[-] (y< ∷ ys) (there x∈) | tri≈ ¬a b ¬c = inj₂ (there x∈)
union-elim {x ∷ []} {y ∷ .(_ ∷ _)} Linked.[-] (y< ∷ ys) (here refl) | tri> ¬a ¬b c = inj₂ (here refl)
union-elim {x ∷ []} {y₁ ∷ y₂ ∷ _} Linked.[-] (y₁<y₂ ∷ ys) (there x∈) | tri> ¬a ¬b c
  with compare isStrictTotalOrder x y₂
union-elim {x ∷ []} {y₁ ∷ .(_ ∷ _)} Linked.[-] (y₁<y₂ ∷ ys) (there (here px)) | tri> ¬a ¬b c | tri< a ¬b₁ ¬c = inj₁ (here px)
union-elim {x ∷ []} {y₁ ∷ .(_ ∷ _)} Linked.[-] (y₁<y₂ ∷ ys) (there (there x∈)) | tri> ¬a ¬b c | tri< a ¬b₁ ¬c = inj₂ (there x∈)
union-elim {x ∷ []} {y₁ ∷ .(_ ∷ _)} Linked.[-] (y₁<y₂ ∷ ys) (there (here px)) | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c = inj₁ (here px)
union-elim {x ∷ []} {y₁ ∷ .(_ ∷ _)} Linked.[-] (y₁<y₂ ∷ ys) (there (there x∈)) | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c = inj₂ (there (there x∈))
union-elim {x ∷ []} {y₁ ∷ .(_ ∷ _)} Linked.[-] (y₁<y₂ ∷ ys) (there (here px)) | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ = inj₂ (there (here px))
union-elim {x ∷ []} {y₁ ∷ .(_ ∷ _)} Linked.[-] (y₁<y₂ ∷ Linked.[-]) (there (there x∈)) | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ = inj₁ x∈
union-elim {x ∷ []} {y₁ ∷ y₂ ∷ ys} Linked.[-] (y₁<y₂ ∷ y₂< ∷ ys<) (there (there x∈)) | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁
  with union-elim {x ∷ []} {ys} Linked.[-] ys< x∈
... | inj₁ x₁ = inj₁ x₁
... | inj₂ y = inj₂ (there (there y))
union-elim (x ∷ xs) Linked.[] (here px) = inj₁ (here px)
union-elim (x ∷ xs) Linked.[] (there x∈) = inj₁ (there x∈)
union-elim {x ∷ xs} {y ∷ []} (x< ∷ xs<) Linked.[-] x∈
  with compare isStrictTotalOrder x y
union-elim {x ∷ .(_ ∷ _)} {y ∷ []} (x< ∷ xs<) Linked.[-] (here px) | tri< a ¬b ¬c = inj₁ (here px)
union-elim {x ∷ .(_ ∷ _)} {y ∷ []} (x< ∷ xs<) Linked.[-] (there x∈) | tri< a ¬b ¬c = Data.Sum.map there id (union-elim xs< Linked.[-] x∈)
... | tri≈ ¬a b ¬c = inj₁ x∈
union-elim {x ∷ .(_ ∷ _)} {y ∷ []} (x< ∷ xs<) Linked.[-] (here px) | tri> ¬a ¬b c = inj₂ (here px)
union-elim {x ∷ .(_ ∷ _)} {y ∷ []} (x< ∷ xs<) Linked.[-] (there x∈) | tri> ¬a ¬b c = inj₁ x∈
union-elim {x ∷ xs} {y ∷ ys} (x< ∷ xs<) (y< ∷ ys<) x∈
  with compare isStrictTotalOrder x y
union-elim {x ∷ .(_ ∷ _)} {y ∷ .(_ ∷ _)} (x< ∷ xs<) (y< ∷ ys<) (here px) | tri< a ¬b ¬c = inj₁ (here px)
union-elim {x ∷ .(_ ∷ _)} {y ∷ .(_ ∷ _)} (x< ∷ xs<) (y< ∷ ys<) (there x∈) | tri< a ¬b ¬c = Data.Sum.map there id (union-elim xs< (y< ∷ ys<) x∈)
union-elim {x ∷ .(_ ∷ _)} {y ∷ .(_ ∷ _)} (x< ∷ xs<) (y< ∷ ys<) (here px) | tri≈ ¬a b ¬c = inj₁ (here px)
union-elim {x₁ ∷ x₂ ∷ xs} {y₁ ∷ y₂ ∷ ys} (x< ∷ xs<) (y< ∷ ys<) (there x∈) | tri≈ ¬a b ¬c = Data.Sum.map there there (union-elim xs< ys< x∈ )
union-elim {x ∷ .(_ ∷ _)} {y ∷ .(_ ∷ _)} (x< ∷ xs<) (y< ∷ ys<) (here px) | tri> ¬a ¬b c = inj₂ (here px)
union-elim {x₁ ∷ x₂ ∷ xs} {y₁ ∷ y₂ ∷ ys} (x< ∷ xs<) (y< ∷ ys<) (there x∈) | tri> ¬a ¬b c = Data.Sum.map id there (union-elim (x< ∷ xs<) ys< x∈)

----------------------------------------------------------------------
-- intersection

{-# TERMINATING #-}
intersect₀ : List Carrier → List Carrier → List Carrier
intersect₀ [] ys = []
intersect₀ (x ∷ xs) [] = []
intersect₀ (x ∷ xs) (y ∷ ys)
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = intersect₀ xs (y ∷ ys)
... | tri≈ ¬a b ¬c = x ∷ intersect₀ xs ys
... | tri> ¬a ¬b c = intersect₀ (x ∷ xs) ys

_<<_ : Carrier → List Carrier → Set _
x << [] = ⊤
x << (y ∷ ys) = x < y

lemma-ordered-tail : ∀ {x y ys} → x < y → FreshOrderedList (y ∷ ys) → x << ys
lemma-ordered-tail x<y Linked.[-] = Level.lift Agda.Builtin.Unit.tt
lemma-ordered-tail x<y (y₁<y₂ ∷ ys<) = IsStrictPartialOrder.trans
                                     (isStrictPartialOrder isStrictTotalOrder) x<y y₁<y₂

{-# TERMINATING #-}
lemma-intersect₀-head : ∀ {x} ys zs → FreshOrderedList ys → FreshOrderedList zs → x << ys → x << zs
  → x << intersect₀ ys zs
lemma-intersect₀-head {x} [] [] foy foz x<<y x<<z = Level.lift Agda.Builtin.Unit.tt
lemma-intersect₀-head {x} [] (z₁ ∷ zs) foy foz x<<y x<<z = Level.lift Agda.Builtin.Unit.tt
lemma-intersect₀-head {x} (y₁ ∷ ys) [] foy foz x<<y x<<z = Level.lift Agda.Builtin.Unit.tt
lemma-intersect₀-head {x} (y₁ ∷ ys) (z₁ ∷ zs) foy foz x<<y x<<z
  with compare isStrictTotalOrder y₁ z₁
lemma-intersect₀-head {x} (y₁ ∷ ys) (z₁ ∷ zs) Linked.[-] foz x<<y x<<z | tri< a ¬b ¬c =  lemma-intersect₀-head ys (z₁ ∷ zs) Linked.[] foz (Level.lift Agda.Builtin.Unit.tt) x<<z
lemma-intersect₀-head {x} (y₁ ∷ ys) (z₁ ∷ zs) (y₁< ∷ foy) foz x<<y x<<z | tri< a ¬b ¬c =  lemma-intersect₀-head ys (z₁ ∷ zs) foy foz (lemma-ordered-tail x<<y (y₁< ∷ foy)) x<<z
... | tri≈ ¬a b ¬c = x<<y
lemma-intersect₀-head {x} (y₁ ∷ ys) (z₁ ∷ zs) foy Linked.[-] x<<y x<<z | tri> ¬a ¬b c =  lemma-intersect₀-head (y₁ ∷ ys) zs foy Linked.[] x<<y (Level.lift Agda.Builtin.Unit.tt)
lemma-intersect₀-head {x} (y₁ ∷ ys) (z₁ ∷ zs) foy (z₁< ∷ foz) x<<y x<<z | tri> ¬a ¬b c =  lemma-intersect₀-head (y₁ ∷ ys) zs foy foz x<<y (lemma-ordered-tail x<<z (z₁< ∷ foz))

lemma-intersect₀-head′ : ∀ {x₁ x₂} ys zs → FreshOrderedList ys → FreshOrderedList zs
  → x₁ ≈ x₂ → x₁ << ys → x₂ << zs
  → x₁ << intersect₀ ys zs
lemma-intersect₀-head′ [] [] foy foz x₁≈x₂ x₁<< x₂<< = Level.lift Agda.Builtin.Unit.tt
lemma-intersect₀-head′ [] (x ∷ zs) foy foz x₁≈x₂ x₁<< x₂<< = Level.lift Agda.Builtin.Unit.tt
lemma-intersect₀-head′ (x ∷ ys) [] foy foz x₁≈x₂ x₁<< x₂<< = Level.lift Agda.Builtin.Unit.tt
lemma-intersect₀-head′ (y ∷ ys) (z ∷ zs) foy foz x₁≈x₂ x₁<< x₂<<
  with compare isStrictTotalOrder y z
lemma-intersect₀-head′ (y ∷ ys) (z ∷ zs) Linked.[-] foz x₁≈x₂ x₁<< x₂<< | tri< y<z ¬b ¬c = lemma-intersect₀-head′ ys (z ∷ zs) Linked.[] foz (IsEquivalence.refl
                                                                                                                                             (IsStrictPartialOrder.isEquivalence
                                                                                                                                              (isStrictPartialOrder isStrictTotalOrder))) (Level.lift Agda.Builtin.Unit.tt) y<z
lemma-intersect₀-head′ (y ∷ ys) (z ∷ zs) (x ∷ foy) foz x₁≈x₂ x₁<< x₂<< | tri< a ¬b ¬c = lemma-intersect₀-head′ ys (z ∷ zs) foy foz (IsEquivalence.refl
                                                                                                                                      (IsStrictPartialOrder.isEquivalence
                                                                                                                                       (isStrictPartialOrder isStrictTotalOrder))) (IsStrictPartialOrder.trans
                                                                                                                                                                                      (isStrictPartialOrder isStrictTotalOrder) x₁<< x) (IsStrictPartialOrder.trans
                                                                                                                                                                                                                                           (isStrictPartialOrder isStrictTotalOrder) x₁<< a)
... | tri≈ ¬a b ¬c = x₁<<
lemma-intersect₀-head′ (y ∷ ys) (z ∷ zs) foy Linked.[-] x₁≈x₂ x₁<< x₂<< | tri> ¬a ¬b c = lemma-intersect₀-head′ (y ∷ ys) zs foy Linked.[] (IsEquivalence.refl
                                                                                                                                             (IsStrictPartialOrder.isEquivalence
                                                                                                                                              (isStrictPartialOrder isStrictTotalOrder))) c (Level.lift Agda.Builtin.Unit.tt)
lemma-intersect₀-head′ (y ∷ ys) (z ∷ zs) foy (x ∷ foz) x₁≈x₂ x₁<< x₂<< | tri> ¬a ¬b c = lemma-intersect₀-head′ (y ∷ ys) zs foy foz (IsEquivalence.refl
                                                                                                                                      (IsStrictPartialOrder.isEquivalence
                                                                                                                                       (isStrictPartialOrder isStrictTotalOrder))) x₁<< (IsStrictPartialOrder.<-resp-≈
                                                                                                                                                                                           (isStrictPartialOrder isStrictTotalOrder) .proj₂
                                                                                                                                                                                           (IsEquivalence.sym
                                                                                                                                                                                            (IsStrictPartialOrder.isEquivalence
                                                                                                                                                                                             (isStrictPartialOrder isStrictTotalOrder))
                                                                                                                                                                                            x₁≈x₂)
                                                                                                                                                                                           (IsStrictPartialOrder.trans
                                                                                                                                                                                            (isStrictPartialOrder isStrictTotalOrder) x₂<< x))


{-# TERMINATING #-}
intersect : {xs′ ys′ : List Carrier} → FreshOrderedList xs′ → FreshOrderedList ys′ → FreshOrderedList (intersect₀ xs′ ys′)
intersect Linked.[] ys = Linked.[]
intersect Linked.[-] Linked.[] = Linked.[]
intersect {x ∷ []} {y ∷ []} Linked.[-] Linked.[-]
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = Linked.[]
... | tri≈ ¬a b ¬c = Linked.[-]
... | tri> ¬a ¬b c = Linked.[]
intersect {x ∷ []} {y ∷ _} Linked.[-] (y₁<y₂ ∷ ys<)
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = Linked.[]
... | tri≈ ¬a b ¬c = Linked.[-]
... | tri> ¬a ¬b c = intersect Linked.[-] ys<
intersect (x ∷ xs) Linked.[] = Linked.[]
intersect {x ∷ xs} {y ∷ []} (x₁<x₂ ∷ xs<) Linked.[-]
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = intersect xs< Linked.[-]
... | tri≈ ¬a b ¬c = Linked.[-]
... | tri> ¬a ¬b c = Linked.[]
intersect {x ∷ xs} {y ∷ ys} (x₁<x₂ ∷ xs<) (y₁<y₂ ∷ ys<)
  with compare isStrictTotalOrder x y
... | tri< a ¬b ¬c = intersect xs< (y₁<y₂ ∷ ys<)
... | tri> ¬a ¬b c = intersect (x₁<x₂ ∷ xs<) ys< 
intersect {x₁ ∷ xs@(x₂ ∷ _)} {y₁ ∷ ys@(y₂ ∷ _)} (x₁<x₂ ∷ xs<) (y₁<y₂ ∷ ys<) | tri≈ ¬a x₁≈y₁ ¬c
  with intersect₀ xs ys in eq
... | [] = Linked.[-]
... | x₀ ∷ r
  with intersect xs< ys< | lemma-intersect₀-head′ _ _ xs< ys< x₁≈y₁ x₁<x₂ y₁<y₂
... | ih | lem rewrite eq = lem ∷ ih
