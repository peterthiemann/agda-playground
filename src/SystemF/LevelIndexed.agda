module LevelIndexed where

-- Level as levels
-- quantification over levels

open import Level
open import Data.Nat using (ℕ; zero; suc) renaming (_⊔_ to _⊔ℕ_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map; _++_; foldr; foldl)
open import Data.List.Properties using (map-∘; map-cong)
open import Data.List.NonEmpty using (List⁺; head; tail; [_]; _∷_; foldl₁; foldr₁; _++⁺_; _⁺++⁺_; toList) renaming (map to map⁺)
open import Data.List.NonEmpty.Properties using () renaming (map-∘ to map⁺-∘; map-cong to map⁺-cong)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using (Vec; lookup; _∷_)
open import Data.Product using (∃-syntax)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; _≗_)
open Relation.Binary.PropositionalEquality.≡-Reasoning

variable n : ℕ

data LX (n : ℕ) : Set where
  `_ : Fin n → LX n
  `ℓ : Level → LX n
  _`⊔_ : LX n → LX n → LX n
  `ω : LX n

record LV (n : ℕ) : Set where
  constructor ⟨_,_⟩
  field
    k : ℕ
    x : Fin n

  weak : LV (ℕ.suc n)
  weak = record{ k = k ; x = Fin.suc x }

  succ : LV n
  succ = record{ k = ℕ.suc k ; x = x }

data NLmode : Set where
  V X : NLmode

variable m : NLmode

data NL (n : ℕ) : NLmode → Set where
  VAR : List⁺ (LV n) → NL n V
  LEV : Level → List (LV n) → NL n V
  FIN : NL n V → NL n X
  OMG : NL n X

data Lvl* : NLmode → Set where
  LEV : Level → Lvl* m
  OMG : Lvl* X

succ : Lvl* m → Lvl* m
succ (LEV x) = LEV (Level.suc x)
succ OMG = OMG

NLV : ℕ → Set
NLV n = NL n V

-- data NLV (n : ℕ) : Set where
--   VAR : List⁺ (LV n) → NLV n
--   LEV : Level → List (LV n) → NLV n

NLX : ℕ → Set
NLX n = NL n X

OMGX : NLX n
OMGX = OMG

-- data NLX (n : ℕ) : Set where
--   VAR : List⁺ (LV n) → NLX n
--   LEV : Level → List (LV n) → NLX n
--   OMG : NLX n

Level* = Lvl* X

getLvl : Lvl* V → Level
getLvl (LEV x) = x

-- data Level* : Set where
--   LEV : Level → Level*
--   OMG : Level*

data L⟦_⟧ : Level* → Setω₁ where
  LEV : ∀ {ℓ} → Set ℓ → L⟦ LEV ℓ ⟧
  OMG : Setω → L⟦ OMG ⟧

getOMG : L⟦ OMG ⟧ → Setω
getOMG (OMG x) = x

getLEV : ∀{ℓ} → L⟦ LEV ℓ ⟧ → Set ℓ
getLEV (LEV x) = x

coe : ∀ {x y} → (eq : x ≡ y) → L⟦ x ⟧ → L⟦ y ⟧
coe refl lx = lx

lof : ℕ → Level → Level
lof ℕ.zero = id
lof (ℕ.suc n) = Level.suc ∘ lof n

evalLV : Vec Level n → LV n → Level
evalLV v ⟨ k , x ⟩ = lof k (lookup v x)


evalNLV : NLV n → Vec Level n → Level
evalNLV (VAR x) v = foldl₁ _⊔_ (map⁺ (evalLV v) x)
evalNLV (LEV l x) v = foldl _⊔_ l (map (evalLV v) x)

evalNL : NL n m → Vec Level n → Lvl* m
evalNL (VAR x) v = LEV (foldl₁ _⊔_ (map⁺ (evalLV v) x))
evalNL (LEV l x) v = LEV (foldl _⊔_ l (map (evalLV v) x))
evalNL (FIN x) v = LEV (evalNLV x v)
evalNL OMG v = OMG


evalLX : NLX n → Vec Level n → Level*
evalLX = evalNL

norm⊔ : ∀{m} → NL n m → NL n m → NL n m
norm⊔ (VAR x) (VAR y) = VAR (x ⁺++⁺ y)
norm⊔ (VAR x) (LEV l y) = LEV l (toList x ++ y)
norm⊔ (FIN x) OMG = OMG
norm⊔ (FIN x) (FIN y) = FIN (norm⊔ x y)
norm⊔ (LEV l x) (VAR y) = LEV l (toList y ++ x)
norm⊔ (LEV l₁ x) (LEV l₂ y) = LEV (l₁ ⊔ l₂) (x ++ y)
norm⊔ OMG _ = OMG

norm-suc : NL n m → NL n m
norm-suc (VAR x) = VAR (map⁺ LV.succ x)
norm-suc (LEV l x) = LEV (Level.suc l) (map LV.succ x)
norm-suc (FIN x) = FIN (norm-suc x)
norm-suc OMG = OMG

weakNL : NL n m → NL (ℕ.suc n) m
weakNL (VAR x) = VAR (map⁺ LV.weak x)
weakNL (LEV l x) = LEV l (map LV.weak x)
weakNL (FIN x) = FIN (weakNL x)
weakNL OMG = OMG

nlx : NLV n → NLX n
nlx = FIN
-- nlx OMG = OMG

module _ (v : Vec Level n) where

  evalLX-LV : (l : NLV n) → evalLX (nlx l) v ≡ LEV (evalNLV l v)
  evalLX-LV (VAR x) = refl
  evalLX-LV (LEV l x) = refl

  eval-succ : (x : LV n) → evalLV v (LV.succ x) ≡ Level.suc (evalLV v x)
  eval-succ x = refl

-- general

lift-∘ : {A C : Set} {f : A → C} {g : A → A} {h : C → C} → f ∘ g ≗ h ∘ f → map f ∘ map g ≗ map h ∘ map f
lift-∘ fg=hf [] = refl
lift-∘ fg=hf (x ∷ xs) = cong₂ _∷_ (fg=hf x) (lift-∘ fg=hf xs)

lift⁺-∘ : {A C : Set} {f : A → C} {g : A → A} {h : C → C} → f ∘ g ≗ h ∘ f → map⁺ f ∘ map⁺ g ≗ map⁺ h ∘ map⁺ f
lift⁺-∘ fg=hf (head₁ ∷ tail₁) = cong₂ _∷_ (fg=hf head₁) (lift-∘ fg=hf tail₁)

foldl-assoc : ∀{a}{A : Set a} (_⊕_ : A → A → A) (assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z))
  → ∀ x y xs → foldl _⊕_ (x ⊕ y) xs ≡ x ⊕ foldl _⊕_ y xs
foldl-assoc _⊕_ assoc x y [] = refl
foldl-assoc _⊕_ assoc x y (z ∷ zs) = trans (cong (λ □ → foldl _⊕_ □ zs) (assoc x y z))
                                           (foldl-assoc _⊕_ assoc x (y ⊕ z) zs)

foldl-assoc-∷ : ∀{a}{A : Set a} (_⊕_ : A → A → A) (assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z))
  → ∀ x y zs → foldl _⊕_ x (y ∷ zs) ≡ x ⊕ foldl _⊕_ y zs
foldl-assoc-∷ _⊕_ assoc x y zs = foldl-assoc _⊕_ assoc x y zs


foldr-suc : ∀ {ℓ} (x : List Level) → foldr _⊔_ (Level.suc ℓ) (map Level.suc x) ≡ Level.suc (foldr _⊔_ ℓ x)
foldr-suc [] = refl
foldr-suc{ℓ = ℓ} (x ∷ xs) = cong (Level.suc x ⊔_) (foldr-suc{ℓ = ℓ} xs)

-- by level magic
⊔-suc : ∀ x y → Level.suc x ⊔ Level.suc y ≡ Level.suc (x ⊔ y)
⊔-suc x y = refl


foldl-suc : ∀ (x : Level) (xs : List Level)
  → foldl _⊔_ (Level.suc x) (map Level.suc xs) ≡ Level.suc (foldl _⊔_ x xs)
foldl-suc y [] = refl
foldl-suc y (x ∷ xs) = foldl-suc (y ⊔ x) xs

foldl₁-suc : ∀ (x : List⁺ Level) → foldl₁ _⊔_ (map⁺ Level.suc x) ≡ Level.suc (foldl₁ _⊔_ x)
foldl₁-suc (head₁ ∷ tail₁) = foldl-suc head₁ tail₁

evalLX-var-var : ∀ {ℓ₁ ℓ₂} → (xh : LV n) (xt  : List (LV n)) (x₂  : List⁺ (LV n)) (v   : Vec Level n)
  (eq₁ : (foldl₁ _⊔_ (map⁺ (evalLV v) (xh ∷ xt))) ≡ ℓ₁) (eq₂ : foldl₁ _⊔_ (map⁺ (evalLV v) x₂) ≡ ℓ₂)
  → (foldl _⊔_ (lof (LV.k xh) (lookup v (LV.x xh)))
       (map (evalLV v) (xt ++ head x₂ ∷ tail x₂))) ≡ (ℓ₁ ⊔ ℓ₂)
evalLX-var-var xh [] x₂ v eq₁ eq₂ =
  trans (foldl-assoc _⊔_ (λ x y z → refl) (evalLV v xh) (evalLV v (head x₂)) (map (evalLV v) (tail x₂)))
        (cong₂ _⊔_ eq₁ eq₂)
evalLX-var-var{ℓ₁ = ℓ₁}{ℓ₂ = ℓ₂} xh (x ∷ xt) x₂ v eq₁ eq₂ =
  let eq₃ = foldl-assoc _⊔_ (λ x y z → refl) (evalLV v xh) (evalLV v x) (map (evalLV v) xt) in
  let eq₄ = trans (sym eq₃) eq₁ in
  let ih = evalLX-var-var x xt x₂ v refl eq₂ in 
  trans (foldl-assoc _⊔_ (λ x y z → refl) (evalLV v xh) (evalLV v x) (map (evalLV v) (xt ++ head x₂ ∷ tail x₂)))
        (begin
          evalLV v xh ⊔ foldl _⊔_ (evalLV v x) (map (evalLV v) (xt ++ head x₂ ∷ tail x₂))
        ≡⟨ cong (evalLV v xh ⊔_) ih ⟩
          evalLV v xh ⊔ (foldl₁ _⊔_ (map⁺ (evalLV v) (x ∷ xt)) ⊔ ℓ₂)
        ≡⟨ cong (_⊔ ℓ₂) eq₄ ⟩
          ℓ₁ ⊔ ℓ₂
        ∎)

evalLX-var-var+ : ∀ {ℓ₁ ℓ₂} → (x₁  : List⁺ (LV n)) (x₂  : List⁺ (LV n)) (v   : Vec Level n)
  (eq₁ : evalLX (FIN (VAR x₁)) v ≡ LEV ℓ₁) (eq₂ : evalLX (FIN (VAR x₂)) v ≡ LEV ℓ₂)
  → evalLX (FIN (VAR (x₁ ⁺++⁺ x₂))) v ≡ LEV (ℓ₁ ⊔ ℓ₂)
evalLX-var-var+ (head₁ ∷ tail₁) x₂ v refl refl = cong LEV (evalLX-var-var head₁ tail₁ x₂ v refl refl)

evalLX-lev-var+ :
  ∀ {ℓ₂ ℓ₃ ℓ₄ : Level} →
  (v   : Vec Level n)
  (x₁  : List⁺ (LV n))
  (x₂  : List (LV n))
  (eq₁ : foldl₁ _⊔_ (map⁺ (evalLV v) x₁) ≡ ℓ₃)
  (eq₂ : foldl _⊔_ ℓ₂ (map (evalLV v) x₂) ≡ ℓ₄)
  → foldl _⊔_ ℓ₂ (map (evalLV v) (head x₁ ∷ tail x₁ ++ x₂)) ≡ ℓ₃ ⊔ ℓ₄
evalLX-lev-var+ {n} {ℓ₂} {.(foldl₁ _⊔_ (map⁺ (evalLV v) (xh ∷ [])))} {ℓ₄} v (xh ∷ []) ys refl eq₂ =
  begin
    foldl _⊔_ ℓ₂ (map (evalLV v) (xh ∷ [] ++ ys))
  ≡⟨ foldl-assoc _⊔_ (λ x y z → refl) (evalLV v xh) ℓ₂ (map (evalLV v) ys) ⟩
    evalLV v xh ⊔ foldl _⊔_ ℓ₂ (map (evalLV v) ys)
  ≡⟨ cong (evalLV v xh ⊔_) eq₂ ⟩
    evalLV v xh ⊔ ℓ₄
  ≡⟨ refl ⟩
    foldl₁ _⊔_ (map⁺ (evalLV v) (xh ∷ [])) ⊔ ℓ₄
  ∎
evalLX-lev-var+ {n} {ℓ₂} {ℓ₃} {ℓ₄} v (xh ∷ x ∷ xt) ys eq₁ eq₂ =
  let ℓ₃′ = foldl _⊔_ (evalLV v xh) (map (evalLV v) xt) in
  let eq₀ = trans (sym eq₁) (foldl-assoc _⊔_ (λ x y z → refl) (evalLV v x) (evalLV v xh) (map (evalLV v) xt)) in
  let ih = evalLX-lev-var+ {n} {ℓ₂} {ℓ₃′} v (xh ∷ xt) ys refl eq₂ in
  begin
    foldl _⊔_ ℓ₂ (map (evalLV v) (xh ∷ (x ∷ xt) ++ ys))
  ≡⟨ foldl-assoc _⊔_ (λ x y z → refl) (evalLV v x) (ℓ₂ ⊔ evalLV v xh) (map (evalLV v) (xt ++ ys)) ⟩
    evalLV v x ⊔
      foldl _⊔_ (ℓ₂ ⊔ evalLV v xh) (map (evalLV v) (xt ++ ys))
  ≡⟨ cong (evalLV v x ⊔_) ih ⟩
    evalLV v x ⊔ (ℓ₃′ ⊔ ℓ₄)
  ≡⟨ sym (cong (ℓ₄ ⊔_) eq₀) ⟩
    ℓ₃ ⊔ ℓ₄
  ∎

evalLX-lev-lev : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
  (v   : Vec Level n)
  (xs ys : List (LV n))
  (eq₁ : (foldl _⊔_ ℓ₁ (map (evalLV v) xs)) ≡ ℓ₃)
  (eq₂ : (foldl _⊔_ ℓ₂ (map (evalLV v) ys)) ≡ ℓ₄)
  → foldl _⊔_ (ℓ₁ ⊔ ℓ₂) (map (evalLV v) (xs ++ ys)) ≡ ℓ₃ ⊔ ℓ₄
evalLX-lev-lev {n} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} v [] ys refl eq₂ =
  begin
    foldl _⊔_ (ℓ₁ ⊔ ℓ₂) (map (evalLV v) ([] ++ ys))
  ≡⟨ foldl-assoc _⊔_ (λ x y z → refl) ℓ₁ ℓ₂ (map (evalLV v) ys) ⟩
    ℓ₁ ⊔ foldl _⊔_ ℓ₂ (map (evalLV v) ys)
  ≡⟨ cong (ℓ₁ ⊔_) eq₂ ⟩
    ℓ₃ ⊔ ℓ₄
  ∎
evalLX-lev-lev {n} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} v (x ∷ xs) ys eq₁ eq₂ =
  let ℓ₃′ = foldl _⊔_ ℓ₁ (map (evalLV v) xs) in
  let eq₀ = trans (sym eq₁) (foldl-assoc _⊔_ (λ x y z → refl) (evalLV v x) ℓ₁ (map (evalLV v) xs)) in
  begin
    foldl _⊔_ (ℓ₁ ⊔ ℓ₂) (map (evalLV v) ((x ∷ xs) ++ ys))
  ≡⟨ foldl-assoc _⊔_ (λ x y z → refl) (evalLV v x) (ℓ₁ ⊔ ℓ₂) (map (evalLV v) (xs ++ ys)) ⟩
    evalLV v x ⊔ foldl _⊔_ (ℓ₁ ⊔ ℓ₂) (map (evalLV v) (xs ++ ys))
  ≡⟨ cong (evalLV v x ⊔_) (evalLX-lev-lev {n} {ℓ₁} {ℓ₂} {ℓ₃′} {ℓ₄} v xs ys refl eq₂)  ⟩
    evalLV v x ⊔ (ℓ₃′ ⊔ ℓ₄)
  ≡⟨ cong (ℓ₄ ⊔_) (sym eq₀) ⟩
    ℓ₃ ⊔ ℓ₄
  ∎

module _  (v : Vec Level n) where

  evalLX-norm⊔ : {x₁ x₂ : Level} (l₁ l₂ : NLX n)
    → evalLX l₁ v ≡ LEV x₁ → evalLX l₂ v ≡ LEV x₂
    → evalLX (norm⊔ l₁ l₂) v ≡ LEV (x₁ ⊔ x₂)
  evalLX-norm⊔ (FIN (VAR x₁)) (FIN (VAR x₂)) eq₁ eq₂ = evalLX-var-var+ x₁ x₂ v eq₁ eq₂
  evalLX-norm⊔ (FIN (VAR x₁)) (FIN (LEV ℓ₂ x₂)) refl refl = cong LEV (evalLX-lev-var+ {ℓ₂ = ℓ₂} v x₁ x₂ refl refl)
  evalLX-norm⊔ (FIN (LEV ℓ₁ x₁)) (FIN (VAR x₂)) refl refl = cong LEV (evalLX-lev-var+ {ℓ₂ = ℓ₁} v x₂ x₁ refl refl)
  evalLX-norm⊔ (FIN (LEV ℓ₁ x₁)) (FIN (LEV ℓ₂ x₂)) refl refl = cong LEV (evalLX-lev-lev {ℓ₁ = ℓ₁}{ℓ₂} v x₁ x₂ refl refl)

  evalLX-norm⊔-OMGʳ : {x₁ : Level} (l₁ l₂ : NLX n) → evalLX l₁ v ≡ LEV x₁ → evalLX l₂ v ≡ OMG → evalLX (norm⊔ l₁ l₂) v ≡ OMG
  evalLX-norm⊔-OMGʳ (FIN (VAR x)) OMG eq₁ eq₂ = refl
  evalLX-norm⊔-OMGʳ (FIN (LEV x x₁)) OMG eq₁ eq₂ = refl

  evalLX-norm⊔-OMGˡ : {x₂ : Level} (l₁ l₂ : NLX n) → evalLX l₁ v ≡ OMG → evalLX l₂ v ≡ LEV x₂ → evalLX (norm⊔ l₁ l₂) v ≡ OMG
  evalLX-norm⊔-OMGˡ OMG l₂ eq₁ eq₂ = refl

  evalLX-norm⊔-OMG² : (l₁ l₂ : NLX n) → evalLX l₁ v ≡ OMG → evalLX l₂ v ≡ OMG → evalLX (norm⊔ l₁ l₂) v ≡ OMG
  evalLX-norm⊔-OMG² OMG OMG eq₁ eq₂ = refl

  evalLX-suc : (l : NLV n) → evalLX (norm-suc (nlx l)) v ≡ LEV (Level.suc (evalNLV l v))
  evalLX-suc (VAR x) = cong LEV (trans (cong (foldl₁ _⊔_) (lift⁺-∘ {f = evalLV v} {g = LV.succ} {h = Level.suc} (eval-succ v) x))
                                       (foldl₁-suc (map⁺ (evalLV v) x)))
  evalLX-suc (LEV ℓ x) = cong LEV (trans (cong (foldl _⊔_ (Level.suc ℓ)) (lift-∘ {f = evalLV v} {g = LV.succ} {h = Level.suc} (eval-succ v) x))
                                           (foldl-suc ℓ (map (evalLV v) x)))

  evalLX-all : {x′ : Level} (lev : NLV n) (l′ : NLX n)
    → evalLX l′ v ≡ LEV x′
    → evalLX (norm⊔ (norm-suc (nlx lev)) l′) v ≡ LEV (Level.suc (evalNLV lev v) Level.⊔ x′)
  evalLX-all {x′ = x′} lev l′ eq =
    begin
      evalLX (norm⊔ (norm-suc (nlx lev)) l′) v
    ≡⟨ evalLX-norm⊔ (norm-suc (nlx lev)) l′ (evalLX-suc lev) eq ⟩
      LEV (Level.suc (evalNLV lev v) ⊔ x′)
    ∎

  evalLX-all-OMG : (lev : NLV n) (l′ : NLX n)
    → evalLX l′ v ≡ OMG
    → evalLX (norm⊔ (norm-suc (nlx lev)) l′) v ≡ OMG
  evalLX-all-OMG (VAR x) OMG eq = refl
  evalLX-all-OMG (LEV x x₁) OMG eq = refl


LEnv : ℕ → Set
LEnv n = List (NLV n)

variable Δ : LEnv n
variable l : NLV n
variable l₁ l₂ l′ : NLX n

data Type (n : ℕ) (Δ : LEnv n) : NLX n → Set where
  `_ : l ∈ Δ → Type n Δ (nlx l)
  _`⇒_ : Type n Δ l₁ → Type n Δ l₂ → Type n Δ (norm⊔ l₁ l₂)
  `∀ℓ_ : Type (ℕ.suc n) (map weakNL Δ) l′ → Type n Δ OMG
  `∀α_,_ : (lev : NLV n) → Type n (lev ∷ Δ) l′ → Type n Δ (norm⊔ (norm-suc (nlx lev)) l′)

Env* : Vec Level n → LEnv n → Setω
Env* v Δ = ∀ {l} → l ∈ Δ → Set (evalNLV l v)

pushLV : ∀{ℓ} (v : Vec Level n) (x : LV n) → evalLV v x ≡ evalLV (ℓ ∷ v) (LV.weak x)
pushLV v ⟨ k , x ⟩ = refl

pushNLV : ∀ {ℓ} (v : Vec Level n) (l : NLV n) → evalNLV l v ≡ evalNLV (weakNL l) (ℓ ∷ v)
pushNLV{ℓ = ℓ} v (VAR x) = cong (foldl₁ _⊔_) (trans  (map⁺-cong (pushLV{ℓ = ℓ} v) x)  (map⁺-∘ {g = evalLV (ℓ ∷ v)}{f = LV.weak} x))
pushNLV{ℓ = ℓ} v (LEV l x) = cong (foldl _⊔_ l) (trans  (map-cong (pushLV{ℓ = ℓ} v) x)  (map-∘ {g = evalLV (ℓ ∷ v)}{f = LV.weak} x))


coe* : ∀ ℓ (v : Vec Level n) (Δ : LEnv n) → Env* v Δ → Env* (ℓ ∷ v) (map weakNL Δ)
coe* ℓ v (l ∷ Δ) η (here refl) rewrite sym (pushNLV{ℓ = ℓ} v l) = η (here refl)
coe* ℓ v (l ∷ Δ) η (there x) = coe* ℓ v Δ (η ∘ there) x 


ext* : ∀ {lev : NLV n} {v : Vec Level n} → Set (evalNLV lev v) → Env* v Δ → Env* v (lev ∷ Δ)
ext* S η (here refl) = S
ext* S η (there x) = η x

T⟦_⟧ : (T : Type n Δ l′) → (v : Vec Level n) → Env* v Δ → L⟦ evalLX l′ v ⟧
T⟦ `_ {l = l} x ⟧ v η
  rewrite evalLX-LV v l
  = LEV (η x)
T⟦ _`⇒_ {l₁ = l₁}{l₂ = l₂} T₁ T₂ ⟧ v η
  with T⟦ T₁ ⟧ v η | T⟦ T₂ ⟧ v η | evalLX l₁ v in eq₁ | evalLX l₂ v in eq₂
... | S₁ | S₂ | LEV x₁ | LEV x₂
  rewrite eq₁ | eq₂ | evalLX-norm⊔ v l₁ l₂ eq₁ eq₂
  = LEV (getLEV S₁ → getLEV S₂)
... | S₁ | S₂ | LEV x₁ | OMG
  rewrite eq₁ | eq₂ | evalLX-norm⊔-OMGʳ v l₁ l₂ eq₁ eq₂
  = OMG (getLEV S₁ → getOMG S₂)
... | S₁ | S₂ | OMG | LEV x₂
  rewrite eq₁ | eq₂ | evalLX-norm⊔-OMGˡ v l₁ l₂ eq₁ eq₂
  = OMG (getOMG S₁ → getLEV S₂)
... | S₁ | S₂ | OMG | OMG
  rewrite eq₁ | eq₂ | evalLX-norm⊔-OMG² v l₁ l₂ eq₁ eq₂
  = OMG (getOMG S₁ → getOMG S₂)
T⟦ `∀ℓ_ {l′ = l′} T ⟧ v η
  with l′
... | FIN (VAR x) = OMG (∀ (ℓ : Level) → getLEV (coe refl (T⟦ T ⟧ (ℓ ∷ v) (coe* ℓ v _ η))))
... | FIN (LEV ℓ x) = OMG (∀ (ℓ : Level) → getLEV (coe refl (T⟦ T ⟧ (ℓ ∷ v) (coe* ℓ v _ η))))
... | OMG = OMG (∀ (ℓ : Level) → getOMG (coe refl (T⟦ T ⟧ (ℓ ∷ v) (coe* ℓ v _ η))))
T⟦ `∀α_,_ {l′ = l′} lev T ⟧ v η
  with evalLX l′ v in eq′
... | LEV x
  rewrite evalLX-all v lev l′ eq′
  = LEV (∀ α → getLEV (coe eq′ (T⟦ T ⟧ v (ext*{v = v} α η))) )
... | OMG
  rewrite  evalLX-all-OMG v lev l′ eq′
  = OMG (∀ α → getOMG (coe eq′ (T⟦ T ⟧ v (ext*{v = v} α η))))


----------------------------------------------------------------------
-- towards expressions

-- type environments
data Ctx : (n : ℕ) → LEnv n → Set where
  ∅     : Ctx n []
  _◁_   : Type n Δ l′ → Ctx n Δ → Ctx n Δ          
  _◁*_  : (l : NLV n) → Ctx n Δ → Ctx n (l ∷ Δ)
  ◁ℓ_   : Ctx n Δ → Ctx (ℕ.suc n) (map weakNL Δ)

variable
  Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Ctx n Δ
  T T′ : Type n Δ l′


wkₗₑ : LEnv n → LEnv (ℕ.suc n)
wkₗₑ = map weakNL
wkₗ′ = weakNL


postulate
  Twk : Type n Δ l′ → Type n (l ∷ Δ) l′
  _[_]T : Type n (l ∷ Δ) l′ → Type n Δ (nlx l)  → Type n Δ l′
  _[_]ℓℓ : NLX (ℕ.suc n) → NLV n → NLX n
  _[_]ℓ : Type (ℕ.suc n) (wkₗₑ Δ) l′ → (newl : NLV n) → Type n Δ (l′ [ newl ]ℓℓ)

  wkₗₜ : Type n Δ l′ → Type (ℕ.suc n) (map weakNL Δ) (weakNL l′)

--! inn
data inn : Type n Δ l′ → Ctx n Δ → Set where
  here   : inn T (T ◁ Γ)
  there  : inn T Γ → inn T (T′ ◁ Γ)
  tskip  : inn T Γ → inn (Twk T) (l ◁* Γ)
  lskip  : inn T Γ → inn (wkₗₜ T) (◁ℓ Γ)

data Expr {Δ : LEnv n} (Γ : Ctx n Δ) : Type n Δ l′ → Set where
  -- #_    : (k : ℕ) → Expr Γ `ℕ
  -- `suc  : Expr Γ `ℕ → Expr Γ `ℕ
  `_     : ∀ {T : Type n Δ l′} → inn T Γ → Expr Γ T
  ƛ_     : ∀ {T₁ : Type n Δ l₁} {T₂ : Type n Δ l₂} → Expr (T₁ ◁ Γ) T₂ → Expr Γ (T₁ `⇒ T₂)
  _·_    : ∀ {T₁ : Type n Δ l₁} {T₂ : Type n Δ l₂} → Expr Γ (T₁ `⇒ T₂) → Expr Γ T₁ → Expr Γ T₂
  Λ_⇒_  : ∀ (l : NLV n) → {T : Type n (l ∷ Δ) l′} → Expr (l ◁* Γ) T → Expr Γ (`∀α l , T)
  _∙_    : ∀ {T : Type n (l ∷ Δ) l′} → Expr Γ (`∀α l , T) → (T′ : Type n Δ (nlx l)) → Expr Γ (T [ T′ ]T)
  Λℓ_   : ∀ {T : Type (ℕ.suc n) (wkₗₑ Δ) (wkₗ′ l′)} → Expr (◁ℓ Γ) T → Expr Γ (`∀ℓ T)
  _·ℓ_  : ∀ {T : Type (ℕ.suc n) (wkₗₑ Δ) (wkₗ′ l′)} → Expr Γ (`∀ℓ T) → (newl : NLV n) → Expr Γ (T [ newl ]ℓ)


variable e e₁ e₂ e₃ : Expr Γ T

-- level environments

DEnv : ℕ → Set
DEnv = Vec Level


-- value environments

data V⟦_⟧ : {l* : Level*} → L⟦ l* ⟧ → Setω₁ where
  LEV : ∀ {ℓ} → {A : Set ℓ} → (a : A) → V⟦ LEV A ⟧
  OMG : {A : Setω} → (a : A) → V⟦ OMG A ⟧

VEnv : {Δ : LEnv n} → (d : DEnv n) → Ctx n Δ → Env* d Δ → Setω₁
VEnv {n} {Δ} d Γ η = ∀ l′ (T : Type n Δ l′) → (x : inn T Γ) → V⟦ (T⟦ T ⟧ d η) ⟧

extend : ∀ {l} {d : DEnv n} {T : Type n Δ l}{Γ : Ctx n Δ}{η : Env* d Δ}
  → VEnv d Γ η → V⟦  (T⟦ T ⟧ d η) ⟧ → VEnv d (T ◁ Γ) η
extend γ v _ _ here = v
extend γ v _ _ (there x) = γ _ _ x

postulate
  extend-tskip : ∀ {Δ : LEnv n}  {d : DEnv n} {Γ : Ctx n Δ} {η : Env* d Δ} {⟦α⟧ : Set (evalNLV l d)} →
    VEnv d Γ η → VEnv d (l ◁* Γ) (ext* {v = d} ⟦α⟧ η)

  _≡ω₁_ : {A : Setω₁} (a b : A) → Setω₁

  subst-env : ∀ {d : DEnv n} (T : Type n (l ∷ Δ) l′) (T′ : Type n Δ (nlx l)) (η : Env* d Δ)
    → T⟦ T ⟧ d (ext* {v = d} (getLEV (T⟦ T′ ⟧ d η)) η) ≡ω₁ T⟦ T [ T′ ]T ⟧ d η

E⟦_⟧ : ∀ {T : Type n Δ l′}{Γ : Ctx n Δ}
  → (e : Expr Γ T) →  (d : DEnv n) → (η : Env* d Δ) → (γ : VEnv d Γ η) → V⟦ T⟦ T ⟧ d η ⟧
-- E⟦ # n ⟧ η γ = n
-- E⟦ `suc x ⟧ η γ = ℕ.suc (E⟦ x ⟧ η γ)
E⟦ ` x ⟧ d η γ = γ _ _ x
E⟦ ƛ_ {l₁ = l₁}{l₂ = l₂}{T₁ = T₁}{T₂ = T₂} M ⟧ v η γ
  = aux (evalLX l₁ v) (evalLX l₂ v) refl refl (T⟦ T₁ ⟧ v η) (T⟦ T₂ ⟧ v η)
  where aux : (l*₁ l*₂ : Level*) (eq₁ : l*₁ ≡ evalLX l₁ v) (eq₂ : l*₂ ≡ evalLX l₂ v) (S₁ : L⟦ l*₁ ⟧) (S₂ : L⟦ l*₂ ⟧) → V⟦ T⟦ T₁ `⇒ T₂ ⟧ v η ⟧
        aux (LEV x) (LEV x₁) eq₁ eq₂ S₁ S₂ = {!!}
        aux (LEV x) OMG eq₁ eq₂ S₁ S₂ = {!!}
        aux OMG (LEV x) eq₁ eq₂ S₁ S₂ = {!!}
        aux OMG OMG eq₁ eq₂ S₁ S₂ = {!!}
--   λ x → let r = E⟦ M ⟧ η (extend γ (coe (ElLift≤ {l}{l ⊔ l′} (⊔₁ l l′) (encode T η)) x)) in
--         coe (sym (ElLift≤ (⊔₂ l l′) (encode T′ η))) r
-- -- λ x → E⟦ M ⟧ η (extend γ x)
-- E⟦ _·_ {l = l}{l′ = l′}{T = T}{T′ = T′} M N ⟧ η γ =
--   let f = E⟦ M ⟧ η γ ; a = E⟦ N ⟧ η γ in
--   coe (ElLift≤ (⊔₂ l l′) (encode T′ η)) (f (coe (sym (ElLift≤ (⊔₁ l l′) (encode T η))) a))
-- -- E⟦ M ⟧ η γ (E⟦ N ⟧ η γ)
-- E⟦ Λ_⇒_ {l′ = l′} l {T} M ⟧ η γ = λ α →
--   let η′ = coe (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) α ∷ η in
--   let r = E⟦ M ⟧ η′ (extend-tskip γ) in
--   coe (sym (ElLift≤ (⊔₂ (ℕ.suc l) l′) (encode T η′))) r
-- -- E⟦ M ⟧ (α ∷ η) (extend-tskip γ)
-- E⟦ _∙_ {l = l} {l′ = l′}{T = T} M T′ ⟧ η γ =
--   let F = E⟦ M ⟧ η γ in
--   let u′ = encode T′ η in
--   let eq1 = (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) in
--   let eq2 = Uⁱʳ & (ext (λ j → ext (λ p → trans (U<-compute {l} {wf} {j} {p}) (sym U<-compute)))) in
--   let r = F (coe eq2 u′) in
--   coe (trans (trans (cong (λ □ → Elⁱʳ (Lift≤ (⊔₂ (ℕ.suc l) l′) (encode T (□ ∷ η)))) (coe-coe eq2 eq1 {u′}))
--                     (ElLift≤ (⊔₂ (ℕ.suc l) l′) (encode T (u′ ∷ η)))) (subst-env T T′ η)) r
