module LevelIndexed where

-- Level as levels
-- quantification over levels

open import Level
open import Data.Nat using (ℕ; zero; suc) renaming (_⊔_ to _⊔ℕ_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map; _++_; foldr)
open import Data.List.NonEmpty using (List⁺; head; tail; [_]; _∷_; foldr₁; _⁺++⁺_; toList) renaming (map to map⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using (Vec; lookup; _∷_)

open import Function using (id)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

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

data NLV (n : ℕ) : Set where
  VAR : List⁺ (LV n) → NLV n
  LEV : Level → List (LV n) → NLV n

data NLX (n : ℕ) : Set where
  VAR : List⁺ (LV n) → NLX n
  LEV : Level → List (LV n) → NLX n
  OMG : NLX n

data Level* : Set where
  LEV : Level → Level*
  OMG : Level*

data L⟦_⟧ : Level* → Setω₁ where
  LEV : ∀ {ℓ} → Set ℓ → L⟦ LEV ℓ ⟧
  OMG : Setω → L⟦ OMG ⟧

getOMG : L⟦ OMG ⟧ → Setω
getOMG (OMG x) = x

getLEV : ∀{ℓ} → L⟦ LEV ℓ ⟧ → Set ℓ
getLEV (LEV x) = x

coe : ∀ {x y} → (eq : x ≡ y) → L⟦ x ⟧ → L⟦ y ⟧
coe refl lx = lx

evalLV : Vec Level n → LV n → Level
evalLV v ⟨ zero , x ⟩ = lookup v x
evalLV v ⟨ ℕ.suc k , x ⟩ = Level.suc (evalLV v ⟨ k , x ⟩)

evalLX : NLX n → Vec Level n → Level*
evalLX (VAR x) v = LEV (foldr₁ _⊔_ (map⁺ (evalLV v) x))
evalLX (LEV l x) v = LEV (foldr _⊔_ l (map (evalLV v) x))
evalLX OMG v = OMG

evalNLV : NLV n → Vec Level n → Level
evalNLV (VAR x) v = foldr₁ _⊔_ (map⁺ (evalLV v) x)
evalNLV (LEV l x) v = foldr _⊔_ l (map (evalLV v) x)

norm⊔ : NLX n → NLX n → NLX n
norm⊔ (VAR x) (VAR y) = VAR (x ⁺++⁺ y)
norm⊔ (VAR x) (LEV l y) = LEV l (toList x ++ y)
norm⊔ (VAR x) OMG = OMG
norm⊔ (LEV l x) (VAR y) = LEV l (x ++ toList y)
norm⊔ (LEV l₁ x) (LEV l₂ y) = LEV (l₁ ⊔ l₂) (x ++ y)
norm⊔ (LEV l x) OMG = OMG
norm⊔ OMG _ = OMG

norm-suc : NLX n → NLX n
norm-suc (VAR x) = VAR (map⁺ LV.succ x)
norm-suc (LEV l x) = LEV (Level.suc l) (map LV.succ x)
norm-suc OMG = OMG

weakNLX : NLX n → NLX (ℕ.suc n)
weakNLX (VAR x) = VAR (map⁺ LV.weak x)
weakNLX (LEV l x) = LEV (Level.suc l) (map LV.weak x)
weakNLX OMG = OMG

weakNLV : NLV n → NLV (ℕ.suc n)
weakNLV (VAR x) = VAR (map⁺ LV.weak x)
weakNLV (LEV l x) = LEV (Level.suc l) (map LV.weak x)

strongVar : LV (ℕ.suc n) → NLX n
strongVar ⟨ k , Fin.zero ⟩ = OMG
strongVar ⟨ k , Fin.suc x ⟩ = VAR [ ⟨ k , x ⟩ ]

strongVar* : List⁺ (LV (ℕ.suc n)) → NLX n
strongVar* vs = foldr₁ norm⊔ (map⁺ strongVar vs)

strongNLX : NLX (ℕ.suc n) → NLX n
strongNLX (VAR x) = strongVar* x
strongNLX (LEV l x) = foldr norm⊔ (LEV l []) (map strongVar x)
strongNLX (OMG) = OMG

nlx : NLV n → NLX n
nlx (VAR x) = VAR x
nlx (LEV l x) = LEV l x

evalLX-LV : (v : Vec Level n) (l : NLV n) → evalLX (nlx l) v ≡ LEV (evalNLV l v)
evalLX-LV v (VAR x) = refl
evalLX-LV v (LEV l x) = refl

eval-succ : (v : Vec Level n) (x : LV n) → evalLV v (LV.succ x) ≡ Level.suc (evalLV v x)
eval-succ v x = refl

foldr-suc : ∀ {ℓ} (x : List Level) → foldr _⊔_ (Level.suc ℓ) (map Level.suc x) ≡ Level.suc (foldr _⊔_ ℓ x)
foldr-suc [] = refl
foldr-suc{ℓ = ℓ} (x ∷ xs) = cong (Level.suc x ⊔_) (foldr-suc{ℓ = ℓ} xs)

foldr₁-suc : ∀ (x : List⁺ Level) → foldr₁ _⊔_ (map⁺ Level.suc x) ≡ Level.suc (foldr₁ _⊔_ x)
foldr₁-suc (head₁ ∷ tail₁) = {!!}

evalLX-suc : (v : Vec Level n) (l : NLV n) → evalLX (norm-suc (nlx l)) v ≡ LEV (Level.suc (evalNLV l v))
evalLX-suc v (VAR x) = cong LEV (foldr₁-suc (map⁺ (evalLV {!v!}) x))
evalLX-suc v (LEV ℓ x) = cong LEV (foldr-suc {{!!}} (map (evalLV v) x))

evalLX-all : {x′ : Level} (v : Vec Level n) (lev : NLV n) (l′ : NLX n)
  → evalLX l′ v ≡ LEV x′
  → evalLX (norm⊔ (norm-suc (nlx lev)) l′) v ≡ LEV (Level.suc (evalNLV lev v) Level.⊔ x′)
evalLX-all v lev l′ eq = {!!}

evalLX-all-OMG : (v : Vec Level n) (lev : NLV n) (l′ : NLX n)
  → evalLX l′ v ≡ OMG
  → evalLX (norm⊔ (norm-suc (nlx lev)) l′) v ≡ OMG
evalLX-all-OMG v lev l′ eq = {!!}

evalLX-norm⊔ : {x₁ x₂ : Level} (l₁ l₂ : NLX n) (v : Vec Level n) → evalLX l₁ v ≡ LEV x₁ → evalLX l₂ v ≡ LEV x₂ → evalLX (norm⊔ l₁ l₂) v ≡ LEV (x₁ ⊔ x₂)
evalLX-norm⊔ (VAR x₁) (VAR x₂) v eq₁ eq₂ = {!!}
evalLX-norm⊔ (VAR x₁) (LEV ℓ₂ x₂) v eq₁ eq₂ = {!!}
evalLX-norm⊔ (LEV ℓ₁ x₁) (VAR x₂) v eq₁ eq₂ = {!!}
evalLX-norm⊔ (LEV ℓ₁ x₁) (LEV ℓ₂ x₂) v eq₁ eq₂ = {!!}

evalLX-norm⊔-OMGʳ : {x₁ : Level} (l₁ l₂ : NLX n) (v : Vec Level n) → evalLX l₁ v ≡ LEV x₁ → evalLX l₂ v ≡ OMG → evalLX (norm⊔ l₁ l₂) v ≡ OMG
evalLX-norm⊔-OMGʳ l₁ l₂ v eq₁ eq₂ = {!!}

evalLX-norm⊔-OMGˡ : {x₂ : Level} (l₁ l₂ : NLX n) (v : Vec Level n) → evalLX l₁ v ≡ OMG → evalLX l₂ v ≡ LEV x₂ → evalLX (norm⊔ l₁ l₂) v ≡ OMG
evalLX-norm⊔-OMGˡ l₁ l₂ v eq₁ eq₂ = {!!}

evalLX-norm⊔-OMG² : (l₁ l₂ : NLX n) (v : Vec Level n) → evalLX l₁ v ≡ OMG → evalLX l₂ v ≡ OMG → evalLX (norm⊔ l₁ l₂) v ≡ OMG
evalLX-norm⊔-OMG² l₁ l₂ v eq₁ eq₂ = {!!}

LEnv : ℕ → Set
LEnv n = List (NLV n)

variable Δ : LEnv n
variable l : NLV n
variable l₁ l₂ l′ : NLX n

data Type (n : ℕ) (Δ : LEnv n) : NLX n → Set where
  `_ : l ∈ Δ → Type n Δ (nlx l)
  _`⇒_ : Type n Δ l₁ → Type n Δ l₂ → Type n Δ (norm⊔ l₁ l₂)
  `∀ℓ_ : Type (ℕ.suc n) (map weakNLV Δ) l′ → Type n Δ (strongNLX l′)
  `∀α_,_ : (lev : NLV n) → Type n (lev ∷ Δ) l′ → Type n Δ (norm⊔ (norm-suc (nlx lev)) l′)

Env* : Vec Level n → LEnv n → Setω
Env* v Δ = ∀ {l} → l ∈ Δ → Set (evalNLV l v)

ext* : ∀ {lev : NLV n} {v : Vec Level n} → Set (evalNLV lev v) → Env* v Δ → Env* v (lev ∷ Δ)
ext* S η (here refl) = S
ext* S η (there x) = η x

T⟦_⟧ : (T : Type n Δ l′) → (v : Vec Level n) → Env* v Δ → L⟦ evalLX l′ v ⟧
T⟦ `_ {l = l} x ⟧ v η rewrite evalLX-LV v l = LEV (η x)
T⟦ _`⇒_ {l₁ = l₁}{l₂ = l₂} T₁ T₂ ⟧ v η
  with T⟦ T₁ ⟧ v η | T⟦ T₂ ⟧ v η | evalLX l₁ v in eq₁ | evalLX l₂ v in eq₂
... | S₁ | S₂ | LEV x₁ | LEV x₂
  rewrite eq₁ | eq₂ | evalLX-norm⊔ l₁ l₂ v eq₁ eq₂
  with LEV A₁ ← S₁ | LEV A₂ ← S₂ = LEV (A₁ → A₂)
... | S₁ | S₂ | LEV x₁ | OMG
  rewrite eq₁ | eq₂ | evalLX-norm⊔-OMGʳ l₁ l₂ v eq₁ eq₂
  with LEV A₁ ← S₁ | OMG A₂ ← S₂
  = OMG (A₁ → A₂)
... | S₁ | S₂ | OMG | LEV x₂
  rewrite eq₁ | eq₂ | evalLX-norm⊔-OMGˡ l₁ l₂ v eq₁ eq₂
  with OMG A₁ ← S₁ | LEV A₂ ← S₂
  = OMG (A₁ → A₂)
... | S₁ | S₂ | OMG | OMG
  rewrite eq₁ | eq₂ | evalLX-norm⊔-OMG² l₁ l₂ v eq₁ eq₂
  with OMG A₁ ← S₁ | OMG A₂ ← S₂
  = OMG (A₁ → A₂)
T⟦ `∀ℓ_ {l′ = l′} T ⟧ v η
  with evalLX (strongNLX l′) v in eq
... | LEV x = LEV (∀ (ℓ : Level) → getLEV (coe eq {!T⟦ T ⟧ (ℓ ∷ v) !}))
... | OMG = OMG (∀ (ℓ : Level) → {!!})
T⟦ `∀α_,_ {l′ = l′} lev T ⟧ v η
  with evalLX l′ v in eq′
... | LEV x
  rewrite evalLX-all v lev l′ eq′
  = LEV (∀ α → getLEV (coe eq′ (T⟦ T ⟧ v (ext*{v = v} α η))) )
... | OMG
  rewrite  evalLX-all-OMG v lev l′ eq′
  = OMG (∀ α → getOMG (coe eq′ (T⟦ T ⟧ v (ext*{v = v} α η))))
