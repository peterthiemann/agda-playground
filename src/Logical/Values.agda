module Values where

open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Numeri
open import Types
open import Expressions

-- values

data Value : Expr zero → Set where
  vε  : Value ε
  _v·_ : ∀ {v}{w}
    → Value v
    → Value w
    → {v≢ε : v ≡ ε → ⊥}
    → {w≢ε : w ≡ ε → ⊥}
    → {v≢· : ∀ {e₁ e₂} → v ≡ (e₁ · e₂) → ⊥}
    → Value (v · w)
  cst : ∀ {k} → Value (cst k)
  abs : ∀ {μ}{e*} → Value (abs μ e*)
  mab : ∀ {ημ}{e*} → Value (mab ημ e*)

data SingletonValue : Ty → Expr zero → Set where
  sv-cst : ∀ {k μ} → □ <:ₜ μ → SingletonValue μ (cst k)
  sv-abs : ∀ {μ μ₀ ημ e*} → (μ₀ ⇒ ημ) <:ₜ μ → SingletonValue μ (abs μ₀ e*)
  sv-mab : ∀ {μ ημ ημ′ e*} → (ημ ⇛ ημ′) <:ₜ μ → SingletonValue μ (mab ημ e*)

data AbsValue : Expr zero → Set where
  v-abs : ∀ μ e* → AbsValue (abs μ e*)

data MabValue : Expr zero → Set where
  v-mab : ∀ ημ e* → MabValue (mab ημ e*)

AllSingleton : Ty → Expr zero → Set
AllSingleton μ e = ALL (SingletonValue μ) e

data SequenceValue : NTy → Expr zero → Set where
  seq-zero : ∀ {μ} → SequenceValue ⟨ `- , μ ⟩ ε
  seq-one : ∀ {μ e}
    → SingletonValue μ e
    → SequenceValue ⟨ `! , μ ⟩ e
  seq-opt-zero : ∀ {μ} → SequenceValue ⟨ `? , μ ⟩ ε
  seq-opt-one : ∀ {μ e}
    → SingletonValue μ e
    → SequenceValue ⟨ `? , μ ⟩ e
  seq-star : ∀ {μ e}
    → AllSingleton μ e
    → SequenceValue ⟨ `* , μ ⟩ e
  seq-plus : ∀ {μ e}
    → AllSingleton μ e
    → NonEmpty e
    → SequenceValue ⟨ `+ , μ ⟩ e

absbody : ∀{e : Expr zero} → AbsValue e → Expr (suc zero)
absbody (v-abs μ s) = s

mabbody : ∀{e : Expr zero} → MabValue e → Expr (suc zero)
mabbody (v-mab ημ s) = s

