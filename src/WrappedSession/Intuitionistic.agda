{-# OPTIONS --guardedness #-} {- required for IO -}
module WrappedSession.Intuitionistic where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Unit using (⊤; tt)

open import Function.Base using (case_of_)

open import WrappedSession.Experiment

Channel : Session → Set
Channel (select s₁ s₂) = (x : Bool) → case x of (λ{ true → Channel s₂ ; false → Channel s₁})
Channel (choice s₁ s₂) = Σ Bool (λ{ true → Channel s₂ ; false → Channel s₁})
Channel (send x s)     = T⟦ x ⟧ → Channel s
Channel (recv x s)     = T⟦ x ⟧ × Channel s
Channel end            = ⊤

