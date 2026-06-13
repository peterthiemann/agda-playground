module Expressions where

open import Level using (Level) renaming (zero to lzero)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as ℕₚ
open import Data.Fin using (Fin) renaming (zero to fzero)
import Data.Fin.Properties as Finₚ
open import Data.Product using (_×_; Σ; _,_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Function using (_∘_)

open import Types

data Expr (n : ℕ) : Set where
  ε   : Expr n
  _·_ : Expr n → Expr n → Expr n
  var : Fin n → Expr n
  cst : ℕ → Expr n
  abs : Ty → Expr (suc n) → Expr n
  mab : NTy → Expr (suc n) → Expr n
  app : Expr n → Expr n → Expr n
  mtc : Expr zero → Expr n → Expr n → Expr n


_≟Expr_ : ∀ {n} → (e e′ : Expr n) → Dec (e ≡ e′)
ε ≟Expr ε = yes refl
(e₁ · e₂) ≟Expr (e₁′ · e₂′) with e₁ ≟Expr e₁′
... | no e₁≢e₁′ = no λ { refl → e₁≢e₁′ refl }
... | yes refl with e₂ ≟Expr e₂′
... | no e₂≢e₂′ = no λ { refl → e₂≢e₂′ refl }
... | yes refl = yes refl
var x ≟Expr var y with Finₚ._≟_ x y
... | no x≢y = no λ { refl → x≢y refl }
... | yes refl = yes refl
cst k ≟Expr cst l with ℕₚ._≟_ k l
... | no k≢l = no λ { refl → k≢l refl }
... | yes refl = yes refl
abs μ e ≟Expr abs μ′ e′ with μ ≟Ty μ′
... | no μ≢μ′ = no λ { refl → μ≢μ′ refl }
... | yes refl with e ≟Expr e′
... | no e≢e′ = no λ { refl → e≢e′ refl }
... | yes refl = yes refl
mab ημ e ≟Expr mab ημ′ e′ with ημ ≟NTy ημ′
... | no ημ≢ημ′ = no λ { refl → ημ≢ημ′ refl }
... | yes refl with e ≟Expr e′
... | no e≢e′ = no λ { refl → e≢e′ refl }
... | yes refl = yes refl
app e₁ e₂ ≟Expr app e₁′ e₂′ with e₁ ≟Expr e₁′
... | no e₁≢e₁′ = no λ { refl → e₁≢e₁′ refl }
... | yes refl with e₂ ≟Expr e₂′
... | no e₂≢e₂′ = no λ { refl → e₂≢e₂′ refl }
... | yes refl = yes refl
mtc e₁ e₂ e₃ ≟Expr mtc e₁′ e₂′ e₃′ with e₁ ≟Expr e₁′
... | no e₁≢e₁′ = no λ { refl → e₁≢e₁′ refl }
... | yes refl with e₂ ≟Expr e₂′
... | no e₂≢e₂′ = no λ { refl → e₂≢e₂′ refl }
... | yes refl with e₃ ≟Expr e₃′
... | no e₃≢e₃′ = no λ { refl → e₃≢e₃′ refl }
... | yes refl = yes refl
ε ≟Expr (_ · _) = no λ ()
ε ≟Expr var _ = no λ ()
ε ≟Expr cst _ = no λ ()
ε ≟Expr abs _ _ = no λ ()
ε ≟Expr mab _ _ = no λ ()
ε ≟Expr app _ _ = no λ ()
ε ≟Expr mtc _ _ _ = no λ ()
(_ · _) ≟Expr ε = no λ ()
(_ · _) ≟Expr var _ = no λ ()
(_ · _) ≟Expr cst _ = no λ ()
(_ · _) ≟Expr abs _ _ = no λ ()
(_ · _) ≟Expr mab _ _ = no λ ()
(_ · _) ≟Expr app _ _ = no λ ()
(_ · _) ≟Expr mtc _ _ _ = no λ ()
var _ ≟Expr ε = no λ ()
var _ ≟Expr (_ · _) = no λ ()
var _ ≟Expr cst _ = no λ ()
var _ ≟Expr abs _ _ = no λ ()
var _ ≟Expr mab _ _ = no λ ()
var _ ≟Expr app _ _ = no λ ()
var _ ≟Expr mtc _ _ _ = no λ ()
cst _ ≟Expr ε = no λ ()
cst _ ≟Expr (_ · _) = no λ ()
cst _ ≟Expr var _ = no λ ()
cst _ ≟Expr abs _ _ = no λ ()
cst _ ≟Expr mab _ _ = no λ ()
cst _ ≟Expr app _ _ = no λ ()
cst _ ≟Expr mtc _ _ _ = no λ ()
abs _ _ ≟Expr ε = no λ ()
abs _ _ ≟Expr (_ · _) = no λ ()
abs _ _ ≟Expr var _ = no λ ()
abs _ _ ≟Expr cst _ = no λ ()
abs _ _ ≟Expr mab _ _ = no λ ()
abs _ _ ≟Expr app _ _ = no λ ()
abs _ _ ≟Expr mtc _ _ _ = no λ ()
mab _ _ ≟Expr ε = no λ ()
mab _ _ ≟Expr (_ · _) = no λ ()
mab _ _ ≟Expr var _ = no λ ()
mab _ _ ≟Expr cst _ = no λ ()
mab _ _ ≟Expr abs _ _ = no λ ()
mab _ _ ≟Expr app _ _ = no λ ()
mab _ _ ≟Expr mtc _ _ _ = no λ ()
app _ _ ≟Expr ε = no λ ()
app _ _ ≟Expr (_ · _) = no λ ()
app _ _ ≟Expr var _ = no λ ()
app _ _ ≟Expr cst _ = no λ ()
app _ _ ≟Expr abs _ _ = no λ ()
app _ _ ≟Expr mab _ _ = no λ ()
app _ _ ≟Expr mtc _ _ _ = no λ ()
mtc _ _ _ ≟Expr ε = no λ ()
mtc _ _ _ ≟Expr (_ · _) = no λ ()
mtc _ _ _ ≟Expr var _ = no λ ()
mtc _ _ _ ≟Expr cst _ = no λ ()
mtc _ _ _ ≟Expr abs _ _ = no λ ()
mtc _ _ _ ≟Expr mab _ _ = no λ ()
mtc _ _ _ ≟Expr app _ _ = no λ ()

mapE : ∀ {m n} → (Expr m → Expr n) → Expr m → Expr n
mapE f ε = ε
mapE f (e₁ · e₂) = mapE f e₁ · mapE f e₂
mapE f (var x) = f (var x)
mapE f (cst x) = f (cst x)
mapE f (abs x e) = f (abs x e)
mapE f (mab x e) = f (mab x e)
mapE f (app e e₁) = f (app e e₁)
mapE f (mtc e₁ e₂ e₃) = f (mtc e₁ e₂ e₃)

lengthE : ∀ {n} → Expr n → ℕ
lengthE ε = 0
lengthE (e₁ · e₂) = lengthE e₁ +ℕ lengthE e₂
lengthE (var x) = 1
lengthE (cst x) = 1
lengthE (abs x e) = 1
lengthE (mab x e) = 1
lengthE (app e e₁) = 1
lengthE (mtc e e₁ e₂) = 1

NonEmpty : ∀ {n} → Expr n → Set
NonEmpty e = e ≡ ε → ⊥

NonConcat : ∀ {n} → Expr n → Set
NonConcat e = ∀ {e₁ e₂} → e ≡ (e₁ · e₂) → ⊥

Atomic : ∀ {n} → Expr n → Set
Atomic e = NonEmpty e × NonConcat e

monoidal-nf : Expr zero → Set
monoidal-nf ε = ⊤
monoidal-nf (e · e₁) = NonEmpty e × NonEmpty e₁ × NonConcat e × monoidal-nf e₁
monoidal-nf (cst x) = ⊤
monoidal-nf (abs x e) = ⊤
monoidal-nf (mab x e) = ⊤
monoidal-nf (app e e₁) = ⊤
monoidal-nf (mtc e e₁ e₂) = ⊤

data ALL (P : Expr zero → Set) : Expr zero → Set where
  Aε : ALL P ε
  _A·_ : ∀ {e₁}{e₂} → ALL P e₁ → ALL P e₂ → ALL P (e₁ · e₂)
  AP : ∀ {e}
    {e≢ε : e ≡ ε → ⊥}
    {e≢· : ∀ {e₁ e₂} → e ≡ (e₁ · e₂) → ⊥}
    → P e
    → ALL P e

mapALL : ∀ {e : Expr zero} {P Q : Pred (Expr zero) lzero} → (∀ {x} → P x → Q x) → ALL P e → ALL Q e
mapALL P⇒Q Aε = Aε
mapALL P⇒Q (ap A· ap₁) = (mapALL P⇒Q ap) A· (mapALL P⇒Q ap₁)
mapALL P⇒Q (AP {e≢ε = e≢ε} {e≢· = e≢·} x) = AP {e≢ε = e≢ε} {e≢· = e≢·} (P⇒Q x)

AP-cst : ∀ {P} {k} → P (cst k) → ALL P (cst k)
AP-cst p = AP {e≢ε = λ ()} {e≢· = λ ()} p

AP-abs : ∀ {P} {μ} {e*} → P (abs μ e*) → ALL P (abs μ e*)
AP-abs p = AP {e≢ε = λ ()} {e≢· = λ ()} p

AP-mab : ∀ {P} {ημ} {e*} → P (mab ημ e*) → ALL P (mab ημ e*)
AP-mab p = AP {e≢ε = λ ()} {e≢· = λ ()} p

foldALL : ∀ {n} {e : Expr zero} {P : Pred (Expr zero) lzero} → (∀ {x} → P x → Expr n) → ALL P e → Expr n
foldALL f Aε = ε
foldALL f (a A· a₁) = (foldALL f a) · (foldALL f a₁)
foldALL f (AP Pe) = f Pe

mapE-foldALL : ∀ {m n} {e : Expr zero} {P : Pred (Expr zero) lzero} → (g : ∀ {x} → P x → Expr n) → (f : Expr n → Expr m) → (f-map : ∀ {e} → mapE f e ≡ f e) →  (ap : ALL P e) → mapE f (foldALL g ap) ≡ foldALL (f ∘ g) ap
mapE-foldALL g f f-map Aε = refl
mapE-foldALL g f f-map (ap A· ap₁) = cong₂ _·_ (mapE-foldALL g f f-map ap) (mapE-foldALL g f f-map ap₁)
mapE-foldALL g f f-map (AP ap) = f-map
