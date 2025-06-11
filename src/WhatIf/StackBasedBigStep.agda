{-# OPTIONS --allow-unsolved-metas #-}
module StackBasedBigStep where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; map)
open import Data.List.Properties using (length-++; ++-identityʳ; ++-assoc)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Bool using (Bool; true; false) renaming (T to 𝕋)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _<_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (<ᵇ⇒<; +-suc; +-identityʳ; n≤1+n; m≤m+n) renaming (≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import Data.Fin using (Fin; zero; suc; fromℕ; fromℕ<; inject≤)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; proj₁ ; proj₂; Σ; ∃-syntax)
open import Function using (case_of_; const)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; dcong)

-- some Fin lemmas

inject≤-refl : ∀ {n} (i : Fin n) → inject≤ i ≤ℕ-refl ≡ i
inject≤-refl zero = refl
inject≤-refl (suc i) = cong suc (inject≤-refl i)

inject≤-trans : ∀ {n}{m}{o} (i : Fin n) {n≤m : n ≤ℕ m} {m≤o : m ≤ℕ o} → inject≤ (inject≤ i n≤m) m≤o ≡ inject≤ i (≤ℕ-trans n≤m m≤o)
inject≤-trans {n = suc n}{m = suc m}{o = suc o} zero = refl
inject≤-trans {n = suc n} {m = suc m} {o = suc o} (suc i) {s≤s n≤m} {s≤s m≤o} = cong suc (inject≤-trans i {n≤m} {m≤o})

fromℕ-inject≤ : ∀ {m}{n}{i} → (n≤m : n ≤ℕ m) → (i< : i < n) → fromℕ< (≤ℕ-trans i< n≤m) ≡ inject≤ (fromℕ< i<) n≤m
fromℕ-inject≤ {m} {suc n} {zero} (s≤s n≤m) (s≤s i<) = refl
fromℕ-inject≤ {m} {suc n} {suc i} (s≤s n≤m) (s≤s i<) = cong suc (fromℕ-inject≤ n≤m i<)

-- Nat lemmas

≡⇒≤ : ∀ {x y : ℕ} → x ≡ y → x ≤ℕ y
≡⇒≤ refl = ≤ℕ-refl

-- List lemmas

length-≤ : ∀ {a}{A : Set a} (xs ys : List A) → length xs ≤ℕ length (xs ++ ys)
length-≤ [] ys = z≤n
length-≤ (x ∷ xs) ys = s≤s (length-≤ xs ys)

lookup-++ : ∀ {a} {A : Set a} → (xs ys : List A) → (i : Fin (length xs))
  → lookup xs i ≡ lookup (xs ++ ys) (inject≤ i (≤ℕ-trans (m≤m+n (length xs) (length ys)) (≡⇒≤ (sym (length-++ xs)))))
lookup-++ (x ∷ xs) ys zero = refl
lookup-++ (x ∷ xs) ys (suc i) = lookup-++ xs ys i

length-< : ∀ {a} {A : Set a} → (y : A) (xs ys : List A) → length xs < length (xs ++ (y ∷ ys))
length-< y [] ys = s≤s z≤n
length-< y (x ∷ xs) ys = s≤s (length-< y xs ys)

lookup-last : ∀ {a} {A : Set a} → (y : A) (xs : List A) → lookup (xs ++ [ y ]) (fromℕ< (length-< y xs [])) ≡ y
lookup-last y [] = refl
lookup-last y (x ∷ xs) = lookup-last y xs

lookup-from-i : ∀ {a}{A : Set a} (xs : List A) {ys : List A} {i}
  → (i< : i < length xs)
  → lookup (xs ++ ys) (fromℕ< (≤ℕ-trans i< (length-≤ xs ys))) ≡ lookup xs (fromℕ< i<)
lookup-from-i (x ∷ xs) {i = zero} i< = refl
lookup-from-i (x ∷ xs) {i = suc i} (s≤s i<) = lookup-from-i xs i<

lookup-from-i′ : ∀ {a}{A : Set a} (xs : List A) {ys zs : List A} {i}
  → (i< : i < length xs)
  → (eq : xs ++ ys ≡ zs)
  → lookup zs (fromℕ< (≤ℕ-trans i< (subst (λ zs → length xs ≤ℕ length zs) eq (length-≤ xs ys)))) ≡ lookup xs (fromℕ< i<)
lookup-from-i′ xs i< refl = lookup-from-i xs i<


--

Ident = String
StackMap = Ident → Maybe ℕ

open import Qualifiers


-- well-formed types

data Type (q : Qual) : Set
record QType : Set where
  inductive
  constructor mkQ
  field
    q-of : Qual
    t-of : Type q-of
open QType public

data Type q where
  Unit : Type q
  Base : Type q
  Fun  : (S₁ : QType) → (S₂ : QType) → q-of S₁ ≤ q → q-of S₂ ≤ q → Type q
  Ref  : (S : QType) → q-of S ≤ q → Type q

syntax mkQ q t = t ^ q

-- variables

record Var : Set where
  inductive
  constructor X
  field
    ident : Ident
    q-var : Qual
open Var public

-- values
data Val : Set
data Local : Set where
  ∅ : Local
  ⟨_≔_,_⟩ : Ident → Val → Local → Local
Env = Local
Heap = List Val

data Expr : Set where
  cst    : ℕ → Expr
  unit   : Expr
  var    : Var → Expr
  lam    : Qual → Var → Expr → Qual → Expr
  app    : Expr → Expr → Expr
  seq    : Expr → Expr → Expr
  ref    : Qual → Expr → Expr
  deref  : Qual → Expr → Expr
  setref : Expr → Expr → Expr

data Val where
  unit : Val
  cst  : ℕ → Val
  clos : Qual → Env → Maybe StackMap → Var → Expr → Qual → Val
  ref  : Qual → ℕ → Val

↑expr : Val → Expr
↑expr unit = unit
↑expr (clos q 𝓔 σ? x e q₂) = lam q x e q₂
↑expr (cst x) = cst x
↑expr (ref q n) = ref q (cst n)


Stack : Set
Stack = List⁺ (List Val)


postulate
  _[_]≔_ : List Val → ℕ → Val → List Val
  

variable
  𝓔 𝓔′ : Env
  𝓗 𝓗′ 𝓗″ 𝓗‴ : Heap
  𝓢 𝓢′ 𝓢″ 𝓢‴ 𝓢₁ 𝓢₂ 𝓢₃ : Stack
  𝓛 : List (List Val)
  σ σ′ σ″ : StackMap
  σ? : Maybe StackMap
  𝓢σ : Stack × StackMap
  s s′ : Ident
  v v′ v″ v₁ v₂ : Val
  vs vs′ : List Val
  x x′ : Var
  e e₁ e₂ : Expr
  Φ Φ′ Φ″ : Local
  n ℓ : ℕ


-- typing

data Context : Set where

  ∅ : Context
  _,_⦂_[_] : (Γ : Context) → (x : Var) → (S : QType) → (q-of S ≡ q-var x) → Context

variable
  Γ Γ′ Γ″ Γ‴ : Context
  T T₁ T₂ : Type q
  S S′ S₁ S₂ S₃ S₄ : QType

data _∋_⦂_ : Context → Var → QType → Set where

  here   : ∀ {S≤x} → (Γ , x ⦂ S [ S≤x ]) ∋ x ⦂ S
  there  : ∀ {S≤x} → Γ ∋ x ⦂ S → x ≢ x′ → (Γ , x′ ⦂ S′ [ S≤x ]) ∋ x ⦂ S

q-var-type : Γ ∋ x ⦂ S → q-of S ≤ q-var x
q-var-type (here {S≤x = refl}) = ≤-refl -- S≤x
q-var-type (there x∈ x≢x′) = q-var-type x∈


-- lower bounds for qualifiers

q-val : Val → Qual
q-val unit = 𝟙
q-val (clos q _ _ _ _ _) = q
q-val (cst x) = 𝟙
q-val (ref q _) = q

q-env : Env → Qual
q-env ∅ = 𝟙
q-env ⟨ s ≔ v , 𝓔 ⟩ = q-val v ⊔ q-env 𝓔

-- q-bound : Context → Qual
-- q-bound ∅ = 𝟙
-- q-bound (Γ , _ ⦂ (_ ^ q) [ _ ]) = (q-bound Γ) ⊔ q

-- q-bounded : Qual → Context → Context
-- q-bounded q ∅ = ∅
-- q-bounded q (Γ , s ⦂ S [ S≤x ])
--   with q-of S ≤ᵇ q
-- ... | false = q-bounded q Γ
-- ... | true = q-bounded q Γ , s ⦂ S [ S≤x ]

-- 𝟚-bounded : (Γ : Context) → Γ ≡ q-bounded 𝟚 Γ
-- 𝟚-bounded ∅ = refl
-- 𝟚-bounded (Γ , s ⦂ S [ S≤x ])
--   rewrite ≤ᵇ-top {q-of S}
--   = cong (_, s ⦂ S [ S≤x ]) (𝟚-bounded Γ)

module _ (q : Qual) where

  data q-Bound : Context → Set where

    qb-∅ : q-Bound ∅

    qb-add : ∀ {S≤x} → q-of S ≤ q → q-Bound Γ → q-Bound (Γ , x ⦂ S [ S≤x ])

  data q-Bounded : Context → Context → Set where

    qb-∅ : q-Bounded ∅ ∅

    qb-keep : ∀ {S≤x} → q-of S ≤ q → q-Bounded Γ Γ′ → q-Bounded (Γ , x ⦂ S [ S≤x ]) (Γ′ , x ⦂ S [ S≤x ])

    qb-drop : ∀ {S≤x} → q-Bounded Γ Γ′ → (∀ {x′} {S′} → Γ′ ∋ x′ ⦂ S′ → x′ ≢ x)  → q-Bounded (Γ , x ⦂ S [ S≤x ]) (Γ′)

is-bounded : q-Bounded q Γ Γ′ → q-Bound q Γ′
is-bounded qb-∅ = qb-∅
is-bounded (qb-keep x qbdd) = qb-add x (is-bounded qbdd)
is-bounded (qb-drop qbdd _) = is-bounded qbdd

data _<⦂_ : QType → QType → Set where

  SUnit : q₁ ≤ q₂
    → (Unit ^ q₁) <⦂ (Unit ^ q₂)

  SBase : q₁ ≤ q₂
    → (Base ^ q₁) <⦂ (Base ^ q₂)

  SFun : ∀ {wf₁ wf₂ wf₃ wf₄}
    → q₁ ≤ q₂
    → S₃ <⦂ S₁
    → S₂ <⦂ S₄
    → (Fun S₁ S₂ wf₁ wf₂ ^ q₁) <⦂ (Fun S₃ S₄ wf₃ wf₄ ^ q₂)

  SRef :
    q₁ ≤ q₂
    → S₁ <⦂ S₂
    → S₂ <⦂ S₁
    → {wf₁ : q-of S₁ ≤ q₁}
    → {wf₂ : q-of S₂ ≤ q₂}
    → (Ref S₁ wf₁ ^ q₁) <⦂ (Ref S₂ wf₂ ^ q₂)


q-of-mono : S₁ <⦂ S₂ → q-of S₁ ≤ q-of S₂
q-of-mono (SUnit q1≤q2) = q1≤q2
q-of-mono (SBase q1≤q2) = q1≤q2
q-of-mono (SFun q1≤q2 S1<S2 S1<S3) = q1≤q2
q-of-mono (SRef q1≤q2 S1<S2 S2<S1) = q1≤q2

<⦂-refl : S <⦂ S
<⦂-refl {Unit ^ q} = SUnit ≤-refl
<⦂-refl {Base ^ q} = SBase ≤-refl
<⦂-refl {Fun S₁ S₂ wf₁ wf₂ ^ q} = SFun ≤-refl <⦂-refl <⦂-refl
<⦂-refl {Ref S x ^ q} = SRef ≤-refl <⦂-refl <⦂-refl

<⦂-trans : S₁ <⦂ S₂ → S₂ <⦂ S₃ → S₁ <⦂ S₃
<⦂-trans (SUnit x) (SUnit x₁) = SUnit (≤-trans x x₁)
<⦂-trans (SBase x) (SBase x₁) = SBase (≤-trans x x₁)
<⦂-trans (SFun x <⦂-arg₁ <⦂-res₁) (SFun x₁ <⦂-arg₂ <⦂-res₂) = SFun (≤-trans x x₁) (<⦂-trans <⦂-arg₂ <⦂-arg₁) (<⦂-trans <⦂-res₁ <⦂-res₂)
<⦂-trans (SRef x S₁<⦂S₂ S₂<⦂S₁) (SRef x₁ S₂<⦂S₃ S₃<⦂S₂) = SRef (≤-trans x x₁) (<⦂-trans S₁<⦂S₂ S₂<⦂S₃) (<⦂-trans S₃<⦂S₂ S₂<⦂S₁)


<⦂-antisym : S₁ <⦂ S₂ → S₂ <⦂ S₁ → S₁ ≡ S₂
<⦂-antisym (SUnit x) (SUnit x₁) = cong (λ q → _ ^ q) (≤-antisym x x₁)
<⦂-antisym (SBase x) (SBase x₁) = cong (λ q → _ ^ q) (≤-antisym x x₁)
<⦂-antisym (SFun q₁<q₂ S₁<⦂S₂ S₁<⦂S₃) (SFun q₂<q₁ S₂<⦂S₁ S₂<⦂S₂)
  with refl ← ≤-antisym q₁<q₂ q₂<q₁
  with refl ← <⦂-antisym S₂<⦂S₁ S₁<⦂S₂
  with refl ← <⦂-antisym S₁<⦂S₃ S₂<⦂S₂
  = cong (λ T → T ^ _) (cong₂ (Fun _ _) ≤-irrelevant ≤-irrelevant)
<⦂-antisym (SRef q₁<q₂ S₁<⦂S₂ _) (SRef q₂<q₁  S₂<⦂S₁ _)
  with refl ← ≤-antisym q₁<q₂ q₂<q₁
  with refl ← <⦂-antisym S₁<⦂S₂ S₂<⦂S₁
  = cong (λ T → T ^ _) (cong (Ref _) ≤-irrelevant)

subsume-aux : Type 𝟙 → Type 𝟚
subsume-aux Unit = Unit
subsume-aux Base = Base
subsume-aux (Fun S₁ S₂ wf₁ wf₂) = Fun S₁ S₂ ≤-top ≤-top
subsume-aux (Ref S wf) = Ref S ≤-top

subsume : (S : QType) → q-of S ≡ 𝟙 → QType
subsume (mkQ q T) refl = subsume-aux T ^ 𝟚

<⦂-subsume : (S : QType) → (q=𝟙 : q-of S ≡ 𝟙) → S <⦂ subsume S q=𝟙
<⦂-subsume (mkQ q Unit) refl = SUnit ≤-bottop
<⦂-subsume (mkQ q Base) refl = SBase ≤-bottop
<⦂-subsume (mkQ q (Fun S₁ S₂ ≤-refl ≤-refl)) refl = SFun ≤-bottop <⦂-refl <⦂-refl
<⦂-subsume (mkQ q (Ref S ≤-refl)) refl = SRef ≤-bottop <⦂-refl <⦂-refl

-- context subtyping

data _<<⦂_ : Context → Context → Set where
  ∅  : ∅ <<⦂ ∅
  _,⦂_ : ∀ {S≤x S′≤x} → Γ′ <<⦂ Γ → S′ <⦂ S → (Γ′ , x ⦂ S′ [ S′≤x ]) <<⦂ (Γ , x ⦂ S [ S≤x ])

<<⦂-refl : Γ <<⦂ Γ
<<⦂-refl {∅} = ∅
<<⦂-refl {Γ , s ⦂ S [ _ ]} = <<⦂-refl ,⦂ <⦂-refl

-- typing

data _⊢_⦂_ : Context → Expr → QType → Set where

  TUnit : Γ ⊢ unit ⦂ (Unit ^ q)

  TVar : Γ ∋ x ⦂ S
    →    Γ ⊢ var x ⦂ S

  TAbs : ∀ {S≤x}
    → (Γ′ , x ⦂ S₁ [ S≤x ]) ⊢ e ⦂ S₂
    → q-Bounded q Γ Γ′
    → let q₁ = q-of S₁ ; q₂ = q-of S₂
    in q-var x ≡ q-of S₁
    → {wf₁ : q₁ ≤ q}
    → {wf₂ : q₂ ≤ q}
    → Γ ⊢ lam q x e q₂ ⦂ ((Fun S₁ S₂ wf₁ wf₂) ^ q)

  TApp : ∀ {wf₁ wf₂}
    → Γ ⊢ e₁ ⦂ (Fun S₁ S₂ wf₁ wf₂ ^ 𝟚)
    → Γ ⊢ e₂ ⦂ S₁
    → Γ ⊢ app e₁ e₂ ⦂ S₂

  TSub : Γ ⊢ e ⦂ S
    → S <⦂ S′
    → Γ ⊢ e ⦂ S′

  TSeq : q₁ ≤ q₂
    → Γ ⊢ e₁ ⦂ (Unit ^ q₁)
    → Γ ⊢ e₂ ⦂ S
    → q₁ ≤ q-of S
    → Γ ⊢ seq e₁ e₂ ⦂ S

  TRef :
    Γ′ ⊢ e ⦂ S
    → q-Bounded q Γ Γ′
    → {wf : q-of S ≤ q}
    → Γ ⊢ ref q e ⦂ (Ref S wf ^ q)

  TDeref : {wf : q-of S ≤ q}
    → Γ ⊢ e ⦂ (Ref S wf ^ q)
    → Γ ⊢ deref q e ⦂ S

  TSetref : {wf : q-of S ≤ q}
    → Γ ⊢ e₁ ⦂ (Ref S wf ^ q)
    → Γ ⊢ e₂ ⦂ S
    → Γ ⊢ setref e₁ e₂ ⦂ (Unit ^ q)

-- typing is closed under context subtyping

q-Bounded-<<⦂ : Γ′ <<⦂ Γ → q-Bounded q Γ Γ″ → ∃[ Γ‴ ] Γ‴ <<⦂ Γ″ × q-Bounded q Γ′ Γ‴
q-Bounded-<<⦂ ∅ qb-∅ = ∅ , ∅ , qb-∅
q-Bounded-<<⦂ (Γ′<<⦂Γ ,⦂ S′<⦂S) (qb-keep qS≤ qbdd)
  with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
... | Γ‴ , Γ‴<<⦂Γ″ , qbdd-out = (Γ‴ , _ ⦂ _ [ _ ]) , (Γ‴<<⦂Γ″ ,⦂ S′<⦂S) , qb-keep (≤-trans (q-of-mono S′<⦂S) qS≤) qbdd-out
q-Bounded-<<⦂ (Γ′<<⦂Γ ,⦂ S′<⦂S) (qb-drop qbdd f)
  with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
... | Γ‴ , Γ‴<<⦂Γ″ , qbdd-out =  Γ‴ , Γ‴<<⦂Γ″ , qb-drop qbdd-out {!!}

context-sub-variable : Γ ∋ x ⦂ S → Γ′ <<⦂ Γ → ∃[ S′ ] S′ <⦂ S × Γ′ ∋ x ⦂ S′
context-sub-variable here (_ ,⦂ S′<⦂S) = _ , S′<⦂S , here
context-sub-variable (there x∈ x≢) (Γ′<<⦂Γ ,⦂ _)
  with context-sub-variable x∈ Γ′<<⦂Γ
... | S′ , S′<⦂S , x∈′ = S′ , S′<⦂S , there x∈′ x≢

context-subtyping : Γ ⊢ e ⦂ S → Γ′ <<⦂ Γ → Γ′ ⊢ e ⦂ S
context-subtyping TUnit Γ′<<⦂Γ = TUnit
context-subtyping (TVar x∈) Γ′<<⦂Γ
  with context-sub-variable x∈ Γ′<<⦂Γ
... | S′ , S′<⦂S , x∈′ = TSub (TVar x∈′) S′<⦂S
context-subtyping {Γ = Γ}{Γ′ = Γ′} (TAbs {S≤x = S≤x} ⊢e qbdd eq) Γ′<<⦂Γ
  with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
... | _ , Γ‴<<⦂Γ′ , qbdd-out
  = TAbs {S≤x = S≤x} (context-subtyping ⊢e (Γ‴<<⦂Γ′ ,⦂ <⦂-refl)) qbdd-out eq
context-subtyping (TApp ⊢e ⊢e₁) Γ′<<⦂Γ = TApp (context-subtyping ⊢e Γ′<<⦂Γ) (context-subtyping ⊢e₁ Γ′<<⦂Γ)
context-subtyping (TSub ⊢e x) Γ′<<⦂Γ = TSub (context-subtyping ⊢e Γ′<<⦂Γ) x
context-subtyping (TSeq x ⊢e ⊢e₁ x₁) Γ′<<⦂Γ = TSeq x (context-subtyping ⊢e Γ′<<⦂Γ) (context-subtyping ⊢e₁ Γ′<<⦂Γ) x₁
context-subtyping (TRef ⊢e qbdd) Γ′<<⦂Γ
  with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
... | _ , Γ‴<<⦂Γ′ , qbdd-out = TRef (context-subtyping ⊢e Γ‴<<⦂Γ′) qbdd-out 
context-subtyping (TDeref ⊢e) Γ′<<⦂Γ = TDeref (context-subtyping ⊢e Γ′<<⦂Γ)
context-subtyping (TSetref ⊢e ⊢e₁) Γ′<<⦂Γ = TSetref (context-subtyping ⊢e Γ′<<⦂Γ) (context-subtyping ⊢e₁ Γ′<<⦂Γ)


-- heap & stack typing

_↓_ : Stack → Maybe ℕ → Maybe Val
(xs ∷ _) ↓ just n
  with n <ᵇ length xs in eq
... | false = nothing
... | true = just (lookup xs (fromℕ< (<ᵇ⇒< n (length xs) (subst 𝕋 (sym eq) tt))))
(xs ∷ _) ↓ nothing = nothing

-- (H,∅)(x 1) = v
data Access : Env → String → Val → Set where

  here   : Access ⟨ s ≔ v , 𝓔 ⟩ s v
  there  : Access 𝓔 s v → s′ ≢ s → Access ⟨ s′ ≔ v′ , 𝓔 ⟩ s v

data GenAccess : Env → Stack → StackMap → Var → Val → Set where

  on-heap   : Access 𝓔 s v → GenAccess 𝓔 𝓢 σ (X s 𝟙) v
  on-stack  : just v ≡ 𝓢 ↓ σ s → GenAccess 𝓔 𝓢 σ (X s 𝟚) v

-- heap and stack types

HSType = (q : Qual) → List (Type q)

variable
  Σₕₛ Σₕₛ′ Σₕₛ″ : HSType

extend-Σ : HSType → (q : Qual) → Type q → HSType
extend-Σ Σₕₛ 𝟙 T 𝟙 = Σₕₛ 𝟙 ++ [ T ]
extend-Σ Σₕₛ 𝟙 T 𝟚 = Σₕₛ 𝟚
extend-Σ Σₕₛ 𝟚 T 𝟙 = Σₕₛ 𝟙
extend-Σ Σₕₛ 𝟚 T 𝟚 = Σₕₛ 𝟚 ++ [ T ]

adjust-stack : HSType → List (Type 𝟚) → HSType
adjust-stack Σₕₛ Σₛ 𝟙 = Σₕₛ 𝟙
adjust-stack Σₕₛ Σₛ 𝟚 = Σₛ

_≼_ : HSType → HSType → Set
Σₕₛ ≼ Σₕₛ′ = ∀ q → ∃[ qts ] Σₕₛ q ++ qts ≡  Σₕₛ′ q

≼-refl : Σₕₛ ≼ Σₕₛ
≼-refl {Σₕₛ} q = [] , ++-identityʳ (Σₕₛ q)

≼-trans : Σₕₛ ≼ Σₕₛ′ →  Σₕₛ′ ≼ Σₕₛ″ →  Σₕₛ ≼ Σₕₛ″
≼-trans { Σₕₛ} Σ≼ Σ≼″ q
  with Σ≼ q | Σ≼″ q
... | qts1 , eq1 | qts2 , eq2
  rewrite sym eq2 = (qts1 ++ qts2) , trans (sym (++-assoc (Σₕₛ q) qts1 qts2)) (cong (_++ qts2) eq1)

≼-extend-Σ : ∀ q₁ S₁ → Σₕₛ ≼ extend-Σ Σₕₛ q₁ S₁
≼-extend-Σ 𝟙 S₁ 𝟙 = [ S₁ ] , refl
≼-extend-Σ 𝟙 S₁ 𝟚 = [] , (++-identityʳ _)
≼-extend-Σ 𝟚 S₁ 𝟙 = [] , (++-identityʳ _)
≼-extend-Σ 𝟚 S₁ 𝟚 = [ S₁ ] , refl

≼⇒length : Σₕₛ ≼ Σₕₛ′ → ∀ q → length (Σₕₛ q) ≤ℕ length (Σₕₛ′ q)
≼⇒length {Σₕₛ} Σ≼ q
  with Σ≼ q
... | qts , eq
  with length-≤ (Σₕₛ q) qts
... | r
  rewrite eq
  = r

≼-lookup-aux : ∀ {a}{A : Set a} (xs ys zs : List A)
  → (eq : xs ++ ys ≡ zs)
  → (i : Fin (length xs))
  → lookup (xs ++ ys) (inject≤ i (length-≤ xs ys)) ≡ lookup zs (inject≤ i (subst (λ xx → length xs ≤ℕ length xx) eq (length-≤ xs ys)))
≼-lookup-aux xs ys zs refl i = refl

≼-lookup : (Σ≼ : Σₕₛ ≼ Σₕₛ′) → ∀ q → (i : Fin (length (Σₕₛ q))) → lookup (Σₕₛ q) i ≡ lookup (Σₕₛ′ q) (inject≤ i (≼⇒length Σ≼ q))
≼-lookup {Σₕₛ = Σₕₛ}{Σₕₛ′} Σ≼ q i
  using qts , eq ← Σ≼ q
  = trans (lookup-++ (Σₕₛ q) qts i) (≼-lookup-aux (Σₕₛ q) qts (Σₕₛ′ q) eq i)

data ⟨_⟩⊢[_⦂_] (Σₕₛ : HSType) : Val → QType → Set

record ⟨_,_⟩⊨_/_ (Σₕₛ : HSType) (Γ : Context) (𝓔 : Env) (𝓢σ : Stack × StackMap) : Set where
  inductive
  constructor mk-⊨
  field
    ⊨-heap : ∀ {s}{T}{v} → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) →  Access 𝓔 s v → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
    ⊨-stack : let 𝓢 , σ = 𝓢σ in ∀ {s}{q}{T}{v} → Γ ∋ X s 𝟚 ⦂ (T ^ q) → just v ≡ (𝓢 ↓ σ s) → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ q) ]
open ⟨_,_⟩⊨_/_ public

-- value typing

resolve : Qual → StackMap → Maybe StackMap
resolve 𝟙 σ = nothing
resolve 𝟚 σ = just σ

data ⟨_⟩⊢[_⦂_] Σₕₛ where {- cf. p 15:11 of WhatIf -}

  TVUnit : ⟨ Σₕₛ ⟩⊢[ unit ⦂ (Unit ^ q) ]

  TVCst : ⟨ Σₕₛ ⟩⊢[ cst n ⦂ (Base ^ q) ]

  TVClos : ∀ {S₁≤x}
    → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / (𝓢 , σ)
    → q-Bound q Γ
    → (Γ , x ⦂ S₁ [ S₁≤x ]) ⊢ e ⦂ S₂
    → σ? ≡ resolve q σ
    → let q₂ = q-of S₂ in
      let q₁ = q-of S₁ in
      (wf₁ : q₁ ≤ q)
    → (wf₂ : q₂ ≤ q)
    → (Fun S₁ S₂ wf₁ wf₂ ^ q) <⦂ S
    → ⟨ Σₕₛ ⟩⊢[ clos q 𝓔 σ? x e q₂′ ⦂ S ]

  TVRef :
    (ℓ< : ℓ < length (Σₕₛ q))
    → lookup (Σₕₛ q) (fromℕ< ℓ<) ≡ T
    → (Ref (T ^ q) ≤-refl ^ q) <⦂ S
    → ⟨ Σₕₛ ⟩⊢[ ref q ℓ ⦂ S ]

-- heap typing
⊢ᵥ-adjust : ∀ { vs : List Val} {Σₛ : List (Type 𝟚)}
  → Pointwise (λ v T → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]) vs Σₛ
  → (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ])
  → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ]
⊨-adjust :  ∀ { vs : List Val}{Σₛ : List (Type 𝟚)}
  → Pointwise (λ v T → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]) vs Σₛ
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / (𝓢 , σ)
  → ⟨ adjust-stack Σₕₛ Σₛ , Γ ⟩⊨ 𝓔 / (vs ∷⁺ 𝓢 , const nothing)

-- stack adjustment does not happen for a stack-allocated closure
-- in this case, the caller's stack is carried over to the callee

⊢ᵥ-adjust ⊢ₛvs TVUnit = TVUnit
⊢ᵥ-adjust ⊢ₛvs TVCst = TVCst
⊢ᵥ-adjust ⊢ₛvs (TVClos {q = 𝟙} ⊨𝓔 qbd ⊢e σ?≡ wf₁ wf₂ <⦂S) = TVClos (⊨-adjust ⊢ₛvs ⊨𝓔) qbd ⊢e σ?≡ wf₁ wf₂ <⦂S
⊢ᵥ-adjust ⊢ₛvs (TVClos {q = 𝟚} ⊨𝓔 qbd ⊢e σ?≡ wf₁ wf₂ (SFun () <⦂S <⦂S₁))
⊢ᵥ-adjust ⊢ₛvs (TVRef ℓ< lkup≡ (SRef ≤-refl x₂ x₃)) = TVRef ℓ< lkup≡ (SRef ≤-refl x₂ x₃)

⊨-adjust ⊢ₛvs ⊨𝓔 = mk-⊨ (λ x∈ acc → ⊢ᵥ-adjust ⊢ₛvs (⊨-heap ⊨𝓔 x∈ acc))
                        (λ{ x∈ () })


_⊢ₕ_ : HSType → Heap → Set
Σₕₛ ⊢ₕ 𝓗 = Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙)]) 𝓗 (Σₕₛ 𝟙)

⊢ₕₛ-length-aux : ∀ {q}{Σₕ : List (Type q)} {vs : List Val} → Pointwise (λ x y → ⟨ Σₕₛ ⟩⊢[ x ⦂ (y ^ q) ]) vs Σₕ → length Σₕ ≡ length vs
⊢ₕₛ-length-aux [] = refl
⊢ₕₛ-length-aux (x∼y ∷ pws) = cong suc (⊢ₕₛ-length-aux pws)

⊢ₕ-length : Σₕₛ ⊢ₕ 𝓗 → length (Σₕₛ 𝟙) ≡ length 𝓗
⊢ₕ-length ⊢𝓗 = ⊢ₕₛ-length-aux ⊢𝓗

⊢ₕ-adjust-aux : ∀ {Σₕ}{vs vs′ : List Val}
  → (Σₛ : List (Type 𝟚))
  → Pointwise (λ v T → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]) vs′ Σₛ
  → Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙)]) vs Σₕ
  → Pointwise (λ v T → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙)]) vs Σₕ
⊢ₕ-adjust-aux Σₛ ⊢ₛvs [] = []
⊢ₕ-adjust-aux Σₛ ⊢ₛvs (x∼y ∷ pws) = ⊢ᵥ-adjust ⊢ₛvs x∼y ∷ ⊢ₕ-adjust-aux Σₛ ⊢ₛvs pws

⊢ₕ-adjust : ∀ {vs : List Val} (Σₛ : List (Type 𝟚))
  → Pointwise (λ v T → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]) vs Σₛ
  → Σₕₛ ⊢ₕ 𝓗
  → adjust-stack Σₕₛ Σₛ ⊢ₕ 𝓗
⊢ₕ-adjust Σₛ ⊢ₛvs ⊢𝓗 = ⊢ₕ-adjust-aux Σₛ ⊢ₛvs ⊢𝓗

-- stack typing

_⊢ₛ_ : HSType → Stack → Set
Σₕₛ ⊢ₛ 𝓢 = Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟚)]) (𝓢 .head) (Σₕₛ 𝟚)

⊢ₛ-length : Σₕₛ ⊢ₛ 𝓢 → length (Σₕₛ 𝟚) ≡ length (𝓢 .head)
⊢ₛ-length ⊢𝓢 = ⊢ₕₛ-length-aux ⊢𝓢

-- value typing extends

⊨-extend-Σ : Σₕₛ ≼ Σₕₛ′ → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢σ → ⟨ Σₕₛ′ , Γ ⟩⊨ 𝓔 / 𝓢σ

[⦂]-≼ : Σₕₛ ≼ Σₕₛ′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ] → ⟨ Σₕₛ′ ⟩⊢[ v ⦂ S ]
[⦂]-≼ Σ≼ TVUnit = TVUnit
[⦂]-≼ Σ≼ TVCst = TVCst
[⦂]-≼ Σ≼ (TVClos ⊨𝓔 qbd ⊢e σ?≡ wf₁ wf₂ <⦂S) = TVClos (⊨-extend-Σ Σ≼ ⊨𝓔) qbd ⊢e σ?≡ wf₁ wf₂ <⦂S
[⦂]-≼ {Σₕₛ = Σₕₛ} Σ≼ (TVRef {q = q} ℓ< lkup≡ <⦂S)
  with Σ≼ q in eq
... | qts , eq1 = TVRef (≤ℕ-trans ℓ< (≼⇒length Σ≼ q)) (trans (lookup-from-i′ (Σₕₛ q) ℓ< eq1) lkup≡) <⦂S

-- agreement extends


⊨-extend-Σ Σ≼ ⊨Γ = mk-⊨ (λ x∈ acc → [⦂]-≼ Σ≼ (⊨-heap ⊨Γ x∈ acc))
                        (λ x∈ v≡ → [⦂]-≼ Σ≼ (⊨-stack ⊨Γ x∈ v≡))


-- heap typing extends (needed?)

⊢ₕ-≼-aux : Σₕₛ ≼ Σₕₛ′ → ∀ {Σₕ} → Pointwise (⟨_⟩⊢[_⦂_] Σₕₛ) 𝓗 Σₕ → Pointwise (⟨_⟩⊢[_⦂_] Σₕₛ′) 𝓗 Σₕ
⊢ₕ-≼-aux Σ≼ [] = []
⊢ₕ-≼-aux Σ≼ (x∼y ∷ pws) = ([⦂]-≼ Σ≼ x∼y) ∷ (⊢ₕ-≼-aux Σ≼ pws)

{-
⊢ₕ-≼ : Σₕₛ ≼ Σₕₛ′ → Σₕₛ ⊢ₕ 𝓗 → Σₕₛ′ ⊢ₕ 𝓗
⊢ₕ-≼ {Σₕₛ} Σ≼ ⊢𝓗 = {!⊢ₕ-≼-aux Σ≼ {Σₕₛ 𝟙} ⊢𝓗!}
-}

-- -- typing relations

-- _≲_ : Stack → Stack → Set
-- 𝓢₁ ≲ 𝓢₂ =
--   let l1 = length (𝓢₁ .head)
--       l2 = length (𝓢₂ .head)
--   in  Σ (l1 ≤ℕ l2) λ l1≤l2 → ∀ (i : Fin l1) → ∀ S → [ lookup (𝓢₁ .head) i ⦂ S ] → [ lookup (𝓢₂ .head) (inject≤ i l1≤l2) ⦂ S ]

-- ≲-refl : 𝓢 ≲ 𝓢
-- ≲-refl .proj₁ = ≤ℕ-refl
-- ≲-refl .proj₂ i S lkup rewrite inject≤-refl i = lkup

-- ≲-trans : {𝓢₁ 𝓢₂ 𝓢₃ : Stack} → 𝓢₁ ≲ 𝓢₂ → 𝓢₂ ≲ 𝓢₃ → 𝓢₁ ≲ 𝓢₃
-- ≲-trans (l1≤l2 , cond12) (l2≤l3 , cond23) .proj₁ = ≤ℕ-trans l1≤l2 l2≤l3
-- ≲-trans {𝓢₃ = 𝓢₃} (l1≤l2 , cond12) (l2≤l3 , cond23) .proj₂ =
--   λ i S lkup → let lkup₁ = cond12 i S lkup in subst (λ □ → [ lookup (𝓢₃ .head) □ ⦂ S ]) (inject≤-trans i {l1≤l2} {l2≤l3}) (cond23 (inject≤ i l1≤l2) S lkup₁)


rename-bounded′ : q-Bounded q Γ Γ′ → Γ′ ∋ x ⦂ S → Γ ∋ x ⦂ S
rename-bounded′ (qb-keep x qbdd) (here) = here
rename-bounded′ (qb-keep x qbdd) (there x∈ x≢) = there (rename-bounded′ qbdd x∈) x≢
rename-bounded′ (qb-drop qbdd f) x∈ = there (rename-bounded′ qbdd x∈) (f x∈)

restrict′ : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢σ → q-Bounded q Γ Γ′ → ⟨ Σₕₛ , Γ′ ⟩⊨ 𝓔 / 𝓢σ
restrict′ {𝓢σ = 𝓢 , σ} Γ⊨ qbdd = mk-⊨ (λ x∈ access → ⊨-heap Γ⊨ (rename-bounded′ qbdd x∈) access)
                                      (λ x∈ v≡ → ⊨-stack Γ⊨ (rename-bounded′ qbdd x∈) v≡)


⊨-extend-𝟙 : ∀ s T → (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙)]) → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢σ → ⟨ Σₕₛ , (Γ , X s 𝟙 ⦂ (T ^ 𝟙) [ refl ]) ⟩⊨ ⟨ s ≔ v , 𝓔 ⟩ / 𝓢σ
⊨-extend-𝟙 s T ⊢v ⊨Γ = mk-⊨ (λ{ here here → ⊢v
                              ; here (there x∈ x≢x) → ⊥-elim (x≢x refl)
                              ; (there x∈ x≢x) here → ⊥-elim (x≢x refl)
                              ; (there x∈ x≢) (there access s≢) → ⊨-heap ⊨Γ x∈ access})
                            λ{ (there x∈ x≢) v≡ → ⊨-stack ⊨Γ x∈ v≡}

{-
rename-bounded : Γ′ ≡ q-bounded q Γ → Γ′ ∋ x ⦂ S → Γ ∋ x ⦂ S
rename-bounded {q = q} {Γ = ∅} {S = S} refl ()
rename-bounded {q = q} {Γ = Γ , s ⦂ S₁ [ S₁≤x ]} {S = S} Γ′≡ x∈
  with q-of S₁ ≤ᵇ q
... | false = there (rename-bounded Γ′≡ x∈) {!!}
rename-bounded {q = q} {Γ , s ⦂ S₁ [ S₁≤x ]} {S = S} refl (here) | true = here
rename-bounded {q = q} {Γ , s ⦂ S₁ [ S₁≤x ]} {S = S} refl (there x∈ x≢) | true = there (rename-bounded refl x∈) x≢

restrict : Γ ⊨ 𝓔 / 𝓢σ → Γ′ ≡ q-bounded q Γ → Γ′ ⊨ 𝓔 / 𝓢σ
restrict {𝓢σ = 𝓢 , σ} Γ⊨ refl = record { ⊨-heap = λ x∈ access → ⊨-heap Γ⊨ (rename-bounded refl x∈) access
                                       ; ⊨-stack = λ x∈ v≡ → ⊨-stack Γ⊨ (rename-bounded refl x∈) v≡ }
-}

access-soundness : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢σ → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) → Access 𝓔 s v → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
access-soundness Γ⊨ x∈ access = ⊨-heap Γ⊨ x∈ access

genaccess-soundness : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / (𝓢 , σ) → Γ ∋ x ⦂ (T ^ q) → GenAccess 𝓔 𝓢 σ x v → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ q) ]
genaccess-soundness {𝓢 = 𝓢} {σ} {q = 𝟙} Γ⊨ x∈ (on-heap x) = access-soundness Γ⊨ x∈ x
genaccess-soundness {𝓢 = 𝓢} {σ} {q = 𝟚} Γ⊨ x∈ (on-heap x) = ⊥-elim (¬2≤1 (q-var-type x∈))
genaccess-soundness Γ⊨ x∈ (on-stack x) = ⊨-stack Γ⊨ x∈ x

{-
q-bounded-idem : Γ′ ≡ q-bounded q Γ → Γ′ ≡ q-bounded q Γ′
q-bounded-idem {q = q} {∅} refl = refl
q-bounded-idem {q = q} {Γ , s ⦂ S [ S≤x ]} eq
  with q-of S ≤ᵇ q in eq1
... | false = q-bounded-idem {Γ = Γ} eq
q-bounded-idem {q = q} {Γ , s ⦂ S [ S≤x ]} refl | true
  with q-of S ≤ᵇ q
... | true = cong (_, s ⦂ S [ S≤x ]) (q-bounded-idem{Γ = Γ} refl)
... | false
  with eq1
... | ()
-}

<⦂-val-lift : ⟨ Σₕₛ ⟩⊢[ v ⦂ S₁ ] → S₁ <⦂ S₂ → ⟨ Σₕₛ ⟩⊢[ v ⦂ S₂ ]
<⦂-val-lift TVUnit (SUnit x) = TVUnit
<⦂-val-lift TVCst (SBase x) = TVCst
<⦂-val-lift (TVClos ⊨𝓔 qbd ⊢e σ?≡ wf₁ wf₂ <⦂S₁) S₁<⦂S₂ = TVClos ⊨𝓔 qbd ⊢e σ?≡ wf₁ wf₂ (<⦂-trans <⦂S₁ S₁<⦂S₂)
<⦂-val-lift (TVRef ℓ< lkup≡ <⦂S₁) S₁<⦂S₂ = TVRef ℓ< lkup≡ (<⦂-trans <⦂S₁ S₁<⦂S₂)


-- operational semantics

data read : List Val → ℕ → Val → Set where

  read0 : read (v ∷ vs) zero v
  read1 : read vs n v → read (v′ ∷ vs) (suc n) v

data sread : Stack → ℕ → Val → Set where

  sread0 : read vs ℓ v → sread (vs ∷ 𝓛) ℓ v

data write : List Val → ℕ → Val → List Val → Set where

  write0 : write (v′ ∷ vs) zero v (v ∷ vs)
  write1 : write vs n v vs′ → write (v′ ∷ vs) (suc n) v (v′ ∷ vs′)

data swrite : Stack → ℕ → Val → Stack → Set where

  -- swrite0 : write vs ℓ v vs′ → swrite (vs ∷ 𝓛) ℓ v (vs′ ∷ 𝓛)
  swrite0 : write (𝓢 .head) ℓ v vs′ → swrite 𝓢 ℓ v (vs′ ∷ 𝓢 .tail)

typed-read-aux : ∀ {q}{T : Type q}{Σₕ : List (Type q)}
  → Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ q) ] ) 𝓗 Σₕ
  → {ℓ : ℕ}
  → (ℓ< : ℓ < length Σₕ)
  → (lkup≡ : lookup Σₕ (fromℕ< ℓ<) ≡ T)
  → read 𝓗 ℓ v
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ q) ]
typed-read-aux (x∼y ∷ pws) {zero} ℓ< refl read0 = x∼y
typed-read-aux (x∼y ∷ pws) {suc ℓ} (s≤s ℓ<) lkup≡ (read1 rd) = typed-read-aux pws {ℓ} ℓ< lkup≡ rd

typed-read : Σₕₛ ⊢ₕ 𝓗
  → (ℓ< : ℓ < length (Σₕₛ 𝟙))
  → (lkup≡ : lookup (Σₕₛ 𝟙) (fromℕ< ℓ<) ≡ T)
  → read 𝓗 ℓ v
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
typed-read {Σₕₛ = Σₕₛ} ⊢𝓗 ℓ< lkup≡ xread = typed-read-aux {Σₕ = Σₕₛ 𝟙}  ⊢𝓗 ℓ< lkup≡ xread 

typed-sread : Σₕₛ ⊢ₛ 𝓢
  → (ℓ< : ℓ < length (Σₕₛ 𝟚))
  → (lkup≡ : lookup (Σₕₛ 𝟚) (fromℕ< ℓ<) ≡ T)
  → sread 𝓢 ℓ v
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]
typed-sread {Σₕₛ = Σₕₛ} ⊢𝓢 ℓ< lkup≡ (sread0 xread) = typed-read-aux {Σₕ = Σₕₛ 𝟚} ⊢𝓢 ℓ< lkup≡ xread

typed-write-aux : ∀ {q}{T : Type q}{Σₕ}
  → Pointwise (λ w T → ⟨ Σₕₛ ⟩⊢[ w ⦂ (T ^ q) ] ) 𝓗 Σₕ
  → {ℓ : ℕ}
  → (ℓ< : ℓ < length Σₕ)
  → (lkup≡ : lookup Σₕ (fromℕ< ℓ<) ≡ T)
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ q) ]
  → write 𝓗 ℓ v 𝓗′
  → Pointwise (λ w T → ⟨ Σₕₛ ⟩⊢[ w ⦂ (T ^ q) ] ) 𝓗′ Σₕ
typed-write-aux (x∼y ∷ pws) {zero} ℓ< refl ⊢v write0 = ⊢v ∷ pws
typed-write-aux (x∼y ∷ pws) {suc ℓ} (s≤s ℓ<) lkup≡ ⊢v (write1 xwrite) = x∼y ∷ (typed-write-aux pws ℓ< lkup≡ ⊢v xwrite)

typed-write : ∀ {T : Type 𝟙}
  → Σₕₛ ⊢ₕ 𝓗
  → (ℓ< : ℓ < length (Σₕₛ 𝟙))
  → (lkup≡ : lookup (Σₕₛ 𝟙) (fromℕ< ℓ<) ≡ T)
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
  → write 𝓗 ℓ v 𝓗′
  → Σₕₛ ⊢ₕ 𝓗′
typed-write {Σₕₛ = Σₕₛ} ⊢𝓗 ℓ< lkup≡ ⊢v xwrite = typed-write-aux {Σₕ = Σₕₛ 𝟙} ⊢𝓗 ℓ< lkup≡ ⊢v xwrite

typed-swrite : ∀ {T : Type 𝟚}
  → Σₕₛ ⊢ₛ 𝓢
  → (ℓ< : ℓ < length (Σₕₛ 𝟚))
  → (lkup≡ : lookup (Σₕₛ 𝟚) (fromℕ< ℓ<) ≡ T)
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]
  → swrite 𝓢 ℓ v 𝓢′
  → Σₕₛ ⊢ₛ 𝓢′
typed-swrite {Σₕₛ = Σₕₛ} ⊢𝓢 ℓ< lkup≡ ⊢v (swrite0 xwrite) = typed-write-aux {Σₕ = Σₕₛ 𝟚} ⊢𝓢 ℓ< lkup≡ ⊢v xwrite

⊢𝓗-extend-𝟙-aux : ∀ {Σₕ} → (T : Type 𝟙) (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ])
  → (⊢𝓗    : Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ T ^ 𝟙 ]) 𝓗 Σₕ)
  → Pointwise (λ v T′ → ⟨ (extend-Σ Σₕₛ 𝟙 T) ⟩⊢[ v ⦂ (T′ ^ 𝟙)] ) (𝓗 ++ v ∷ []) (Σₕ ++ [ T ])
⊢𝓗-extend-𝟙-aux T ⊢v [] = [⦂]-≼ (≼-extend-Σ 𝟙 T) ⊢v ∷ []
⊢𝓗-extend-𝟙-aux T ⊢v (x∼y ∷ ⊢𝓗) = [⦂]-≼ (≼-extend-Σ 𝟙 T) x∼y ∷ (⊢𝓗-extend-𝟙-aux T ⊢v ⊢𝓗)

⊢𝓗-extend-𝟙 : (T : Type 𝟙) (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ]) (⊢𝓗 : Σₕₛ ⊢ₕ 𝓗)
  → Pointwise (λ v T′ → ⟨ (extend-Σ Σₕₛ 𝟙 T) ⟩⊢[ v ⦂ (T′ ^ 𝟙)] ) (𝓗 ++ v ∷ []) (Σₕₛ 𝟙 ++ [ T ])
⊢𝓗-extend-𝟙 T ⊢v ⊢𝓗 = ⊢𝓗-extend-𝟙-aux T ⊢v ⊢𝓗

⊢𝓢-extend-𝟙-aux : ∀ {Σₛ} {xs : List Val} → (T : Type 𝟙)
  → (⊢𝓢 : Pointwise (λ v T′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T′ ^ 𝟚) ]) xs Σₛ)
  → Pointwise (λ v T′ → ⟨ (extend-Σ Σₕₛ 𝟙 T) ⟩⊢[ v ⦂ (T′ ^ 𝟚) ]) xs Σₛ
⊢𝓢-extend-𝟙-aux T [] = []
⊢𝓢-extend-𝟙-aux T (x∼y ∷ ⊢𝓢) = ([⦂]-≼ (≼-extend-Σ 𝟙 T) x∼y) ∷ (⊢𝓢-extend-𝟙-aux T ⊢𝓢)

⊢𝓢-extend-𝟙 : (T : Type 𝟙) → (⊢𝓢 : Σₕₛ ⊢ₛ 𝓢) → extend-Σ Σₕₛ 𝟙 T ⊢ₛ 𝓢
⊢𝓢-extend-𝟙 T ⊢𝓢 = ⊢𝓢-extend-𝟙-aux T ⊢𝓢

⊢𝓗-extend-𝟚-aux : ∀ {Σₛ} {xs : List Val} → (T : Type 𝟚)
  → Pointwise (λ v T′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T′ ^ 𝟙)]) xs Σₛ
  → Pointwise (λ v T′ → ⟨ (extend-Σ Σₕₛ 𝟚 T) ⟩⊢[ v ⦂ (T′ ^ 𝟙)] ) xs Σₛ
⊢𝓗-extend-𝟚-aux S [] = []
⊢𝓗-extend-𝟚-aux S (x∼y ∷ pws) = ([⦂]-≼ (≼-extend-Σ 𝟚 S) x∼y) ∷ ⊢𝓗-extend-𝟚-aux S pws

⊢𝓗-extend-𝟚 : (T : Type 𝟚) → (⊢𝓗 : Σₕₛ ⊢ₕ 𝓗) → extend-Σ Σₕₛ 𝟚 T ⊢ₕ 𝓗
⊢𝓗-extend-𝟚 T ⊢𝓗 = ⊢𝓗-extend-𝟚-aux T ⊢𝓗

⊢𝓢-extend-𝟚-aux : ∀ {Σₛ} {xs : List Val} → (S : Type 𝟚) (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ (S ^ 𝟚) ])
  → (⊢𝓢 : Pointwise (λ v S′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ (S′ ^ 𝟚)]) xs Σₛ)
  → Pointwise (λ v S′ → ⟨ (extend-Σ Σₕₛ 𝟚 S) ⟩⊢[ v ⦂ (S′ ^ 𝟚)] ) (xs ++ [ v ]) (Σₛ ++ [ S ])
⊢𝓢-extend-𝟚-aux S ⊢v [] = [⦂]-≼ (≼-extend-Σ 𝟚 S) ⊢v ∷ []
⊢𝓢-extend-𝟚-aux S ⊢v (x∼y ∷ pws) = ([⦂]-≼ (≼-extend-Σ 𝟚 S) x∼y) ∷ ⊢𝓢-extend-𝟚-aux S ⊢v pws

⊢𝓢-extend-𝟚 : (S : Type 𝟚) (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ (S ^ 𝟚) ]) (⊢𝓢 : Σₕₛ ⊢ₛ 𝓢)
  → Pointwise (λ v S′ → ⟨ (extend-Σ Σₕₛ 𝟚 S) ⟩⊢[ v ⦂ (S′ ^ 𝟚)]) (𝓢 .head ++ [ v ]) (Σₕₛ 𝟚 ++ [ S ])
⊢𝓢-extend-𝟚 S ⊢v ⊢𝓢 = ⊢𝓢-extend-𝟚-aux S ⊢v ⊢𝓢

-- -- UNSAFE --
-- postulate
--   ≲-write : swrite 𝓢 n v 𝓢′ → 𝓢 ≲ 𝓢′

∣_∣ʰ = length

∣_∣ˢ : Stack → ℕ
∣ (vs ∷ _) ∣ˢ = length vs

update : StackMap → Ident → ℕ → StackMap
update σ x n = λ s → case (x ≟ s) of λ where
  (no ¬a) → σ s
  (yes a) → just n

_⊕ₕ_ : Env → (Var × Val) → Env
𝓔 ⊕ₕ (X s 𝟙 , v) = ⟨ s ≔ v , 𝓔 ⟩
𝓔 ⊕ₕ (X s 𝟚 , v) = 𝓔

_⊕ₛ_ : (Stack × StackMap) → (Var × Val) → (Stack × StackMap)
(𝓢 , σ) ⊕ₛ (X s 𝟙 , v) = (𝓢 , σ)
((vs ∷ 𝓛) , σ) ⊕ₛ (X s 𝟚 , v) = (vs ++ [ v ]) ∷ 𝓛 , update σ s (length vs)

alloc : Stack → Val → Stack × ℕ
alloc (vs ∷ 𝓛) v = (vs ++ [ v ]) ∷ 𝓛 , length vs

alloc-length : ∀ 𝓢 → length (alloc 𝓢 v .proj₁ .head) ≡ suc (length (𝓢 .head))
alloc-length {v = v} 𝓢 = trans (length-++ (𝓢 .head) {[ v ]}) (trans (+-suc (length (𝓢 .head)) zero) (cong suc (+-identityʳ (length (𝓢 .head)))))

-- ≲-alloc : 𝓢 ≲ alloc 𝓢 v .proj₁
-- ≲-alloc {𝓢}{v} .proj₁ rewrite alloc-length {v} 𝓢 = n≤1+n _
-- ≲-alloc {𝓢}{v} .proj₂ i S lkup = subst (λ □ → [ □ ⦂ S ]) (lookup-++ (𝓢 .head) [ v ] i) lkup

push-𝟙 : (Stack × StackMap) → Maybe StackMap → (Stack × StackMap)
push-𝟙 (𝓢 , _) (just σ) = 𝓢 , σ
push-𝟙 (𝓢 , _) nothing = ([] ∷⁺ 𝓢) , const nothing

push-𝟚 : (Stack × StackMap) → Maybe StackMap → (Stack × StackMap)
push-𝟚 (𝓢 , _) (just σ) = 𝓢 , σ
push-𝟚 (𝓢 , _) nothing  = 𝓢 , const nothing

-- H,S ⊢ c ⇓q s c ⊣ S
data _,_,_⊢_⇓[_]_⊣_,_
  : Env → Heap → Stack × StackMap → Expr → Qual → Val → Heap → Stack → Set
  where

  EUnit  :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ unit ⇓[ q ] unit ⊣ 𝓗 , 𝓢

  EVarH :
        Access 𝓔 s v
       → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ var (X s 𝟙) ⇓[ 𝟙 ] v ⊣ 𝓗 , 𝓢

  EVarS :
        GenAccess 𝓔 𝓢 σ x v
       → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ var x ⇓[ 𝟚 ] v ⊣ 𝓗 , 𝓢

  EAbsH :
       𝓔 , 𝓗 , (𝓢 , σ) ⊢ lam 𝟙 x e 𝟙 ⇓[ 𝟙 ] clos 𝟙 𝓔 nothing x e 𝟙 ⊣ 𝓗 , 𝓢

  EAbsS :
       𝓔 , 𝓗 , (𝓢 , σ) ⊢ lam q x e q₂ ⇓[ 𝟚 ] clos q 𝓔 (resolve q σ) x e q₂ ⊣ 𝓗 , 𝓢
  
  EAppH :
         𝓔 , 𝓗  , (𝓢  , σ) ⊢ e₁ ⇓[ 𝟚  ] clos q 𝓔′ σ? (X s q₂) e 𝟙 ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q₂ ] v₂ ⊣ 𝓗″ , 𝓢″
       → (𝓔′ ⊕ₕ (X s q₂ , v₂)) , 𝓗″ , push-𝟙 (𝓢″ , σ) σ? ⊕ₛ (X s q₂ , v₂) ⊢ e ⇓[ 𝟙 ] v ⊣ 𝓗‴ , 𝓢‴
       → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ app e₁ e₂ ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢
       
  EAppS :
         𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟚 ] clos q 𝓔′ σ? (X s q₁) e q₂ ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q₁ ] v₂ ⊣ 𝓗″ , 𝓢″
       → (𝓔′ ⊕ₕ (X s q₁ , v₂)) , 𝓗″ , push-𝟚 (𝓢″ , σ) σ? ⊕ₛ (X s q₁ , v₂) ⊢ e ⇓[ q₂ ] v ⊣ 𝓗‴ , 𝓢‴
        ---------------------------------------------------------
       → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ app e₁ e₂ ⇓[ 𝟚 ] v ⊣ 𝓗‴ , 𝓢‴

  ERefH :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢′
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ ref 𝟙 e ⇓[ 𝟙 ] ref 𝟙 ∣ 𝓗′ ∣ʰ ⊣ 𝓗′ ++ [ v ] , 𝓢′


  ERefS :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
      → (q ≡ 𝟙 → 𝓢″ ≡ 𝓢′ × n ≡ ∣ 𝓗′ ∣ʰ × 𝓗″ ≡ 𝓗′ ++ [ v ])
      → (q ≡ 𝟚 → 𝓗″ ≡ 𝓗′ × (𝓢″ , n) ≡ alloc 𝓢′ v)
        --------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ ref q e ⇓[ 𝟚 ] ref q n ⊣ 𝓗″ , 𝓢″

  EDerefH :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ 𝟙 ] ref 𝟙 ℓ ⊣ 𝓗′ , 𝓢′
      → read 𝓗′ ℓ v
        ----------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ deref 𝟙 e ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢′

  EDerefS :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ 𝟚 ] ref q ℓ ⊣ 𝓗′ , 𝓢′
      → (q ≡ 𝟙 → read 𝓗′ ℓ v)
      → (q ≡ 𝟚 → sread 𝓢′ ℓ v)
        -------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ deref 𝟚 e ⇓[ 𝟚 ] v ⊣ 𝓗′ , 𝓢′

  ESetrefH :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟙 ] ref 𝟙 ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ 𝟙 ] v ⊣ 𝓗″ , 𝓢″
      → write 𝓗″ ℓ v 𝓗‴
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ setref e₁ e₂ ⇓[ 𝟙 ] unit ⊣ 𝓗‴ , 𝓢″

  ESetrefS :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟚 ] ref q ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q ] v ⊣ 𝓗″ , 𝓢″
      → (q ≡ 𝟙 → write 𝓗″ ℓ v 𝓗‴ × 𝓢‴ ≡ 𝓢″)
      → (q ≡ 𝟚 → 𝓗‴ ≡ 𝓗″ × swrite 𝓢″ ℓ v 𝓢‴)
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ setref e₁ e₂ ⇓[ 𝟚 ] unit ⊣ 𝓗‴ , 𝓢‴

  ESeq :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟚 ] v₁ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ seq e₁ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
