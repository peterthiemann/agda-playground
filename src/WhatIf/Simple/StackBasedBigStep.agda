-- {-# OPTIONS --allow-unsolved-metas #-}
module Simple.StackBasedBigStep where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; map; take)
open import Data.List.Properties using (length-++; ++-identityʳ; ++-assoc)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Bool using (Bool; true; false) renaming (T to 𝕋)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _<_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (<ᵇ⇒<; +-suc; +-identityʳ; n≤1+n; m≤m+n) renaming (≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import Data.Fin using (Fin; zero; suc; fromℕ; fromℕ<; inject≤)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; proj₁ ; proj₂; Σ; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; const; _∘_)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; dcong)

{-
** The problem

If we pass stack arguments to a heap closure, then we need to ensure that the
callers' stack does not get corrupted. Corruption can only happen in the presence of
references.

As an example, suppose we pass a stack reference r which contains another stack reference.
That is r : ref 2 (ref 2 Int). On the local stack, we allocate a new reference as in
x = ref 2 (42)
and overwrite the content of r with it
r := x
Now the callers' stack contains a reference to the current stackframe, which becomes
invalid after return from the heap closure (as this return pops the stack).

** Design alternatives

1. Disallow passing stack references to heap closures.
   A well-formedness constraint on function types can help: if the function is heap, then its arguments and results must be heap, too.

2. If we pass a stack reference to a heap function, then it should not be written to.
   To this end, we might introduce a type of read-only references as a supertype of read-write references such that ref 2 T <: roref 2 T' where T' is a read-only supertype of T.
   Writing to a stack reference could happen indirectly via a stack closure, so we'd have to have a simple effect that all writeable references are on the heap.

   (on the other hand, references to primitive type are ok as we cannot introduce backpointers through this avenue.)

** Here we choose option 1.

-}

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
Address = ℕ

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

x≢⇒s≢ : ∀ {s s′ : Ident}{q : Qual} → X s q ≢ X s′ q → s ≢ s′
x≢⇒s≢ xneq refl = xneq refl

-- values


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

data Val : Set
data Local : Set where
  ∅ : Local
  ⟨_≔_,_⟩ : Ident → Val → Local → Local
  ⟨_⇒_,_⟩ : Ident → Address → Local → Local
Env = Local
Heap = List Val

record Stack : Set where
  inductive
  constructor mkS
  field
    vars : List Val
    refs : List Val
open Stack public


data Val where

  unit : Val
  cst  : ℕ → Val
  clos : (q : Qual) → (𝓔 : Env) → (𝓢 : Stack)  → Var → Expr → Qual → Val
  ref  : (q : Qual) → (ℓ : ℕ) → Val

data _∋_⇒_ : Env → Var → Address → Set where

  here  : ∀ {𝓔}{s}{i} → ⟨ s ⇒ i , 𝓔 ⟩ ∋ X s 𝟚 ⇒ i
  there : ∀ {𝓔}{x}{i}{s}{j} → 𝓔 ∋ x ⇒ i → ⟨ s ⇒ j , 𝓔 ⟩ ∋ x ⇒ i
  skip  : ∀ {𝓔}{x}{i}{s}{v} → 𝓔 ∋ x ⇒ i → ⟨ s ≔ v , 𝓔 ⟩ ∋ x ⇒ i



variable
  𝓔 𝓔′ : Env
  𝓗 𝓗′ 𝓗″ 𝓗‴ : Heap
  𝓢 𝓢′ 𝓢″ 𝓢‴ 𝓢⁗ 𝓢₁ 𝓢₂ 𝓢₃ 𝓢ᶜ : Stack
  𝓛 : List (List Val)
  -- σ σ′ σ″ : StackMap
  -- σ? : Maybe StackMap
  -- 𝓢σ : Stack × StackMap
  s s′ : Ident
  v v′ v″ v₀ v₁ v₂ : Val
  vs vs′ : List Val
  x x′ : Var
  e e₁ e₂ e′ : Expr
  Φ Φ′ Φ″ : Local
  n ℓ : ℕ

-- push an argument on the stack

push : Stack → Val → Stack
push (mkS vars refs) v = mkS (vars ++ [ v ]) refs

-- allocate a reference on the stack

push-refs : Stack → List Val → Stack
push-refs (mkS vv rr) vs = mkS vv (rr ++ vs)

salloc : Stack → Val → Stack × ℕ
salloc (mkS vars₁ refs₁) v = (mkS vars₁ (refs₁ ++ [ v ])) , (length refs₁)


_≼ₛ_ : Stack → Stack → Set
𝓢₁ ≼ₛ 𝓢₂ = (∃[ vs ] 𝓢₁ .vars ++ vs ≡ 𝓢₂ .vars) × length (𝓢₁ .refs) ≤ℕ length (𝓢₂ .refs)

≼ₛ-bot : (𝓢 : Stack) → mkS [] [] ≼ₛ 𝓢
≼ₛ-bot 𝓢 = (𝓢 .vars , refl) , z≤n

≼ₛ-refl : 𝓢 ≼ₛ 𝓢
≼ₛ-refl = ([] , (++-identityʳ _)) , ≤ℕ-refl

≼ₛ-trans : 𝓢₁ ≼ₛ 𝓢₂ → 𝓢₂ ≼ₛ 𝓢₃ → 𝓢₁ ≼ₛ 𝓢₃
≼ₛ-trans ((vs , refl) , ≤-12) ((vs₁ , refl) , ≤-23) = ((vs ++ vs₁) , (sym (++-assoc _ vs vs₁))) , ≤ℕ-trans ≤-12 ≤-23

≼ₛ-push : 𝓢 ≼ₛ push 𝓢 v
≼ₛ-push {𝓢 = 𝓢}{v = v} = ([ v ] , refl) , ≤ℕ-refl

≼ₛ-salloc : 𝓢 ≼ₛ salloc 𝓢 v .proj₁
≼ₛ-salloc {𝓢 = 𝓢} = ([] , (++-identityʳ _)) , ≤ℕ-trans (m≤m+n _ 1) (≡⇒≤ (sym (length-++ (𝓢 .refs))))

≼ₛ-extend : ∀ vs → 𝓢 ≼ₛ mkS (𝓢 .vars) (𝓢 .refs ++ vs)
≼ₛ-extend {𝓢} vs = ([] , ++-identityʳ _) , (≤ℕ-trans (m≤m+n _ (length vs)) (≡⇒≤ (sym (length-++ (𝓢 .refs)))))

-- typing

data Context : Set where

  ∅ : Context
  _,_⦂_[_] : (Γ : Context) → (x : Var) → (S : QType) → (q-of S ≡ q-var x) → Context

variable
  Γ Γ′ Γ″ Γ‴ : Context
  T T₁ T₂ : Type q
  S S′ S₀ S₁ S₂ S₃ S₄ : QType

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
q-env ⟨ s ⇒ _ , 𝓔 ⟩ = q-env 𝓔

{-
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
-}

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


𝟙-bound⇒∀𝟚∉ : q-Bound 𝟙 Γ → (∀ s S → ¬ (Γ ∋ X s 𝟚 ⦂ S))
𝟙-bound⇒∀𝟚∉ qb-∅ s S ()
𝟙-bound⇒∀𝟚∉ (qb-add {S≤x = ()} ≤-refl qbd) s S here
𝟙-bound⇒∀𝟚∉ (qb-add x qbd) s S (there x∈ x₁) = 𝟙-bound⇒∀𝟚∉ qbd s S x∈


data _<⦂′_ {q₁ q₂ : Qual} {qsub : q₁ ≤ q₂} : Type q₁ → Type q₂ → Set

data _<⦂_ : QType → QType → Set where

  SQual : (qsub : q₁ ≤ q₂)
    → _<⦂′_ {qsub = qsub} T₁  T₂
    → (T₁ ^ q₁) <⦂ (T₂ ^ q₂)

data _<⦂′_ {q₁ q₂ qsub} where

  SUnit : Unit <⦂′ Unit

  SBase : Base <⦂′ Base

  SFun : ∀ {wf₁ wf₂ wf₃ wf₄}
    → S₃ <⦂ S₁
    → S₂ <⦂ S₄
    → Fun S₁ S₂ wf₁ wf₂ <⦂′ Fun S₃ S₄ wf₃ wf₄

  SRef : ∀ {wf₁ wf₂}
    → S₁ <⦂ S₂
    → S₂ <⦂ S₁
    → Ref S₁ wf₁ <⦂′ Ref S₂ wf₂

q-of-mono : S₁ <⦂ S₂ → q-of S₁ ≤ q-of S₂
q-of-mono (SQual q1≤q2 _) = q1≤q2


<⦂-refl : S <⦂ S
<⦂′-refl : ∀ {T : Type q} → _<⦂′_ {qsub = ≤-refl} T  T

<⦂-refl {mkQ q T} = SQual ≤-refl <⦂′-refl

<⦂′-refl {T = Unit} = SUnit
<⦂′-refl {T = Base} = SBase
<⦂′-refl {T = Fun S₁ S₂ wf₁ wf₂} = SFun <⦂-refl <⦂-refl
<⦂′-refl {T = Ref S x} = SRef <⦂-refl <⦂-refl

<⦂-trans : S₁ <⦂ S₂ → S₂ <⦂ S₃ → S₁ <⦂ S₃
<⦂′-trans : ∀ {T₁ : Type q₁}{T₂ : Type q₂}{T₃ : Type q₃}{qsub₁ : q₁ ≤ q₂}{qsub₂ : q₂ ≤ q₃}
  → _<⦂′_ {qsub = qsub₁} T₁ T₂ → _<⦂′_ {qsub = qsub₂} T₂ T₃ → _<⦂′_ {qsub = ≤-trans qsub₁ qsub₂} T₁ T₃

<⦂-trans (SQual qsub T₁<⦂T₂) (SQual qsub₁ T₂<⦂T₃) = SQual (≤-trans qsub qsub₁) (<⦂′-trans T₁<⦂T₂ T₂<⦂T₃)

<⦂′-trans (SUnit) (SUnit) = SUnit
<⦂′-trans (SBase) (SBase) = SBase
<⦂′-trans (SFun <⦂-arg₁ <⦂-res₁) (SFun <⦂-arg₂ <⦂-res₂) = SFun (<⦂-trans <⦂-arg₂ <⦂-arg₁) (<⦂-trans <⦂-res₁ <⦂-res₂)
<⦂′-trans (SRef S₁<⦂S₂ S₂<⦂S₁) (SRef S₂<⦂S₃ S₃<⦂S₂) = SRef (<⦂-trans S₁<⦂S₂ S₂<⦂S₃) (<⦂-trans S₃<⦂S₂ S₂<⦂S₁)

<⦂-antisym : S₁ <⦂ S₂ → S₂ <⦂ S₁ → S₁ ≡ S₂
<⦂′-antisym : ∀ {T₁ T₂ : Type q} → _<⦂′_ {qsub = ≤-refl} T₁ T₂ → _<⦂′_ {qsub = ≤-refl} T₂ T₁ → T₁ ≡ T₂

<⦂-antisym (SQual qsub T₁<⦂T₂) (SQual qsub₁ T₂<⦂T₁)
  with ≤-antisym qsub qsub₁
<⦂-antisym (SQual ≤-refl T₁<⦂T₂) (SQual ≤-refl T₂<⦂T₁) | refl
  = cong (mkQ _) (<⦂′-antisym T₁<⦂T₂ T₂<⦂T₁)

<⦂′-antisym (SUnit) (SUnit) = refl
<⦂′-antisym (SBase) (SBase) = refl
<⦂′-antisym (SFun S₁<⦂S₂ S₁<⦂S₃) (SFun S₂<⦂S₁ S₂<⦂S₂)
  with refl ← <⦂-antisym S₂<⦂S₁ S₁<⦂S₂
  with refl ← <⦂-antisym S₁<⦂S₃ S₂<⦂S₂
  = cong₂ (Fun _ _) ≤-irrelevant ≤-irrelevant
<⦂′-antisym (SRef S₁<⦂S₂ _) (SRef  S₂<⦂S₁ _)
  with refl ← <⦂-antisym S₁<⦂S₂ S₂<⦂S₁
  = cong (Ref _) ≤-irrelevant


-- data _<⦂_ : QType → QType → Set where

--   SUnit : q₁ ≤ q₂
--     → (Unit ^ q₁) <⦂ (Unit ^ q₂)

--   SBase : q₁ ≤ q₂
--     → (Base ^ q₁) <⦂ (Base ^ q₂)

--   SFun : ∀ {wf₂ wf₄}
--     → q₁ ≤ q₂
--     → S₃ <⦂ S₁
--     → S₂ <⦂ S₄
--     → (Fun S₁ S₂ wf₂ ^ q₁) <⦂ (Fun S₃ S₄ wf₄ ^ q₂)

--   SRef :
--     q₁ ≤ q₂
--     → S₁ <⦂ S₂
--     → S₂ <⦂ S₁
--     → {wf₁ : q-of S₁ ≤ q₁}
--     → {wf₂ : q-of S₂ ≤ q₂}
--     → (Ref S₁ wf₁ ^ q₁) <⦂ (Ref S₂ wf₂ ^ q₂)


-- q-of-mono : S₁ <⦂ S₂ → q-of S₁ ≤ q-of S₂
-- q-of-mono (SUnit q1≤q2) = q1≤q2
-- q-of-mono (SBase q1≤q2) = q1≤q2
-- q-of-mono (SFun q1≤q2 S1<S2 S1<S3) = q1≤q2
-- q-of-mono (SRef q1≤q2 S1<S2 S2<S1) = q1≤q2

-- <⦂-refl : S <⦂ S
-- <⦂-refl {Unit ^ q} = SUnit ≤-refl
-- <⦂-refl {Base ^ q} = SBase ≤-refl
-- <⦂-refl {Fun S₁ S₂ wf₂ ^ q} = SFun ≤-refl <⦂-refl <⦂-refl
-- <⦂-refl {Ref S x ^ q} = SRef ≤-refl <⦂-refl <⦂-refl

-- <⦂-trans : S₁ <⦂ S₂ → S₂ <⦂ S₃ → S₁ <⦂ S₃
-- <⦂-trans (SUnit x) (SUnit x₁) = SUnit (≤-trans x x₁)
-- <⦂-trans (SBase x) (SBase x₁) = SBase (≤-trans x x₁)
-- <⦂-trans (SFun x <⦂-arg₁ <⦂-res₁) (SFun x₁ <⦂-arg₂ <⦂-res₂) = SFun (≤-trans x x₁) (<⦂-trans <⦂-arg₂ <⦂-arg₁) (<⦂-trans <⦂-res₁ <⦂-res₂)
-- <⦂-trans (SRef x S₁<⦂S₂ S₂<⦂S₁) (SRef x₁ S₂<⦂S₃ S₃<⦂S₂) = SRef (≤-trans x x₁) (<⦂-trans S₁<⦂S₂ S₂<⦂S₃) (<⦂-trans S₃<⦂S₂ S₂<⦂S₁)


-- <⦂-antisym : S₁ <⦂ S₂ → S₂ <⦂ S₁ → S₁ ≡ S₂
-- <⦂-antisym (SUnit x) (SUnit x₁) = cong (λ q → _ ^ q) (≤-antisym x x₁)
-- <⦂-antisym (SBase x) (SBase x₁) = cong (λ q → _ ^ q) (≤-antisym x x₁)
-- <⦂-antisym (SFun q₁<q₂ S₁<⦂S₂ S₁<⦂S₃) (SFun q₂<q₁ S₂<⦂S₁ S₂<⦂S₂)
--   with refl ← ≤-antisym q₁<q₂ q₂<q₁
--   with refl ← <⦂-antisym S₂<⦂S₁ S₁<⦂S₂
--   with refl ← <⦂-antisym S₁<⦂S₃ S₂<⦂S₂
--   = cong (mkQ _) (cong (Fun _ _) ≤-irrelevant)
-- <⦂-antisym (SRef q₁<q₂ S₁<⦂S₂ _) (SRef q₂<q₁  S₂<⦂S₁ _)
--   with refl ← ≤-antisym q₁<q₂ q₂<q₁
--   with refl ← <⦂-antisym S₁<⦂S₂ S₂<⦂S₁
--   = cong (λ T → T ^ _) (cong (Ref _) ≤-irrelevant)

-- subsume-type : Type 𝟙 → Type 𝟚
-- subsume-type Unit = Unit
-- subsume-type Base = Base
-- subsume-type (Fun S₁ S₂ wf₁ wf₂) = Fun S₁ S₂ ≤-top ≤-top
-- subsume-type (Ref S wf) = Ref S ≤-top

-- subsume : (S : QType) → q-of S ≡ 𝟙 → QType
-- subsume (mkQ q T) refl = subsume-type T ^ 𝟚

-- <⦂-subsume : (S : QType) → (q=𝟙 : q-of S ≡ 𝟙) → S <⦂ subsume S q=𝟙
-- <⦂-subsume (mkQ q Unit) refl = SUnit ≤-bottop
-- <⦂-subsume (mkQ q Base) refl = SBase ≤-bottop
-- <⦂-subsume (mkQ q (Fun S₁ S₂ ≤-refl)) refl = SFun ≤-bottop <⦂-refl <⦂-refl
-- <⦂-subsume (mkQ q (Ref S ≤-refl)) refl = SRef ≤-bottop <⦂-refl <⦂-refl

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
    → let q₁ = q-of S₁; q₂ = q-of S₂
    in {wf₁ : q₁ ≤ q}
    → {wf₂ : q₂ ≤ q}
    → Γ ⊢ lam q x e q₂ ⦂ ((Fun S₁ S₂ wf₁ wf₂) ^ q)

  TApp : ∀ {wf₁ wf₂}
    → Γ ⊢ e₁ ⦂ (Fun S₁ S₂ wf₁ wf₂ ^ 𝟚)
    → Γ ⊢ e₂ ⦂ S₁
    → Γ ⊢ app e₁ e₂ ⦂ S₂

  TSub : Γ ⊢ e ⦂ S
    → S <⦂ S′
    → Γ ⊢ e ⦂ S′

  TSeq :
    Γ ⊢ e₁ ⦂ (Unit ^ 𝟚)
    → Γ ⊢ e₂ ⦂ S
    → Γ ⊢ seq e₁ e₂ ⦂ S

  TRef : {wf : q-of S ≤ q}
    → Γ ⊢ e ⦂ S
    → Γ ⊢ ref q e ⦂ (Ref S wf ^ q)

  TDeref : {wf : q-of S ≤ q}
    → Γ ⊢ e ⦂ (Ref S wf ^ q)
    → Γ ⊢ deref q e ⦂ S

  TSetref : {wf : q-of S ≤ q}
    → Γ ⊢ e₁ ⦂ (Ref S wf ^ q)
    → Γ ⊢ e₂ ⦂ S
    → Γ ⊢ setref e₁ e₂ ⦂ (Unit ^ 𝟚)

-- typing is closed under context subtyping

-- q-Bounded-<<⦂ : Γ′ <<⦂ Γ → q-Bounded q Γ Γ″ → ∃[ Γ‴ ] Γ‴ <<⦂ Γ″ × q-Bounded q Γ′ Γ‴
-- q-Bounded-<<⦂ ∅ qb-∅ = ∅ , ∅ , qb-∅
-- q-Bounded-<<⦂ (Γ′<<⦂Γ ,⦂ S′<⦂S) (qb-keep qS≤ qbdd)
--   with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
-- ... | Γ‴ , Γ‴<<⦂Γ″ , qbdd-out = (Γ‴ , _ ⦂ _ [ _ ]) , (Γ‴<<⦂Γ″ ,⦂ S′<⦂S) , qb-keep (≤-trans (q-of-mono S′<⦂S) qS≤) qbdd-out
-- q-Bounded-<<⦂ (Γ′<<⦂Γ ,⦂ S′<⦂S) (qb-drop qbdd f)
--   with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
-- ... | Γ‴ , Γ‴<<⦂Γ″ , qbdd-out =  Γ‴ , Γ‴<<⦂Γ″ , qb-drop qbdd-out {!!}

-- context-sub-variable : Γ ∋ x ⦂ S → Γ′ <<⦂ Γ → ∃[ S′ ] S′ <⦂ S × Γ′ ∋ x ⦂ S′
-- context-sub-variable here (_ ,⦂ S′<⦂S) = _ , S′<⦂S , here
-- context-sub-variable (there x∈ x≢) (Γ′<<⦂Γ ,⦂ _)
--   with context-sub-variable x∈ Γ′<<⦂Γ
-- ... | S′ , S′<⦂S , x∈′ = S′ , S′<⦂S , there x∈′ x≢

-- context-subtyping : Γ ⊢ e ⦂ S → Γ′ <<⦂ Γ → Γ′ ⊢ e ⦂ S
-- context-subtyping TUnit Γ′<<⦂Γ = TUnit
-- context-subtyping (TVar x∈) Γ′<<⦂Γ
--   with context-sub-variable x∈ Γ′<<⦂Γ
-- ... | S′ , S′<⦂S , x∈′ = TSub (TVar x∈′) S′<⦂S
-- context-subtyping {Γ = Γ}{Γ′ = Γ′} (TAbs {S≤x = S≤x} ⊢e qbdd eq) Γ′<<⦂Γ
--   with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
-- ... | _ , Γ‴<<⦂Γ′ , qbdd-out
--   = TAbs {S≤x = S≤x} (context-subtyping ⊢e (Γ‴<<⦂Γ′ ,⦂ <⦂-refl)) qbdd-out eq
-- context-subtyping (TApp ⊢e ⊢e₁) Γ′<<⦂Γ = TApp (context-subtyping ⊢e Γ′<<⦂Γ) (context-subtyping ⊢e₁ Γ′<<⦂Γ)
-- context-subtyping (TSub ⊢e x) Γ′<<⦂Γ = TSub (context-subtyping ⊢e Γ′<<⦂Γ) x
-- context-subtyping (TSeq x ⊢e ⊢e₁ x₁) Γ′<<⦂Γ = TSeq x (context-subtyping ⊢e Γ′<<⦂Γ) (context-subtyping ⊢e₁ Γ′<<⦂Γ) x₁
-- context-subtyping (TRef ⊢e qbdd) Γ′<<⦂Γ
--   with q-Bounded-<<⦂ Γ′<<⦂Γ qbdd
-- ... | _ , Γ‴<<⦂Γ′ , qbdd-out = TRef (context-subtyping ⊢e Γ‴<<⦂Γ′) qbdd-out 
-- context-subtyping (TDeref ⊢e) Γ′<<⦂Γ = TDeref (context-subtyping ⊢e Γ′<<⦂Γ)
-- context-subtyping (TSetref ⊢e ⊢e₁) Γ′<<⦂Γ = TSetref (context-subtyping ⊢e Γ′<<⦂Γ) (context-subtyping ⊢e₁ Γ′<<⦂Γ)


-- heap & stack typing

_↓′_ : List Val → ℕ → Maybe Val
[] ↓′ i = nothing
(x ∷ xs) ↓′ zero = just x
(x ∷ xs) ↓′ (suc i) = xs ↓′ i

↓′-[] : (i : ℕ) → [] ↓′ i ≡ nothing
↓′-[] i = refl

_↓ᵥ_ : Stack → ℕ → Maybe Val
𝓢 ↓ᵥ i = 𝓢 .vars ↓′ i

_↓ᵣ_ : Stack → ℕ → Maybe Val
𝓢 ↓ᵣ i = 𝓢 .refs ↓′ i

↓′-mono : ∀ {v} i → just v ≡ vs ↓′ i → just v ≡ (vs ++ vs′) ↓′ i
↓′-mono {x₁ ∷ vs} {vs′} {i} zero vs↓≡ = vs↓≡
↓′-mono {x₁ ∷ vs} {vs′} {i} (suc x) vs↓≡ = ↓′-mono {vs} {vs′} {i} x vs↓≡

↓ᵥ-mono : ∀ {v}{i : ℕ} → 𝓢 ≼ₛ 𝓢′ →  just v ≡ 𝓢 ↓ᵥ i → just v ≡ 𝓢′ ↓ᵥ i
↓ᵥ-mono {𝓢 = 𝓢} {v = v} {i = i} ((fst , refl) , snd) 𝓢↓≡ = ↓′-mono {vs = 𝓢 .vars} {v = v} i 𝓢↓≡

↓′-last : ∀ vs → just v ≡ (vs ++ [ v ]) ↓′ (length vs)
↓′-last [] = refl
↓′-last (_ ∷ vs) = ↓′-last vs

{-
-- not needed anymore
↓′-mono : ∀ {n : ℕ} {xs : List Val} {mi : Maybe ℕ} {r : Val}
  → just r ≡ take n xs ↓′ mi → just r ≡ xs ↓ mi
↓′-mono {suc n} {x ∷ xs} {just zero} refl = refl
↓′-mono {suc n} {x ∷ xs} {just (suc i)} take↓≡ = ↓′-mono {n} {xs} {just i} take↓≡
-}

{-
update : (Ident → Maybe ℕ) → Ident → ℕ → (Ident → Maybe ℕ)
update σ x n s = case (x ≟ s) of λ where
  (no ¬a) → σ s
  (yes a) → just n

update-access : ∀ σ s n → update σ s n s ≡ just n
update-access σ s n
  with s ≟ s
... | no ¬a = ⊥-elim (¬a refl)
... | yes refl = refl

↓-update : ∀ {σ} (xs : List Val) (v′ : Val) (s′ s : Ident) (neq : s′ ≢ s) → just v ≡ (xs ↓′ σ s) → just v ≡ (xs ++ [ v′ ]) ↓′ update σ s′ (length xs) s
↓-update {v} {σ} xs x s′ s s′≢s eq
  with update σ s′ (length xs) s in upd-eq
... | nothing
  with s′ ≟ s
↓-update {v} {σ} [] x s′ s s′≢s eq | nothing | no ¬a rewrite ↓′-[] (σ s) = eq
↓-update {v} {σ} (x₁ ∷ xs) x s′ s s′≢s eq | nothing | no ¬a rewrite upd-eq = eq

↓-update {v} {σ} xs x s′ s s′≢s eq | just x₁
  with s′ ≟ s
... | no ¬a rewrite upd-eq = ↓′-mono {vs = xs}{vs′ = [ x ]}{mi = just x₁} eq
... | yes a = ⊥-elim (s′≢s a)
-}

variable
  a a′  : Address
  va va′ : Val ⊎ Address

-- (H,∅)(x 1) = v
data Access : Env → Var → Val → Set where

  here   : Access ⟨ s ≔ v , 𝓔 ⟩ (X s 𝟙) v
  there  : Access 𝓔 x v → X s′ 𝟙 ≢ x → Access ⟨ s′ ≔ v′ , 𝓔 ⟩ x v
  skip   : Access 𝓔 x v → X s′ 𝟚 ≢ x → Access ⟨ s′ ⇒ a′ , 𝓔 ⟩ x v

data StackAccess : Env → Var → Address → Set where

  here   : StackAccess ⟨ s ⇒ a , 𝓔 ⟩ (X s 𝟚) a
  there  : StackAccess 𝓔 x a → X s′ 𝟚 ≢ x → StackAccess ⟨ s′ ⇒ a′ , 𝓔 ⟩ x a
  skip   : StackAccess 𝓔 x a → X s′ 𝟙 ≢ x → StackAccess ⟨ s′ ≔ v′ , 𝓔 ⟩ x a

data GenAccess : Env → Var → (Val ⊎ Address) → Set where

  on-heap   : Access 𝓔 (X s 𝟙) v → GenAccess 𝓔 (X s 𝟙) (inj₁ v)
  on-stack  : StackAccess 𝓔 (X s 𝟚) a → GenAccess 𝓔 (X s 𝟚) (inj₂ a)

access-unique : Access 𝓔 x v → Access 𝓔 x v′ → v ≡ v′
access-unique here here = refl
access-unique here (there acc′ x) = ⊥-elim (x refl)
access-unique (there acc x) here = ⊥-elim (x refl)
access-unique (there acc x) (there acc′ x₁) = access-unique acc acc′
access-unique (skip acc x) (skip acc′ x₁) = access-unique acc acc′

stack-access-unique : StackAccess 𝓔 x a → StackAccess 𝓔 x a′ → a ≡ a′
stack-access-unique here here = refl
stack-access-unique here (there sa′ x) = ⊥-elim (x refl)
stack-access-unique (there sa x) here = ⊥-elim (x refl)
stack-access-unique (there sa x) (there sa′ x₁) = stack-access-unique sa sa′
stack-access-unique (skip sa x) (skip sa′ x₁) = stack-access-unique sa sa′

gen-access-unique : GenAccess 𝓔 x va → GenAccess 𝓔 x va′ → va ≡ va′
gen-access-unique (on-heap x) (on-heap x₁) = cong inj₁ (access-unique x x₁)
gen-access-unique (on-stack x) (on-stack x₁) = cong inj₂ (stack-access-unique x x₁)

-- heap and stack types

Typeof : Qual → Set
Typeof 𝟙 = Type 𝟙               -- heap types
Typeof 𝟚 = QType                -- stack types

_^^_ : (q : Qual) → Typeof q → QType
𝟙 ^^ T = T ^ 𝟙
𝟚 ^^ S = S

q-^^-≤ : {S : Typeof q} → q-of (q ^^ S) ≤ q
q-^^-≤ {𝟙} = ≤-refl
q-^^-≤ {𝟚} = ≤-top

HSType = (q : Qual) → List (Typeof q)

variable
  Σₕₛ Σₕₛ′ Σₕₛ″ : HSType

extend-Σ : HSType → (q : Qual) → Typeof q → HSType
extend-Σ Σₕₛ 𝟙 T 𝟙 = Σₕₛ 𝟙 ++ [ T ]
extend-Σ Σₕₛ 𝟙 T 𝟚 = Σₕₛ 𝟚
extend-Σ Σₕₛ 𝟚 T 𝟙 = Σₕₛ 𝟙
extend-Σ Σₕₛ 𝟚 T 𝟚 = Σₕₛ 𝟚 ++ [ T ]


adjust-stack : HSType → List QType → HSType
adjust-stack Σₕₛ Σₛ 𝟙 = Σₕₛ 𝟙
adjust-stack Σₕₛ Σₛ 𝟚 = Σₛ


---- heap/stack typing extension

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

≼-adjust : ∀ {Σ₁ Σ₂ : HSType} → Σ₁ ≼ Σ₂ → Σ₁ ≼ adjust-stack Σ₂ (Σ₁ 𝟚)
≼-adjust ≼Σ₁ 𝟙 = ≼Σ₁ 𝟙
≼-adjust {Σ₁} ≼Σ₁ 𝟚 = [] , ++-identityʳ (Σ₁ 𝟚)

≼-adjust-[] : ∀ {Σ₁ Σ₂ : HSType} → adjust-stack Σ₁ [] ≼ Σ₂ → Σ₁ ≼ adjust-stack Σ₂ (Σ₁ 𝟚)
≼-adjust-[] ≼Σ₁ 𝟙 = ≼Σ₁ 𝟙
≼-adjust-[] {Σ₁} ≼Σ₁ 𝟚 = [] , ++-identityʳ (Σ₁ 𝟚)

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

---- value typing & environment agreement


bound-stack : Qual → Stack → Stack
bound-stack 𝟙 𝓢 = mkS [] []
bound-stack 𝟚 𝓢 = 𝓢

data ⟨_⟩⊢[_⦂_] (Σₕₛ : HSType) : Val → QType → Set

record ⟨_,_⟩⊨_/_ (Σₕₛ : HSType) (Γ : Context) (𝓔 : Env) (𝓢 : Stack) : Set where
  inductive
  constructor mk-⊨
  field
    ⊨-heap  : ∀ {s}{T} → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) → ∃[ v ] Access 𝓔 (X s 𝟙) v × ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
    ⊨-stack : ∀ {s}{S} → Γ ∋ X s 𝟚 ⦂ S → ∃[ a ] StackAccess 𝓔 (X s 𝟚) a × ∃[ v ] just v ≡ (𝓢 ↓ᵥ a) × ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]
open ⟨_,_⟩⊨_/_ public

-- value typing

-- resolve : Qual → StackMap → Maybe StackMap
-- resolve 𝟙 σ = nothing
-- resolve 𝟚 σ = just σ

data ⟨_⟩⊢[_⦂_] Σₕₛ where {- cf. p 15:11 of WhatIf -}

  TVUnit : ⟨ Σₕₛ ⟩⊢[ unit ⦂ (Unit ^ q) ]

  TVCst : ⟨ Σₕₛ ⟩⊢[ cst n ⦂ (Base ^ q) ]

  TVClos : ∀ {S₁≤x}
    → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢′
    → 𝓢 ≼ₛ 𝓢′
    → 𝓢 ≡ bound-stack q 𝓢
    → q-Bound q Γ
    → (Γ , x ⦂ S₁ [ S₁≤x ]) ⊢ e ⦂ S₂
    → let q₂ = q-of S₂ in
      let q₁ = q-of S₁ in
      (wf₁ : q₁ ≤ q)
      (wf₂ : q₂ ≤ q)
    → (Fun S₁ S₂ wf₁ wf₂ ^ q) <⦂ S
    → ⟨ Σₕₛ ⟩⊢[ clos q 𝓔 𝓢 x e q₂′ ⦂ S ]

  TVRef : ∀ {T : Typeof q}
    → (ℓ< : ℓ < length (Σₕₛ q))
    → lookup (Σₕₛ q) (fromℕ< ℓ<) ≡ T
    → (Ref (q ^^ T) q-^^-≤ ^ q) <⦂ S
    → ⟨ Σₕₛ ⟩⊢[ ref q ℓ ⦂ S ]


rename-bounded′ : q-Bounded q Γ Γ′ → Γ′ ∋ x ⦂ S → Γ ∋ x ⦂ S
rename-bounded′ (qb-keep x qbdd) (here) = here
rename-bounded′ (qb-keep x qbdd) (there x∈ x≢) = there (rename-bounded′ qbdd x∈) x≢
rename-bounded′ (qb-drop qbdd f) x∈ = there (rename-bounded′ qbdd x∈) (f x∈)

restrict′ : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢 → q-Bounded q Γ Γ′ → ⟨ Σₕₛ , Γ′ ⟩⊨ 𝓔 / bound-stack q 𝓢
restrict′ {q = 𝟚} ⊨𝓔 qbdd =
  mk-⊨ (λ x∈ → ⊨-heap ⊨𝓔 (rename-bounded′ qbdd x∈))
       (λ x∈ → ⊨-stack ⊨𝓔 (rename-bounded′ qbdd x∈))
restrict′ {q = 𝟙} ⊨𝓔 qbdd =
  mk-⊨ (λ x∈ → ⊨-heap ⊨𝓔 (rename-bounded′ qbdd x∈))
       (λ{ x∈ → ⊥-elim (𝟙-bound⇒∀𝟚∉ (is-bounded qbdd) _ _ x∈)})


-- heap typing

⊨-adjust-≼ₛ : 𝓢 ≼ₛ 𝓢′
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢′

⊨-adjust-≼ₛ {𝓢 = 𝓢}{𝓢′ = 𝓢′} 𝓢≼ₛ𝓢′ ⊨𝓔 =
  mk-⊨ (λ x∈ → ⊨-heap ⊨𝓔 x∈)
       (λ x∈ → let a , sa , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , sa , v , (↓ᵥ-mono {𝓢 = 𝓢}{𝓢′ = 𝓢′} 𝓢≼ₛ𝓢′ eq) , ⊢v)

-- allocate one heap allocated argument and create a new stack frame

⊢ᵥ-adjust : ∀ {Σₛ}
  → (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ])
  → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ]

⊨-adjust :  ∀ {Σₛ}
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → (∀ s S → ¬ (Γ ∋ X s 𝟚 ⦂ S))
  → ⟨ adjust-stack Σₕₛ Σₛ , Γ ⟩⊨ 𝓔 / mkS [] []

-- stack adjustment does not happen for a stack-allocated closure
-- in this case, the caller's stack is carried over to the callee

⊢ᵥ-adjust TVUnit = TVUnit
⊢ᵥ-adjust TVCst = TVCst
⊢ᵥ-adjust (TVClos {𝓢 = 𝓢}{q = 𝟙} ⊨𝓔 ≼𝓢 refl qbd ⊢e wf₁ wf₂ <⦂S) = TVClos (⊨-adjust ⊨𝓔 (𝟙-bound⇒∀𝟚∉ qbd)) (≼ₛ-refl {𝓢}) refl qbd ⊢e wf₁ wf₂ <⦂S
⊢ᵥ-adjust (TVClos {q = 𝟚} ⊨𝓔 ≼𝓢 𝓢≡ qbd ⊢e wf₁ wf₂ (SQual () x))
⊢ᵥ-adjust (TVRef {q = 𝟙} ℓ< lkup≡ <⦂S) = TVRef ℓ< lkup≡ <⦂S
⊢ᵥ-adjust (TVRef {q = 𝟚} ℓ< lkup≡ (SQual () x))

⊨-adjust ⊨𝓔 ∀𝟚∉ =
  mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , acc , (⊢ᵥ-adjust ⊢v))
       (λ x∈ → ⊥-elim (∀𝟚∉ _ _ x∈))

{-

⊢ᵥ-adjust-𝟚 : ∀ { vs : List Val} {Σₛ : List (Type 𝟚)}
  → Pointwise (λ v T → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]) vs Σₛ
  → (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ])
  → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟚) ]

⊢ᵥ-adjust-𝟚 ⊢ₛvs TVUnit = TVUnit
⊢ᵥ-adjust-𝟚 ⊢ₛvs TVCst = TVCst
⊢ᵥ-adjust-𝟚 ⊢ₛvs (TVClos x x₁ x₂ x₃ wf₂ x₄) = {!!}
⊢ᵥ-adjust-𝟚 ⊢ₛvs (TVRef {q = 𝟙} ℓ< lkup≡ <⦂S) = TVRef ℓ< lkup≡ <⦂S
⊢ᵥ-adjust-𝟚 ⊢ₛvs (TVRef {q = 𝟚} ℓ< lkup≡ <⦂S) = TVRef {!!} {!!} <⦂S
-}

_⊢ₕ_ : HSType → Heap → Set
Σₕₛ ⊢ₕ 𝓗 = Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙)]) 𝓗 (Σₕₛ 𝟙)

⊢ₕₛ-length-aux : ∀ {q}{Σₕ} {vs : List Val} → Pointwise (λ x y → ⟨ Σₕₛ ⟩⊢[ x ⦂ (q ^^ y) ]) vs Σₕ → length Σₕ ≡ length vs
⊢ₕₛ-length-aux [] = refl
⊢ₕₛ-length-aux (x∼y ∷ pws) = cong suc (⊢ₕₛ-length-aux pws)

⊢ₕ-length : Σₕₛ ⊢ₕ 𝓗 → length (Σₕₛ 𝟙) ≡ length 𝓗
⊢ₕ-length ⊢𝓗 = ⊢ₕₛ-length-aux ⊢𝓗


⊢ₕ-adjust-aux : ∀ {Σₕ}{vs vs′ : List Val}
  → ∀ Σₛ
  → Pointwise (λ v S → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ S ]) vs′ Σₛ
  → Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙)]) vs Σₕ
  → Pointwise (λ v T → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ (T ^ 𝟙)]) vs Σₕ
⊢ₕ-adjust-aux Σₛ ⊢ₛvs [] = []
⊢ₕ-adjust-aux Σₛ ⊢ₛvs (x∼y ∷ pws) = ⊢ᵥ-adjust x∼y ∷ ⊢ₕ-adjust-aux Σₛ ⊢ₛvs pws


⊢ₕ-adjust : ∀ {vs : List Val}
  → ∀ Σₛ
  → Pointwise (λ v S → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ S ]) vs Σₛ
  → Σₕₛ ⊢ₕ 𝓗
  → adjust-stack Σₕₛ Σₛ ⊢ₕ 𝓗
⊢ₕ-adjust Σₛ ⊢ₛvs ⊢𝓗 = ⊢ₕ-adjust-aux Σₛ ⊢ₛvs ⊢𝓗

-- stack typing

_⊢ₛ_ : HSType → Stack → Set
Σₕₛ ⊢ₛ 𝓢 = Pointwise ⟨ Σₕₛ ⟩⊢[_⦂_] (𝓢 .refs) (Σₕₛ 𝟚)

⊢ₛ-length : Σₕₛ ⊢ₛ 𝓢 → length (Σₕₛ 𝟚) ≡ length (𝓢 .refs)
⊢ₛ-length ⊢𝓢 = ⊢ₕₛ-length-aux ⊢𝓢

{-
⊢ₛ-adjust-aux : ∀ {vs : List Val} {Σₛ : List QType}
  → Σₕₛ ≼ Σₕₛ′
  → Pointwise (λ v S → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]) vs Σₛ
  → Pointwise (λ v S → ⟨ adjust-stack Σₕₛ′ (Σₕₛ 𝟚) ⟩⊢[ v ⦂ S ]) vs Σₛ
⊢ₛ-adjust-aux ≼Σ [] = []
⊢ₛ-adjust-aux ≼Σ (x∼y ∷ pws) = {! !} ∷ (⊢ₛ-adjust-aux ≼Σ pws)

⊢ₛ-adjust :
  Σₕₛ ≼ Σₕₛ′
  → Σₕₛ ⊢ₛ 𝓢
  → adjust-stack Σₕₛ′ (Σₕₛ 𝟚) ⊢ₛ 𝓢
⊢ₛ-adjust ≼Σ ⊢𝓢 = ⊢ₛ-adjust-aux ≼Σ ⊢𝓢
-}

⊨-adjust-[] :
  adjust-stack Σₕₛ [] ≼ Σₕₛ′
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → ⟨ adjust-stack Σₕₛ′ (Σₕₛ 𝟚) , Γ ⟩⊨ 𝓔 / 𝓢

⊢ᵥ-adjust-[] :
  adjust-stack Σₕₛ [] ≼ Σₕₛ′
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]
  → ⟨ adjust-stack Σₕₛ′ (Σₕₛ 𝟚) ⟩⊢[ v ⦂ S ]
⊢ᵥ-adjust-[] ≼Σ TVUnit = TVUnit
⊢ᵥ-adjust-[] ≼Σ TVCst = TVCst
⊢ᵥ-adjust-[] ≼Σ (TVClos ⊨𝓔 ≼𝓢 𝓢≡ qbd ⊢e wf₁ wf₂ <⦂S) = TVClos (⊨-adjust-[] ≼Σ ⊨𝓔) ≼𝓢 𝓢≡ qbd ⊢e wf₁ wf₂ <⦂S
⊢ᵥ-adjust-[] {Σₕₛ} ≼Σ (TVRef {𝟙} ℓ< lkup≡ <⦂S)
  with ≼Σ 𝟙 in eq
... | qts , eq1  
  = TVRef (≤ℕ-trans ℓ< (≼⇒length ≼Σ 𝟙)) (trans (lookup-from-i′ (Σₕₛ 𝟙) ℓ< eq1) lkup≡) <⦂S
⊢ᵥ-adjust-[] ≼Σ (TVRef {𝟚} ℓ< lkup≡ <⦂S) = TVRef ℓ< lkup≡ <⦂S

⊨-adjust-[] ≼Σ ⊨𝓔
  = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , acc , ⊢ᵥ-adjust-[] ≼Σ ⊢v)
         (λ x∈ → let a , sa , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , sa , v , eq , ⊢ᵥ-adjust-[] ≼Σ ⊢v)

⊢ₛ-adjust-aux-[] : ∀ {vs : List Val} {Σₛ : List QType}
  → adjust-stack Σₕₛ [] ≼ Σₕₛ′
  → Pointwise ⟨ Σₕₛ ⟩⊢[_⦂_] vs Σₛ
  → Pointwise ⟨ adjust-stack Σₕₛ′ (Σₕₛ 𝟚) ⟩⊢[_⦂_] vs Σₛ
⊢ₛ-adjust-aux-[] ≼Σ [] = []
⊢ₛ-adjust-aux-[] ≼Σ (x∼y ∷ pws) = ⊢ᵥ-adjust-[] ≼Σ x∼y ∷ (⊢ₛ-adjust-aux-[] ≼Σ pws)


⊢ₛ-adjust-[] :
  adjust-stack Σₕₛ [] ≼ Σₕₛ′
  → Σₕₛ ⊢ₛ 𝓢
  → adjust-stack Σₕₛ′ (Σₕₛ 𝟚) ⊢ₛ 𝓢
⊢ₛ-adjust-[] ≼Σ ⊢𝓢 = ⊢ₛ-adjust-aux-[] ≼Σ ⊢𝓢

⊢ᵥ-adjust-push : ∀ {Σₛ}
  → (vs : List Val)
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ S₀ ]
  → ⟨ adjust-stack Σₕₛ (Σₕₛ 𝟚 ++ Σₛ)  ⟩⊢[ v ⦂ S₀ ]

⊨-adjust-push : ∀ {vs}{Σₛ}
  → (⊨𝓔   : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢)
  → ⟨ adjust-stack Σₕₛ (Σₕₛ 𝟚 ++ Σₛ) , Γ ⟩⊨ 𝓔 / mkS (𝓢 .vars) (𝓢 .refs ++ vs)

⊢ᵥ-adjust-push vs TVUnit = TVUnit
⊢ᵥ-adjust-push vs TVCst = TVCst
⊢ᵥ-adjust-push vs (TVClos {𝓢′ = 𝓢′}{q = 𝟙} ⊨𝓔 ≼𝓢 refl qbd ⊢e wf₁ wf₂ (SQual qsub (SFun x₃ x₄)))
  = TVClos (⊨-adjust-push {vs = vs} ⊨𝓔) (≼ₛ-trans{mkS [] []}{𝓢′}{push-refs 𝓢′ vs} (≼ₛ-bot 𝓢′) (≼ₛ-extend{𝓢′} vs)) refl qbd ⊢e wf₁ wf₂ (SQual qsub (SFun x₃ x₄))
⊢ᵥ-adjust-push vs (TVClos {𝓢′ = 𝓢′} {𝓢 = 𝓢}{q = 𝟚} ⊨𝓔 ≼𝓢 refl qbd ⊢e wf₁ wf₂ (SQual qsub (SFun x₃ x₄)))
  = TVClos (⊨-adjust-push {vs = vs} ⊨𝓔) (≼ₛ-trans {𝓢} {𝓢′} {push-refs 𝓢′ vs} ≼𝓢 (≼ₛ-extend{𝓢′} vs)) refl qbd ⊢e wf₁ wf₂ (SQual qsub (SFun x₃ x₄))
⊢ᵥ-adjust-push vs (TVRef {𝟙} ℓ< x <⦂S) = TVRef ℓ< x <⦂S
⊢ᵥ-adjust-push {Σₕₛ = Σₕₛ} {Σₛ = Σₛ} vs (TVRef {𝟚} ℓ< lkup≡ <⦂S)
  = TVRef (≤ℕ-trans ℓ< (length-≤ (Σₕₛ 𝟚) Σₛ)) (trans (lookup-from-i (Σₕₛ 𝟚) ℓ<) lkup≡) <⦂S

⊨-adjust-push {𝓢 = 𝓢}{vs = vs} ⊨𝓔
  = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈
                 in  v , acc , ⊢ᵥ-adjust ⊢v)
         (λ x∈ → let a , sa , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈
                 in  a , sa , v , trans (↓′-mono {𝓢 .vars} {[]} a eq) (cong (_↓′ a) (++-identityʳ (𝓢 .vars))) , ⊢ᵥ-adjust-push vs ⊢v)

⊢ₛ-adjust-aux-push : ∀ {Σₛ}
  (xs : List Val)
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ S₀ ]
  → Pointwise ⟨ Σₕₛ ⟩⊢[_⦂_] vs Σₛ
  → Pointwise ⟨ adjust-stack Σₕₛ (Σₕₛ 𝟚 ++ [ S₀ ]) ⟩⊢[_⦂_] (vs ++ [ v ]) (Σₛ ++ [ S₀ ])
⊢ₛ-adjust-aux-push xs ⊢v [] = (⊢ᵥ-adjust-push xs ⊢v) ∷ []
⊢ₛ-adjust-aux-push xs ⊢v (x∼y ∷ pws) = ⊢ᵥ-adjust-push xs x∼y ∷ ⊢ₛ-adjust-aux-push xs ⊢v pws

⊢ₛ-adjust-push :
  ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]
  → Σₕₛ ⊢ₛ 𝓢
  → adjust-stack Σₕₛ (Σₕₛ 𝟚 ++ [ S ]) ⊢ₛ (mkS (𝓢 .vars) (𝓢 .refs ++ [ v ]))
⊢ₛ-adjust-push {𝓢 = 𝓢} ⊢v ⊢𝓢 = ⊢ₛ-adjust-aux-push (𝓢 .refs) ⊢v ⊢𝓢


⊨-adjust-push-update : ∀ s
  → ⟨ Σₕₛ ⟩⊢[ v₀ ⦂ (T ^ 𝟚) ]
  → (⊨𝓔   : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢)
  → ⟨ adjust-stack Σₕₛ (Σₕₛ 𝟚 ++ [ (T ^ 𝟚) ]) , (Γ , X s 𝟚 ⦂ (T ^ 𝟚) [ refl ]) ⟩⊨ ⟨ s ⇒ length (𝓢 .vars) , 𝓔 ⟩ / mkS (𝓢 .vars ++ [ v₀ ]) (𝓢 .refs)

⊨-adjust-push-update {Σₕₛ = Σₕₛ} {v₀ = v₀}{T = T} {𝓢 = 𝓢} s′ ⊢v₀ ⊨𝓔
  = mk-⊨ (λ{ (there x∈ x≢) → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , skip acc (x≢ ∘ sym) , ⊢ᵥ-adjust-push [ v₀ ] ⊢v})
         (λ{ here → length (𝓢 .vars) , here , v₀ , ↓′-last (𝓢 .vars) , (⊢ᵥ-adjust-push [ v₀ ] ⊢v₀)
           ; (there x∈ x≢) → let a , acc , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , there acc (x≢ ∘ sym) , v , ↓′-mono {vs = 𝓢 .vars} {vs′ = [ v₀ ]} a eq , ⊢ᵥ-adjust-push [ v₀ ] ⊢v})

-- value typing extends

⊨-extend-Σ : Σₕₛ ≼ Σₕₛ′ → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢 → ⟨ Σₕₛ′ , Γ ⟩⊨ 𝓔 / 𝓢

[⦂]-≼ : Σₕₛ ≼ Σₕₛ′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ] → ⟨ Σₕₛ′ ⟩⊢[ v ⦂ S ]
[⦂]-≼ Σ≼ TVUnit = TVUnit
[⦂]-≼ Σ≼ TVCst = TVCst
[⦂]-≼ Σ≼ (TVClos ⊨𝓔 ≼𝓢 𝓢≡ qbd ⊢e σ?≡ wf₂ <⦂S) = TVClos (⊨-extend-Σ Σ≼ ⊨𝓔) ≼𝓢 𝓢≡ qbd ⊢e σ?≡ wf₂ <⦂S
[⦂]-≼ {Σₕₛ = Σₕₛ} Σ≼ (TVRef {q = q} ℓ< lkup≡ <⦂S)
  with Σ≼ q in eq
... | qts , eq1 = TVRef (≤ℕ-trans ℓ< (≼⇒length Σ≼ q)) (trans (lookup-from-i′ (Σₕₛ q) ℓ< eq1) lkup≡) <⦂S

-- agreement extends


⊨-extend-Σ Σ≼ ⊨Γ = mk-⊨ (λ x∈ → let v , acc , ⊢v = ⊨-heap ⊨Γ x∈ in v , acc , [⦂]-≼ Σ≼ ⊢v)
                        (λ x∈ → let a , sa , v , eq , ⊢v = ⊨-stack ⊨Γ x∈ in a , sa , v , eq , [⦂]-≼ Σ≼ ⊢v)


-- heap typing extends (needed?)

⊢ₕ-≼-aux : Σₕₛ ≼ Σₕₛ′ → ∀ {Σₕ}
  → Pointwise ⟨ Σₕₛ ⟩⊢[_⦂_] 𝓗 Σₕ
  → Pointwise ⟨ Σₕₛ′ ⟩⊢[_⦂_] 𝓗 Σₕ
⊢ₕ-≼-aux Σ≼ [] = []
⊢ₕ-≼-aux Σ≼ (x∼y ∷ pws) = ([⦂]-≼ Σ≼ x∼y) ∷ (⊢ₕ-≼-aux Σ≼ pws)

{-
⊢ₕ-≼ : Σₕₛ ≼ Σₕₛ′ → Σₕₛ ⊢ₕ 𝓗 → Σₕₛ′ ⊢ₕ 𝓗
⊢ₕ-≼ {Σₕₛ} Σ≼ ⊢𝓗 = {!⊢ₕ-≼-aux Σ≼ {Σₕₛ 𝟙} ⊢𝓗!}
-}

⊨-extend-𝟙 : ∀ s T
  → (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙)])
  → ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢
  → ⟨ Σₕₛ , (Γ , X s 𝟙 ⦂ (T ^ 𝟙) [ refl ]) ⟩⊨ ⟨ s ≔ v , 𝓔 ⟩ / 𝓢
⊨-extend-𝟙 {v = v} s T ⊢v ⊨𝓔 =
  mk-⊨ (λ{ here → v , here , ⊢v
       ; (there x∈ x≢) → let v , acc , ⊢v = ⊨-heap ⊨𝓔 x∈ in v , there acc (x≢ ∘ sym) , ⊢v})
       (λ{ (there x∈ x≢) → let a , sa , v , eq , ⊢v = ⊨-stack ⊨𝓔 x∈ in a , (skip sa (x≢ ∘ sym)) , v , eq , ⊢v})

access-soundness : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢 → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) → Access 𝓔 (X s 𝟙) v → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ 𝟙) ]
access-soundness Γ⊨ x∈ access
  with ⊨-heap Γ⊨ x∈
... | v , acc′ , ⊢v
  rewrite access-unique access acc′ = ⊢v

¬x𝟙∈𝟚 : ¬ (Γ ∋ X s 𝟙 ⦂ mkQ 𝟚 T)
¬x𝟙∈𝟚 (there x∈ x≢) = ¬x𝟙∈𝟚 x∈

genaccess-soundness : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢 → Γ ∋ x ⦂ (T ^ q) → GenAccess 𝓔 x (inj₁ v) → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ q) ]
genaccess-soundness {q = 𝟙} ⊨𝓔 x∈ (on-heap acc) = access-soundness ⊨𝓔 x∈ acc
genaccess-soundness {q = 𝟚} ⊨𝓔 x∈ (on-heap acc) = contradiction x∈ ¬x𝟙∈𝟚

genaccess-soundness-𝟚 : ⟨ Σₕₛ , Γ ⟩⊨ 𝓔 / 𝓢 → Γ ∋ x ⦂ (T ^ q) → GenAccess 𝓔 x (inj₂ a) → ∀ v → just v ≡ 𝓢 ↓ᵥ a → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T ^ q) ]
genaccess-soundness-𝟚 ⊨𝓔 x∈ (on-stack sa) v eq
  with ⊨-stack ⊨𝓔 x∈
... | a , sa′ , v′ , eq′ , ⊢v
  rewrite stack-access-unique sa sa′ | sym eq
  with eq′
... | refl = ⊢v




<⦂-val-lift : ⟨ Σₕₛ ⟩⊢[ v ⦂ S₁ ] → S₁ <⦂ S₂ → ⟨ Σₕₛ ⟩⊢[ v ⦂ S₂ ]
<⦂-val-lift TVUnit (SQual qsub SUnit) = TVUnit
<⦂-val-lift TVCst (SQual qsub SBase) = TVCst
<⦂-val-lift (TVClos ⊨𝓔 ≼𝓢 𝓢≡ qbd ⊢e wf₁ wf₂ <⦂S₁) S₁<⦂S₂ = TVClos ⊨𝓔 ≼𝓢 𝓢≡ qbd ⊢e wf₁ wf₂ (<⦂-trans <⦂S₁ S₁<⦂S₂)
<⦂-val-lift (TVRef ℓ< lkup≡ <⦂S₁) S₁<⦂S₂ = TVRef ℓ< lkup≡ (<⦂-trans <⦂S₁ S₁<⦂S₂)


-- operational semantics

-- operations on references: deref and update

data read : List Val → ℕ → Val → Set where

  read0 : read (v ∷ vs) zero v
  read1 : read vs n v → read (v′ ∷ vs) (suc n) v

data sread : Stack → ℕ → Val → Set where

  sread0 : read (𝓢 .refs) ℓ v → sread 𝓢 ℓ v

data write : List Val → ℕ → Val → List Val → Set where

  write0 : write (v′ ∷ vs) zero v (v ∷ vs)
  write1 : write vs n v vs′ → write (v′ ∷ vs) (suc n) v (v′ ∷ vs′)

data swrite : Stack → ℕ → Val → Stack → Set where

  swrite0 : ∀{vars} → write vs ℓ v vs′ → swrite (mkS vars vs) ℓ v (mkS vars vs′)

length-write : write vs ℓ v vs′ → length vs ≡ length vs′
length-write write0 = refl
length-write (write1 wr) = cong suc (length-write wr)

≼ₛ-swrite : swrite 𝓢 ℓ v 𝓢′ → 𝓢 ≼ₛ 𝓢′
≼ₛ-swrite (swrite0 wr) = ([] , ++-identityʳ _) , ≡⇒≤ (length-write wr)

typed-read-aux : ∀ {q}{T : Typeof q}{Σₕ : List (Typeof q)}
  → Pointwise (λ v T → ⟨ Σₕₛ ⟩⊢[ v ⦂ (q ^^ T) ] ) 𝓗 Σₕ
  → {ℓ : ℕ}
  → (ℓ< : ℓ < length Σₕ)
  → (lkup≡ : lookup Σₕ (fromℕ< ℓ<) ≡ T)
  → read 𝓗 ℓ v
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (q ^^ T) ]
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
  → (lkup≡ : lookup (Σₕₛ 𝟚) (fromℕ< ℓ<) ≡ S)
  → sread 𝓢 ℓ v
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]
typed-sread {Σₕₛ = Σₕₛ} ⊢𝓢 ℓ< lkup≡ (sread0 xread) = typed-read-aux {Σₕ = Σₕₛ 𝟚} ⊢𝓢 ℓ< lkup≡ xread

typed-write-aux : ∀ {q}{T : Typeof q}{Σₕ}
  → Pointwise (λ w T → ⟨ Σₕₛ ⟩⊢[ w ⦂ (q ^^ T) ] ) 𝓗 Σₕ
  → {ℓ : ℕ}
  → (ℓ< : ℓ < length Σₕ)
  → (lkup≡ : lookup Σₕ (fromℕ< ℓ<) ≡ T)
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ (q ^^ T) ]
  → write 𝓗 ℓ v 𝓗′
  → Pointwise (λ w T → ⟨ Σₕₛ ⟩⊢[ w ⦂ (q ^^ T) ] ) 𝓗′ Σₕ
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

typed-swrite : ∀ {S}
  → Σₕₛ ⊢ₛ 𝓢
  → (ℓ< : ℓ < length (Σₕₛ 𝟚))
  → (lkup≡ : lookup (Σₕₛ 𝟚) (fromℕ< ℓ<) ≡ S)
  → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]
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
  → (⊢𝓢 : Pointwise (λ v S → ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]) xs Σₛ)
  → Pointwise (λ v S → ⟨ (extend-Σ Σₕₛ 𝟙 T) ⟩⊢[ v ⦂ S ]) xs Σₛ
⊢𝓢-extend-𝟙-aux T [] = []
⊢𝓢-extend-𝟙-aux T (x∼y ∷ ⊢𝓢) = ([⦂]-≼ (≼-extend-Σ 𝟙 T) x∼y) ∷ (⊢𝓢-extend-𝟙-aux T ⊢𝓢)

⊢𝓢-extend-𝟙 : (T : Type 𝟙) → (⊢𝓢 : Σₕₛ ⊢ₛ 𝓢) → extend-Σ Σₕₛ 𝟙 T ⊢ₛ 𝓢
⊢𝓢-extend-𝟙 T ⊢𝓢 = ⊢𝓢-extend-𝟙-aux T ⊢𝓢

⊢𝓗-extend-𝟚-aux : ∀ {Σₛ} {xs : List Val} → (S : QType)
  → Pointwise (λ v T′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ (T′ ^ 𝟙)]) xs Σₛ
  → Pointwise (λ v T′ → ⟨ (extend-Σ Σₕₛ 𝟚 S) ⟩⊢[ v ⦂ (T′ ^ 𝟙)] ) xs Σₛ
⊢𝓗-extend-𝟚-aux S [] = []
⊢𝓗-extend-𝟚-aux S (x∼y ∷ pws) = ([⦂]-≼ (≼-extend-Σ 𝟚 S) x∼y) ∷ ⊢𝓗-extend-𝟚-aux S pws

⊢𝓗-extend-𝟚 : (S : QType) → (⊢𝓗 : Σₕₛ ⊢ₕ 𝓗) → extend-Σ Σₕₛ 𝟚 S ⊢ₕ 𝓗
⊢𝓗-extend-𝟚 S ⊢𝓗 = ⊢𝓗-extend-𝟚-aux S ⊢𝓗

⊢𝓢-extend-𝟚-aux : ∀ {Σₛ : List QType} {xs : List Val}
  → (T : QType) (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ T ])
  → (⊢𝓢 : Pointwise (λ v S′ → ⟨ Σₕₛ ⟩⊢[ v ⦂ S′ ]) xs Σₛ)
  → Pointwise (λ v S′ → ⟨ (extend-Σ Σₕₛ 𝟚 T) ⟩⊢[ v ⦂ S′ ] ) (xs ++ [ v ]) (Σₛ ++ [ T ])
⊢𝓢-extend-𝟚-aux T ⊢v [] = [⦂]-≼ (≼-extend-Σ 𝟚 T) ⊢v ∷ []
⊢𝓢-extend-𝟚-aux T ⊢v (x∼y ∷ pws) = ([⦂]-≼ (≼-extend-Σ 𝟚 T) x∼y) ∷ ⊢𝓢-extend-𝟚-aux T ⊢v pws

⊢𝓢-extend-𝟚 : (T : QType) (⊢v : ⟨ Σₕₛ ⟩⊢[ v ⦂ T ])
  → (⊢𝓢 : Σₕₛ ⊢ₛ 𝓢)
  → Pointwise (λ v T′ → ⟨ (extend-Σ Σₕₛ 𝟚 T) ⟩⊢[ v ⦂ T′ ]) (𝓢 .refs ++ [ v ]) (Σₕₛ 𝟚 ++ [ T ])
⊢𝓢-extend-𝟚 S ⊢v ⊢𝓢 = ⊢𝓢-extend-𝟚-aux S ⊢v ⊢𝓢

{-
postulate
  ⊢𝓢-revert-𝟚-value : ⟨ Σₕₛ ⟩⊢[ v ⦂ S ]
    → (Σₛ : List (Type 𝟚))
    → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ S ]

⊢𝓗-revert-𝟚-env : ⟨ Σₕₛ′ , Γ ⟩⊨ 𝓔 / (𝓢 , σ) → (Σₛ : List (Type 𝟚))
  → ⟨ adjust-stack Σₕₛ′ Σₛ , Γ ⟩⊨ 𝓔 / (take (length Σₛ) 𝓢 , σ)
⊢𝓗-revert-𝟚-value : ⟨ Σₕₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ]
  → (Σₛ : List (Type 𝟚))
  → ⟨ adjust-stack Σₕₛ Σₛ ⟩⊢[ v ⦂ mkQ 𝟙 T ]

⊢𝓗-revert-𝟚-env {𝓢 = 𝓢}{σ = σ} ⊨𝓔 Σₛ = mk-⊨ (λ x∈ x≢ → ⊢𝓗-revert-𝟚-value (⊨-heap ⊨𝓔 x∈ x≢) Σₛ)
                                             (λ {s = s} x∈ v≡ → ⊢𝓢-revert-𝟚-value (⊨-stack ⊨𝓔 x∈ (↓-mono {n = length Σₛ}{xs = 𝓢}{mi = σ s} v≡)) Σₛ )

⊢𝓗-revert-𝟚-value TVUnit Σₛ = TVUnit
⊢𝓗-revert-𝟚-value TVCst Σₛ = TVCst
⊢𝓗-revert-𝟚-value (TVClos ⊨𝓔 qbd ⊢e σ?≡ wf₂ <⦂S) Σₛ = TVClos (⊢𝓗-revert-𝟚-env ⊨𝓔 Σₛ) qbd ⊢e σ?≡ wf₂ <⦂S
⊢𝓗-revert-𝟚-value (TVRef ℓ< lkup≡ (SQual ≤-refl <⦂′T)) Σₛ = TVRef ℓ< lkup≡ (SQual ≤-refl <⦂′T)

⊢𝓗-revert-𝟚-aux : ∀ {Σₕ} {xs : List Val}
  → Σₕₛ ≼ Σₕₛ′
  → Pointwise (λ v T′ → ⟨ Σₕₛ′ ⟩⊢[ v ⦂ (T′ ^ 𝟙)]) xs Σₕ
  → Pointwise (λ v T′ → ⟨ adjust-stack Σₕₛ′ (Σₕₛ 𝟚) ⟩⊢[ v ⦂ (T′ ^ 𝟙)]) xs Σₕ
⊢𝓗-revert-𝟚-aux ≼Σ [] = []
⊢𝓗-revert-𝟚-aux {Σₕₛ = Σₕₛ} ≼Σ (x∼y ∷ pws) = ⊢𝓗-revert-𝟚-value x∼y (Σₕₛ 𝟚) ∷ (⊢𝓗-revert-𝟚-aux ≼Σ pws)

⊢𝓗-revert-𝟚 : Σₕₛ ≼ Σₕₛ′ → (⊢𝓗 : Σₕₛ′ ⊢ₕ 𝓗) → adjust-stack Σₕₛ′ (Σₕₛ 𝟚) ⊢ₕ 𝓗
⊢𝓗-revert-𝟚 ≼Σ ⊢𝓗 = ⊢𝓗-revert-𝟚-aux ≼Σ ⊢𝓗
-}


∣_∣ʰ = length

∣_∣ˢ : Stack → ℕ
∣_∣ˢ = length ∘ vars

_⊕_ : Env → (Var × Val × Address) → Env
𝓔 ⊕ (X s 𝟙 , v , a) = ⟨ s ≔ v , 𝓔 ⟩
𝓔 ⊕ (X s 𝟚 , v , a) = ⟨ s ⇒ a , 𝓔 ⟩

_⊕ₛ_ : Stack → (Var × Val) → Stack
𝓢 ⊕ₛ (X s 𝟙 , v) = 𝓢
𝓢 ⊕ₛ (X s 𝟚 , v) = push 𝓢 v
{-
alloc : Stack → Val → Stack × ℕ
alloc 𝓢 v = push 𝓢 v , ∣ 𝓢 ∣ˢ

alloc-length : ∀ 𝓢 → ∣ alloc 𝓢 v .proj₁ ∣ˢ ≡ suc ∣ 𝓢 ∣ˢ
alloc-length {v = v} 𝓢 = trans (length-++ (𝓢 .head) {[ v ]}) (trans (+-suc (∣ 𝓢 ∣ˢ) zero) (cong suc (+-identityʳ ∣ 𝓢 ∣ˢ)))
-}
new-frame? : Qual → Stack → Stack
new-frame? 𝟙 𝓢 = mkS [] []
new-frame? 𝟚 𝓢 = 𝓢

restore-frame? : Qual → Stack → Stack → Stack
restore-frame? 𝟙 𝓢₁ 𝓢₂ = 𝓢₁
restore-frame? 𝟚 𝓢₁ 𝓢₂ = 𝓢₂

decode : Val ⊎ Address → Stack → Maybe Val
decode (inj₁ v) 𝓢 = just v
decode (inj₂ a) 𝓢 = 𝓢 ↓ᵥ a


-- H,S ⊢ c ⇓q s c ⊣ S
data _,_,_⊢_⇓[_]_⊣_,_
  : Env → Heap → Stack → Expr → Qual → Val → Heap → Stack → Set
  where

  EUnit  :
        𝓔 , 𝓗 , 𝓢 ⊢ unit ⇓[ q ] unit ⊣ 𝓗 , 𝓢

  EVarH :
        Access 𝓔 (X s 𝟙) v
       → 𝓔 , 𝓗 , 𝓢 ⊢ var (X s 𝟙) ⇓[ 𝟙 ] v ⊣ 𝓗 , 𝓢

  EVarS :
        GenAccess 𝓔 x va
       → just v ≡ decode va 𝓢
       → 𝓔 , 𝓗 , 𝓢 ⊢ var x ⇓[ 𝟚 ] v ⊣ 𝓗 , 𝓢

  EAbs : ∀ {𝓢ᶜ}
       → q₁ ≤ q
       → q₂ ≤ q
       → (case q₁ of λ{ 𝟙 → 𝓢ᶜ ≡ mkS [] [] ; 𝟚 → 𝓢ᶜ ≡ 𝓢 })
       → 𝓔 , 𝓗 , 𝓢 ⊢ lam q₁ x e q₂ ⇓[ q ] clos q₁ 𝓔 𝓢ᶜ x e q₂ ⊣ 𝓗 , 𝓢

  EAbsH :
       𝓔 , 𝓗 , 𝓢 ⊢ lam 𝟙 x e 𝟙 ⇓[ 𝟙 ] clos 𝟙 𝓔 (mkS [] []) x e 𝟙 ⊣ 𝓗 , 𝓢

  EAbsS :
       𝓔 , 𝓗 , 𝓢 ⊢ lam q x e q₂ ⇓[ 𝟚 ] clos q 𝓔 𝓢 x e q₂ ⊣ 𝓗 , 𝓢

       
  EApp : q₂ ≤ q₀
       → 𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ] clos q 𝓔′ 𝓢ᶜ (X s q₁) e q₂ ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q₁ ] v₂ ⊣ 𝓗″ , 𝓢″
       → (𝓔′ ⊕ (X s q₁ , v₂ , ∣ 𝓢″ ∣ˢ)) , 𝓗″ , new-frame? q 𝓢″ ⊕ₛ (X s q₁ , v₂) ⊢ e ⇓[ q₂ ] v ⊣ 𝓗‴ , 𝓢‴
       → 𝓢⁗ ≡ restore-frame? q 𝓢″ 𝓢‴
        ---------------------------------------------------------
       → 𝓔 , 𝓗 , 𝓢 ⊢ app e₁ e₂ ⇓[ q₀ ] v ⊣ 𝓗‴ , 𝓢⁗

  
  EAppH :
         𝓔 , 𝓗  , 𝓢 ⊢ e₁ ⇓[ 𝟚  ] clos q 𝓔′ 𝓢ᶜ (X s q₂) e 𝟙 ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q₂ ] v₂ ⊣ 𝓗″ , 𝓢″
       → (𝓔′ ⊕ (X s q₂ , v₂ , ∣ 𝓢″ ∣ˢ)) , 𝓗″ , new-frame? q 𝓢″ ⊕ₛ (X s q₂ , v₂) ⊢ e ⇓[ 𝟙 ] v ⊣ 𝓗‴ , 𝓢‴
       → 𝓢⁗ ≡ restore-frame? q 𝓢″ 𝓢‴
        ---------------------------------------------------------
       → 𝓔 , 𝓗 , 𝓢 ⊢ app e₁ e₂ ⇓[ 𝟙 ] v ⊣ 𝓗‴ , 𝓢⁗
       
  EAppS :
         𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ] clos q 𝓔′ 𝓢ᶜ (X s q₁) e q₂ ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q₁ ] v₂ ⊣ 𝓗″ , 𝓢″
       → (𝓔′ ⊕ (X s q₁ , v₂ , ∣ 𝓢″ ∣ˢ)) , 𝓗″ , new-frame? q 𝓢″ ⊕ₛ (X s q₁ , v₂) ⊢ e ⇓[ q₂ ] v ⊣ 𝓗‴ , 𝓢‴
       → 𝓢⁗ ≡ restore-frame? q 𝓢″ 𝓢‴
        ---------------------------------------------------------
       → 𝓔 , 𝓗 , 𝓢 ⊢ app e₁ e₂ ⇓[ 𝟚 ] v ⊣ 𝓗‴ , 𝓢⁗


  ERef :  q₁ ≤ q
      → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q₁ ] v ⊣ 𝓗′ , 𝓢′
      → case q of (λ{ 𝟙 → 𝓢″ ≡ 𝓢′ × n ≡ ∣ 𝓗′ ∣ʰ × 𝓗″ ≡ 𝓗′ ++ [ v ]
                    ; 𝟚 → 𝓗″ ≡ 𝓗′ × (𝓢″ , n) ≡ salloc 𝓢′ v })
        --------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ ref q₁ e ⇓[ q ] ref q₁ n ⊣ 𝓗″ , 𝓢″


  ERefH :
        𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢′
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ ref 𝟙 e ⇓[ 𝟙 ] ref 𝟙 ∣ 𝓗′ ∣ʰ ⊣ 𝓗′ ++ [ v ] , 𝓢′


  ERefS :
        𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
      → (q ≡ 𝟙 → 𝓢″ ≡ 𝓢′ × n ≡ ∣ 𝓗′ ∣ʰ × 𝓗″ ≡ 𝓗′ ++ [ v ])
      → (q ≡ 𝟚 → 𝓗″ ≡ 𝓗′ × (𝓢″ , n) ≡ salloc 𝓢′ v)
        --------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ ref q e ⇓[ 𝟚 ] ref q n ⊣ 𝓗″ , 𝓢″


  EDeref :  q₁ ≤ q
      → 𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ 𝟚 ] ref q₁ ℓ ⊣ 𝓗′ , 𝓢′
      → case q of (λ{ 𝟙 → read 𝓗′ ℓ v ; 𝟚 → sread 𝓢′ ℓ v })
        ----------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ deref q e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′


  EDerefH :
        𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ 𝟙 ] ref 𝟙 ℓ ⊣ 𝓗′ , 𝓢′
      → read 𝓗′ ℓ v
        ----------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ deref 𝟙 e ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢′

  EDerefS :
        𝓔 , 𝓗 , 𝓢 ⊢ e ⇓[ 𝟚 ] ref q ℓ ⊣ 𝓗′ , 𝓢′
      → (q ≡ 𝟙 → read 𝓗′ ℓ v)
      → (q ≡ 𝟚 → sread 𝓢′ ℓ v)
        -------------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ deref 𝟚 e ⇓[ 𝟚 ] v ⊣ 𝓗′ , 𝓢′

  ESetref :
        𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ] ref q₁ ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q₁ ] v ⊣ 𝓗″ , 𝓢″
      → case q₁ of (λ{ 𝟙 → write 𝓗″ ℓ v 𝓗‴ × 𝓢‴ ≡ 𝓢″
                     ; 𝟚 → 𝓗‴ ≡ 𝓗″ × swrite 𝓢″ ℓ v 𝓢‴ })
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ setref e₁ e₂ ⇓[ q ] unit ⊣ 𝓗‴ , 𝓢‴

  ESetrefH :
        𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟙 ] ref 𝟙 ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ 𝟙 ] v ⊣ 𝓗″ , 𝓢″
      → write 𝓗″ ℓ v 𝓗‴
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ setref e₁ e₂ ⇓[ 𝟙 ] unit ⊣ 𝓗‴ , 𝓢″

  ESetrefS :
        𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ] ref q ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q ] v ⊣ 𝓗″ , 𝓢″
      → (q ≡ 𝟙 → write 𝓗″ ℓ v 𝓗‴ × 𝓢‴ ≡ 𝓢″)
      → (q ≡ 𝟚 → 𝓗‴ ≡ 𝓗″ × swrite 𝓢″ ℓ v 𝓢‴)
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ setref e₁ e₂ ⇓[ 𝟚 ] unit ⊣ 𝓗‴ , 𝓢‴

  ESeq :
        𝓔 , 𝓗 , 𝓢 ⊢ e₁ ⇓[ 𝟚 ] v₁ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , 𝓢′ ⊢ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , 𝓢 ⊢ seq e₁ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
