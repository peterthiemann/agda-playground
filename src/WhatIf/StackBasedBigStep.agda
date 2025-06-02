module StackBasedBigStep where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup)
open import Data.List.Properties using (length-++)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.Bool using (Bool; true; false) renaming (T to 𝕋)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _<_)
open import Data.Nat.Properties using (<ᵇ⇒<; +-suc; +-identityʳ)
open import Data.Fin using (Fin; fromℕ; fromℕ<)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; proj₁ ; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; subst; cong; cong₂; dcong)

Ident = String
StackMap = Ident → Maybe ℕ

open import Qualifiers

-- variables
data Var : Set where
  X : Ident → Qual → Var

-- values
data Val : Set
data Local : Set where
  ∅ : Local
  ⟨_≔_,_⟩ : Ident → Val → Local → Local
Env = Local
Heap = List Val

data Expr : Set where
  cst : ℕ → Expr
  unit : Expr
  var : Var → Expr
  lam : Var → Expr → Qual → Expr
  app : Expr → Expr → Expr
  seq : Expr → Expr → Expr
  ref : Qual → Expr → Expr
  deref : Qual → Expr → Expr
  setref : Expr → Expr → Expr

data Val where
  unit : Val
  clos : Env → Maybe StackMap → Var → Expr → Qual → Val
  cst : ℕ → Val
  ref : Qual → ℕ → Val

↑expr : Val → Expr
↑expr unit = unit
↑expr (clos 𝓔 σ? x e q) = lam x e q
↑expr (cst x) = cst x
↑expr (ref q n) = ref q (cst n)


Stack : Set
Stack = List⁺ (List Val)


postulate
  _[_]≔_ : List Val → ℕ → Val → List Val
  

variable
  𝓔 𝓔′ : Env
  𝓗 𝓗′ 𝓗″ 𝓗‴ : Heap
  𝓢 𝓢′ 𝓢″ 𝓢‴ : Stack
  𝓛 : List (List Val)
  σ σ′ σ″ : StackMap
  σ? : Maybe StackMap
  𝓢σ : Stack × StackMap
  s s′ : Ident
  v v′ v″ v₁ v₂ : Val
  vs vs′ : List Val
  x : Var
  e e₁ e₂ : Expr
  Φ Φ′ Φ″ : Local
  n ℓ : ℕ


-- typing

data Type (q : Qual) : Set
record QType : Set where
  inductive
  constructor _^_
  field
    q-of : Qual
    t-of : Type q-of
open QType public

data Type q where
  Unit : Type q
  Base : Type q
  Fun  : (S₁ : QType) → (S₂ : QType) → Type q
  Ref  : (S : QType) → q-of S ≤ q → Type q

q-var : Var → Qual
q-var (X s q) = q


data Context : Set where

  ∅ : Context
  _,_⦂_ : (Γ : Context) → (s : Ident) → (S : QType) → Context

variable
  Γ Γ′ : Context
  T T₁ T₂ : Type q
  S S′ S₁ S₂ S₃ S₄ : QType

-- data wf : QType → Set where

--   wf-Unit : wf (q ^ Unit)
--   wf-Base : wf (q ^ Base)
--   wf-Fun  : wf S₁ → wf S₂ → wf (q ^ Fun S₁ S₂)
--   wf-Ref  : wf S → q-of S ≤ q → wf (q ^ Ref S)

data _∋_⦂_ : Context → Var → QType → Set where

  here   : q-of S ≤ q → (Γ , s ⦂ S) ∋ (X s q) ⦂ S
  there  : Γ ∋ x ⦂ S → (Γ , s′ ⦂ S′) ∋ x ⦂ S

q-var-type : Γ ∋ x ⦂ S → q-of S ≤ q-var x
q-var-type (here x) = x
q-var-type (there x∈) = q-var-type x∈


-- lower bounds for qualifiers

q-val : Val → Qual
q-val unit = 𝟙
q-val (clos _ _ _ _ q) = q
q-val (cst x) = 𝟙
q-val (ref q _) = q

q-env : Env → Qual
q-env ∅ = 𝟙
q-env ⟨ s ≔ v , 𝓔 ⟩ = q-val v ⊔ q-env 𝓔

q-bound : Context → Qual
q-bound ∅ = 𝟙
q-bound (Γ , _ ⦂ (q ^ _)) = (q-bound Γ) ⊔ q

q-bounded : Qual → Context → Context
q-bounded q ∅ = ∅
q-bounded q (Γ , s ⦂ S)
  with q-of S ≤ᵇ q
... | false = q-bounded q Γ
... | true = q-bounded q Γ , s ⦂ S

𝟚-bounded : (Γ : Context) → Γ ≡ q-bounded 𝟚 Γ
𝟚-bounded ∅ = refl
𝟚-bounded (Γ , s ⦂ S)
  rewrite ≤ᵇ-top {q-of S}
  = cong (_, s ⦂ S) (𝟚-bounded Γ)

data _<⦂_ : QType → QType → Set where

  SUnit : q₁ ≤ q₂
    → (q₁ ^ Unit) <⦂ (q₂ ^ Unit)

  SBase : q₁ ≤ q₂
    → (q₁ ^ Base) <⦂ (q₂ ^ Base)

  SFun : q₁ ≤ q₂
    → S₃ <⦂ S₁
    → S₂ <⦂ S₄
    → (q₁ ^ Fun S₁ S₂) <⦂ (q₂ ^ Fun S₃ S₄)

  SRef :
    q₁ ≤ q₂
    → S₁ <⦂ S₂
    → S₂ <⦂ S₁
    → {wf₁ : q-of S₁ ≤ q₁}
    → {wf₂ : q-of S₂ ≤ q₂}
    → (q₁ ^ Ref S₁ wf₁) <⦂ (q₂ ^ Ref S₂ wf₂)


q-of-mono : S₁ <⦂ S₂ → q-of S₁ ≤ q-of S₂
q-of-mono (SUnit q1≤q2) = q1≤q2
q-of-mono (SBase q1≤q2) = q1≤q2
q-of-mono (SFun q1≤q2 S1<S2 S1<S3) = q1≤q2
q-of-mono (SRef q1≤q2 S1<S2 S2<S1) = q1≤q2


<⦂-antisym : S₁ <⦂ S₂ → S₂ <⦂ S₁ → S₁ ≡ S₂
<⦂-antisym (SUnit x) (SUnit x₁) = cong (_^ Unit) (≤-antisym x x₁)
<⦂-antisym (SBase x) (SBase x₁) = cong (_^ Base) (≤-antisym x x₁)
<⦂-antisym (SFun q₁<q₂ S₁<⦂S₂ S₁<⦂S₃) (SFun q₂<q₁ S₂<⦂S₁ S₂<⦂S₂)
  with refl ← ≤-antisym q₁<q₂ q₂<q₁
  = cong (_ ^_) (cong₂ Fun (<⦂-antisym S₂<⦂S₁ S₁<⦂S₂) (<⦂-antisym S₁<⦂S₃ S₂<⦂S₂))
<⦂-antisym (SRef q₁<q₂ S₁<⦂S₂ S₁<⦂S₃) (SRef q₂<q₁  S₂<⦂S₁ S₂<⦂S₂)
  with refl ← ≤-antisym q₁<q₂ q₂<q₁
  with refl ← <⦂-antisym S₁<⦂S₂ S₂<⦂S₁
  = cong (_ ^_) (cong (Ref _) ≤-irrelevant)

<⦂-refl : S <⦂ S
<⦂-refl {q-of₁ ^ Unit} = SUnit ≤-refl
<⦂-refl {q-of₁ ^ Base} = SBase ≤-refl
<⦂-refl {q-of₁ ^ Fun S₁ S₂} = SFun ≤-refl <⦂-refl <⦂-refl
<⦂-refl {q-of₁ ^ Ref S x} = SRef ≤-refl <⦂-refl <⦂-refl

<⦂-trans : S₁ <⦂ S₂ → S₂ <⦂ S₃ → S₁ <⦂ S₃
<⦂-trans (SUnit x) (SUnit x₁) = SUnit (≤-trans x x₁)
<⦂-trans (SBase x) (SBase x₁) = SBase (≤-trans x x₁)
<⦂-trans (SFun x <⦂-arg₁ <⦂-res₁) (SFun x₁ <⦂-arg₂ <⦂-res₂) = SFun (≤-trans x x₁) (<⦂-trans <⦂-arg₂ <⦂-arg₁) (<⦂-trans <⦂-res₁ <⦂-res₂)
<⦂-trans (SRef x S₁<⦂S₂ S₁<⦂S₃) (SRef x₁ S₂<⦂S₃ S₂<⦂S₄) = SRef (≤-trans x x₁) (<⦂-trans S₁<⦂S₂ S₂<⦂S₃) (<⦂-trans S₂<⦂S₄ S₁<⦂S₃)

data _⊢_⦂_ : Context → Expr → QType → Set where

  TUnit : Γ ⊢ unit ⦂ (q ^ Unit)

  TVar : Γ ∋ x ⦂ S
    →    Γ ⊢ var x ⦂ S

  TAbs : 
    (Γ′ , s ⦂ (q₁ ^ T₁)) ⊢ e ⦂ (q₂ ^ T₂)
    → Γ′ ≡ q-bounded q Γ
    → Γ ⊢ lam (X s q₁) e q₂ ⦂ (q ^ (Fun (q₁ ^ T₁) (q₂ ^ T₂)))

  TApp : Γ ⊢ e₁ ⦂ (𝟚 ^ Fun S₁ S₂)
    → Γ ⊢ e₂ ⦂ S₁
    → Γ ⊢ app e₁ e₂ ⦂ S₂

  TSub : Γ ⊢ e ⦂ S
    → S <⦂ S′
    → Γ ⊢ e ⦂ S′

  TSeq : q₁ ≤ q₂
    → Γ ⊢ e₁ ⦂ (q₁ ^ Unit)
    → Γ ⊢ e₂ ⦂ S
    → q₁ ≤ q-of S
    → Γ ⊢ seq e₁ e₂ ⦂ S

  TRef :
    Γ′ ⊢ e ⦂ S
    → Γ′ ≡ q-bounded q Γ
    → {wf : q-of S ≤ q}
    → Γ ⊢ ref q e ⦂ (q ^ Ref S wf)

  TDeref : {wf : q-of S ≤ q}
    → Γ ⊢ e ⦂ (q ^ Ref S wf)
    → Γ ⊢ deref q e ⦂ S

  TSetref : {wf : q-of S ≤ q}
    → Γ ⊢ e₁ ⦂ (q ^ Ref S wf)
    → Γ ⊢ e₂ ⦂ S′
    → S′ <⦂ S
    → Γ ⊢ setref e₁ e₂ ⦂ (q ^ Unit)


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
  there  : Access 𝓔 s v → Access ⟨ s′ ≔ v′ , 𝓔 ⟩ s v

data GenAccess : Env → Stack → StackMap → Var → Val → Set where

  on-heap   : Access 𝓔 s v → GenAccess 𝓔 𝓢 σ (X s 𝟙) v
  on-stack  : just v ≡ 𝓢 ↓ σ s → GenAccess 𝓔 𝓢 σ (X s 𝟚) v

data [_⦂_] : Val → QType → Set

record _⊨_/_ (Γ : Context) (𝓔 : Env) (𝓢σ : Stack × StackMap) : Set where
  inductive
  constructor mk-⊨
  field
    ⊨-heap : ∀ {s}{T}{v} → Γ ∋ X s 𝟙 ⦂ (𝟙 ^ T) →  Access 𝓔 s v → [ v ⦂ (𝟙 ^ T) ]
    ⊨-stack : let 𝓢 , σ = 𝓢σ in ∀ {s}{q}{T}{v} → Γ ∋ X s 𝟚 ⦂ (q ^ T) → just v ≡ (𝓢 ↓ σ s) → [ v ⦂ (q ^ T) ]
open _⊨_/_ public

rename-bounded : Γ′ ≡ q-bounded q Γ → Γ′ ∋ x ⦂ S → Γ ∋ x ⦂ S
rename-bounded {q = q} {Γ = ∅} {S = S} refl ()
rename-bounded {q = q} {Γ = Γ , s ⦂ S₁} {S = S} Γ′≡ x∈
  with q-of S₁ ≤ᵇ q
... | false = there (rename-bounded Γ′≡ x∈)
rename-bounded {q = q} {Γ , s ⦂ S₁} {S = S} refl (here x) | true = here x
rename-bounded {q = q} {Γ , s ⦂ S₁} {S = S} refl (there x∈) | true = there (rename-bounded refl x∈)

restrict : Γ ⊨ 𝓔 / 𝓢σ → Γ′ ≡ q-bounded q Γ → Γ′ ⊨ 𝓔 / 𝓢σ
restrict {𝓢σ = 𝓢 , σ} Γ⊨ refl = record { ⊨-heap = λ x∈ access → ⊨-heap Γ⊨ (rename-bounded refl x∈) access
                                       ; ⊨-stack = λ x∈ v≡ → ⊨-stack Γ⊨ (rename-bounded refl x∈) v≡ }

access-soundness : Γ ⊨ 𝓔 / 𝓢σ → Γ ∋ X s 𝟙 ⦂ (𝟙 ^ T) → Access 𝓔 s v → [ v ⦂ (𝟙 ^ T) ]
access-soundness Γ⊨ x∈ access = ⊨-heap Γ⊨ x∈ access

genaccess-soundness : Γ ⊨ 𝓔 / (𝓢 , σ) → Γ ∋ x ⦂ (q ^ T) → GenAccess 𝓔 𝓢 σ x v → [ v ⦂ (q ^ T) ]
genaccess-soundness {𝓢 = 𝓢} {σ} {q = 𝟙} Γ⊨ x∈ (on-heap x) = access-soundness Γ⊨ x∈ x
genaccess-soundness {𝓢 = 𝓢} {σ} {q = 𝟚} Γ⊨ x∈ (on-heap x) = ⊥-elim (¬2≤1 (q-var-type x∈))
genaccess-soundness Γ⊨ x∈ (on-stack x) = ⊨-stack Γ⊨ x∈ x


q-bounded-idem : Γ′ ≡ q-bounded q Γ → Γ′ ≡ q-bounded q Γ′
q-bounded-idem {q = q} {∅} refl = refl
q-bounded-idem {q = q} {Γ , s ⦂ S} eq
  with q-of S ≤ᵇ q in eq1
... | false = q-bounded-idem {Γ = Γ} eq
q-bounded-idem {q = q} {Γ , s ⦂ S} refl | true
  with q-of S ≤ᵇ q
... | true = cong (_, s ⦂ S) (q-bounded-idem{Γ = Γ} refl)
... | false
  with eq1
... | ()

-- value typing

data [_⦂_] where {- cf. p 15:11 of WhatIf -}

  TVUnit : [ unit ⦂ (q ^ Unit) ]

  TVCst : [ cst n ⦂ (q ^ Base) ]

  TVClos :
    Γ ⊨ 𝓔 / (𝓢 , σ)
    -- → q-env 𝓔 ≡ q
    → Γ ≡ q-bounded q Γ
    → (Γ , s ⦂ S₁) ⊢ e ⦂ S₂
    → σ? ≡ (case q of λ{ 𝟙 → nothing ; 𝟚 → just σ})
    → let q₂ = q-of S₂ in
      let q₁ = q-of S₁ in
      [ clos 𝓔 σ? (X s q₁) e q₂ ⦂ q ^ Fun S₁ S₂ ]

  -- TVSub : S₁ <⦂ S₂
  --   → [ v ⦂ S₁ ]
  --   → [ v ⦂ S₂ ]

  TVRef : {- construction -}
          {wf : q-of S ≤ q}
    → [ ref q ℓ ⦂ q ^ Ref S wf ]

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

  swrite0 : swrite (vs ∷ 𝓛) ℓ v (vs′ ∷ 𝓛)

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

push : (Stack × StackMap) → Maybe StackMap → (Stack × StackMap)
push (𝓢 , _) (just σ) = 𝓢 , σ
push (𝓢 , _) nothing = ([] ∷⁺ 𝓢) , (λ _ → nothing)

alloc-length : length (alloc 𝓢 v .proj₁ .head) ≡ suc (length (𝓢 .head))
alloc-length {𝓢 = 𝓢}{v = v} = trans (length-++ (𝓢 .head) {[ v ]}) (trans (+-suc (length (𝓢 .head)) zero) (cong suc (+-identityʳ (length (𝓢 .head)))))

postulate
  ↓-alloc : ∀ mn → just v ≡ 𝓢 ↓ mn → just v ≡ alloc 𝓢 v′ .proj₁ ↓ mn
-- ↓-alloc {𝓢 = 𝓢}{v′} (just x) eq
--   with 𝓢 ↓ just x
-- ... | just x₁ rewrite eq = {!!}

postulate
  ⊨-alloc : Γ ⊨ 𝓔 / (𝓢 , σ) → Γ ⊨ 𝓔 / (alloc 𝓢 v .proj₁ , σ)
-- ⊨-alloc {𝓢 = 𝓢} {σ = σ} {v = v} (mk-⊨ ⊨-hp ⊨-st) =
--   mk-⊨ ⊨-hp (λ{ {s = s} x mv → ⊨-st {s = s} x (let vv  = ↓-alloc {𝓢 = 𝓢} {!!} mv in {!!})})


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
       𝓔 , 𝓗 , (𝓢 , σ) ⊢ lam x e q ⇓[ 𝟙 ] clos 𝓔 nothing x e q ⊣ 𝓗 , 𝓢

  EAbsS :
       𝓔 , 𝓗 , (𝓢 , σ) ⊢ lam x e q ⇓[ 𝟚 ] clos 𝓔 (just σ) x e q ⊣ 𝓗 , 𝓢
  
  EAppH :
         𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟚 ] clos 𝓔′ σ? (X s q₁) e 𝟙 ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q₁ ] v₂ ⊣ 𝓗″ , 𝓢″
       → (𝓔′ ⊕ₕ (X s q₁ , v₂)) , 𝓗″ , push (𝓢″ , σ) σ? ⊕ₛ (X s q₁ , v₂) ⊢ e ⇓[ 𝟙 ] v ⊣ 𝓗‴ , 𝓢‴
       → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ app e₁ e₂ ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢
       
  EAppS :
         𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟚 ] clos 𝓔′ σ? (X s q₁) e q₂ ⊣ 𝓗′ , 𝓢′
       → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q₁ ] v₂ ⊣ 𝓗″ , 𝓢″
       → (𝓔′ ⊕ₕ (X s q₁ , v₂)) , 𝓗″ , push (𝓢″ , σ) σ? ⊕ₛ (X s q₁ , v₂) ⊢ e ⇓[ q₂ ] v ⊣ 𝓗‴ , 𝓢‴
        ---------------------------------------------------------
       → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ app e₁ e₂ ⇓[ 𝟚 ] v ⊣ 𝓗‴ , 𝓢‴

  ERefH :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢′
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ ref 𝟙 e ⇓[ 𝟙 ] ref 𝟙 ∣ 𝓗′ ∣ʰ ⊣ 𝓗′ ++ [ v ] , 𝓢′


  ERefS :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
      → (q ≡ 𝟙 → 𝓢″ ≡ 𝓢′ × n ≡ ∣ 𝓗′ ∣ʰ × 𝓗″ ≡ 𝓗 ++ [ v ])
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
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ q ] ref 𝟙 ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q ] v ⊣ 𝓗″ , 𝓢″
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ setref e₁ e₂ ⇓[ 𝟙 ] unit ⊣ 𝓗″ [ ℓ ]≔ v , 𝓢″

  ESetrefS :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟚 ] ref q ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ 𝟚 ] v ⊣ 𝓗″ , 𝓢″
      → (q ≡ 𝟙 → 𝓗‴ ≡ 𝓗″ [ ℓ ]≔ v × 𝓢‴ ≡ 𝓢″)
      → (q ≡ 𝟚 → 𝓗‴ ≡ 𝓗″ × swrite 𝓢″ ℓ v 𝓢‴)
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ setref e₁ e₂ ⇓[ 𝟚 ] unit ⊣ 𝓗‴ , 𝓢‴

  ESeq :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ q ] v₁ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ seq e₁ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
