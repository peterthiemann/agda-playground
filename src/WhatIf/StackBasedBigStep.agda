module StackBasedBigStep where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; proj₁ ; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

Ident = String
StackMap = Ident → Maybe ℕ

data Qual : Set where
  𝟙 𝟚 : Qual
data Var : Set where
  X : Ident → Qual → Var
data Val : Set
data Local : Set where
  ∅ : Local
  ⟨_≔_,_⟩ : Ident → Val → Local → Local
Env = Local
Heap = List Val
data Stack : Set where
  ⟪_⟫ : List Val → Stack
  ⟨_,_⟩ : Stack → List Val → Stack
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

postulate
  _[_]≔_ : List Val → ℕ → Val → List Val
  

variable
  𝓔 𝓔′ : Env
  𝓗 𝓗′ 𝓗″ 𝓗‴ : Heap
  𝓢 𝓢′ 𝓢″ 𝓢‴ : Stack
  σ σ′ σ″ : StackMap
  σ? : Maybe StackMap
  𝓢σ : Stack × StackMap
  s s′ : Ident
  q q₁ q₂ q₃ q₄ : Qual
  v v′ v″ v₁ v₂ : Val
  vs vs′ : List Val
  x : Var
  e e₁ e₂ : Expr
  Φ Φ′ Φ″ : Local
  n ℓ : ℕ


data _≤_ : Qual → Qual → Set where
  ≤-bottop  : 𝟙 ≤ 𝟚
  -- ≤-top  : q ≤ 𝟚
  ≤-refl : q ≤ q

≤-trans : q₁ ≤ q₂ → q₂ ≤ q₃ → q₁ ≤ q₃
≤-trans ≤-bottop ≤-refl = ≤-bottop
≤-trans ≤-refl ≤-bottop = ≤-bottop
≤-trans ≤-refl ≤-refl = ≤-refl

¬2≤1 : ¬ (𝟚 ≤ 𝟙)
¬2≤1 ()

_⊔_ : Qual → Qual → Qual
𝟙 ⊔ q₂ = q₂
𝟚 ⊔ q₂ = 𝟚

_≤ᵇ_ : Qual → Qual → Bool
𝟙 ≤ᵇ q₂ = true
𝟚 ≤ᵇ 𝟙 = false
𝟚 ≤ᵇ 𝟚 = true

≤-sound : q₁ ≤ q₂ → q₁ ≤ᵇ q₂ ≡ true
≤-sound {𝟙} ≤-refl = refl
≤-sound {𝟚} ≤-refl = refl
≤-sound ≤-bottop = refl

≤-complete : q₁ ≤ᵇ q₂ ≡ true → q₁ ≤ q₂
≤-complete {𝟙} {𝟙} ≤b = ≤-refl
≤-complete {𝟙} {𝟚} ≤b = ≤-bottop
≤-complete {𝟚} {𝟚} ≤b = ≤-refl

-- typing

data Type : Set
data QType : Set where
  _^_ : (T : Type) → (q : Qual) → QType

data Type where
  Unit : Type
  Base : Type
  Fun  : (S₁ : QType) → (S₂ : QType) → Type
  Ref  : (S : QType) → Type

q-of : QType → Qual
q-of (T ^ q) = q

q-var : Var → Qual
q-var (X s q) = q


data Context : Set where

  ∅ : Context
  _,_⦂_ : (Γ : Context) → (s : Ident) → (S : QType) → Context

variable
  Γ Γ′ : Context
  T T₁ T₂ : Type
  S S′ S₁ S₂ S₃ S₄ : QType

data wf : QType → Set where

  wf-Unit : wf (Unit ^ q)
  wf-Base : wf (Base ^ q)
  wf-Fun  : wf S₁ → wf S₂ → wf (Fun S₁ S₂ ^ q)
  wf-Ref  : wf S → q-of S ≤ q → wf (Ref S ^ q)

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
q-bound (Γ , _ ⦂ (_ ^ q)) = (q-bound Γ) ⊔ q

q-bounded : Qual → Context → Context
q-bounded q ∅ = ∅
q-bounded q (Γ , s ⦂ S)
  with q-of S ≤ᵇ q
... | false = q-bounded q Γ
... | true = q-bounded q Γ , s ⦂ S



data _<⦂_ : QType → QType → Set where

  SRfl : q₁ ≤ q₂
    → (Unit ^ q₁) <⦂ (Unit ^ q₂)

  SBase : q₁ ≤ q₂
    → (Base ^ q₁) <⦂ (Base ^ q₂)

  SFun : q₁ ≤ q₂
    → S₃ <⦂ S₁
    → S₂ <⦂ S₄
    → (Fun S₁ S₂ ^ q₁) <⦂ (Fun S₃ S₄ ^ q₂)

  SRef : 
    q₁ ≤ q₂
    → S₁ <⦂ S₂
    → q-of S₂ ≤ q₂
    → (Ref S₁ ^ q₁) <⦂ (Ref S₂ ^ q₂)

<⦂-refl : wf S → S <⦂ S
<⦂-refl wf-Unit = SRfl ≤-refl
<⦂-refl wf-Base = SBase ≤-refl
<⦂-refl (wf-Fun wf₁ wf₂) = SFun ≤-refl (<⦂-refl wf₁) (<⦂-refl wf₂)
<⦂-refl (wf-Ref wf₁ x) = SRef ≤-refl (<⦂-refl wf₁) x

<⦂-trans : S₁ <⦂ S₂ → S₂ <⦂ S₃ → S₁ <⦂ S₃
<⦂-trans (SRfl q1q2) (SRfl q2q3) = SRfl (≤-trans q1q2 q2q3)
<⦂-trans (SBase q1q2) (SBase q2q3) = SBase (≤-trans q1q2 q2q3)
<⦂-trans (SFun q1q2 S1S2 S1S3) (SFun q2q3 S2S3 S2S4) = SFun (≤-trans q1q2 q2q3) (<⦂-trans S2S3 S1S2) (<⦂-trans S1S3 S2S4)
<⦂-trans (SRef q1q2 S1S2 x₁) (SRef q2q3 S2S3 x₂) = SRef (≤-trans q1q2 q2q3) (<⦂-trans S1S2 S2S3) x₂

data _⊢_⦂_ : Context → Expr → QType → Set where

  TUnit : Γ ⊢ unit ⦂ (Unit ^ q)

  TVar : Γ ∋ x ⦂ S
    →    Γ ⊢ var x ⦂ S

  TAbs : (Γ′ , s ⦂ (T₁ ^ q₁)) ⊢ e ⦂ (T₂ ^ q₂)
    → Γ′ ≡ q-bounded q Γ
    → Γ ⊢ lam (X s q₁) e q₂ ⦂ ((Fun (T₁ ^ q₁) (T₂ ^ q₂)) ^ q)

  TApp : Γ ⊢ e₁ ⦂ (Fun S₁ S₂ ^ 𝟚)
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

  TRef : Γ′ ⊢ e ⦂ S
    → Γ′ ≡ q-bounded q Γ
    → Γ ⊢ ref q e ⦂ (Ref S ^ q)

  TDeref : Γ ⊢ e ⦂ (Ref S ^ q)
    → Γ ⊢ deref q e ⦂ S

  TSetref : Γ ⊢ e₁ ⦂ (Ref S ^ q)
    → Γ ⊢ e₂ ⦂ S′
    → S′ <⦂ S
    → Γ ⊢ setref e₁ e₂ ⦂ (Unit ^ q)

--

q-of-mono : S₁ <⦂ S₂ → q-of S₁ ≤ q-of S₂
q-of-mono (SRfl q1≤q2) = q1≤q2
q-of-mono (SBase q1≤q2) = q1≤q2
q-of-mono (SFun q1≤q2 S1<S2 S1<S3) = q1≤q2
q-of-mono (SRef q1≤q2 S1<S2 x₁) = q1≤q2


-- heap & stack typing

postulate _↓_ : Stack → Maybe ℕ → Val

-- (H,∅)(x 1) = v
data Access : Env → String → Val → Set where

  here   : Access ⟨ s ≔ v , 𝓔 ⟩ s v
  there  : Access 𝓔 s v → Access ⟨ s′ ≔ v′ , 𝓔 ⟩ s v

data GenAccess : Env → Stack → StackMap → Var → Val → Set where

  on-heap   : Access 𝓔 s v → GenAccess 𝓔 𝓢 σ (X s 𝟙) v
  on-stack  : v ≡ 𝓢 ↓ σ s → GenAccess 𝓔 𝓢 σ (X s 𝟚) v

data [_⦂_] : Val → QType → Set

record _⊨_/_ (Γ : Context) (𝓔 : Env) (𝓢σ : Stack × StackMap) : Set where
  inductive
  field
    ⊨-heap : ∀ {s}{T}{v} → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) →  Access 𝓔 s v → [ v ⦂ (T ^ 𝟙) ]
    ⊨-stack : let 𝓢 , σ = 𝓢σ in ∀ {s}{T}{v}{q} → Γ ∋ X s 𝟚 ⦂ (T ^ q) → v ≡ (𝓢 ↓ σ s) → [ v ⦂ (T ^ q) ]
open _⊨_/_

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

access-soundness : Γ ⊨ 𝓔 / 𝓢σ → Γ ∋ X s 𝟙 ⦂ (T ^ 𝟙) → Access 𝓔 s v → [ v ⦂ (T ^ 𝟙) ]
access-soundness Γ⊨ x∈ access = ⊨-heap Γ⊨ x∈ access

genaccess-soundness : Γ ⊨ 𝓔 / (𝓢 , σ) → Γ ∋ x ⦂ (T ^ q) → GenAccess 𝓔 𝓢 σ x v → [ v ⦂ (T ^ q) ]
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

  TVUnit : [ unit ⦂ (Unit ^ q) ]

  TVCst : [ cst n ⦂ (Base ^ q) ]

  TVClos :
    Γ ⊨ 𝓔 / (𝓢 , σ)
    -- → q-env 𝓔 ≡ q
    → Γ ≡ q-bounded q Γ
    → (Γ , s ⦂ S₁) ⊢ e ⦂ S₂
    → σ? ≡ (case q of λ{ 𝟙 → nothing ; 𝟚 → just σ})
    → let q₂ = q-of S₂ in
      let q₁ = q-of S₁ in
      [ clos 𝓔 σ? (X s q₁) e q₂ ⦂ Fun S₁ S₂ ^ q ]

  TVSub : S₁ <⦂ S₂
    → [ v ⦂ S₁ ]
    → [ v ⦂ S₂ ]

  TVRef : {- construction -}
    [ ref q ℓ ⦂ Ref S ^ q ]

-- operational semantics

data read : List Val → ℕ → Val → Set where

  read0 : read (v ∷ vs) zero v
  read1 : read vs n v → read (v′ ∷ vs) (suc n) v

data sread : Stack → ℕ → Val → Set where

  sread0 : read vs ℓ v → sread ⟪ vs ⟫ ℓ v
  sread1 : read vs ℓ v → sread ⟨ 𝓢 , vs ⟩ ℓ v

data write : List Val → ℕ → Val → List Val → Set where

  write0 : write (v′ ∷ vs) zero v (v ∷ vs)
  write1 : write vs n v vs′ → write (v′ ∷ vs) (suc n) v (v′ ∷ vs′)

data swrite : Stack → ℕ → Val → Stack → Set where

  swrite0 : swrite ⟪ vs ⟫ ℓ v ⟪ vs′ ⟫
  swrite1 : swrite ⟨ 𝓢 , vs ⟩ ℓ v ⟨ 𝓢 , vs′ ⟩

infix 30 ⟨_,_⟩

∣_∣ʰ = length

∣_∣ˢ : Stack → ℕ
∣ ⟪ vs ⟫ ∣ˢ = length vs
∣ ⟨ 𝓢 , vs ⟩ ∣ˢ = length vs

update : StackMap → Ident → ℕ → StackMap
update σ x n = λ s → case (x ≟ s) of λ where
  (no ¬a) → σ s
  (yes a) → just n

_⊕ₕ_ : Env → (Var × Val) → Env
𝓔 ⊕ₕ (X s 𝟙 , v) = ⟨ s ≔ v , 𝓔 ⟩
𝓔 ⊕ₕ (X s 𝟚 , v) = 𝓔

_⊕ₛ_ : (Stack × StackMap) → (Var × Val) → (Stack × StackMap)
(𝓢 , σ) ⊕ₛ (X s 𝟙 , v) = (𝓢 , σ)
(⟪ vs ⟫ , σ) ⊕ₛ (X s 𝟚 , v) = ⟪ (vs ++ [ v ]) ⟫ , update σ s (length vs)
(⟨ 𝓢 , vs ⟩ , σ) ⊕ₛ (X s 𝟚 , v) = ⟨ 𝓢 , vs ++ [ v ] ⟩ , update σ s (length vs)

alloc : Stack → Val → Stack × ℕ
alloc ⟪ vs ⟫ v = ⟪ vs ++ [ v ] ⟫ , length vs
alloc ⟨ 𝓢 , vs ⟩ v = ⟨ 𝓢 , vs ++ [ v ] ⟩ , length vs

push : (Stack × StackMap) → Maybe StackMap → (Stack × StackMap)
push (𝓢 , _) (just σ) = 𝓢 , σ
push (𝓢 , _) nothing = ⟨ 𝓢 , [] ⟩ , (λ _ → nothing)

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
       → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ app e₁ e₂ ⇓[ 𝟚 ] v ⊣ 𝓗‴ , 𝓢‴

  ERefH :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ 𝟙 ] v ⊣ 𝓗′ , 𝓢′
        ---------------------------------------------------------
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ ref 𝟙 e ⇓[ 𝟙 ] ref 𝟙 ∣ 𝓗′ ∣ʰ ⊣ 𝓗′ ++ [ v ] , 𝓢′


  ERefS :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e ⇓[ q ] v ⊣ 𝓗′ , 𝓢′
        --------------------------------------------------
      → let (𝓢″ , n) = alloc 𝓢′ v in
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ ref q e ⇓[ 𝟚 ] ref 𝟚 n ⊣ 𝓗′ , 𝓢″

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
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ setref e₁ e₂ ⇓[ 𝟙 ] unit ⊣ 𝓗″ [ ℓ ]≔ v , 𝓢″

  ESetrefS :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ 𝟚 ] ref q ℓ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ 𝟚 ] v ⊣ 𝓗″ , 𝓢″
      → (q ≡ 𝟙 → 𝓗‴ ≡ 𝓗″ [ ℓ ]≔ v × 𝓢‴ ≡ 𝓢″)
      → (q ≡ 𝟚 → 𝓗‴ ≡ 𝓗″ × swrite 𝓢″ ℓ v 𝓢‴)
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ setref e₁ e₂ ⇓[ 𝟚 ] unit ⊣ 𝓗‴ , 𝓢‴

  ESeq :
        𝓔 , 𝓗 , (𝓢 , σ) ⊢ e₁ ⇓[ q ] v₁ ⊣ 𝓗′ , 𝓢′
      → 𝓔 , 𝓗′ , (𝓢′ , σ) ⊢ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
      → 𝓔 , 𝓗 , (𝓢 , σ) ⊢ seq e₁ e₂ ⇓[ q ] v₂ ⊣ 𝓗″ , 𝓢″
