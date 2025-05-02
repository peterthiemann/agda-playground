module StackBasedBigStep where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_ ; proj₁ ; proj₂)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

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
  ≤-bot  : 𝟙 ≤ q
  ≤-top  : q ≤ 𝟚
  ≤-refl : q ≤ q

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
≤-sound ≤-bot = refl
≤-sound {𝟙} ≤-top = refl
≤-sound {𝟚} ≤-top = refl

≤-complete : q₁ ≤ᵇ q₂ ≡ true → q₁ ≤ q₂
≤-complete {𝟙} {𝟙} ≤b = ≤-bot
≤-complete {𝟙} {𝟚} ≤b = ≤-top
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

data Context : Set where

  ∅ : Context
  _,_⦂_ : (Γ : Context) → (s : Ident) → (S : QType) → Context

variable
  Γ Γ′ : Context
  T T₁ T₂ : Type
  S S′ S₁ S₂ S₃ S₄ : QType

data _∋_⦂_ : Context → Var → QType → Set where

  here   : (Γ , s ⦂ S) ∋ (X s q) ⦂ S
  there  : Γ ∋ x ⦂ S → (Γ , s′ ⦂ S′) ∋ x ⦂ S

q-bound : Context → Qual
q-bound ∅ = 𝟙
q-bound (Γ , _ ⦂ (_ ^ q)) = (q-bound Γ) ⊔ q

q-of : QType → Qual
q-of (T ^ q) = q

q-bounded : Qual → Context → Context
q-bounded q ∅ = ∅
q-bounded q (Γ , s ⦂ S)
  with q-of S ≤ᵇ q
... | false = q-bounded q Γ
... | true = q-bounded q Γ , s ⦂ S

data _<⦂_ : QType → QType → Set where

  SRfl : q₁ ≤ q₂
    → (Unit ^ q₁) <⦂ (Unit ^ q₂)

  SFun : q₁ ≤ q₂
    → S₃ <⦂ S₁
    → S₂ <⦂ S₄
    → (Fun S₁ S₂ ^ q₃) <⦂ (Fun S₃ S₄ ^ q₄)

  SRef : q₁ ≤ q₂
    → S₁ <⦂ S₂
    → q-of S₂ ≤ q₂
    → (Ref S₁ ^ q₁) <⦂ (Ref S₂ ^ q₂)

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

-- value typing

data [_⦂_] : Val → QType → Set where

  TVUnit : [ unit ⦂ (Unit ^ q) ]

  TVCst : [ cst n ⦂ (Base ^ q) ]

  TVClos : {- construction -}
    (Γ , s ⦂ S₁) ⊢ e ⦂ S₂
    → let q₂ = q-of S₂ in
      let q₁ = q-of S₂ in
      [ clos 𝓔 σ? (X s q₁) e q₂ ⦂ Fun S₁ S₂ ^ q ]

  TVRef : {- construction -} [ ref q ℓ ⦂ Ref S ^ q ]

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

postulate _↓_ : Stack → Maybe ℕ → Val

update : StackMap → Ident → ℕ → StackMap
update σ x n = λ s → case (x ≟ s) of λ where
  (no ¬a) → σ s
  (yes a) → just n

-- (H,∅)(x 1) = v
data Access : Env → String → Val → Set where

  here   : Access ⟨ s ≔ v , 𝓔 ⟩ s v
  there  : Access 𝓔 s v → Access ⟨ s′ ≔ v′ , 𝓔 ⟩ s v

data GenAccess : Env → Stack → StackMap → Var → Val → Set where

  on-heap   : Access 𝓔 s v → GenAccess 𝓔 𝓢 σ (X s 𝟙) v
  on-stack  : v ≡ 𝓢 ↓ σ s → GenAccess 𝓔 𝓢 σ (X s 𝟚) v

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
