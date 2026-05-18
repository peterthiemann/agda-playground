module SimplyExprQuotient where

open import Level using (Level) renaming (zero to lzero)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; foldr; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; +-identityʳ; +-assoc)
open import Data.Fin using (Fin)
open import Data.Product using (Σ ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_;_⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; cong; cong₂; sym; subst; trans)

open import Interval

open import Numeri
open import Types
open import Expressions

-- expressions

variable m n : ℕ

-- renaming and substitution

open import Substitution

-- values

open import Values

fold-to-singleton : ∀ {n} {e : Expr zero} {P : Pred (Expr zero) lzero} → (∀ {x} → P x → Expr n) → Atomic e → ALL P e → Expr n
fold-to-singleton f (e≢ε , snd) Aε = ⊥-elim (e≢ε refl)
fold-to-singleton f (fst , e≢·) (all-e A· all-e₁) = ⊥-elim (e≢· refl)
fold-to-singleton f (fst , snd) (AP x) = f x

fold-to-list : ∀ {n} {e : Expr zero} {P : Pred (Expr zero) lzero} → (∀ {x} → P x → Expr n) → Value e → ALL P e → List (Expr n)
fold-to-list f vε Aε = []
fold-to-list f vε (AP x) =  f x ∷ []
fold-to-list f ((val-e v· val-e₁) {v≢ε = v≢ε}{v≢· = v≢·}) (all-e A· all-e₁) = (fold-to-singleton f (v≢ε , v≢·) all-e) ∷ fold-to-list f val-e₁ all-e₁
fold-to-list f (val-e v· val-e₁) (AP {e≢· = e≢·} x) = ⊥-elim (e≢· refl)
fold-to-list f cst (AP x) = f x ∷ []
fold-to-list f abs (AP x) = f x ∷ []
fold-to-list f mab (AP x) = f x ∷ []

-- reduction

data _⟶_ : Expr zero → Expr zero → Set where

  ξ-app₁ : ∀ {s₁}{s₁′}{s₂}
    → s₁ ⟶ s₁′
    → app s₁ s₂ ⟶ app s₁′ s₂

  ξ-app₂ : ∀ {s₁}{s₂}{s₂′}
    → Value s₁
    → s₂ ⟶ s₂′
    → app s₁ s₂ ⟶ app s₁ s₂′

  ξ-head : ∀ {e}{e′}{s}
    → e ⟶ e′
    → (e · s) ⟶ (e′ · s)

  ξ-tail : ∀ {e}{s}{s′}
    → Value e
    → s ⟶ s′
    → (e · s) ⟶ (e · s′)

  mon-ε-unit-left : ∀ {e}
    → (ε · e) ⟶ e

  mon-ε-unit-right : ∀ {e}
    → (e · ε) ⟶ e

  mon-·-assoc : ∀ {e₁ e₂ e₃}
    → ((e₁ · e₂) · e₃) ⟶ (e₁ · (e₂ · e₃))

  β₁ : ∀ {s}{w}
    → Value s
    → (abs₁ : ALL AbsValue s)
    → Value w
    → app s w ⟶ mapE (λ v → mapE (λ b → sub₁ v b) (foldALL absbody abs₁)) w

  βₙ : ∀ {s}{w}
    → Value s
    → (mab₁ : ALL MabValue s)
    → Value w
    → app s w ⟶ mapE (sub₁ w) (foldALL mabbody mab₁)
--    → app s w ⟶ foldALL (sub₁ w ∘ mabbody) mab₁

data _⟶'_ : Expr zero → Expr zero → Set where

  βₙ : ∀ {s}{w}
    → (val-s : Value s)
    → (mab₁ : ALL MabValue s)
    → Value w
    → app s w ⟶' let bodies = fold-to-list mabbody val-s mab₁
                   in  foldr (λ b e₀ → sub₁ w b · e₀) ε bodies

data _⟶*_ : Expr zero → Expr zero → Set where
  ⟶-refl : ∀ {e*} → e* ⟶* e*
  ⟶-step : ∀ {e₁* e₂* e₃*} → e₁* ⟶ e₂* → e₂* ⟶* e₃* → e₁* ⟶* e₃*

data Monoidal-Red : ∀ {e₁ e₂} → e₁ ⟶ e₂ → Set where
  mon-ε-unit-left : ∀ {e}
    → Monoidal-Red (mon-ε-unit-left {e})

  mon-ε-unit-right : ∀ {e}
    → Monoidal-Red (mon-ε-unit-right {e})

  mon-·-assoc : ∀ {e₁ e₂ e₃}
    → Monoidal-Red (mon-·-assoc {e₁}{ e₂}{ e₃})

  m-ξ-head : ∀ {e e′ s} {e⟶e′ : e ⟶ e′}
    → Monoidal-Red e⟶e′
    → Monoidal-Red (ξ-head {s = s} e⟶e′)

  m-ξ-tail : ∀ {e s s′} (val-e : Value e) {s⟶s′ : s ⟶ s′}
    → Monoidal-Red s⟶s′
    → Monoidal-Red (ξ-tail val-e s⟶s′)
  

data Monoidal-Red* : ∀ {e₁ e₂} → e₁ ⟶* e₂ → Set where
  ⟶-refl : ∀ {e} → Monoidal-Red* {e}{e} ⟶-refl
  ⟶-step : ∀ {e₁ e₂ e₃} {e₁⟶e₂ : e₁ ⟶ e₂} {e₂⟶*e₃ : e₂ ⟶* e₃} → Monoidal-Red (e₁⟶e₂) → Monoidal-Red* (e₂⟶*e₃) → Monoidal-Red* (⟶-step e₁⟶e₂ e₂⟶*e₃)
  


ξ-* : ∀{s}{s′} → {f : Expr 0 → Expr 0} (tag : ∀ {e₁ e₂} → e₁ ⟶ e₂ → f e₁ ⟶ f e₂) → s ⟶* s′ → f s ⟶* f s′
ξ-* tag ⟶-refl = ⟶-refl
ξ-* tag (⟶-step x red) = ⟶-step (tag x) (ξ-* tag red)

ξ-tail-* : ∀ {e}{s}{s′} → Value e → s ⟶* s′ → (e · s) ⟶* (e · s′)
ξ-tail-* val-e = ξ-* (ξ-tail val-e)

ξ-head-* : ∀ {e e′ s} → e ⟶* e′ → (e · s) ⟶* (e′ · s)
ξ-head-* = ξ-* ξ-head

ξ-app₁-* : ∀ {e e′ s} → e ⟶* e′ → (app e s) ⟶* (app e′ s)
ξ-app₁-* = ξ-* ξ-app₁

ξ-app₂-* : ∀ {e}{s}{s′} → Value e → s ⟶* s′ → (app e s) ⟶* (app e s′)
ξ-app₂-* val-e = ξ-* (ξ-app₂ val-e)

⟶*-snoc : ∀ {e₁ e₂ e₃} → e₁ ⟶* e₂ → e₂ ⟶ e₃ → e₁ ⟶* e₃
⟶*-snoc ⟶-refl step = ⟶-step step ⟶-refl
⟶*-snoc (⟶-step x red) step = ⟶-step x (⟶*-snoc red step)

⟶*-trans : ∀ {e₁ e₂ e₃} → e₁ ⟶* e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃
⟶*-trans red₁ ⟶-refl = red₁
⟶*-trans red₁ (⟶-step x red₂) = ⟶*-trans (⟶*-snoc red₁ x) red₂

m-ξ-head-* : ∀ {e e′ s} {red : e ⟶* e′} → Monoidal-Red* red → Monoidal-Red* (ξ-head-* red)
m-ξ-head-* Monoidal-Red*.⟶-refl = Monoidal-Red*.⟶-refl
m-ξ-head-* {s = s} (Monoidal-Red*.⟶-step {e₁⟶e₂ = step} mred mreds)
  = Monoidal-Red*.⟶-step {e₁⟶e₂ = ξ-head {s = s} step} (m-ξ-head {s = s} mred) (m-ξ-head-* {s = s} mreds)

m-ξ-tail-* : ∀ {e s s′} (val-e : Value e) {red : s ⟶* s′} → Monoidal-Red* red → Monoidal-Red* (ξ-tail-* val-e red)
m-ξ-tail-* val-e Monoidal-Red*.⟶-refl = Monoidal-Red*.⟶-refl
m-ξ-tail-* val-e (Monoidal-Red*.⟶-step {e₁⟶e₂ = step} mred mreds)
  = Monoidal-Red*.⟶-step {e₁⟶e₂ = ξ-tail val-e step} (m-ξ-tail val-e mred) (m-ξ-tail-* val-e mreds)

Monoidal-Red*-snoc : ∀ {e₁ e₂ e₃} {red : e₁ ⟶* e₂} {step : e₂ ⟶ e₃}
  → Monoidal-Red* red → Monoidal-Red step → Monoidal-Red* (⟶*-snoc red step)
Monoidal-Red*-snoc Monoidal-Red*.⟶-refl mstep = Monoidal-Red*.⟶-step mstep Monoidal-Red*.⟶-refl
Monoidal-Red*-snoc (Monoidal-Red*.⟶-step mred mreds) mstep = Monoidal-Red*.⟶-step mred (Monoidal-Red*-snoc mreds mstep)

Monoidal-Red*-trans : ∀ {e₁ e₂ e₃} {red₁ : e₁ ⟶* e₂} {red₂ : e₂ ⟶* e₃}
  → Monoidal-Red* red₁ → Monoidal-Red* red₂ → Monoidal-Red* (⟶*-trans red₁ red₂)
Monoidal-Red*-trans mreds₁ Monoidal-Red*.⟶-refl = mreds₁
Monoidal-Red*-trans mreds₁ (Monoidal-Red*.⟶-step mred mreds₂) = Monoidal-Red*-trans (Monoidal-Red*-snoc mreds₁ mred) mreds₂

Atom : Set
Atom = Σ (Expr zero) (λ e → Value e × NonEmpty e × NonConcat e)

atoms : ∀ {e} → ALL Value e → List Atom
atoms Aε = []
atoms (all₁ A· all₂) = atoms all₁ ++ atoms all₂
atoms (AP {e = e} {e≢ε = e≢ε} {e≢· = e≢·} v) = (e , (v , e≢ε , (λ {x} {y} e≡x·y → e≢· e≡x·y))) ∷ []

pack : List Atom → Expr zero
pack [] = ε
pack ((e , _) ∷ []) = e
pack ((e , _) ∷ a₂ ∷ as) = e · pack (a₂ ∷ as)

pack-nonempty : ∀ {a as} → NonEmpty (pack (a ∷ as))
pack-nonempty {(e , (_ , e≢ε , _))} {[]} = e≢ε
pack-nonempty {a} {a₂ ∷ as} ()

pack-value : ∀ as → Value (pack as)
pack-value [] = vε
pack-value ((e , (v , _ , _)) ∷ []) = v
pack-value ((e , (v , e≢ε , e≢·)) ∷ a₂ ∷ as)
  = ((v v· pack-value (a₂ ∷ as))
      {v≢ε = e≢ε}
      {w≢ε = λ eqε → pack-nonempty {a = a₂} {as = as} eqε}
      {v≢· = λ {x} {y} e≡x·y → e≢· e≡x·y})

pack-append : ∀ xs ys → (pack xs · pack ys) ⟶* pack (xs ++ ys)
pack-append [] ys = ⟶-step mon-ε-unit-left ⟶-refl
pack-append (a ∷ []) [] = ⟶-step mon-ε-unit-right ⟶-refl
pack-append (a ∷ []) (a₂ ∷ as) = ⟶-refl
pack-append ((e , (v , e≢ε , e≢·)) ∷ a₂ ∷ as) ys
  = ⟶-step mon-·-assoc (ξ-tail-* v (pack-append (a₂ ∷ as) ys))

normalize-all : ∀ {e} (allv : ALL Value e) → e ⟶* pack (atoms allv)
normalize-all Aε = ⟶-refl
normalize-all (all₁ A· all₂)
  = ⟶*-trans
      (⟶*-trans
        (ξ-head-* (normalize-all all₁))
        (ξ-tail-* (pack-value (atoms all₁)) (normalize-all all₂)))
      (pack-append (atoms all₁) (atoms all₂))
normalize-all (AP {e = e} v) = ⟶-refl

all-pres-mono : ∀ {e e′} {step : e ⟶ e′} → ALL Value e → Monoidal-Red step → ALL Value e′
all-pres-mono (Aε A· all₂) Monoidal-Red.mon-ε-unit-left = all₂
all-pres-mono (AP {e≢ε = e≢ε} x A· all₂) Monoidal-Red.mon-ε-unit-left = ⊥-elim (e≢ε refl)
all-pres-mono (all₁ A· Aε) Monoidal-Red.mon-ε-unit-right = all₁
all-pres-mono (all₁ A· AP {e≢ε = e≢ε} x) Monoidal-Red.mon-ε-unit-right = ⊥-elim (e≢ε refl)
all-pres-mono ((all₁ A· all₂) A· all₃) Monoidal-Red.mon-·-assoc = all₁ A· (all₂ A· all₃)
all-pres-mono (AP {e≢· = e≢·} x A· all₃) Monoidal-Red.mon-·-assoc = ⊥-elim (e≢· refl)
all-pres-mono (all₁ A· all₂) (m-ξ-head mred) = all-pres-mono all₁ mred A· all₂
all-pres-mono (all₁ A· all₂) (m-ξ-tail _ mred) = all₁ A· all-pres-mono all₂ mred
all-pres-mono (AP {e≢· = e≢·} x) (m-ξ-head mred) = ⊥-elim (e≢· refl)
all-pres-mono (AP {e≢· = e≢·} x) (m-ξ-tail _ mred) = ⊥-elim (e≢· refl)
all-pres-mono (AP {e≢· = e≢·} x) Monoidal-Red.mon-ε-unit-left = ⊥-elim (e≢· refl)
all-pres-mono (AP {e≢· = e≢·} x) Monoidal-Red.mon-ε-unit-right = ⊥-elim (e≢· refl)
all-pres-mono (AP {e≢· = e≢·} x) Monoidal-Red.mon-·-assoc = ⊥-elim (e≢· refl)

all-pres-mono* : ∀ {e e′} {red : e ⟶* e′} → ALL Value e → Monoidal-Red* red → ALL Value e′
all-pres-mono* all Monoidal-Red*.⟶-refl = all
all-pres-mono* all (Monoidal-Red*.⟶-step mred mreds) = all-pres-mono* (all-pres-mono all mred) mreds

atomsE : ∀ {e} → ALL Value e → List (Expr zero)
atomsE Aε = []
atomsE (all₁ A· all₂) = atomsE all₁ ++ atomsE all₂
atomsE (AP {e = e} x) = e ∷ []

atomsE-unique : ∀ {e} (all₁ all₂ : ALL Value e) → atomsE all₁ ≡ atomsE all₂
atomsE-unique Aε Aε = refl
atomsE-unique Aε (AP {e≢ε = e≢ε} x) = ⊥-elim (e≢ε refl)
atomsE-unique (all₁ A· all₂) (all₁′ A· all₂′) = cong₂ _++_ (atomsE-unique all₁ all₁′) (atomsE-unique all₂ all₂′)
atomsE-unique (all₁ A· all₂) (AP {e≢· = e≢·} x) = ⊥-elim (e≢· refl)
atomsE-unique (AP {e≢ε = e≢ε} x) Aε = ⊥-elim (e≢ε refl)
atomsE-unique (AP {e≢· = e≢·} x) (all₁ A· all₂) = ⊥-elim (e≢· refl)
atomsE-unique (AP {e = e} x) (AP {e = .e} x₁) = refl

atomsE-map : ∀ {e} (all : ALL Value e) → map proj₁ (atoms all) ≡ atomsE all
atomsE-map Aε = refl
atomsE-map (all₁ A· all₂)
  rewrite map-++ proj₁ (atoms all₁) (atoms all₂)
        | atomsE-map all₁
        | atomsE-map all₂
  = refl
atomsE-map (AP {e = e} x) = refl

packE : List (Expr zero) → Expr zero
packE [] = ε
packE (e ∷ []) = e
packE (e ∷ e₁ ∷ es) = e · packE (e₁ ∷ es)

pack-map : ∀ as → pack as ≡ packE (map proj₁ as)
pack-map [] = refl
pack-map (a ∷ []) = refl
pack-map (a ∷ a₁ ∷ as) rewrite pack-map (a₁ ∷ as) = refl

pack-atomsE : ∀ {e} (all : ALL Value e) → pack (atoms all) ≡ packE (atomsE all)
pack-atomsE all = trans (pack-map (atoms all)) (cong packE (atomsE-map all))

atomsE-pres-mono : ∀ {e e′} {step : e ⟶ e′} (all : ALL Value e) (mred : Monoidal-Red step)
  → atomsE all ≡ atomsE (all-pres-mono all mred)
atomsE-pres-mono (Aε A· all₂) Monoidal-Red.mon-ε-unit-left
  = atomsE-unique all₂ (all-pres-mono (Aε A· all₂) Monoidal-Red.mon-ε-unit-left)
atomsE-pres-mono (AP {e≢ε = e≢ε} x A· all₂) Monoidal-Red.mon-ε-unit-left = ⊥-elim (e≢ε refl)
atomsE-pres-mono (all₁ A· Aε) Monoidal-Red.mon-ε-unit-right
  = trans
      (++-identityʳ (atomsE all₁))
      (atomsE-unique all₁ (all-pres-mono (all₁ A· Aε) Monoidal-Red.mon-ε-unit-right))
atomsE-pres-mono (all₁ A· AP {e≢ε = e≢ε} x) Monoidal-Red.mon-ε-unit-right = ⊥-elim (e≢ε refl)
atomsE-pres-mono ((all₁ A· all₂) A· all₃) Monoidal-Red.mon-·-assoc
  = trans
      (++-assoc (atomsE all₁) (atomsE all₂) (atomsE all₃))
      (atomsE-unique (all₁ A· (all₂ A· all₃)) (all-pres-mono ((all₁ A· all₂) A· all₃) Monoidal-Red.mon-·-assoc))
atomsE-pres-mono (AP {e≢· = e≢·} x A· all₃) Monoidal-Red.mon-·-assoc = ⊥-elim (e≢· refl)
atomsE-pres-mono (all₁ A· all₂) (m-ξ-head mred)
  = trans
      (cong (λ xs → xs ++ atomsE all₂) (atomsE-pres-mono all₁ mred))
      (atomsE-unique
        (all-pres-mono all₁ mred A· all₂)
        (all-pres-mono (all₁ A· all₂) (m-ξ-head mred)))
atomsE-pres-mono (all₁ A· all₂) (m-ξ-tail val-e mred)
  = trans
      (cong (λ xs → atomsE all₁ ++ xs) (atomsE-pres-mono all₂ mred))
      (atomsE-unique
        (all₁ A· all-pres-mono all₂ mred)
        (all-pres-mono (all₁ A· all₂) (m-ξ-tail val-e mred)))
atomsE-pres-mono (AP {e≢· = e≢·} x) (m-ξ-head mred) = ⊥-elim (e≢· refl)
atomsE-pres-mono (AP {e≢· = e≢·} x) (m-ξ-tail _ mred) = ⊥-elim (e≢· refl)
atomsE-pres-mono (AP {e≢· = e≢·} x) Monoidal-Red.mon-ε-unit-left = ⊥-elim (e≢· refl)
atomsE-pres-mono (AP {e≢· = e≢·} x) Monoidal-Red.mon-ε-unit-right = ⊥-elim (e≢· refl)
atomsE-pres-mono (AP {e≢· = e≢·} x) Monoidal-Red.mon-·-assoc = ⊥-elim (e≢· refl)

atomsE-pres-mono* : ∀ {e e′} {red : e ⟶* e′} (all : ALL Value e) (mreds : Monoidal-Red* red)
  → atomsE all ≡ atomsE (all-pres-mono* all mreds)
atomsE-pres-mono* all Monoidal-Red*.⟶-refl = refl
atomsE-pres-mono* all (Monoidal-Red*.⟶-step mred mreds)
  = trans
      (atomsE-pres-mono all mred)
      (atomsE-pres-mono* (all-pres-mono all mred) mreds)

monoidal-confluence-ALL
  : ∀ {v v₁ v₂}
  → ALL Value v
  → {red₁ : v ⟶* v₁} {red₂ : v ⟶* v₂}
  → Monoidal-Red* red₁
  → Monoidal-Red* red₂
  → ∃[ w ] v₁ ⟶* w × v₂ ⟶* w
monoidal-confluence-ALL {v = v} {v₁ = v₁} {v₂ = v₂} allv mred₁ mred₂ =
  let allv₁ = all-pres-mono* allv mred₁
      allv₂ = all-pres-mono* allv mred₂
      red₁  = normalize-all allv₁
      red₂  = normalize-all allv₂
      eq₁   = atomsE-pres-mono* allv mred₁
      eq₂   = atomsE-pres-mono* allv mred₂
      eqE   = trans (sym eq₁) eq₂
      red₁′ = subst (λ t → v₁ ⟶* t) (pack-atomsE allv₁) red₁
      red₂′ = subst (λ t → v₂ ⟶* t) (pack-atomsE allv₂) red₂
      red₂″ = subst (λ t → v₂ ⟶* t) (sym (cong packE eqE)) red₂′
  in packE (atomsE allv₁)
   , red₁′
   , red₂″

-- reduction properties

value-· : ∀ {e₁ e₂ : Expr zero} → Value e₁ → Value e₂ → ∃[ w ] Value w × (e₁ · e₂) ⟶* w
value-· {e₂ = e₂} vε v₂ = e₂ , v₂ , (⟶-step mon-ε-unit-left ⟶-refl)
value-· (_v·_  {v = e₁} v₁ v₃ {v≢ε}{w≢ε}{v≢·}) v₂
  with value-· v₃ v₂
... | _ , vε , red =
  e₁
  , v₁
  , ⟶-step mon-·-assoc (⟶*-snoc (ξ-tail-* v₁ red) mon-ε-unit-right)
... | e₃₂ , ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}) , red =
  e₁ · e₃₂
  , ((v₁ v· ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}))
      {v≢ε = v≢ε}
      {w≢ε = λ ()}
      {v≢· = v≢·})
  , ⟶-step mon-·-assoc (ξ-tail-* v₁ red)
... | e₃₂ , cst , red =
  e₁ · e₃₂
  , ((v₁ v· cst)
      {v≢ε = v≢ε}
      {w≢ε = λ ()}
      {v≢· = v≢·})
  , ⟶-step mon-·-assoc (ξ-tail-* v₁ red)
... | e₃₂ , abs , red =
  e₁ · e₃₂
  , ((v₁ v· abs)
      {v≢ε = v≢ε}
      {w≢ε = λ ()}
      {v≢· = v≢·})
  , ⟶-step mon-·-assoc (ξ-tail-* v₁ red)
... | e₃₂ , mab , red =
  e₁ · e₃₂
  , ((v₁ v· mab)
      {v≢ε = v≢ε}
      {w≢ε = λ ()}
      {v≢· = v≢·})
  , ⟶-step mon-·-assoc (ξ-tail-* v₁ red)
value-· {e₂ = e₂} cst v₂ with v₂
... | vε = cst _ , cst , ⟶-step mon-ε-unit-right ⟶-refl
... | ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}) =
  (cst _ · e₂)
  , ((cst v· ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}))
      {v≢ε = λ ()}
      {w≢ε = λ ()}
      {v≢· = λ {e₁} {e₂} ()})
  , ⟶-refl
... | cst = (cst _ · e₂) , ((cst v· cst) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
... | abs = (cst _ · e₂) , ((cst v· abs) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
... | mab = (cst _ · e₂) , ((cst v· mab) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
value-· {e₂ = e₂} (abs {μ = μ} {e* = e*}) v₂ with v₂
... | vε = abs μ e* , abs , ⟶-step mon-ε-unit-right ⟶-refl
... | ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}) =
  (abs μ e* · e₂)
  , ((abs v· ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}))
      {v≢ε = λ ()}
      {w≢ε = λ ()}
      {v≢· = λ {e₁} {e₂} ()})
  , ⟶-refl
... | cst = (abs μ e* · e₂) , ((abs v· cst) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
... | abs = (abs μ e* · e₂) , ((abs v· abs) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
... | mab = (abs μ e* · e₂) , ((abs v· mab) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
value-· {e₂ = e₂} (mab {ημ = ημ} {e* = e*}) v₂ with v₂
... | vε = mab ημ e* , mab , ⟶-step mon-ε-unit-right ⟶-refl
... | ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}) =
  (mab ημ e* · e₂)
  , ((mab v· ((vv v· vw) {v≢ε = vv≢ε} {w≢ε = vw≢ε} {v≢· = vv≢·}))
      {v≢ε = λ ()}
      {w≢ε = λ ()}
      {v≢· = λ {e₁} {e₂} ()})
  , ⟶-refl
... | cst = (mab ημ e* · e₂) , ((mab v· cst) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
... | abs = (mab ημ e* · e₂) , ((mab v· abs) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)
... | mab = (mab ημ e* · e₂) , ((mab v· mab) {v≢ε = λ()} {w≢ε = λ()} {v≢· = λ {e₁} {e₂} ()} , ⟶-refl)

value→ALL : ∀ {e} → Value e → ALL Value e
value→ALL vε = Aε
value→ALL ((vv v· vw) {v≢ε = v≢ε} {v≢· = v≢·})
  = AP {e≢ε = v≢ε} {e≢· = v≢·} vv A· value→ALL vw
value→ALL cst = AP-cst cst
value→ALL abs = AP-abs abs
value→ALL mab = AP-mab mab

-- typing contexts

data Ctx : ℕ → Set where
  ∅ : Ctx zero
  _▻_ : NTy → Ctx n → Ctx (suc n)

variable Γ : Ctx n

lookup : Fin n → Ctx n → NTy
lookup Fin.zero (ημ ▻ _) = ημ
lookup (Fin.suc x) (_ ▻ Γ) = lookup x Γ

-- syntactic typing

data _⊢_⦂_  {n} : Ctx n → Expr n → NTy → Set where

  t-var : ∀ {x} → Γ ⊢ var x ⦂ lookup x Γ

  t-cst : ∀ {k} → Γ ⊢ cst k ⦂ ⟨ `! , □ ⟩

  t-abs : ∀ {μ}{s}{ημ}
    → (⟨ `! , μ ⟩ ▻ Γ) ⊢ s ⦂ ημ
    → Γ ⊢ abs μ s  ⦂ ⟨ `! , (μ ⇒ ημ) ⟩

  t-mab : ∀ {ημ}{s}{ημ′}
    → (ημ ▻ Γ) ⊢ s ⦂ ημ′
    → Γ ⊢ mab ημ s  ⦂ ⟨ `! , (ημ ⇛ ημ′) ⟩

  t-app-s : ∀ {s₁}{s₂}{η₁ μ₁ η₂ μ₂ η₃ η η′}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ⟨ η₃ , μ₁ ⟩
    → MUL η₁ η₂ η′ → MUL η′ η₃ η
    → Γ ⊢ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩

  t-app-p : ∀ {s₁}{s₂}{η₁ ημ η₂ μ₂ η}
    → Γ ⊢ s₁ ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
    → Γ ⊢ s₂ ⦂ ημ
    → MUL η₁ η₂ η
    → Γ ⊢ app s₁ s₂  ⦂ ⟨ η , μ₂ ⟩

  t-sub : ∀ {e : Expr n}{ημ₁ ημ₂}
    → Γ ⊢ e ⦂ ημ₁
    → ημ₁ <:ₙ ημ₂
    → Γ ⊢ e  ⦂ ημ₂

  t-empty : ∀ {μ}
    → Γ ⊢ ε ⦂ ⟨ `- , μ ⟩

  t-head : ∀ {e₁}{e₂}{η₁ η₂ η μ}
    → Γ ⊢ e₁ ⦂ ⟨ η₁ , μ ⟩
    → Γ ⊢ e₂ ⦂ ⟨ η₂ , μ ⟩
    → η ≡ ADD η₁ η₂
    → Γ ⊢ (e₁ · e₂) ⦂ ⟨ η , μ ⟩

-- typed renaming and substitution

infix 2 _⊢ₛ_∶_
_⊢ₛ_∶_ : Ctx n → Sub m n → Ctx m → Set
Δ ⊢ₛ σ ∶ Γ = ∀ x → Δ ⊢ σ x ⦂ lookup x Γ

infix 2 _⊢ᵣ_∶_
_⊢ᵣ_∶_ : Ctx n → Ren m n → Ctx m → Set
Δ ⊢ᵣ ρ ∶ Γ = ∀ x → lookup (ρ x) Δ ≡ lookup x Γ

ren-typed-ext : ∀ {Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n}{ημ}
  → Δ ⊢ᵣ ρ ∶ Γ
  → (ημ ▻ Δ) ⊢ᵣ extRen ρ ∶ (ημ ▻ Γ)
ren-typed-ext ρ⊢ Fin.zero = refl
ren-typed-ext ρ⊢ (Fin.suc x) = ρ⊢ x

ren-pres : ∀ {Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n}{e : Expr m}{ημ}
  → Γ ⊢ e ⦂ ημ
  → Δ ⊢ᵣ ρ ∶ Γ
  → Δ ⊢ ren ρ e ⦂ ημ
ren-pres (t-var {x = x}) ρ⊢
  with ρ⊢ x
... | eq rewrite sym eq = t-var
ren-pres t-cst ρ⊢ = t-cst
ren-pres (t-abs ⊢s) ρ⊢ = t-abs (ren-pres ⊢s (ren-typed-ext ρ⊢))
ren-pres (t-mab ⊢s) ρ⊢ = t-mab (ren-pres ⊢s (ren-typed-ext ρ⊢))
ren-pres (t-app-s ⊢s₁ ⊢s₂ x x₁) ρ⊢ = t-app-s (ren-pres ⊢s₁ ρ⊢) (ren-pres ⊢s₂ ρ⊢) x x₁
ren-pres (t-app-p ⊢s₁ ⊢s₂ x) ρ⊢ = t-app-p (ren-pres ⊢s₁ ρ⊢) (ren-pres ⊢s₂ ρ⊢) x
ren-pres (t-sub ⊢e ημ<:) ρ⊢ = t-sub (ren-pres ⊢e ρ⊢) ημ<:
ren-pres t-empty ρ⊢ = t-empty
ren-pres (t-head ⊢e₁ ⊢e₂ refl) ρ⊢ = t-head (ren-pres ⊢e₁ ρ⊢) (ren-pres ⊢e₂ ρ⊢) refl

weaken-typed : ∀ {Γ : Ctx m}{e : Expr m}{ημ}{ημ′}
  → Γ ⊢ e ⦂ ημ
  → (ημ′ ▻ Γ) ⊢ weaken e ⦂ ημ
weaken-typed {Γ = Γ} {ημ′ = ημ′} ⊢e = ren-pres ⊢e ρ⊢
  where
  ρ⊢ : (ημ′ ▻ Γ) ⊢ᵣ Fin.suc ∶ Γ
  ρ⊢ x = refl

sub-typed-ext : ∀ {Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n}{ημ}
  → Δ ⊢ₛ σ ∶ Γ
  → (ημ ▻ Δ) ⊢ₛ liftSub σ ∶ (ημ ▻ Γ)
sub-typed-ext σ⊢ Fin.zero = t-var
sub-typed-ext σ⊢ (Fin.suc x) = weaken-typed (σ⊢ x)

sub-pres : ∀ {Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n}{e : Expr m}{ημ}
  → Δ ⊢ₛ σ ∶ Γ
  → Γ ⊢ e ⦂ ημ
  → Δ ⊢ sub σ e ⦂ ημ
sub-pres σ⊢ (t-var {x = x}) = σ⊢ x
sub-pres σ⊢ t-cst = t-cst
sub-pres σ⊢ (t-abs ⊢s) = t-abs (sub-pres (sub-typed-ext σ⊢) ⊢s)
sub-pres σ⊢ (t-mab ⊢s) = t-mab (sub-pres (sub-typed-ext σ⊢) ⊢s)
sub-pres σ⊢ (t-app-s ⊢s₁ ⊢s₂ x x₁) = t-app-s (sub-pres σ⊢ ⊢s₁) (sub-pres σ⊢ ⊢s₂) x x₁
sub-pres σ⊢ (t-app-p ⊢s₁ ⊢s₂ x) = t-app-p (sub-pres σ⊢ ⊢s₁) (sub-pres σ⊢ ⊢s₂) x
sub-pres σ⊢ (t-sub ⊢e ημ<:) = t-sub (sub-pres σ⊢ ⊢e) ημ<:
sub-pres σ⊢ t-empty = t-empty
sub-pres σ⊢ (t-head ⊢e₁ ⊢e₂ refl) = t-head (sub-pres σ⊢ ⊢e₁) (sub-pres σ⊢ ⊢e₂) refl

-- inversion lemmas

t-head-inversion : ∀ {e₁}{e₂}{η μ}
  → ∅ ⊢ (e₁ · e₂) ⦂ ⟨ η , μ ⟩
  → ∃[ η₀ ] ∃[ η₁ ] ∃[ η₂ ] ∃[ μ₀ ]
    ∅ ⊢ e₁ ⦂ ⟨ η₁ , μ₀ ⟩
  × ∅ ⊢ e₂ ⦂ ⟨ η₂ , μ₀ ⟩
  × η₀ <:₀ η
  × μ₀ <:ₜ μ
  × ADD η₁ η₂ ≡ η₀
t-head-inversion (t-sub ⊢e₁·e₂ (<:ₙ-comb η₁<:₀η μ₁<:ₜμ))
  with t-head-inversion ⊢e₁·e₂
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<: , μ₀<: , add-eq = η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ ,  (<:₀-trans η₀<: η₁<:₀η) , ((<:ₜ-trans μ₀<: μ₁<:ₜμ) , add-eq)
t-head-inversion {η = η} {μ = μ} (t-head {η₁ = η₁}{η₂} ⊢e₁ ⊢e₂ refl) = η , η₁ , η₂ , μ , ⊢e₁ , ⊢e₂ , <:₀-refl , <:ₜ-refl , refl

t-cst-inversion : ∀ {k}{ημ}
  → ∅ ⊢ cst k ⦂ ημ
  → ⟨ `! , □ ⟩ <:ₙ ημ

t-abs-inversion : ∀ {μ}{e}{ημ}
  → ∅ ⊢ abs μ e ⦂ ημ
  → ∃[ ημ₀ ]
    ⟨ `! , (μ ⇒ ημ₀) ⟩ <:ₙ ημ
  × (⟨ `! , μ ⟩ ▻ ∅) ⊢ e ⦂ ημ₀

t-mab-inversion : ∀ {ημ}{e}{ημ₁}
  → ∅ ⊢ mab ημ e ⦂ ημ₁
  → ∃[ ημ₀ ]
    ⟨ `! , (ημ ⇛ ημ₀) ⟩ <:ₙ ημ₁
  × (ημ ▻ ∅) ⊢ e ⦂ ημ₀

value-nonempty-one-lower : ∀ {e η μ}
  → Value e
  → NonEmpty e
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → `! <:₀ η

value-nonempty-plus : ∀ {e η μ}
  → Value e
  → NonEmpty e
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → ∅ ⊢ e ⦂ ⟨ `+ , μ ⟩
value-nonempty-plus vε e≢ε ⊢e
  with e≢ε refl
... | ()
value-nonempty-plus cst e≢ε ⊢e
  with t-cst-inversion ⊢e
... | <:ₙ-comb !<:η □<:μ = t-sub t-cst (<:ₙ-comb <:₀-!+ □<:μ)
value-nonempty-plus abs e≢ε ⊢e
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η abs<:μ , ⊢body = t-sub (t-abs ⊢body) (<:ₙ-comb <:₀-!+ abs<:μ)
value-nonempty-plus mab e≢ε ⊢e
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η mab<:μ , ⊢body = t-sub (t-mab ⊢body) (<:ₙ-comb <:₀-!+ mab<:μ)
value-nonempty-plus
  ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε}) e≢ε ⊢e
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢v , ⊢w , η₀<:η , μ₀<:μ , add-eq
  = t-sub
      (t-head
        (value-nonempty-plus vh v≢ε ⊢v)
        (value-nonempty-plus vw w≢ε ⊢w)
        refl)
      (<:ₙ-comb <:₀-refl μ₀<:μ)

value-atomic-one : ∀ {e η μ}
  → Value e
  → NonEmpty e
  → (∀ {e₁ e₂} → e ≡ (e₁ · e₂) → ⊥)
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → ∅ ⊢ e ⦂ ⟨ `! , μ ⟩
value-atomic-one vε e≢ε e≢· ⊢e
  with e≢ε refl
... | ()
value-atomic-one ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) e≢ε e≢· ⊢e
  with e≢· refl
... | ()
value-atomic-one cst e≢ε e≢· ⊢e
  with t-cst-inversion ⊢e
... | <:ₙ-comb !<:η □<:μ = t-sub t-cst (<:ₙ-comb <:₀-refl □<:μ)
value-atomic-one abs e≢ε e≢· ⊢e
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η abs<:μ , ⊢body = t-sub (t-abs ⊢body) (<:ₙ-comb <:₀-refl abs<:μ)
value-atomic-one mab e≢ε e≢· ⊢e
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb !<:η mab<:μ , ⊢body = t-sub (t-mab ⊢body) (<:ₙ-comb <:₀-refl mab<:μ)

t-head-inversion-value : ∀ {e₁}{e₂}{η μ}
  → ∅ ⊢ (e₁ · e₂) ⦂ ⟨ η , μ ⟩
  → Value (e₁ · e₂)
  → ∃[ μ₀ ]
    ∅ ⊢ e₁ ⦂ ⟨ `! , μ₀ ⟩
  × ∅ ⊢ e₂ ⦂ ⟨ `+ , μ₀ ⟩
  × `+ <:₀ η
  × μ₀ <:ₜ μ
t-head-inversion-value {η = η} {μ = μ} ⊢e
  ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:η , μ₀<:μ , add-eq
  = μ₀
  , value-atomic-one vh v≢ε v≢· ⊢e₁
  , value-nonempty-plus vw w≢ε ⊢e₂
  , <:₀-trans
      (subst (λ x → `+ <:₀ x) add-eq
        (ADD-both-one-super
          (value-nonempty-one-lower vh v≢ε ⊢e₁)
          (value-nonempty-one-lower vw w≢ε ⊢e₂)))
      η₀<:η
  , μ₀<:μ


t-cst-inversion t-cst = <:ₙ-refl
t-cst-inversion (t-sub ⊢e ημ<:)
  with t-cst-inversion ⊢e
... | !□<: = <:ₙ-trans !□<: ημ<:

t-abs-inversion (t-abs {ημ = ημ} ⊢e) = ημ , <:ₙ-refl , ⊢e
t-abs-inversion (t-sub ⊢e ημ₁<:)
  with t-abs-inversion ⊢e
... | ημ₀ , <:ημ , ⊢body = ημ₀ , (<:ₙ-trans <:ημ ημ₁<:) , ⊢body

t-mab-inversion (t-mab {ημ′ = ημ′} ⊢e) = ημ′ , <:ₙ-refl , ⊢e
t-mab-inversion (t-sub ⊢e x)
  with t-mab-inversion ⊢e
... | ημ₀ , <:ημ , ⊢body = ημ₀ , <:ₙ-trans <:ημ x , ⊢body

t-empty-inversion : ∀ {η μ}
  → ∅ ⊢ ε ⦂ ⟨ η , μ ⟩
  → `- <:₀ η
t-empty-inversion t-empty = <:₀-refl
t-empty-inversion (t-sub ⊢e (<:ₙ-comb η₁<:η _)) = <:₀-trans (t-empty-inversion ⊢e) η₁<:η

-- canonical forms

canonical-zero :  ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `- , μ ⟩ → Value e → e ≡ ε
canonical-zero ⊢e vε = refl
canonical-zero ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , <:₀-refl , μ₀<:μ , add-eq
  with ADD-zero η₁ η₂ (sym add-eq)
... | refl , refl
  with canonical-zero ⊢e₁ v-e
... | eq₁
  with v≢ε eq₁
... | ()
canonical-zero ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb () x₁
canonical-zero ⊢e abs
  with t-abs-inversion ⊢e
... | ημ , <:ₙ-comb () _ , _
canonical-zero ⊢e mab
  with t-mab-inversion ⊢e
... | _ , <:ₙ-comb () _ , _

value-nonempty-one-lower {η = `- } vw e≢ε ⊢e
  = ⊥-elim (e≢ε (canonical-zero ⊢e vw))
value-nonempty-one-lower {η = `! } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-refl
value-nonempty-one-lower {η = `? } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-!?
value-nonempty-one-lower {η = `* } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-!*
value-nonempty-one-lower {η = `+ } vw e≢ε ⊢e
  with value-nonempty-plus vw e≢ε ⊢e
... | _ = <:₀-!+

canonical-one : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `! , μ ⟩ → Value e → SingletonValue μ e
canonical-one ⊢e vε
  with t-empty-inversion ⊢e
... | ()
canonical-one {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , <:₀-refl , μ₀<:μ , add-eq
  with ADD-one η₁ η₂ (sym add-eq)
... | add-one = impossible add-one
  where
  impossible : (`! ≡ η₁ × `- ≡ η₂) ⊎ (`- ≡ η₁ × `! ≡ η₂) → SingletonValue μ (v · w)
  impossible (inj₁ (refl , refl))
    with w≢ε (canonical-zero ⊢e₂ v-e₁)
  ... | ()
  impossible (inj₂ (refl , refl))
    with v≢ε (canonical-zero ⊢e₁ v-e)
  ... | ()
canonical-one ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb <:₀-refl □<:μ = sv-cst □<:μ
canonical-one ⊢e abs
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-refl abs<:μ , ⊢body = sv-abs abs<:μ
canonical-one ⊢e mab
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-refl mab<:μ , ⊢body = sv-mab mab<:μ

canonical-opt : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `? , μ ⟩ → Value e → (e ≡ ε) ⊎ SingletonValue μ e
canonical-opt ⊢e vε = inj₁ refl
canonical-opt {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:? , μ₀<:μ , add-eq = impossible η₀<:?
  where
  impossible : η₀ <:₀ `? → (v · w ≡ ε) ⊎ SingletonValue μ (v · w)
  impossible <:₀-refl
    with ADD-opt η₁ η₂ (sym add-eq)
  ... | add-opt = impossible-opt add-opt
    where
    impossible-opt : (`- ≡ η₁ × `? ≡ η₂) ⊎ (`? ≡ η₁ × `- ≡ η₂) → (v · w ≡ ε) ⊎ SingletonValue μ (v · w)
    impossible-opt (inj₁ (refl , refl))
      with v≢ε (canonical-zero ⊢e₁ v-e)
    ... | ()
    impossible-opt (inj₂ (refl , refl))
      with w≢ε (canonical-zero ⊢e₂ v-e₁)
    ... | ()
  impossible <:₀--?
    with ADD-zero η₁ η₂ (sym add-eq)
  ... | refl , refl
    with v≢ε (canonical-zero ⊢e₁ v-e)
  ... | ()
  impossible <:₀-!?
    with ADD-one η₁ η₂ (sym add-eq)
  ... | add-one = impossible-one add-one
    where
    impossible-one : (`! ≡ η₁ × `- ≡ η₂) ⊎ (`- ≡ η₁ × `! ≡ η₂) → (v · w ≡ ε) ⊎ SingletonValue μ (v · w)
    impossible-one (inj₁ (refl , refl))
      with w≢ε (canonical-zero ⊢e₂ v-e₁)
    ... | ()
    impossible-one (inj₂ (refl , refl))
      with v≢ε (canonical-zero ⊢e₁ v-e)
    ... | ()
canonical-opt ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb <:₀-!? □<:μ = inj₂ (sv-cst □<:μ)
canonical-opt ⊢e abs
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!? abs<:μ , ⊢body = inj₂ (sv-abs abs<:μ)
canonical-opt ⊢e mab
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!? mab<:μ , ⊢body = inj₂ (sv-mab mab<:μ)

canonical-star : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `* , μ ⟩ → Value e → AllSingleton μ e
canonical-star ⊢e vε = Aε
canonical-star {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε})
  with t-head-inversion ⊢e
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:* , μ₀<:μ , add-eq
  = canonical-star (t-sub ⊢e₁ (<:ₙ-comb (num-to-star η₁) μ₀<:μ)) v-e
  A· canonical-star (t-sub ⊢e₂ (<:ₙ-comb (num-to-star η₂) μ₀<:μ)) v-e₁
canonical-star ⊢e cst
  with t-cst-inversion ⊢e
... | <:ₙ-comb <:₀-!* □<:μ = AP-cst (sv-cst □<:μ)
canonical-star ⊢e abs
  with t-abs-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!* abs<:μ , ⊢body = AP-abs (sv-abs abs<:μ)
canonical-star ⊢e mab
  with t-mab-inversion ⊢e
... | ημ₀ , <:ₙ-comb <:₀-!* mab<:μ , ⊢body = AP-mab (sv-mab mab<:μ)

canonical-plus : ∀{e : Expr zero} → {μ : Ty} → ∅ ⊢ e ⦂ ⟨ `+ , μ ⟩ → Value e → AllSingleton μ e × NonEmpty e
canonical-plus ⊢e vε
  with t-empty-inversion ⊢e
... | ()
canonical-plus {e = v · w} {μ = μ} ⊢e ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) ((v-e v· v-e₁) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  , λ ()
canonical-plus {e = cst k} {μ = μ} ⊢e cst
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) cst
  , λ ()
canonical-plus {e = abs μ₀ e*} {μ = μ} ⊢e abs
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) abs
  , λ ()
canonical-plus {e = mab ημ e*} {μ = μ} ⊢e mab
  = canonical-star (t-sub ⊢e (<:ₙ-comb <:₀-+* <:ₜ-refl)) mab
  , λ ()

canonical-sequence : ∀ {η μ} {e : Expr zero}
  → ∅ ⊢ e ⦂ ⟨ η , μ ⟩
  → Value e
  → SequenceValue ⟨ η , μ ⟩ e
canonical-sequence {η = `- } {e = e} ⊢e ve
  with canonical-zero ⊢e ve
... | refl = seq-zero
canonical-sequence {η = `! } ⊢e ve = seq-one (canonical-one ⊢e ve)
canonical-sequence {η = `? } {e = e} ⊢e ve
  with canonical-opt ⊢e ve
... | inj₁ eq rewrite eq = seq-opt-zero
... | inj₂ sv = seq-opt-one sv
canonical-sequence {η = `* } ⊢e ve = seq-star (canonical-star ⊢e ve)
canonical-sequence {η = `+ } ⊢e ve
  with canonical-plus ⊢e ve
... | allsv , ne = seq-plus allsv ne

-- type preservation

mixed-mab-num-empty : ∀ {s η₁ μ₁ η₂ μ₂}
  → (mab₁ : ALL MabValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → `- <:₀ η₁
mixed-mab-num-empty Aε ⊢s = t-empty-inversion ⊢s
mixed-mab-num-empty (mab₁ A· mab₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = <:₀-trans (subst (λ x → `- <:₀ x) add-eq
      (ADD-empty-super
        (mixed-mab-num-empty mab₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
        (mixed-mab-num-empty mab₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))))
      η₀<:
mixed-mab-num-empty (AP (v-mab ημ e*)) ⊢s
  with t-mab-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mixed-abs-num-empty : ∀ {s η₁ ημ η₂ μ₂}
  → (abs₁ : ALL AbsValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → `- <:₀ η₁
mixed-abs-num-empty Aε ⊢s = t-empty-inversion ⊢s
mixed-abs-num-empty (abs₁ A· abs₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = <:₀-trans (subst (λ x → `- <:₀ x) add-eq
      (ADD-empty-super
        (mixed-abs-num-empty abs₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
        (mixed-abs-num-empty abs₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))))
      η₀<:
mixed-abs-num-empty (AP (v-abs μ e*)) ⊢s
  with t-abs-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mixed-mab-minus : ∀ {s w η₁ μ₁ η₂ μ₂}
  → (mab₁ : ALL MabValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ mapE (λ b → sub₁ w b) (foldALL mabbody mab₁) ⦂ ⟨ `- , μ₂ ⟩
mixed-mab-minus Aε ⊢s = t-empty
mixed-mab-minus (mab₁ A· mab₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = t-head
      (mixed-mab-minus mab₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
      (mixed-mab-minus mab₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))
      refl
mixed-mab-minus (AP (v-mab ημ e*)) ⊢s
  with t-mab-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mixed-abs-minus : ∀ {s v η₁ ημ η₂ μ₂}
  → (abs₁ : ALL AbsValue s)
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ mapE (λ b → sub₁ v b) (foldALL absbody abs₁) ⦂ ⟨ `- , μ₂ ⟩
mixed-abs-minus Aε ⊢s = t-empty
mixed-abs-minus (abs₁ A· abs₂) ⊢s
  with t-head-inversion ⊢s
... | η₀ , η₁ , η₂ , μ₀ , ⊢s₁ , ⊢s₂ , η₀<: , μ₀<: , add-eq
  = t-head
      (mixed-abs-minus abs₁ (t-sub ⊢s₁ (<:ₙ-comb <:₀-refl μ₀<:)))
      (mixed-abs-minus abs₂ (t-sub ⊢s₂ (<:ₙ-comb <:₀-refl μ₀<:)))
      refl
mixed-abs-minus (AP (v-abs μ e*)) ⊢s
  with t-abs-inversion ⊢s
... | ημ₀ , <:ₙ-comb _ () , ⊢body

mapE-minus : ∀ {e : Expr zero}{μ}
  → (f : Expr zero → Expr zero)
  → (∀ {x} → ∅ ⊢ f x ⦂ ⟨ `- , μ ⟩)
  → ∅ ⊢ mapE f e ⦂ ⟨ `- , μ ⟩
mapE-minus {e = ε} f f⊢ = t-empty
mapE-minus {e = e₁ · e₂} f f⊢ = t-head (mapE-minus {e = e₁} f f⊢) (mapE-minus {e = e₂} f f⊢) refl
mapE-minus {e = var ()} f f⊢
mapE-minus {e = cst k} f f⊢ = f⊢
mapE-minus {e = abs μ e} f f⊢ = f⊢
mapE-minus {e = mab ημ e} f f⊢ = f⊢
mapE-minus {e = app e₁ e₂} f f⊢ = f⊢

mapE-sub₁ : ∀ {w : Expr zero}{e : Expr (suc zero)}
  → mapE (λ b′ → sub₁ w b′) e ≡ sub₁ w e
mapE-sub₁ {e = ε} = refl
mapE-sub₁ {w = w} {e = e₁ · e₂}
  rewrite mapE-sub₁ {w = w} {e = e₁} | mapE-sub₁ {w = w} {e = e₂} = refl
mapE-sub₁ {e = var x} = refl
mapE-sub₁ {e = cst x} = refl
mapE-sub₁ {e = abs x e} = refl
mapE-sub₁ {e = mab x e} = refl
mapE-sub₁ {e = app e e₁} = refl


β₁-pres-s-A· : ∀ {s₁ s₂ w η₁ μ₁ η₂ μ₂ η₃ η η′}
  → Value (s₁ · s₂)
  → (abs₁ : ALL AbsValue s₁)
  → (abs₂ : ALL AbsValue s₂)
  → Value w
  → ∅ ⊢ (s₁ · s₂) ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ v → mapE (λ b → sub₁ v b) (foldALL absbody (abs₁ A· abs₂))) w ⦂ ⟨ η , μ₂ ⟩


β₁-pres-s-AP-concat : ∀ {v w μ₁ μ₂ η₃ η η′ b}
  → (vh : Value v)
  → (vw : Value w)
  → (v≢ε : v ≡ ε → ⊥)
  → (w≢ε : w ≡ ε → ⊥)
  → (v≢· : ∀ {e₁ e₂} → v ≡ (e₁ · e₂) → ⊥)
  → ∅ ⊢ (v · w) ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ x → mapE (λ b′ → sub₁ x b′) b) v ⦂ ⟨ η , μ₂ ⟩
  → ∅ ⊢ mapE (λ x → mapE (λ b′ → sub₁ x b′) b) w ⦂ ⟨ η , μ₂ ⟩
  → ∅ ⊢ mapE (λ x → mapE (λ b′ → sub₁ x b′) b) (v · w) ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s-AP-concat vh vw v≢ε w≢ε v≢· ⊢vw m₂ ⊢v ⊢w
  with t-head-inversion-value ⊢vw ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = t-sub
      (t-head ⊢v ⊢w refl)
      (<:ₙ-comb (ADD-self-super-plus +<:η₃ m₂) <:ₜ-refl)

β₁-pres-s-AP : ∀ {w η₁ μ₁ η₂ μ₂ η₃ η η′ μ ημ₀ b}
  → Value w
  → ∅ ⊢ abs μ b ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → (ημ₀<:η₂μ₂ : ημ₀ <:ₙ ⟨ η₂ , μ₂ ⟩)
  → (⟨ `! , μ ⟩ ▻ ∅) ⊢ b ⦂ ημ₀
  → ∅ ⊢ mapE (λ v → mapE (λ b′ → sub₁ v b′) b) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s-AP {μ₂ = μ₂} vε ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-empty-inversion ⊢w
... | η₃-empty = t-sub t-empty (<:ₙ-comb (MUL-right-empty η₃-empty m₂) <:ₜ-refl)
β₁-pres-s-AP {w = (v · w)} ((vε v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with v≢ε refl
... | ()
β₁-pres-s-AP {w = (v · w)} (((v-v₁ v· v-v₂) v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with v≢· refl
... | ()
β₁-pres-s-AP {w = (v · w)} {b = b} ((cst v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-head-inversion-value ⊢w ((cst v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-AP cst ⊢s ⊢v₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
      tail-pres = β₁-pres-s-AP w-v ⊢s ⊢w₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
    in β₁-pres-s-AP-concat {b = b} cst w-v v≢ε w≢ε (λ ()) ⊢w m₂ head-pres tail-pres
β₁-pres-s-AP {w = (v · w)} {b = b} ((abs v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-head-inversion-value ⊢w ((abs v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-AP abs ⊢s ⊢v₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
      tail-pres = β₁-pres-s-AP w-v ⊢s ⊢w₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
    in β₁-pres-s-AP-concat {b = b} abs w-v v≢ε w≢ε (λ ()) ⊢w m₂ head-pres tail-pres
β₁-pres-s-AP {w = (v · w)} {b = b} ((mab v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-head-inversion-value ⊢w ((mab v· w-v) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-AP mab ⊢s ⊢v₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
      tail-pres = β₁-pres-s-AP w-v ⊢s ⊢w₃ m₁ m₂ ημ₀<:η₂μ₂ ⊢b
    in β₁-pres-s-AP-concat {b = b} mab w-v v≢ε w≢ε (λ ()) ⊢w m₂ head-pres tail-pres
β₁-pres-s-AP {w = cst k} {b = b} cst ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-abs-inversion ⊢s
... | ημs , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημs<:η₂μ₂) , ⊢sbody
  with t-cst-inversion ⊢w
... | <:ₙ-comb !<:η₃ □<:μ₁
  rewrite mapE-sub₁ {w = cst k} {e = b}
  = let
      η₂<:η′ = MUL-left-one-super !<:η₁ m₁
      η′<:η = MUL-right-one-super !<:η₃ m₂
      η₂<:η = <:₀-trans η₂<:η′ η′<:η
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub t-cst (<:ₙ-comb <:₀-refl (<:ₜ-trans □<:μ₁ μ₁<:μ))
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)
β₁-pres-s-AP {w = abs μw bw} {b = b} abs ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-abs-inversion ⊢s
... | ημs , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημs<:η₂μ₂) , ⊢sbody
  with t-abs-inversion ⊢w
... | ημw , <:ₙ-comb !<:η₃ abs<:μ₁ , ⊢wbody
  rewrite mapE-sub₁ {w = abs μw bw} {e = b}
  = let
      η₂<:η′ = MUL-left-one-super !<:η₁ m₁
      η′<:η = MUL-right-one-super !<:η₃ m₂
      η₂<:η = <:₀-trans η₂<:η′ η′<:η
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub (t-abs ⊢wbody) (<:ₙ-comb <:₀-refl (<:ₜ-trans abs<:μ₁ μ₁<:μ))
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)
β₁-pres-s-AP {w = mab ημw bw} {b = b} mab ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  with t-abs-inversion ⊢s
... | ημs , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημs<:η₂μ₂) , ⊢sbody
  with t-mab-inversion ⊢w
... | ημw′ , <:ₙ-comb !<:η₃ mab<:μ₁ , ⊢wbody
  rewrite mapE-sub₁ {w = mab ημw bw} {e = b}
  = let
      η₂<:η′ = MUL-left-one-super !<:η₁ m₁
      η′<:η = MUL-right-one-super !<:η₃ m₂
      η₂<:η = <:₀-trans η₂<:η′ η′<:η
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub (t-mab ⊢wbody) (<:ₙ-comb <:₀-refl (<:ₜ-trans mab<:μ₁ μ₁<:μ))
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)

β₁-pres-s-AP-single : ∀ {w η₁ μ₁ η₂ μ₂ η₃ η η′ μ ημ₀ b}
  → Value w
  → ∅ ⊢ abs μ b ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → (ημ₀<:η₂μ₂ : ημ₀ <:ₙ ⟨ η₂ , μ₂ ⟩)
  → (⟨ `! , μ ⟩ ▻ ∅) ⊢ b ⦂ ημ₀
  → ∅ ⊢ mapE (λ v → mapE (λ b′ → sub₁ v b′) b) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s-AP-single vw ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b
  = β₁-pres-s-AP vw ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b

β₁-pres-s : ∀ {s w η₁ μ₁ η₂ μ₂ η₃ η η′}
  → Value s
  → (abs₁ : ALL AbsValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ v → mapE (λ b → sub₁ v b) (foldALL absbody abs₁)) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-s {w = w} {μ₂ = μ₂} vs Aε vw ⊢s ⊢w m₁ m₂
  = t-sub
      (mapE-minus {e = w}
        (λ _ → ε)
        (λ {x} → t-empty {μ = μ₂}))
      (<:ₙ-comb (MUL-left-empty (MUL-left-empty (t-empty-inversion ⊢s) m₁) m₂) <:ₜ-refl)
β₁-pres-s vs (abs₁ A· abs₂) vw ⊢s ⊢w m₁ m₂ = β₁-pres-s-A· vs abs₁ abs₂ vw ⊢s ⊢w m₁ m₂
β₁-pres-s vs (AP (v-abs μ b)) vw ⊢s ⊢w m₁ m₂
  with t-abs-inversion ⊢s
... | ημ₀ , <:ₙ-comb !<:η₁ (<:ₜ-⇒ μ₁<:μ ημ₀<:η₂μ₂) , ⊢b = β₁-pres-s-AP vw ⊢s ⊢w m₁ m₂ ημ₀<:η₂μ₂ ⊢b

β₁-pres-s-A· {μ₂ = μ₂}
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ vε ⊢s ⊢w m₁ m₂
  with t-empty-inversion ⊢w
... | η₃-empty = t-sub t-empty (<:ₙ-comb (MUL-right-empty η₃-empty m₂) <:ₜ-refl)
β₁-pres-s-A·
  {w = (v · w)}
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂
  ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  ⊢s ⊢vw m₁ m₂
  with t-head-inversion-value ⊢vw ((vh v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
... | μ₀ , ⊢v! , ⊢w+ , +<:η₃ , μ₀<:μ₁
  = let
      ⊢v₃ = t-sub ⊢v! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₃) μ₀<:μ₁)
      ⊢w₃ = t-sub ⊢w+ (<:ₙ-comb +<:η₃ μ₀<:μ₁)
      head-pres = β₁-pres-s-A· ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·}) abs₁ abs₂ vh ⊢s ⊢v₃ m₁ m₂
      tail-pres = β₁-pres-s-A· ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·}) abs₁ abs₂ vw ⊢s ⊢w₃ m₁ m₂
    in β₁-pres-s-AP-concat {b = foldALL absbody (abs₁ A· abs₂)} vh vw v≢ε w≢ε v≢· ⊢vw m₂ head-pres tail-pres
β₁-pres-s-A·
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ cst ⊢s ⊢w m₁ m₂
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μ₀ , ⊢s₁! , ⊢s₂+ , +<:η₁ , μ₀<:μ₁⇒η₂μ₂
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μ₀<:μ₁⇒η₂μ₂)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μ₀<:μ₁⇒η₂μ₂)
      head-pres = β₁-pres-s vs₁ abs₁ cst ⊢s₁η₁ ⊢w m₁ m₂
      tail-pres = β₁-pres-s vs₂ abs₂ cst ⊢s₂η₁ ⊢w m₁ m₂
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul +<:η₁ m₁ m₂) <:ₜ-refl)
β₁-pres-s-A·
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ abs ⊢s ⊢w m₁ m₂
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μ₀ , ⊢s₁! , ⊢s₂+ , +<:η₁ , μ₀<:μ₁⇒η₂μ₂
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μ₀<:μ₁⇒η₂μ₂)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μ₀<:μ₁⇒η₂μ₂)
      head-pres = β₁-pres-s vs₁ abs₁ abs ⊢s₁η₁ ⊢w m₁ m₂
      tail-pres = β₁-pres-s vs₂ abs₂ abs ⊢s₂η₁ ⊢w m₁ m₂
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul +<:η₁ m₁ m₂) <:ₜ-refl)
β₁-pres-s-A·
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  abs₁ abs₂ mab ⊢s ⊢w m₁ m₂
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μ₀ , ⊢s₁! , ⊢s₂+ , +<:η₁ , μ₀<:μ₁⇒η₂μ₂
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μ₀<:μ₁⇒η₂μ₂)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μ₀<:μ₁⇒η₂μ₂)
      head-pres = β₁-pres-s vs₁ abs₁ mab ⊢s₁η₁ ⊢w m₁ m₂
      tail-pres = β₁-pres-s vs₂ abs₂ mab ⊢s₂η₁ ⊢w m₁ m₂
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul +<:η₁ m₁ m₂) <:ₜ-refl)

βₙ-pres-s : ∀ {s w η₁ μ₁ η₂ μ₂ η₃ η η′}
  → (mab₁ : ALL MabValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , μ₁ ⇒ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ⟨ η₃ , μ₁ ⟩
  → MUL η₁ η₂ η′
  → MUL η′ η₃ η
  → ∅ ⊢ mapE (λ b → sub₁ w b) (foldALL mabbody mab₁) ⦂ ⟨ η , μ₂ ⟩
βₙ-pres-s mab₁ vw ⊢s ⊢w m₁ m₂
  = t-sub
      (mixed-mab-minus mab₁ ⊢s)
      (<:ₙ-comb (MUL-left-empty (MUL-left-empty (mixed-mab-num-empty mab₁ ⊢s) m₁) m₂) <:ₜ-refl)

β₁-pres-p : ∀ {s w η₁ ημ η₂ μ₂ η}
  → (abs₁ : ALL AbsValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ημ
  → MUL η₁ η₂ η
  → ∅ ⊢ mapE (λ v → mapE (λ b → sub₁ v b) (foldALL absbody abs₁)) w ⦂ ⟨ η , μ₂ ⟩
β₁-pres-p {w = w} abs₁ vw ⊢s ⊢w m
  = t-sub
      (mapE-minus {e = w}
        (λ v → mapE (λ b → sub₁ v b) (foldALL absbody abs₁))
        (λ {x} → mixed-abs-minus abs₁ ⊢s))
      (<:ₙ-comb (MUL-left-empty (mixed-abs-num-empty abs₁ ⊢s) m) <:ₜ-refl)


βₙ-pres-p : ∀ {s w η₁ ημ η₂ μ₂ η}
  → Value s
  → (mab₁ : ALL MabValue s)
  → Value w
  → ∅ ⊢ s ⦂ ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩
  → ∅ ⊢ w ⦂ ημ
  → MUL η₁ η₂ η
  → ∅ ⊢ mapE (λ b → sub₁ w b) (foldALL mabbody mab₁) ⦂ ⟨ η , μ₂ ⟩
βₙ-pres-p vε Aε vw ⊢s ⊢w m
  = t-sub
      t-empty
      (<:ₙ-comb (MUL-left-empty (t-empty-inversion ⊢s) m) <:ₜ-refl)
βₙ-pres-p
  ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
  (mab₁ A· mab₂)
  vw
  ⊢s
  ⊢w
  m
  with t-head-inversion-value ⊢s ((vs₁ v· vs₂) {v≢ε = s₁≢ε} {w≢ε = s₂≢ε} {v≢· = s₁≢·})
... | μv , ⊢s₁! , ⊢s₂+ , +<:η₁ , μv<:μ
  = let
      ⊢s₁η₁ = t-sub ⊢s₁! (<:ₙ-comb (<:₀-trans <:₀-!+ +<:η₁) μv<:μ)
      ⊢s₂η₁ = t-sub ⊢s₂+ (<:ₙ-comb +<:η₁ μv<:μ)
      head-pres = βₙ-pres-p vs₁ mab₁ vw ⊢s₁η₁ ⊢w m
      tail-pres = βₙ-pres-p vs₂ mab₂ vw ⊢s₂η₁ ⊢w m
    in t-sub
        (t-head head-pres tail-pres refl)
        (<:ₙ-comb (ADD-self-super-mul-left +<:η₁ m) <:ₜ-refl)
βₙ-pres-p {w = w} mab (AP (v-mab ημw b)) vw ⊢s ⊢w m
  with t-mab-inversion ⊢s
... | ημ₀ , <:ₙ-comb !<:η₁ (<:ₜ-⇛ ημ<:ημw ημ₀<:η₂μ₂) , ⊢b
  rewrite mapE-sub₁ {w = w} {e = b}
  = let
      η₂<:η = MUL-left-one-super !<:η₁ m
    in t-sub
        (t-sub
          (sub-pres
            (λ where
              Fin.zero → t-sub ⊢w ημ<:ημw
            )
            ⊢b)
          ημ₀<:η₂μ₂)
        (<:ₙ-comb η₂<:η <:ₜ-refl)

preserve : ∀ {e e′ ημ}
  → ∅ ⊢ e ⦂ ημ
  → e ⟶ e′
  → ∅ ⊢ e′ ⦂ ημ
preserve (t-var {x = ()}) red
preserve t-cst ()
preserve (t-abs ⊢e) ()
preserve (t-mab ⊢e) ()
preserve (t-app-s ⊢s₁ ⊢s₂ m₁ m₂) (ξ-app₁ red) = t-app-s (preserve ⊢s₁ red) ⊢s₂ m₁ m₂
preserve (t-app-s ⊢s₁ ⊢s₂ m₁ m₂) (ξ-app₂ v₁ red) = t-app-s ⊢s₁ (preserve ⊢s₂ red) m₁ m₂
preserve (t-app-s ⊢s₁ ⊢s₂ m₁ m₂) (β₁ vs abs₁ v) = β₁-pres-s vs abs₁ v ⊢s₁ ⊢s₂ m₁ m₂
preserve (t-app-s {s₂ = s₂} ⊢s₁ ⊢s₂ m₁ m₂) (βₙ vs mab₁ v)  = βₙ-pres-s mab₁ v ⊢s₁ ⊢s₂ m₁ m₂
--  rewrite sym (mapE-foldALL mabbody (sub₁ s₂) (λ {e} → mapE-sub e) mab₁)
-- 
preserve (t-app-p ⊢s₁ ⊢s₂ m) (ξ-app₁ red) = t-app-p (preserve ⊢s₁ red) ⊢s₂ m
preserve (t-app-p ⊢s₁ ⊢s₂ m) (ξ-app₂ v₁ red) = t-app-p ⊢s₁ (preserve ⊢s₂ red) m
preserve (t-app-p ⊢s₁ ⊢s₂ m) (β₁ vs abs₁ v) = β₁-pres-p abs₁ v ⊢s₁ ⊢s₂ m
preserve (t-app-p {s₂ = s₂} ⊢s₁ ⊢s₂ m) (βₙ vs mab₁ v) = βₙ-pres-p vs mab₁ v ⊢s₁ ⊢s₂ m
--  rewrite sym (mapE-foldALL mabbody (sub₁ s₂) (λ {e} → mapE-sub e) mab₁)
preserve (t-sub ⊢e ημ<:) red = t-sub (preserve ⊢e red) ημ<:
preserve t-empty ()
preserve (t-head ⊢e₁ ⊢e₂ refl) (ξ-head red) = t-head (preserve ⊢e₁ red) ⊢e₂ refl
preserve (t-head ⊢e₁ ⊢e₂ refl) (ξ-tail v red) = t-head ⊢e₁ (preserve ⊢e₂ red) refl
preserve (t-head {η₁ = η₁} ⊢e₁ ⊢e₂ refl) mon-ε-unit-left
  = t-sub ⊢e₂ (<:ₙ-comb (ADD-left-empty-super (t-empty-inversion ⊢e₁)) <:ₜ-refl)
preserve (t-head {η₁ = η₁} {η₂ = η₂} ⊢e₁ ⊢e₂ refl) mon-ε-unit-right
  = t-sub ⊢e₁ (<:ₙ-comb (ADD-right-empty-super (t-empty-inversion ⊢e₂)) <:ₜ-refl)
preserve (t-head {η₁ = η₁₂} {η₂ = η₃} ⊢e₁₂ ⊢e₃ refl) mon-·-assoc
  with t-head-inversion ⊢e₁₂
... | η₀ , η₁ , η₂ , μ₀ , ⊢e₁ , ⊢e₂ , η₀<:η₁₂ , μ₀<:μ , add-eq
  = t-sub
      (t-head
        (t-sub ⊢e₁ (<:ₙ-comb <:₀-refl μ₀<:μ))
        (t-head (t-sub ⊢e₂ (<:ₙ-comb <:₀-refl μ₀<:μ)) ⊢e₃ refl)
        refl)
      (<:ₙ-comb η<: <:ₜ-refl)
  where
  η-assoc : ADD η₁ (ADD η₂ η₃) <:₀ ADD (ADD η₁ η₂) η₃
  η-assoc rewrite ADD-assoc η₁ η₂ η₃ = <:₀-refl

  η-step : ADD (ADD η₁ η₂) η₃ <:₀ ADD η₁₂ η₃
  η-step = subst
    (λ x → ADD x η₃ <:₀ ADD η₁₂ η₃)
    (sym add-eq)
    (ADD-monotone-left η₀<:η₁₂)

  η<: : ADD η₁ (ADD η₂ η₃) <:₀ ADD η₁₂ η₃
  η<: = <:₀-trans η-assoc η-step

-- progress

all-single-absvalue : ∀ {μ}{ημ}{s} → (v   : Value s) (x   : AllSingleton (μ ⇒ ημ) s) → ALL AbsValue s
all-single-absvalue vε Aε = Aε
all-single-absvalue (v v· v₁) (x A· x₁) = (all-single-absvalue v x) A· (all-single-absvalue v₁ x₁)
all-single-absvalue cst (AP (sv-cst ()))
all-single-absvalue abs (AP (sv-abs (<:ₜ-⇒ x x₁))) = AP-abs (v-abs _ _)
all-single-absvalue mab (AP (sv-mab ()))

all-single-mabvalue : ∀ {ημ}{ημ₁}{s} → (v   : Value s) (x   : AllSingleton (ημ ⇛ ημ₁) s) → ALL MabValue s
all-single-mabvalue vε Aε = Aε
all-single-mabvalue (v v· v₁) (x A· x₁) = (all-single-mabvalue v x) A· (all-single-mabvalue v₁ x₁)
all-single-mabvalue cst (AP (sv-cst ()))
all-single-mabvalue abs (AP (sv-abs ()))
all-single-mabvalue mab (AP (sv-mab x)) = AP-mab (v-mab _ _)


data Progress (e : Expr zero) : Set where

  step : ∀ {e′} → e ⟶ e′ → Progress e
  done : Value e → Progress e

progress : ∀ {e}{ημ} → ∅ ⊢ e ⦂ ημ → Progress e
progress t-cst = done cst
progress (t-abs ⊢e) = done abs
progress (t-mab ⊢e) = done mab
progress (t-app-s ⊢e ⊢e₁ m m₁)
  with progress ⊢e
... | step e⟶ = step (ξ-app₁ e⟶)
... | done v
  with progress ⊢e₁
... | step e⟶ = step (ξ-app₂ v e⟶)
... | done w
  with canonical-sequence ⊢e v
... | seq-zero = step (β₁ v Aε w)
... | seq-one (sv-abs x) = step (β₁ v (AP-abs (v-abs _ _)) w)
... | seq-opt-zero = step (β₁ v Aε w)
... | seq-opt-one (sv-abs x) = step (β₁ v (AP-abs (v-abs _ _)) w)
... | seq-star x = step (β₁ v (all-single-absvalue v x) w)
... | seq-plus x x₁ = step (β₁ v (all-single-absvalue v x) w)
progress (t-app-p ⊢e ⊢e₁ m)
  with progress ⊢e
... | step e⟶ = step (ξ-app₁ e⟶)
... | done v
  with progress ⊢e₁
... | step e⟶ = step (ξ-app₂ v e⟶)
... | done w
  with canonical-sequence ⊢e v
... | seq-zero = step (β₁ v Aε w)
... | seq-one (sv-mab x) = step (βₙ v (AP-mab (v-mab _ _)) w)
... | seq-opt-zero = step (β₁ v Aε w)
... | seq-opt-one (sv-mab x) = step (βₙ v (AP-mab (v-mab _ _)) w)
... | seq-star all = step (βₙ v (all-single-mabvalue v all) w)
... | seq-plus all x₁ = step (βₙ v (all-single-mabvalue v all) w)
progress (t-sub ⊢e x) = progress ⊢e
progress t-empty = done vε
progress (t-head ⊢e ⊢e₁ add-eq)
  with progress ⊢e
... | step e⟶ = step (ξ-head e⟶)
... | done v
  with progress ⊢e₁
... | step e⟶ = step (ξ-tail v e⟶)
progress (t-head ⊢e ⊢e₁ add-eq) | done vε | done w = step mon-ε-unit-left
progress (t-head ⊢e ⊢e₁ add-eq) | done (v v· v₁) | done w = step mon-·-assoc
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done vε = step mon-ε-unit-right
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done ww@(w v· w₁) = done ((cst v· ww) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done cst = done ((cst v· cst) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done abs
  with t-cst-inversion ⊢e | t-abs-inversion ⊢e₁
... | <:ₙ-comb _ <:ₜ-□ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done cst | done mab
  with t-cst-inversion ⊢e | t-mab-inversion ⊢e₁
... | <:ₙ-comb _ <:ₜ-□ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done vε = step mon-ε-unit-right
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done ww@(w v· w₁) = done ((abs v· ww) {λ ()}{λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done cst
  with t-abs-inversion ⊢e | t-cst-inversion ⊢e₁
... | _ , <:ₙ-comb _ () , _ | <:ₙ-comb _ <:ₜ-□
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done abs = done ((abs v· abs) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done abs | done mab
  with t-abs-inversion ⊢e | t-mab-inversion ⊢e₁
... | _ , <:ₙ-comb _ (<:ₜ-⇒ _ _) , _ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done vε = step mon-ε-unit-right
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done ww@(w v· w₁) = done ((mab v· ww) {λ ()} {λ ()} {λ {e₁} {e₂} ()})
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done cst
  with t-mab-inversion ⊢e | t-cst-inversion ⊢e₁
... | _ , <:ₙ-comb _ () , _ | <:ₙ-comb _ <:ₜ-□
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done abs
  with t-mab-inversion ⊢e | t-abs-inversion ⊢e₁
... | _ , <:ₙ-comb _ (<:ₜ-⇛ _ _) , _ | _ , <:ₙ-comb _ () , _
progress (t-head ⊢e ⊢e₁ add-eq) | done mab | done mab = done ((mab v· mab) {λ ()} {λ ()} {λ {e₁} {e₂} ()})

-- logical relation

irred : Expr zero → Set
irred e = ∀ e′ → ¬ (e ⟶ e′)

head-atomic-no-step
  : ∀ {v v′}
  → Value v
  → (v ≡ ε → ⊥)
  → (∀ {e₁ e₂} → v ≡ (e₁ · e₂) → ⊥)
  → v ⟶ v′
  → ⊥
head-atomic-no-step vε v≢ε v≢· v⟶v′ = v≢ε refl
head-atomic-no-step ((_ v· _) {v≢ε = _} {w≢ε = _} {v≢· = _}) v≢ε v≢· v⟶v′ = v≢· refl
head-atomic-no-step cst v≢ε v≢· ()
head-atomic-no-step abs v≢ε v≢· ()
head-atomic-no-step mab v≢ε v≢· ()

value-no-step : ∀ {e e′} → Value e → e ⟶ e′ → ⊥
value-no-step vε ()
value-no-step cst ()
value-no-step abs ()
value-no-step mab ()
value-no-step ((vv v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) (ξ-head v⟶) =
  head-atomic-no-step vv v≢ε v≢· v⟶
value-no-step ((vv v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) (ξ-tail _ w⟶) =
  value-no-step vw w⟶
value-no-step ((vv v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) mon-ε-unit-left =
  v≢ε refl
value-no-step ((vv v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) mon-ε-unit-right =
  w≢ε refl
value-no-step ((vv v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·}) mon-·-assoc =
  v≢· refl

value-irred : ∀ {e} → Value e → irred e
value-irred v e′ e⟶e′ = value-no-step v e⟶e′

all-value-step-mono : ∀ {e e′} → ALL Value e → (s : e ⟶ e′) → Monoidal-Red s
all-value-step-mono Aε ()
all-value-step-mono (all₁ A· all₂) (ξ-head e⟶e′) = m-ξ-head (all-value-step-mono all₁ e⟶e′)
all-value-step-mono (all₁ A· all₂) (ξ-tail val-e s⟶s′) = m-ξ-tail val-e (all-value-step-mono all₂ s⟶s′)
all-value-step-mono (Aε A· all₂) mon-ε-unit-left = Monoidal-Red.mon-ε-unit-left
all-value-step-mono (AP {e≢ε = e≢ε} x A· all₂) mon-ε-unit-left = ⊥-elim (e≢ε refl)
all-value-step-mono (all₁ A· Aε) mon-ε-unit-right = Monoidal-Red.mon-ε-unit-right
all-value-step-mono (all₁ A· AP {e≢ε = e≢ε} x) mon-ε-unit-right = ⊥-elim (e≢ε refl)
all-value-step-mono ((all₁ A· all₂) A· all₃) mon-·-assoc = Monoidal-Red.mon-·-assoc
all-value-step-mono (AP {e≢· = e≢·} x A· all₃) mon-·-assoc = ⊥-elim (e≢· refl)
all-value-step-mono (AP v) st = ⊥-elim (value-no-step v st)

all-value-red-mono : ∀ {e e′} (all : ALL Value e) (red : e ⟶* e′) → Monoidal-Red* red
all-value-red-mono all ⟶-refl = Monoidal-Red*.⟶-refl
all-value-red-mono all (⟶-step st red)
  = Monoidal-Red*.⟶-step mstep (all-value-red-mono (all-pres-mono all mstep) red)
  where
    mstep : Monoidal-Red st
    mstep = all-value-step-mono all st

monoidal-local-confluence-value
  : ∀ {v v₁ v₂}
  → Value v
  → {red₁ : v ⟶ v₁} {red₂ : v ⟶ v₂}
  → Monoidal-Red red₁
  → Monoidal-Red red₂
  → ∃[ w ] v₁ ⟶* w × v₂ ⟶* w
monoidal-local-confluence-value vv {red₁ = red₁} mred₁ mred₂
  = ⊥-elim (value-no-step vv red₁)

value-no-step* : ∀ {v w} → Value v → v ⟶* w → v ≡ w
value-no-step* vv ⟶-refl = refl
value-no-step* vv (⟶-step v⟶v′ red) = ⊥-elim (value-no-step vv v⟶v′)

monoidal-confluence-value
  : ∀ {v v₁ v₂}
  → Value v
  → {red₁ : v ⟶* v₁} {red₂ : v ⟶* v₂}
  → Monoidal-Red* red₁
  → Monoidal-Red* red₂
  → ∃[ w ] v₁ ⟶* w × v₂ ⟶* w
monoidal-confluence-value {v = v} vv {red₁ = red₁} {red₂ = red₂} mred₁ mred₂
  with value-no-step* vv red₁ | value-no-step* vv red₂
... | refl | refl = v , ⟶-refl , ⟶-refl

monoidal-nf : Expr zero → Set
monoidal-nf ε = ⊤
monoidal-nf (e · e₁) = e ≢ ε × e₁ ≢ ε × (∀ {x y} → e ≢ (x · y)) × monoidal-nf e₁
monoidal-nf (cst x) = ⊤
monoidal-nf (abs x e) = ⊤
monoidal-nf (mab x e) = ⊤
monoidal-nf (app e e₁) = ⊤


𝓥⟦_⟧ : Ty → Pred (Expr zero) lzero
𝓦⟦_⟧ : NTy → Pred (Expr zero) lzero
𝓔⟦_⟧ : NTy → Pred (Expr zero) lzero

𝓥⟦ `⊥ ⟧        e  = ⊥
𝓥⟦ □ ⟧         e  = ∃[ n ] e ≡ cst n
𝓥⟦ μ ⇒ ημ ⟧    e  = ∃[ μ₀ ]  ∃[ s ] e ≡ abs μ₀ s   × μ <:ₜ μ₀     × ∀ v → v ∈ 𝓥⟦ μ ⟧     → sub₁ v s ∈ 𝓔⟦ ημ ⟧

𝓥⟦ ημ₁ ⇛ ημ ⟧  e  = ∃[ ημ₀ ] ∃[ s ] e ≡ mab ημ₀ s  × ημ₁ <:ₙ ημ₀  × ∀ w → w ∈ 𝓦⟦ ημ₁ ⟧  → sub₁ w s ∈ 𝓔⟦ ημ ⟧

𝓦⟦ ⟨ η , μ ⟩ ⟧ s  = ALL 𝓥⟦ μ ⟧ s × monoidal-nf s × (lengthE s ∈∈ 𝓝⟦ η ⟧)

𝓔⟦ ημ ⟧ s          = ∃[ w ] w ∈ 𝓦⟦ ημ ⟧ × (s ⟶* w) 

-- 𝓖⟦ Γ ⟧ characterizes substitutions σ: if x : ημ ∈ Γ then σ(x) ∈ 𝓦⟦ ημ ⟧

𝓖⟦_⟧ : Ctx n → Sub n zero → Set
𝓖⟦ Γ ⟧ σ = ∀ x → σ x ∈ 𝓦⟦ lookup  x Γ ⟧
-- 𝓖⟦ ∅ ⟧ σ = ⊤
-- 𝓖⟦ ημ ▻ Γ ⟧ σ = (∃[ w ] σ Fin.zero ≡ w × w ∈ 𝓦⟦ ημ ⟧) × (σ ∘ Fin.suc) ∈ 𝓖⟦ Γ ⟧

ext-𝓖 : ∀ {Γ : Ctx n}{σ : Sub n zero} {e : Expr zero} {ημ} → σ ∈ 𝓖⟦ Γ ⟧ → e ∈ 𝓦⟦ ημ ⟧ → extSub σ e ∈ 𝓖⟦ ημ ▻ Γ ⟧
ext-𝓖 σ∈𝓖 e∈𝓦 Fin.zero = e∈𝓦
ext-𝓖 σ∈𝓖 e∈𝓦 (Fin.suc x) = σ∈𝓖 x

length-𝓥 : ∀ {e}{μ} → e ∈ 𝓥⟦ μ ⟧ → lengthE e ≡ 1
length-𝓥 {μ = □} (_ , refl) = refl
length-𝓥 {μ = μ ⇒ ημ} (_ , _ , refl , _) = refl
length-𝓥 {μ = ημ ⇛ ημ₁} (_ , _ , refl , _) = refl

𝓥-≢ε : ∀ {e}{μ} → e ∈ 𝓥⟦ μ ⟧ → e ≡ ε → ⊥
𝓥-≢ε {μ = □} (_ , refl) ()
𝓥-≢ε {μ = μ ⇒ ημ} (_ , _ , refl , _) ()
𝓥-≢ε {μ = ημ ⇛ ημ₁} (_ , _ , refl , _) ()

𝓥-≢· : ∀ {e}{μ} → e ∈ 𝓥⟦ μ ⟧ → ∀ {e₁ e₂} → e ≡ (e₁ · e₂) → ⊥
𝓥-≢· {μ = □} (_ , refl) ()
𝓥-≢· {μ = μ ⇒ ημ} (_ , _ , refl , _) ()
𝓥-≢· {μ = ημ ⇛ ημ₁} (_ , _ , refl , _) ()

AP-𝓥 : ∀ {e}{μ} → e ∈ 𝓥⟦ μ ⟧ → ALL 𝓥⟦ μ ⟧ e
AP-𝓥 {e = e} {μ = μ} e∈𝓥 = AP {e≢ε = 𝓥-≢ε e∈𝓥} {e≢· = 𝓥-≢· e∈𝓥} e∈𝓥

toMab : ∀ {ημ η₂ μ₂}{x} → 𝓥⟦ ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟧ x → MabValue x
toMab (ημ₀ , b , refl , _ , _) = v-mab ημ₀ b

value-𝓥 : ∀ {e}{μ} → e ∈ 𝓥⟦ μ ⟧ → Value e
value-𝓥 {μ = □} (_ , refl) = cst
value-𝓥 {μ = μ ⇒ ημ} (_ , _ , refl , _) = abs
value-𝓥 {μ = x ⇛ x₁} (_ , _ , refl , _) = mab

¬𝓥-app : ∀ {w₁ w₂} {μ} → ¬ 𝓥⟦ μ ⟧ (app w₁ w₂)
¬𝓥-app {μ = `⊥} ()
¬𝓥-app {μ = □} ()
¬𝓥-app {μ = μ ⇒ x} ()
¬𝓥-app {μ = x ⇛ x₁} ()

ALL-proj₁ : {P : Pred (Expr zero) lzero}{e₁ e₂ : Expr zero} → ALL P (e₁ · e₂) → ALL P e₁
ALL-proj₁ (all A· all₁) = all
ALL-proj₁ (AP {e≢· = e≢·} x) = ⊥-elim (e≢· refl)
ALL-proj₂ : {P : Pred (Expr zero) lzero}{e₁ e₂ : Expr zero} → ALL P (e₁ · e₂) → ALL P e₂
ALL-proj₂ (all A· all₁) = all₁
ALL-proj₂ (AP {e≢· = e≢·} x) = ⊥-elim (e≢· refl)

all-monoidal-value : ∀ {η} {μ : Ty} {w : Expr 0}
  → ALL 𝓥⟦ μ ⟧ w → monoidal-nf w → lengthE w ∈∈ 𝓝⟦ η ⟧ → 𝓦⟦ ⟨ η , μ ⟩ ⟧ w
all-monoidal-value Aε mono-w len-w = Aε , tt , len-w
all-monoidal-value ap@(all-w A· all-w₁) mono-w len-w = ap , mono-w , len-w
all-monoidal-value {w = ε} (AP {e≢ε = e≢ε} x) mono-w len-w = ⊥-elim (e≢ε refl)
all-monoidal-value {w = w · w₁} (AP {e≢· = e≢·} x) mono-w len-w = ⊥-elim (e≢· refl)
all-monoidal-value {w = cst k} ap@(AP x) mono-w len-w = ap , tt , len-w
all-monoidal-value {w = abs x₁ w} ap@(AP x) mono-w len-w = ap , tt , len-w
all-monoidal-value {w = mab x₁ w} ap@(AP x) mono-w len-w = ap , tt , len-w
all-monoidal-value {w = app w w₁} (AP x) mono-w len-w = ⊥-elim (¬𝓥-app x)

-- irred-monoidal : ∀ {e}{μ} → irred e → ALL 𝓥⟦ μ ⟧ e → monoidal-nf e
-- irred-monoidal {ε} irr all-v = tt
-- irred-monoidal {ε · e₁} irr all-v = ⊥-elim (irr e₁ mon-ε-unit-left)
-- irred-monoidal {(e · e₂) · e₁} irr all-v = ⊥-elim (irr (e · (e₂ · e₁)) mon-·-assoc)
-- irred-monoidal {cst x · ε} irr all-v = ⊥-elim (irr (cst x) mon-ε-unit-right)
-- irred-monoidal {cst x · (e₁ · e₂)} irr all-v = (λ ()) , ((λ ()) , (λ ()) , irred-monoidal {!!} {!!})
-- irred-monoidal {cst x · cst x₁} irr all-v = (λ ()) , ((λ ()) , ((λ ()) , tt))
-- irred-monoidal {cst x · abs x₁ e₁} irr all-v = (λ ()) , (λ ()) , (λ ()) , tt
-- irred-monoidal {cst x · mab x₁ e₁} irr all-v = (λ ()) , (λ ()) , (λ ()) , tt
-- irred-monoidal {cst x · app e₁ e₂} irr all-v = (λ ()) , (λ ()) , (λ ()) , tt
-- irred-monoidal {abs x e · e₁} irr all-v = {!!}
-- irred-monoidal {mab x e · e₁} irr all-v = {!!}
-- irred-monoidal {app e e₂ · e₁} irr all-v = {!!}
-- irred-monoidal {cst x} irr all-v = tt
-- irred-monoidal {abs x e} irr all-v = tt
-- irred-monoidal {mab x e} irr all-v = tt
-- irred-monoidal {app e e₁} irr all-v = tt



value-monoidal-nf : ∀ {e} → Value e → monoidal-nf e
value-monoidal-nf vε = tt
value-monoidal-nf ((vv v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  = v≢ε , w≢ε , (λ {x} {y} → v≢·)  , value-monoidal-nf vw
value-monoidal-nf cst = tt
value-monoidal-nf abs = tt
value-monoidal-nf mab = tt

¬1≤0 : ¬ (1 ≤ℕ 0)
¬1≤0 ()

·-⟶-decompose-value : ∀ {e₁ e₂ w} → Value w → (e₁ · e₂) ⟶* w
  → ∃[ w₁ ] ∃[ w₂ ] Value w₁ × Value w₂ × e₁ ⟶* w₁ × e₂ ⟶* w₂
    ×  Σ ((w₁ · w₂) ⟶* w) Monoidal-Red*
{-# TERMINATING #-}
·-⟶-decompose-value {e₁ = e₁} {e₂ = e₂} vw ⟶-refl
  with vw
... | ((v₁ v· v₂) {v≢ε = _} {w≢ε = _} {v≢· = _})
  = e₁ , e₂ , v₁ , v₂ , ⟶-refl , ⟶-refl , (⟶-refl , Monoidal-Red*.⟶-refl)
·-⟶-decompose-value vw (⟶-step (ξ-head e₁⟶e₁′) red)
  with ·-⟶-decompose-value vw red
... | w₁ , w₂ , vw₁ , vw₂ , e₁′⟶*w₁ , e₂⟶*w₂ , w₁·w₂⟶*w , mon-red
  = w₁ , w₂ , vw₁ , vw₂ , ⟶-step e₁⟶e₁′ e₁′⟶*w₁ , e₂⟶*w₂ , (w₁·w₂⟶*w , mon-red)
·-⟶-decompose-value vw (⟶-step (ξ-tail val-e₁ e₂⟶e₂′) red)
  with ·-⟶-decompose-value vw red
... | w₁ , w₂ , vw₁ , vw₂ , e₁⟶*w₁ , e₂′⟶*w₂ , w₁·w₂⟶*w , mon-red
  = w₁ , w₂ , vw₁ , vw₂ , e₁⟶*w₁ , ⟶-step e₂⟶e₂′ e₂′⟶*w₂ , (w₁·w₂⟶*w , mon-red)
·-⟶-decompose-value {e₂ = e₂} {w = w} vw (⟶-step mon-ε-unit-left red)
  = ε , w , vε , vw
  , ⟶-refl
  , red
  , (⟶-step mon-ε-unit-left ⟶-refl
    , Monoidal-Red*.⟶-step Monoidal-Red.mon-ε-unit-left Monoidal-Red*.⟶-refl)
·-⟶-decompose-value {e₁ = e₁} {w = w} vw (⟶-step mon-ε-unit-right red)
  = w , ε , vw , vε
  , red
  , ⟶-refl
  , (⟶-step mon-ε-unit-right ⟶-refl
    , Monoidal-Red*.⟶-step Monoidal-Red.mon-ε-unit-right Monoidal-Red*.⟶-refl)
·-⟶-decompose-value {e₁ = e₁ · e₂} {e₂ = e₃} vw (⟶-step mon-·-assoc red)
  with ·-⟶-decompose-value vw red
... | w₁ , w₂₃ , vw₁ , vw₂₃ , e₁⟶*w₁ , e₂·e₃⟶*w₂₃ , w₁·w₂₃⟶*w , mon₁
  with ·-⟶-decompose-value vw₂₃ e₂·e₃⟶*w₂₃
... | w₂ , w₃ , vw₂ , vw₃ , e₂⟶*w₂ , e₃⟶*w₃ , w₂·w₃⟶*w₂₃ , mon₂
  with value-· vw₁ vw₂
... | w₁₂ , vw₁₂ , w₁·w₂⟶*w₁₂
  with monoidal-confluence-ALL
         (((value→ALL vw₁) A· (value→ALL vw₂)) A· (value→ALL vw₃))
         (Monoidal-Red*-trans
           (Monoidal-Red*.⟶-step Monoidal-Red.mon-·-assoc Monoidal-Red*.⟶-refl)
           (Monoidal-Red*-trans (m-ξ-tail-* vw₁ mon₂) mon₁))
         (all-value-red-mono
           (((value→ALL vw₁) A· (value→ALL vw₂)) A· (value→ALL vw₃))
           (ξ-head-* w₁·w₂⟶*w₁₂))
... | w′ , w⟶*w′ , w₁₂·w₃⟶*w′
  with value-no-step* vw w⟶*w′
... | refl
  = w₁₂ , w₃ , vw₁₂ , vw₃
  , (⟶*-trans (⟶*-trans (ξ-head-* e₁⟶*w₁) (ξ-tail-* vw₁ e₂⟶*w₂)) w₁·w₂⟶*w₁₂)
  , e₃⟶*w₃
  , (w₁₂·w₃⟶*w′
    , all-value-red-mono ((value→ALL vw₁₂) A· (value→ALL vw₃)) w₁₂·w₃⟶*w′)

·-⟶-decompose : ∀ {e₁ e₂ w} → Value w → (e₁ · e₂) ⟶* w
  → ∃[ w₁ ] ∃[ w₂ ] ALL Value w₁ × ALL Value w₂ × e₁ ⟶* w₁ × e₂ ⟶* w₂
    ×  Σ ((w₁ · w₂) ⟶* w) Monoidal-Red*
·-⟶-decompose vw red
  with ·-⟶-decompose-value vw red
... | w₁ , w₂ , vw₁ , vw₂ , e₁⟶*w₁ , e₂⟶*w₂ , w₁·w₂⟶*w , mon-red
  = w₁ , w₂ , value→ALL vw₁ , value→ALL vw₂ , e₁⟶*w₁ , e₂⟶*w₂ , (w₁·w₂⟶*w , mon-red)

numOfLen : ℕ → Num
numOfLen zero = `-
numOfLen (suc zero) = `!
numOfLen (suc (suc _)) = `+

numOfLen-sound : ∀ n → n ∈∈ 𝓝⟦ numOfLen n ⟧
numOfLen-sound zero = z≤n , z≤n
numOfLen-sound (suc zero) = s≤s z≤n , s≤s z≤n
numOfLen-sound (suc (suc n)) = s≤s z≤n

numOfLen-sub : ∀ {n η} → n ∈∈ 𝓝⟦ η ⟧ → numOfLen n <:₀ η
numOfLen-sub {zero} {`- } n∈ = <:₀-refl
numOfLen-sub {zero} {`!} (() , k≤1)
numOfLen-sub {zero} {`?} n∈ = <:₀--?
numOfLen-sub {zero} {`*} n∈ = <:₀--*
numOfLen-sub {zero} {`+} ()
numOfLen-sub {suc zero} {`- } (0≤n , ())
numOfLen-sub {suc zero} {`!} n∈ = <:₀-refl
numOfLen-sub {suc zero} {`?} n∈ = <:₀-!?
numOfLen-sub {suc zero} {`*} n∈ = <:₀-!*
numOfLen-sub {suc zero} {`+} n∈ = <:₀-!+
numOfLen-sub {suc (suc n)} {`- } (0≤n , ())
numOfLen-sub {suc (suc n)} {`!} (1≤n , s≤s ())
numOfLen-sub {suc (suc n)} {`?} (0≤n , s≤s ())
numOfLen-sub {suc (suc n)} {`*} n∈ = <:₀-+*
numOfLen-sub {suc (suc n)} {`+} n∈ = <:₀-refl

numOfLen-add-super : ∀ n₁ n₂ → ADD (numOfLen n₁) (numOfLen n₂) <:₀ numOfLen (n₁ +ℕ n₂)
numOfLen-add-super zero zero = <:₀-refl
numOfLen-add-super zero (suc zero) = <:₀-refl
numOfLen-add-super zero (suc (suc n₂)) = <:₀-refl
numOfLen-add-super (suc zero) zero = <:₀-refl
numOfLen-add-super (suc zero) (suc zero) = <:₀-refl
numOfLen-add-super (suc zero) (suc (suc n₂)) = <:₀-refl
numOfLen-add-super (suc (suc n₁)) zero = <:₀-refl
numOfLen-add-super (suc (suc n₁)) (suc zero) = <:₀-refl
numOfLen-add-super (suc (suc n₁)) (suc (suc n₂)) = <:₀-refl

all-unpres-mono
  : ∀ {P} {e e′} {step : e ⟶ e′}
  → ALL P e′
  → Monoidal-Red step
  → ALL P e
all-unpres-mono all′ Monoidal-Red.mon-ε-unit-left = Aε A· all′
all-unpres-mono all′ Monoidal-Red.mon-ε-unit-right = all′ A· Aε
all-unpres-mono (AP {e≢· = e≢·} x) Monoidal-Red.mon-·-assoc = ⊥-elim (e≢· refl)
all-unpres-mono (all₁ A· all₂₃) Monoidal-Red.mon-·-assoc with all₂₃
... | (all₂ A· all₃) = (all₁ A· all₂) A· all₃
... | (AP {e≢· = e≢·} x) = ⊥-elim (e≢· refl)
all-unpres-mono all′ (m-ξ-head mred) with all′
... | (all₁ A· all₂) = all-unpres-mono all₁ mred A· all₂
... | (AP {e≢· = e≢·} x) = ⊥-elim (e≢· refl)
all-unpres-mono all′ (m-ξ-tail val-e mred) with all′
... | (all₁ A· all₂) = all₁ A· all-unpres-mono all₂ mred
... | (AP {e≢· = e≢·} x) = ⊥-elim (e≢· refl)

all-unpres-mono*
  : ∀ {P} {e e′} {red : e ⟶* e′}
  → ALL P e′
  → Monoidal-Red* red
  → ALL P e
all-unpres-mono* all′ Monoidal-Red*.⟶-refl = all′
all-unpres-mono* all′ (Monoidal-Red*.⟶-step mred mreds)
  = all-unpres-mono (all-unpres-mono* all′ mreds) mred

monoidal-length-pres : ∀ {e e′} {step : e ⟶ e′} → Monoidal-Red step → lengthE e ≡ lengthE e′
monoidal-length-pres Monoidal-Red.mon-ε-unit-left = refl
monoidal-length-pres {e′ = e′} Monoidal-Red.mon-ε-unit-right rewrite +-identityʳ (lengthE e′) = refl
monoidal-length-pres {e = ((e₁ · e₂) · e₃)} Monoidal-Red.mon-·-assoc
  rewrite +-assoc (lengthE e₁) (lengthE e₂) (lengthE e₃) = refl
monoidal-length-pres (m-ξ-head mred) rewrite monoidal-length-pres mred = refl
monoidal-length-pres (m-ξ-tail _ mred) rewrite monoidal-length-pres mred = refl

monoidal-length-pres* : ∀ {e e′} {red : e ⟶* e′} → Monoidal-Red* red → lengthE e ≡ lengthE e′
monoidal-length-pres* Monoidal-Red*.⟶-refl = refl
monoidal-length-pres* (Monoidal-Red*.⟶-step mred mreds)
  = trans (monoidal-length-pres mred) (monoidal-length-pres* mreds)

atomic-𝓥-value
  : ∀ {e}{μ}
  → ALL 𝓥⟦ μ ⟧ e
  → e ≢ ε
  → (∀ {x y} → e ≢ (x · y))
  → Value e
atomic-𝓥-value Aε e≢ε e≢· = ⊥-elim (e≢ε refl)
atomic-𝓥-value (_ A· _) e≢ε e≢· = ⊥-elim (e≢· refl)
atomic-𝓥-value (AP e∈𝓥) e≢ε e≢· = value-𝓥 e∈𝓥

all-𝓥-nf→value : ∀ {e}{μ} → ALL 𝓥⟦ μ ⟧ e → monoidal-nf e → Value e
all-𝓥-nf→value Aε nf = vε
all-𝓥-nf→value (AP e∈𝓥) nf = value-𝓥 e∈𝓥
all-𝓥-nf→value {e = e₁ · e₂} (all₁ A· all₂) (e₁≢ε , e₂≢ε , e₁≢· , nf₂)
  = ((atomic-𝓥-value all₁ e₁≢ε e₁≢·) v· all-𝓥-nf→value all₂ nf₂)
      {v≢ε = e₁≢ε}
      {w≢ε = e₂≢ε}
      {v≢· = e₁≢·}


𝓔-decompose : ∀ {e₁ e₂}{η μ} → (e₁ · e₂) ∈ 𝓔⟦ ⟨ η , μ ⟩ ⟧
  → ∃[ η₁ ] ∃[ η₂ ] e₁ ∈ 𝓔⟦ ⟨ η₁ , μ ⟩ ⟧ × e₂ ∈ 𝓔⟦ ⟨ η₂ , μ ⟩ ⟧ × ADD η₁ η₂ <:₀ η
𝓔-decompose {η = η} {μ = μ} (w , (allμ , mono-w , len-w∈) , e₁·e₂⟶*w)
  with ·-⟶-decompose-value (all-𝓥-nf→value allμ mono-w) e₁·e₂⟶*w
... | w₁ , w₂ , vw₁ , vw₂ , e₁⟶*w₁ , e₂⟶*w₂ , w₁·w₂⟶*w , mon-red
  = η₁ , η₂
  , (w₁ , (allμ₁ , value-monoidal-nf vw₁ , numOfLen-sound (lengthE w₁)) , e₁⟶*w₁)
  , (w₂ , (allμ₂ , value-monoidal-nf vw₂ , numOfLen-sound (lengthE w₂)) , e₂⟶*w₂)
  , <:₀-trans
      (numOfLen-add-super (lengthE w₁) (lengthE w₂))
      (numOfLen-sub len-sum∈η)
  where
    η₁ : Num
    η₁ = numOfLen (lengthE w₁)

    η₂ : Num
    η₂ = numOfLen (lengthE w₂)

    allμ₁·allμ₂ : ALL 𝓥⟦ μ ⟧ (w₁ · w₂)
    allμ₁·allμ₂ = all-unpres-mono* allμ mon-red

    allμ₁ : ALL 𝓥⟦ μ ⟧ w₁
    allμ₁ = ALL-proj₁ allμ₁·allμ₂

    allμ₂ : ALL 𝓥⟦ μ ⟧ w₂
    allμ₂ = ALL-proj₂ allμ₁·allμ₂

    len-sum∈η : (lengthE w₁ +ℕ lengthE w₂) ∈∈ 𝓝⟦ η ⟧
    len-sum∈η
      = subst (λ n → n ∈∈ 𝓝⟦ η ⟧)
          (sym (monoidal-length-pres* mon-red))
          len-w∈

value-𝓦 : ∀ {e}{ημ} → e ∈ 𝓦⟦ ημ ⟧ → Value e
value-𝓦 {ημ = ⟨ η , μ ⟩} (all∈𝓥 , nf , len∈) = value-all-nf all∈𝓥 nf
  where
    atomic-from-all : ∀ {e}
      → ALL 𝓥⟦ μ ⟧ e
      → e ≢ ε
      → (∀ {x y} → e ≢ (x · y))
      → Value e
    atomic-from-all Aε e≢ε e≢· = ⊥-elim (e≢ε refl)
    atomic-from-all (_ A· _) e≢ε e≢· = ⊥-elim (e≢· refl)
    atomic-from-all (AP e∈𝓥) e≢ε e≢· = value-𝓥 e∈𝓥

    value-all-nf : ∀ {e}
      → ALL 𝓥⟦ μ ⟧ e
      → monoidal-nf e
      → Value e
    value-all-nf Aε nf = vε
    value-all-nf (AP e∈𝓥) nf = value-𝓥 e∈𝓥
    value-all-nf {e = e₁ · e₂} (all₁ A· all₂) (e₁≢ε , e₂≢ε , e₁≢· , nf₂)
      =   ((atomic-from-all all₁ e₁≢ε e₁≢·) v· (value-all-nf all₂ nf₂))
            {v≢ε = e₁≢ε}
            {w≢ε = e₂≢ε}
            {v≢· = e₁≢·}

atomic-length : (v : Expr zero) → v ≢ ε → (∀ {x y} → v ≢ (x · y)) → lengthE v ≡ 1
atomic-length ε v≢ε v≢· = ⊥-elim (v≢ε refl)
atomic-length (v · v₁) v≢ε v≢· = ⊥-elim (v≢· refl)
atomic-length (cst x) v≢ε v≢· = refl
atomic-length (abs x v) v≢ε v≢· = refl
atomic-length (mab x v) v≢ε v≢· = refl
atomic-length (app v v₁) v≢ε v≢· = refl

atomic-ALL :  {v : Expr zero} {P : Pred _ lzero} → ALL P v → v ≢ ε → (∀ {x y} → v ≢ (x · y)) → P v
atomic-ALL Aε v≢ε v≢· = ⊥-elim (v≢ε refl)
atomic-ALL (all A· all₁) v≢ε v≢· = ⊥-elim (v≢· refl)
atomic-ALL (AP x) v≢ε v≢· = x

·-preserves-≢ε : ∀ w₁ w₂ {w₁w₂} → Value w₁ → Value w₂ → w₂ ≢ ε → (w₁ · w₂) ⟶* w₁w₂ → w₁w₂ ≢ ε
·-preserves-≢ε w₁ w₂ v₁ v₂ w₂≢ε ⟶-refl ()
·-preserves-≢ε w₁ w₂ v₁ v₂ w₂≢ε (⟶-step (ξ-head x) red) w₁w₂≡ε = ⊥-elim (value-no-step v₁ x)
·-preserves-≢ε w₁ w₂ v₁ v₂ w₂≢ε (⟶-step (ξ-tail x x₁) red) w₁w₂≡ε = ⊥-elim (value-no-step v₂ x₁)
·-preserves-≢ε w₁ w₂ v₁ v₂ w₂≢ε (⟶-step mon-ε-unit-left red) w₁w₂≡ε with red
... | ⟶-refl = w₂≢ε w₁w₂≡ε
... | ⟶-step x red′ = ⊥-elim (value-no-step v₂ x)
·-preserves-≢ε w₁ w₂ v₁ v₂ w₂≢ε (⟶-step mon-ε-unit-right red) w₁w₂≡ε = ⊥-elim (w₂≢ε refl)
·-preserves-≢ε (v · w) w₂
  ((vv v· vw) {v≢ε = v≢ε} {w≢ε = w≢ε} {v≢· = v≢·})
  v₂
  w₂≢ε
  (⟶-step mon-·-assoc red)
  w₁w₂≡ε
  = go tail-nonempty red w₁w₂≡ε
  where
    tail-nonempty : ∀ {u} → (w · w₂) ⟶* u → u ≢ ε
    tail-nonempty red′ = ·-preserves-≢ε w w₂ vw v₂ w₂≢ε red′

    go : ∀ {t r}
      → (∀ {u} → t ⟶* u → u ≢ ε)
      → (v · t) ⟶* r
      → r ≢ ε
    go t-nonempty ⟶-refl ()
    go t-nonempty (⟶-step (ξ-head x) red′) r≡ε = ⊥-elim (head-atomic-no-step vv v≢ε v≢· x)
    go t-nonempty (⟶-step (ξ-tail x x₁) red′) r≡ε
      = go (λ red″ → t-nonempty (⟶-step x₁ red″)) red′ r≡ε
    go t-nonempty (⟶-step mon-ε-unit-left red′) r≡ε = ⊥-elim (v≢ε refl)
    go t-nonempty (⟶-step mon-ε-unit-right red′) r≡ε = ⊥-elim (t-nonempty ⟶-refl refl)
    go t-nonempty (⟶-step mon-·-assoc red′) r≡ε = ⊥-elim (v≢· refl)

·-ALL-preserves-≢ε' : ∀ w₁ w₂ {w₁w₂} → ALL Value w₁ → ALL Value w₂ → monoidal-nf w₁ → monoidal-nf w₂ → w₂ ≢ ε → (w₁ · w₂) ⟶* w₁w₂ → w₁w₂ ≢ ε
·-ALL-preserves-≢ε' w₁ w₂ all₁ all₂ nf₁ nf₂ w₂≢ε red
  = ·-preserves-≢ε w₁ w₂ (all-value-nf→value all₁ nf₁) (all-value-nf→value all₂ nf₂) w₂≢ε red
  where
    all-value-nf→value : ∀ {e} → ALL Value e → monoidal-nf e → Value e
    all-value-nf→value Aε nf = vε
    all-value-nf→value (AP v) nf = v
    all-value-nf→value {e = e₁ · e₂} (all₁ A· all₂) (e₁≢ε , e₂≢ε , e₁≢· , nf₂)
      = ((atomic-ALL all₁ e₁≢ε e₁≢·) v· all-value-nf→value all₂ nf₂)
          {v≢ε = e₁≢ε}
          {w≢ε = e₂≢ε}
          {v≢· = e₁≢·}

compatible-· : ∀ {w₁ w₂}{η₁ η₂}{μ} → w₁ ∈ 𝓦⟦ ⟨ η₁ , μ ⟩ ⟧ → w₂ ∈ 𝓦⟦ ⟨ η₂ , μ ⟩ ⟧ → w₁ · w₂ ∈ 𝓔⟦ ⟨ (ADD η₁ η₂) , μ ⟩ ⟧
compatible-· {w₂ = w₂} (Aε , mono₁ , len₁) (ap₂ , mono₂ , len₂) = w₂ , (ap₂ , mono₂ , ADD-0-k len₁ len₂) , (⟶-step mon-ε-unit-left ⟶-refl)
compatible-· {w₁ = w₁} (all₁@(_ A· _) , mono₁ , len₁) (Aε , mono₂ , len₂)
  = w₁ , ((all₁ , mono₁ , ADD-k-0 len₁ len₂) , (⟶-step mon-ε-unit-right ⟶-refl))
compatible-· {w₁ = v · w₁} {w₂ = w₂} {η₁} ((ap₁ A· all₁) , (v≢ε , w₁≢ε , v≢· , mono₁) , len₁) w₂∈@(all₂@(_ A· _) , mono₂ , len₂)
  rewrite atomic-length v v≢ε v≢·
  with compatible-· {w₁ = w₁} {w₂ = w₂} {η₁ = DEC η₁} (all₁ , mono₁ , DEC-sound {η₁} len₁) w₂∈
... | w₁w₂ , (all₁₂ , mono₁₂ , len₁₂) , red
  = (v · w₁w₂) , ((ap₁ A· all₁₂) , (v≢ε , (·-ALL-preserves-≢ε' w₁ w₂ {w₁w₂} (mapALL value-𝓥 all₁) (mapALL value-𝓥 all₂) mono₁ mono₂ (λ ()) red  , (v≢· , mono₁₂))) , subst (λ □ → (□ +ℕ lengthE w₁w₂) ∈∈ 𝓝⟦ ADD η₁ _ ⟧) (sym (atomic-length v v≢ε v≢·)) (ADD-DEC (suc-not-empty {η₁} len₁) len₁₂)) , ⟶-step mon-·-assoc (ξ-tail-* (value-𝓥 (atomic-ALL ap₁ v≢ε v≢·)) red)
compatible-· {w₁ = v · w₁} {w₂ = w₂} {η₁} ((ap₁ A· all₁) , (v≢ε , w₁≢ε , v≢· , mono₁) , len₁) w₂∈@(all₂@(AP {e≢ε = w₂≢ε} {e≢· = w₂≢·} x) , mono₂ , len₂)
  rewrite atomic-length v v≢ε v≢·
  with compatible-· {w₁ = w₁} {w₂ = w₂} {η₁ = DEC η₁} (all₁ , mono₁ , DEC-sound {η₁} len₁) w₂∈
... | w₁w₂ , (all₁₂ , mono₁₂ , len₁₂) , red
  = (v · w₁w₂) , ((ap₁ A· all₁₂) , (v≢ε , (·-ALL-preserves-≢ε' w₁ w₂ {w₁w₂} (mapALL value-𝓥 all₁) (mapALL value-𝓥 all₂) mono₁ mono₂ w₂≢ε red  , (v≢· , mono₁₂))) , subst (λ □ → (□ +ℕ lengthE w₁w₂) ∈∈ 𝓝⟦ ADD η₁ _ ⟧) (sym (atomic-length v v≢ε v≢·)) (ADD-DEC (suc-not-empty {η₁} len₁) len₁₂)) , ⟶-step mon-·-assoc (ξ-tail-* (value-𝓥 (atomic-ALL ap₁ v≢ε v≢·)) red)
compatible-· {w₁ = w₁} {w₂ = w₂} (ap₁@(AP v) , mono₁ , len₁) (Aε , mono₂ , len₂)
  = w₁ , (ap₁ , mono₁ , ADD-k-0 len₁ len₂ ) , (⟶-step mon-ε-unit-right ⟶-refl)
compatible-· {w₁ = w₁} {w₂ = w₂} (ap₁@(AP {e≢ε = w₁≢ε} {e≢· = w₁≢·} v) , mono₁ , len₁) (ap₂@(_ A· _) , mono₂ , len₂)
  = (w₁ · w₂) , ((ap₁ A· ap₂) , ((w₁≢ε , ((λ ()) , (w₁≢· , ((mono₂ .proj₁) , ((mono₂ .proj₂ .proj₁) , ((mono₂ .proj₂ .proj₂ .proj₁) , (mono₂ .proj₂ .proj₂ .proj₂))))))) , ADD-i-j len₁ len₂)) , ⟶-refl
compatible-· {w₁ = w₁} {w₂ = w₂} (ap₁@(AP {e≢ε = w₁≢ε} {e≢· = w₁≢·} v) , mono₁ , len₁) (ap₂@(AP {e≢ε = w₂≢ε} {e≢· = w₂≢·} x) , mono₂ , len₂)
  = (w₁ · w₂) , (((AP  {e≢ε = w₁≢ε} {e≢· = w₁≢·} v A· AP {e≢ε = w₂≢ε} {e≢· = w₂≢·} x) , ((w₁≢ε , (w₂≢ε , (w₁≢· , mono₂))) , (ADD-i-j len₁ len₂))) , ⟶-refl)

-- semantic typing

_⊨_⦂_ : Ctx n → Expr n → NTy → Set
Γ ⊨ e ⦂ ημ = ∀ σ → σ ∈ 𝓖⟦ Γ ⟧ → sub σ e ∈ 𝓔⟦ ημ ⟧

-- semantic subtyping

<:ₙ-subset-𝓔 : ∀ {ημ₁ ημ₂} → ημ₁ <:ₙ ημ₂ → 𝓔⟦ ημ₁ ⟧ ⊆ 𝓔⟦ ημ₂ ⟧
<:ₙ-subset : ∀ {ημ₁ ημ₂} → ημ₁ <:ₙ ημ₂ → 𝓦⟦ ημ₁ ⟧ ⊆ 𝓦⟦ ημ₂ ⟧
<:ₜ-subset : ∀ {μ₁ μ₂} → μ₁ <:ₜ μ₂ → 𝓥⟦ μ₁ ⟧ ⊆ 𝓥⟦ μ₂ ⟧

<:ₜ-subset <:ₜ-□ e∈𝓥⟦μ₁⟧ = e∈𝓥⟦μ₁⟧
<:ₜ-subset (<:ₜ-⇒ μ₂<:μ₁ ημ₁<:ημ₂) (μ₀ , e , x≡ , μ₁<:μ₀ , ∀v∈𝓥) = μ₀ , e , x≡ , (<:ₜ-trans μ₂<:μ₁ μ₁<:μ₀) , (λ v v∈𝓥⟦μ₁⟧ → <:ₙ-subset-𝓔 ημ₁<:ημ₂ (∀v∈𝓥 v (<:ₜ-subset μ₂<:μ₁ v∈𝓥⟦μ₁⟧)))
<:ₜ-subset (<:ₜ-⇛ ημ₁′<:ημ₁ ημ₂<:ημ₂′) (ημ₀ , e , x≡ , ημ₁<:ημ₀ , ∀w∈𝓦) = ημ₀ , e , x≡ , (<:ₙ-trans ημ₁′<:ημ₁ ημ₁<:ημ₀) , (λ w w∈𝓦⟦ημ₁⟧ → <:ₙ-subset-𝓔 ημ₂<:ημ₂′ (∀w∈𝓦 w (<:ₙ-subset ημ₁′<:ημ₁ w∈𝓦⟦ημ₁⟧)))

<:ₙ-subset (<:ₙ-comb η₁<:η₂ μ₁<:μ₂) (all∈μ₁ , nf , len∈η₁) = mapALL (<:ₜ-subset μ₁<:μ₂) all∈μ₁ , nf , <:₀-subset η₁<:η₂ len∈η₁

<:ₙ-subset-𝓔 (<:ₙ-comb η₁<:η₂ μ₁<:μ₂) (e , w∈𝓦 , e⟶*w) = e , <:ₙ-subset (<:ₙ-comb η₁<:η₂ μ₁<:μ₂) w∈𝓦 , e⟶*w


-- fundamental lemma

fundamental : ∀ {e}{ημ} → Γ ⊢ e ⦂ ημ → Γ ⊨ e ⦂ ημ
fundamental (t-var {x = x}) σ σ∈ = σ x , σ∈ x , ⟶-refl
fundamental (t-cst {k = k}) σ σ∈ = cst k , (AP-cst (k , refl) , tt , s≤s z≤n , s≤s z≤n) , ⟶-refl
fundamental (t-abs {μ = μ} {s = e} {ημ = ημ} ⊢e) σ σ∈
  = sub σ (abs μ e) , ((AP-abs (μ , (sub (liftSub σ) e , refl , <:ₜ-refl , λ v v∈𝓥 → subst (𝓔⟦ ημ ⟧) (sub-ext-lift {σ = σ} {v = v} {e = e}) (fundamental ⊢e (extSub σ v) (ext-𝓖 σ∈ ((AP-𝓥 v∈𝓥) , value-monoidal-nf (value-𝓥 v∈𝓥) , ≤-reflexive (sym (length-𝓥 v∈𝓥)) , ≤-reflexive (length-𝓥 v∈𝓥))))))) , tt , (s≤s z≤n , s≤s z≤n)) , ⟶-refl
fundamental (t-mab {ημ = ημ} {s} {ημ′} ⊢e) σ σ∈
  = sub σ (mab ημ s) , ((AP-mab (ημ , ((sub (liftSub σ) s) , (refl , (<:ₙ-refl , (λ w w∈𝓦 → subst 𝓔⟦ ημ′ ⟧ (sub-ext-lift {σ = σ} {v = w} {e = s}) (fundamental ⊢e (extSub σ w) (ext-𝓖 σ∈ w∈𝓦)))))))) , tt , s≤s z≤n , s≤s z≤n) , ⟶-refl
fundamental (t-app-s {η₁ = η₁}{μ₁ = μ₁}{η₂ = η₂}{μ₂ = μ₂}{η₃} ⊢e ⊢e₁ m m₁) σ σ∈
  with fundamental ⊢e σ σ∈
... | s , (all∈μ₁⇒η₂μ₂ , _ , len∈η₁) , sub-σ-s₁⟶*s
  with fundamental ⊢e₁ σ σ∈
... | w , (all∈μ₁ , _ , len∈η₃) , sub-σ-s₂⟶*w  = {! !}
fundamental (t-app-p {s₁ = s₁}{s₂}{η₁}{ημ}{η₂}{μ₂}{η} ⊢e ⊢e₁ m) σ σ∈
  with fundamental ⊢e σ σ∈
... | s , 𝓦-s@((all∈μ₁⇒η₂μ₂) , mono-s , len∈η₁) , sub-σ-s₁⟶*s
  with fundamental ⊢e₁ σ σ∈
... | w , 𝓦-w@(all∈μ₁ , _ , len∈η₃) , sub-σ-s₂⟶*w
  using value-s ← value-𝓦 {ημ = ⟨ η₁ , ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟩} 𝓦-s
  using value-w ← value-𝓦 𝓦-w
  using mab-s ← mapALL toMab all∈μ₁⇒η₂μ₂
  using reduce-to-redex ← (⟶*-trans (ξ-app₁-* sub-σ-s₁⟶*s) (ξ-app₂-* value-s sub-σ-s₂⟶*w))
  using redex ← (s · w)
  using reduce-redex ←  ⟶*-snoc reduce-to-redex  (βₙ value-s mab-s value-w)
  = let sem = app-p-sem all∈μ₁⇒η₂μ₂ mono-s len∈η₁ m in
    proj₁ sem , proj₁ (proj₂ sem) , ⟶*-trans reduce-redex (proj₂ (proj₂ sem))
  where
    ¬2≤0 : ¬ (suc (suc zero) ≤ℕ zero)
    ¬2≤0 ()

    ¬2≤1 : ¬ (suc (suc zero) ≤ℕ suc zero)
    ¬2≤1 (s≤s p) = ¬1≤0 p

    mono-nonempty-len-plus : ∀ {e} → monoidal-nf e → e ≢ ε → lengthE e ∈∈ 𝓝⟦ `+ ⟧
    mono-nonempty-len-plus {e = ε} mono e≢ε = ⊥-elim (e≢ε refl)
    mono-nonempty-len-plus {e = e₁ · e₂} (e₁≢ε , e₂≢ε , e₁≢· , mono₂) e≢ε
      rewrite atomic-length e₁ e₁≢ε e₁≢·
      = s≤s z≤n
    mono-nonempty-len-plus {e = cst x} mono e≢ε = s≤s z≤n
    mono-nonempty-len-plus {e = abs x e} mono e≢ε = s≤s z≤n
    mono-nonempty-len-plus {e = mab x e} mono e≢ε = s≤s z≤n
    mono-nonempty-len-plus {e = app e e₁} mono e≢ε = s≤s z≤n

    mono-concat-len-two : ∀ {e₁ e₂} → monoidal-nf (e₁ · e₂) → suc (suc zero) ≤ℕ lengthE (e₁ · e₂)
    mono-concat-len-two {e₁} {e₂} (e₁≢ε , e₂≢ε , e₁≢· , mono₂)
      rewrite atomic-length e₁ e₁≢ε e₁≢·
      with mono-nonempty-len-plus mono₂ e₂≢ε
    ... | len₂∈+ = s≤s len₂∈+

    concat-plus-super : ∀ {e₁ e₂ η₁} → monoidal-nf (e₁ · e₂) → lengthE (e₁ · e₂) ∈∈ 𝓝⟦ η₁ ⟧ → `+ <:₀ η₁
    concat-plus-super {η₁ = `- } mono len = ⊥-elim (¬2≤0 (≤-trans (mono-concat-len-two mono) (len .proj₂)))
    concat-plus-super {η₁ = `!} mono len = ⊥-elim (¬2≤1 (≤-trans (mono-concat-len-two mono) (len .proj₂)))
    concat-plus-super {η₁ = `?} mono len = ⊥-elim (¬2≤1 (≤-trans (mono-concat-len-two mono) (len .proj₂)))
    concat-plus-super {η₁ = `*} mono len = <:₀-+*
    concat-plus-super {η₁ = `+} mono len = <:₀-refl

    app-p-sem
      : ∀ {s η₁}
      → (all∈ : ALL 𝓥⟦ ημ ⇛ ⟨ η₂ , μ₂ ⟩ ⟧ s)
      → monoidal-nf s
      → lengthE s ∈∈ 𝓝⟦ η₁ ⟧
      → MUL η₁ η₂ η
      → ∃[ w* ] w* ∈ 𝓦⟦ ⟨ η , μ₂ ⟩ ⟧ × (mapE (sub₁ w) (foldALL mabbody (mapALL toMab all∈)) ⟶* w*)
    app-p-sem Aε mono len m
      = ε
      , (Aε , tt , <:₀-subset (MUL-left-empty (numOfLen-sub len) m) (z≤n , z≤n))
      , ⟶-refl
    app-p-sem {η₁ = η₁′} (AP {e = e} {e≢ε = e≢ε} {e≢· = e≢·} (ημ₀ , b , refl , ημ<:ημ₀ , fvw)) mono len m
      rewrite mapE-sub₁ {w = w} {e = b}
      = <:ₙ-subset-𝓔 (<:ₙ-comb η₂<:η <:ₜ-refl) (fvw w 𝓦-w)
      where
        len! : 1 ∈∈ 𝓝⟦ η₁′ ⟧
        len! = subst (λ n → n ∈∈ 𝓝⟦ η₁′ ⟧) (atomic-length e e≢ε e≢·) len

        !<:η₁ : `! <:₀ η₁′
        !<:η₁ = numOfLen-sub len!

        η₂<:η : η₂ <:₀ η
        η₂<:η = MUL-left-one-super !<:η₁ m
    app-p-sem {s = s₁ · s₂} {η₁ = η₁′} (all₁ A· all₂) mono-s@(s₁≢ε , s₂≢ε , s₁≢· , mono₂) len m
      with all₁
    ... | Aε = ⊥-elim (s₁≢ε refl)
    ... | (_ A· _) = ⊥-elim (s₁≢· refl)
    ... | AP {e = e₁} {e≢ε = e₁≢ε} {e≢· = e₁≢·} (ημ₀ , b , refl , ημ<:ημ₀ , fvw)
      rewrite mapE-sub₁ {w = w} {e = b}
      with app-p-sem all₂ mono₂ (<:₀-subset (concat-plus-super mono-s len) (mono-nonempty-len-plus mono₂ s₂≢ε)) m
    ... | w₂* , w₂*∈𝓦 , red₂
      with <:ₙ-subset-𝓔 (<:ₙ-comb (MUL-left-one-super (<:₀-trans <:₀-!+ (concat-plus-super mono-s len)) m) <:ₜ-refl) (fvw w 𝓦-w)
    ... | w₁* , w₁*∈𝓦 , red₁
      with compatible-· w₁*∈𝓦 w₂*∈𝓦
    ... | w₁₂* , w₁₂*∈𝓦 , red₁₂
      = <:ₙ-subset-𝓔
          (<:ₙ-comb (ADD-self-super-mul-left +<:η₁ m) <:ₜ-refl)
          (w₁₂* , w₁₂*∈𝓦
          , ⟶*-trans
              (⟶*-trans
                (ξ-head-* red₁)
                (ξ-tail-* (value-𝓦 w₁*∈𝓦) red₂))
              red₁₂)
      where
        +<:η₁ : `+ <:₀ η₁′
        +<:η₁ = concat-plus-super mono-s len

        η₂<:η : η₂ <:₀ η
        η₂<:η = MUL-left-one-super (<:₀-trans <:₀-!+ +<:η₁) m

        len₂∈η₁ : lengthE s₂ ∈∈ 𝓝⟦ η₁′ ⟧
        len₂∈η₁ = <:₀-subset +<:η₁ (mono-nonempty-len-plus mono₂ s₂≢ε)
fundamental (t-sub ⊢e (<:ₙ-comb η₁<:η₂ μ₁<:μ₂)) σ σ∈
  with fundamental ⊢e σ σ∈
... | w , (allv-w , nf , len-w-∈) , subσe⟶*w = w , (mapALL (<:ₜ-subset μ₁<:μ₂) allv-w , nf , <:₀-subset η₁<:η₂ len-w-∈) , subσe⟶*w
fundamental t-empty σ σ∈ = ε , (Aε , tt , z≤n , z≤n) , ⟶-refl
fundamental (t-head {e₁ = e₁} {e₂} ⊢e ⊢e₁ x) σ σ∈
  rewrite x
  with fundamental ⊢e σ σ∈
... | w₁ , w₁∈𝓦 , sub-σ-e₁⟶*w₁
  with fundamental ⊢e₁ σ σ∈
... | w₂ , w₂∈𝓦 , sub-σ-e₂⟶*w₂
  with compatible-· w₁∈𝓦 w₂∈𝓦
... | w , w∈𝓦 , w₁·w₂⟶*w
  = w , w∈𝓦 , ⟶*-trans (⟶*-trans (ξ-head-* sub-σ-e₁⟶*w₁) (ξ-tail-* (value-𝓦 w₁∈𝓦) sub-σ-e₂⟶*w₂)) w₁·w₂⟶*w


