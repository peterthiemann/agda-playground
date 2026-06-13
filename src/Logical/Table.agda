module Table where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc;_≤_; z≤n; s≤s)
open import Data.Product using (Σ; _×_ ; proj₁; proj₂; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)

open import Relation.Unary using (_∈_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; cong; cong₂; sym; subst; trans)
open import Function using (_∘_)

open import Numeri
open import Types
open import Expressions
open import Values
open import Substitution
open import SimplyNumbered

-- maplets

infix 4 [_⦂_↦_] [_⦂_⤇_]

[_⦂_↦_] : ∀ {n} → Expr zero → Ty → Expr n → Expr n
[ v ⦂ μ ↦ s ] = abs μ (mtc v (var fzero) (weaken s))

[_⦂_⤇_] : ∀ {n} → Expr zero → NTy → Expr n → Expr n
[ w ⦂ ημ ⤇ s ] = mab ημ (mtc w (var fzero) (weaken s))

-- semantic typing for maplets

single-maplet-syntactic :  ∀ {Γ : Ctx n} {v : Expr 0} {v′ : Expr n} {μ μ′ : Ty}
  → Value v
  → ∅ ⊢ v ⦂ ⟨ `! , μ ⟩
  → Γ ⊢ v′ ⦂ ⟨ `! , μ′ ⟩
  ----------------------------------------------
  → Γ ⊢ [ v ⦂ μ ↦ v′ ] ⦂ ⟨ `! , μ ⇒ ⟨ `? , μ′ ⟩ ⟩
single-maplet-syntactic val-v ∅⊢v⦂!μ Γ⊢v′⦂!μ′ =
  t-abs (t-mtc ∅⊢v⦂!μ val-v t-var (weaken-typed Γ⊢v′⦂!μ′))

-- the semantic typing follows by the fundamental theorem

weaken-semantic : ∀ {Γ : Ctx n} {ημ ημ′ : NTy} {e : Expr n}
  → Γ ⊨ e ⦂ ημ
  → (ημ′ ▻ Γ) ⊨ weaken e ⦂ ημ
weaken-semantic {ημ = ημ} {e = e} sem-e σ σ∈ =
  subst
    (λ e′ → e′ ∈ 𝓔⟦ ημ ⟧)
    (sym (sub-ren {ρ = fsuc} {σ = σ} {e = e}))
    (sem-e (λ x → σ (fsuc x)) (λ x → σ∈ (fsuc x)))

single-maplet-semantic : ∀ {Γ : Ctx n} {v : Expr 0} {v′ : Expr n} {μ μ′ : Ty}
  → ∅ ⊨ v ⦂ ⟨ `! , μ ⟩
  → Γ ⊨ v′ ⦂ ⟨ `! , μ′ ⟩
  → Value v
  ----------------------------------------------
  → Γ ⊨ [ v ⦂ μ ↦ v′ ] ⦂ ⟨ `! , μ ⇒ ⟨ `? , μ′ ⟩ ⟩
single-maplet-semantic {v = v} {v′ = v′} {μ = μ} {μ′ = μ′} ⊨v⦂!μ Γ⊨v′⦂!μ′ val-v =
  compatible-abs
    {μ = μ}
    {s = mtc v (var fzero) (weaken v′)}
    {ημ = ⟨ `? , μ′ ⟩}
    (compatible-mtc
      {v = v}
      {e = var fzero}
      {s = weaken v′}
      {ημ = ⟨ `! , μ ⟩}
      {η = `!}
      {μ = μ′}
      val-v
      compatible-var
      (weaken-semantic
        {ημ = ⟨ `! , μ′ ⟩}
        {ημ′ = ⟨ `! , μ ⟩}
        {e = v′}
        Γ⊨v′⦂!μ′))

disjoint-maplets : ∀ {Γ : Ctx n} {v₁ v₂ : Expr 0} {v₁′ v₂′ : Expr n} {μ μ′ : Ty}
  → ∅ ⊨ v₁ ⦂ ⟨ `! , μ ⟩
  → ∅ ⊨ v₂ ⦂ ⟨ `! , μ ⟩
  → v₁ ≢ v₂
  → Γ ⊨ v₁′ ⦂ ⟨ `! , μ′ ⟩
  → Γ ⊨ v₂′ ⦂ ⟨ `! , μ′ ⟩
  → Value v₁ → Value v₂
  → Γ ⊨ ([ v₁ ⦂ μ ↦ v₁′ ] · [ v₂ ⦂ μ ↦ v₂′ ]) ⦂ ⟨ `+ , μ ⇒ ⟨ `? , μ′ ⟩ ⟩
disjoint-maplets {v₁ = v₁} {v₂}{v₁′}{v₂′}{μ}{μ′}
  ⊨v₁⦂!μ ⊨v₂⦂!μ v₁≢v₂ Γ⊨v₁′⦂μ′ Γ⊨v₂′⦂μ′ val-v₁ val-v₂ =
  compatible-head
    {e₁ = [ v₁ ⦂ μ ↦ v₁′ ]}
    {e₂ = [ v₂ ⦂ μ ↦ v₂′ ]}
    {η₁ = `!}
    {η₂ = `!}
    {η = `+}
    {μ = μ ⇒ ⟨ `? , μ′ ⟩}
    (single-maplet-semantic
      {v = v₁}
      {v′ = v₁′}
      {μ = μ}
      {μ′ = μ′}
      ⊨v₁⦂!μ Γ⊨v₁′⦂μ′ val-v₁)
    (single-maplet-semantic
      {v = v₂}
      {v′ = v₂′}
      {μ = μ}
      {μ′ = μ′}
      ⊨v₂⦂!μ Γ⊨v₂′⦂μ′ val-v₂)
    refl

disjoint-maplets-stronger : ∀ {Γ : Ctx n} {v₁ v₂ : Expr 0} {v₁′ v₂′ : Expr n} {μ μ′ : Ty}
  → ∅ ⊨ v₁ ⦂ ⟨ `! , μ ⟩
  → ∅ ⊨ v₂ ⦂ ⟨ `! , μ ⟩
  → v₁ ≢ v₂
  → Γ ⊨ v₁′ ⦂ ⟨ `! , μ′ ⟩
  → Γ ⊨ v₂′ ⦂ ⟨ `! , μ′ ⟩
  → Value v₁ → Value v₂
  → Γ ⊨ abs μ (app ([ v₁ ⦂ μ ↦ weaken v₁′ ] · [ v₂ ⦂ μ ↦ weaken v₂′ ]) (var fzero))
      ⦂ ⟨ `! , μ ⇒ ⟨ `? , μ′ ⟩ ⟩
disjoint-maplets-stronger {v₁ = v₁} {v₂} {v₁′} {v₂′} {μ} {μ′}
  ⊨v₁⦂!μ ⊨v₂⦂!μ v₁≢v₂ Γ⊨v₁′⦂!μ′ Γ⊨v₂′⦂!μ′ val-v₁ val-v₂ σ σ∈𝓖 =
  sub σ table
  , (AP-abs table∈𝓥 , tt , (s≤s z≤n , s≤s z≤n))
  , ⟶-refl
  where
    body : Expr _
    body = app ([ v₁ ⦂ μ ↦ weaken v₁′ ] · [ v₂ ⦂ μ ↦ weaken v₂′ ]) (var fzero)

    table : Expr _
    table = abs μ body

    mapE-atomic : ∀ {e} {f : Expr zero → Expr zero}
      → e ≢ ε
      → (∀ {x y} → e ≢ (x · y))
      → mapE f e ≡ f e
    mapE-atomic {e = ε} e≢ε e≢· = ⊥-elim (e≢ε refl)
    mapE-atomic {e = e₁ · e₂} e≢ε e≢· = ⊥-elim (e≢· refl)
    mapE-atomic {e = cst x} e≢ε e≢· = refl
    mapE-atomic {e = abs x e} e≢ε e≢· = refl
    mapE-atomic {e = mab x e} e≢ε e≢· = refl
    mapE-atomic {e = app e e₁} e≢ε e≢· = refl
    mapE-atomic {e = mtc e e₁ e₂} e≢ε e≢· = refl

    table-value : ∀ v → Value (sub (extSub σ v) ([ v₁ ⦂ μ ↦ weaken v₁′ ] · [ v₂ ⦂ μ ↦ weaken v₂′ ]))
    table-value v =
      (abs v· abs)
        {v≢ε = λ ()}
        {w≢ε = λ ()}
        {v≢· = λ ()}

    table-abs : ∀ v → ALL AbsValue (sub (extSub σ v) ([ v₁ ⦂ μ ↦ weaken v₁′ ] · [ v₂ ⦂ μ ↦ weaken v₂′ ]))
    table-abs v = AP-abs (v-abs μ _) A· AP-abs (v-abs μ _)

    payload-sub : ∀ {m} (τ : Sub m zero) (v : Expr zero) (e : Expr m)
      → sub₁ v (sub (liftSub (extSub τ v)) (weaken (weaken e))) ≡ sub τ e
    payload-sub τ v e
      rewrite sub-lift-weaken {τ = extSub τ v} {e = weaken e}
            | sub₁-weaken {v = v} {e = sub (extSub τ v) (weaken e)}
            | sub-ren {ρ = fsuc} {σ = extSub τ v} {e = e}
            | sub-cong {σ = extSub τ v ∘ fsuc} {τ = τ} (λ x → refl) e
      = refl

    table-β-target : ∀ v
      → v ∈ 𝓥⟦ μ ⟧
      → mapE (λ v₃ → mapE (sub₁ v₃) (foldALL absbody (table-abs v))) v
          ≡ (mtc v₁ v (sub σ v₁′) · mtc v₂ v (sub σ v₂′))
    table-β-target v v∈𝓥μ
      rewrite mapE-atomic
                {e = v}
                {f = λ v₃ →
                  mtc v₁ v₃
                    (sub (sub₁σ v₃)
                      (sub (liftSub (extSub σ v)) (weaken (weaken v₁′))))
                  ·
                  mtc v₂ v₃
                    (sub (sub₁σ v₃)
                      (sub (liftSub (extSub σ v)) (weaken (weaken v₂′))))}
                (𝓥-≢ε v∈𝓥μ)
                (𝓥-≢· v∈𝓥μ)
            | payload-sub σ v v₁′
            | payload-sub σ v v₂′
      = refl

    table-β : ∀ v
      → v ∈ 𝓥⟦ μ ⟧
      → sub (extSub σ v) body ⟶*
          (mtc v₁ v (sub σ v₁′) · mtc v₂ v (sub σ v₂′))
    table-β v v∈𝓥μ
      = subst
          (λ e → sub (extSub σ v) body ⟶* e)
          (table-β-target v v∈𝓥μ)
          (⟶-step (β₁ (table-value v) (table-abs v) (𝓥-value v∈𝓥μ)) ⟶-refl)

    table-app : ∀ v → v ∈ 𝓥⟦ μ ⟧ → sub (extSub σ v) body ∈ 𝓔⟦ ⟨ `? , μ′ ⟩ ⟧
    table-app v v∈𝓥μ
      with v₁ ≟Expr v | v₂ ≟Expr v
    ... | yes v₁≡v | yes v₂≡v =
      ⊥-elim (v₁≢v₂ (trans v₁≡v (sym v₂≡v)))
    ... | yes v₁≡v | no v₂≢v =
      let payload₁ = <:ₙ-subset-𝓔 (<:ₙ-comb <:₀-!? <:ₜ-refl) (Γ⊨v₁′⦂!μ′ σ σ∈𝓖)
          w₁ = proj₁ payload₁
          w₁∈𝓦? = proj₁ (proj₂ payload₁)
          payload₁-red = proj₂ (proj₂ payload₁)
          match₁-red = ⟶*-trans (⟶-step (β-match-eq val-v₁ (𝓥-value v∈𝓥μ) v₁≡v) ⟶-refl) payload₁-red
          match₂-red = ⟶-step (β-match-neq val-v₂ (𝓥-value v∈𝓥μ) v₂≢v) ⟶-refl
      in w₁ , w₁∈𝓦?
      , ⟶*-trans
          (table-β v v∈𝓥μ)
          (⟶*-trans
            (ξ-head-* match₁-red)
            (⟶*-trans
              (ξ-tail-* (value-𝓦 {ημ = ⟨ `? , μ′ ⟩} w₁∈𝓦?) match₂-red)
              (⟶-step mon-ε-unit-right ⟶-refl)))
    ... | no v₁≢v | yes v₂≡v =
      let payload₂ = <:ₙ-subset-𝓔 (<:ₙ-comb <:₀-!? <:ₜ-refl) (Γ⊨v₂′⦂!μ′ σ σ∈𝓖)
          w₂ = proj₁ payload₂
          w₂∈𝓦? = proj₁ (proj₂ payload₂)
          payload₂-red = proj₂ (proj₂ payload₂)
          match₁-red = ⟶-step (β-match-neq val-v₁ (𝓥-value v∈𝓥μ) v₁≢v) ⟶-refl
          match₂-red = ⟶*-trans (⟶-step (β-match-eq val-v₂ (𝓥-value v∈𝓥μ) v₂≡v) ⟶-refl) payload₂-red
      in w₂ , w₂∈𝓦?
      , ⟶*-trans
          (table-β v v∈𝓥μ)
          (⟶*-trans
            (ξ-head-* match₁-red)
            (⟶*-trans
              (⟶-step mon-ε-unit-left ⟶-refl)
              match₂-red))
    ... | no v₁≢v | no v₂≢v =
      let match₁-red = ⟶-step (β-match-neq val-v₁ (𝓥-value v∈𝓥μ) v₁≢v) ⟶-refl
          match₂-red = ⟶-step (β-match-neq val-v₂ (𝓥-value v∈𝓥μ) v₂≢v) ⟶-refl
      in ε , (Aε , tt , z≤n , z≤n)
      , ⟶*-trans
          (table-β v v∈𝓥μ)
          (⟶*-trans
            (ξ-head-* match₁-red)
            (⟶*-trans
              (⟶-step mon-ε-unit-left ⟶-refl)
              match₂-red))

    table∈𝓥 : sub σ table ∈ 𝓥⟦ μ ⇒ ⟨ `? , μ′ ⟩ ⟧
    table∈𝓥 =
      μ
      , sub (liftSub σ) body
      , refl
      , <:ₜ-refl
      , λ v v∈𝓥μ →
          subst
            (λ e → e ∈ 𝓔⟦ ⟨ `? , μ′ ⟩ ⟧)
            (sub-ext-lift {σ = σ} {v = v} {e = body})
            (table-app v v∈𝓥μ)
