A Logical Relation for linear GV
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Expressions and values
~~~~~~~~~~~~~~~~~~~~~~

M, N ::= x | λx.M | M N | * | (M, N) | let x, y = M in N
       | send M N | recv M | term M | wait M

V, W ::= x | λx.M | * | (V, W)

Expression evaluation contexts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

𝓔 ::= □ | 𝓔 N | V 𝓔 | (𝓔, N) | (V, 𝓔) | let x, y = 𝓔 in N
    | send 𝓔 N | send V 𝓔 | recv 𝓔 | close 𝓔

[τ-transitions: standard β-value reductions (omitted)]
[labeled transitions]

send c V ⟶c!V  c
recv c   ⟶c?V  (V, c)
term c   ⟶c!   *
wait c   ⟶c?   *

fork V   ⟶fork(V) 

Expression types
~~~~~~~~~~~~~~~~

T, U ::= 𝟙 | T ⊸ U | T ⊗ U | S
S    ::= end! | end? | !T.S | ?T.S

Γ ::= ∅ | Γ, x:T

Γ ⊢ M : T

Processes
~~~~~~~~~

P, Q ::= ⟨ M ⟩ | P ∥ Q | (νab. P)

deadlock free:
P, Q ::= ⟨ M ⟩ | P ∥ Q | (νc. P ∥ Q)

Process evaluation contexts
~~~~~~~~~~~~~~~~~~~~~~~~~~~

𝓟, 𝓠 ::= ⟨ 𝓔 ⟩ ∣ 𝓟 ∥ Q | Q ∥ 𝓟

[key labeled transition: labels match up to a silent transition]

P ⟶α P′
Q ⟶α̂ Q′
----------------
P ∥ Q ⟶ P′ ∥ Q′

P ⟶cX P′
Q ⟶cX̂ Q′
----------------------------
(νc. P ∥ Q) ⟶ (νc. P′ ∥ Q′)

P ⟶c! P′
Q ⟶c? Q′
----------------------------
(νc. P ∥ Q) ⟶ (P′ ∥ Q′)

Process typing
~~~~~~~~~~~~~~

Σ ::= ∅ | Σ, x:S                -- only channels in environment Σ

Σ ⊢ P

Binary logical relation
~~~~~~~~~~~~~~~~~~~~~~~

(P, Q) ∈ 𝓛⟦ Σ ⊢ U ⟧

  iff
  either P = ⟨ V ⟩, Q = ⟨ W ⟩ for some (V, W) ∈ 𝓥⟦ Σ ⊢ U ⟧
  or one of the following holds:

  * Σ = Σ′, Σ″, c: !T.S  and P = 𝓟[ send V c ], Q = 𝓠[ send W c ] for some V, W such that (V, W) ∈ 𝓥⟦ Σ′ ⊢ T ⟧ and (𝓟[ c ], 𝓠[ c ]) ∈ 𝓜⟦ Σ″, c: S ⊢ U ⟧

  * Σ = Σ″, c: ?T.S      and P = 𝓟[ recv c ], Q = 𝓠[ recv c] and for all Σ′, V, W such that (V, W) ∈ 𝓥⟦ Σ′ ⊢ T ⟧, (𝓟[ (V, c) ], 𝓠[ (W, c) ]) ∈ 𝓜⟦ Σ′, Σ″, c: S ⊢ U ⟧

  * Σ = Σ′, c: end!      and P = 𝓟[ term c ], Q = 𝓠[ term c] and (𝓟[ * ], 𝓠[ * ]) ∈ 𝓜⟦ Σ′ ⊢ U ⟧

  * Σ = Σ′, c: end?      and P = 𝓟[ wait c ], Q = 𝓠[ wait c] and (𝓟[ * ], 𝓠[ * ]) ∈ 𝓜⟦ Σ′ ⊢ U ⟧


(P, Q) ∈ 𝓜⟦ Σ ⊢ U ⟧   iff   P ⟶* P′ and Q ⟶* Q′ (τ steps), P′, Q′ irreducible, and (P′, Q′) ∈ 𝓛⟦ Σ ⊢ U ⟧

* maybe 𝓜 should be "one way" as in: `if P ⟶* P′ irred, then Q ⟶* Q′ irred and (P′, Q′) ∈ 𝓛⟦ Σ ⊢ U ⟧
* Bas: both could work, but in the "one way" case you'd need a symmetric variant as well.

(M, N) ∈ 𝓥⟦ ∅ ⊢ 𝟙 ⟧ iff M = * and N = *

(M, N) ∈ 𝓥⟦ Σ ⊢ T → U ⟧ iff M = λx.M′ , N = λx.N′ and for all Σ′, V, W such that (V, W) ∈ 𝓥⟦ Σ′ ⊢ T ⟧, (M′[V/x], N′[W/x]) ∈ 𝓔⟦ Σ, Σ′ ⊢ U ⟧

(M, N) ∈ 𝓥⟦ Σ, Σ′ ⊢ T × U ⟧ iff M = (V, V′), N = (W, W′) and (V, W) ∈ 𝓥⟦ Σ ⊢ T ⟧ and (V′, W′) ∈ 𝓥⟦ Σ′ ⊢ U ⟧

(M, N) ∈ 𝓥⟦ c: S ⊢ S ⟧ iff M = c and N = c


(M, N) ∈ 𝓔⟦ Σ ⊢ T ⟧   iff (⟨ M ⟩ , ⟨ N ⟩) ∈ 𝓜⟦ Σ ⊢ T ⟧

Closing substitution
~~~~~~~~~~~~~~~~~~~~

𝓖⟦ ∅ ⊢ ∅ ⟧ = { (∅, ∅) }

𝓖⟦ Σ, Σ′ ⊢ Γ, x: T ⟧ = { (γ₁[x ↦ V] , γ₂[x ↦ V′]) | (γ₁, γ₂) ∈ Γ⟦ Σ ⊢ Γ ⟧, (V₁, V₂) ∈ 𝓥⟦ Σ′ ⊢ T ⟧ }

Fundamental Lemma
~~~~~~~~~~~~~~~~~

(I)  If Σ, Γ ⊢ M : T
     then for all (γ₁, γ₂) ∈ 𝓖⟦ Σ ⊢ Γ ⟧,
                  (γ₁ (M), γ₂ (M)) ∈ 𝓔⟦ Σ ⊢ T ⟧

(II) If Σ, Γ ⊢ M : T
     then for all process contexts 𝓟 and all (γ₁, γ₂) ∈ 𝓖⟦ Σ ⊢ Γ ⟧,
                  (𝓟[ γ₁ (M) ], 𝓟[ γ₂ (M) ]) ∈ 𝓜⟦ Σ ⊢ T ⟧

Proof:

* Case x:

    x: T ⊢ x : T

    (γ₁, γ₂) ∈ 𝓖⟦ Σ ⊢ ∅, x:T ⟧
    ⇒ By def of 𝓖, (γ₁(x), γ₂(x)) ∈ 𝓥⟦ Σ ⊢ T ⟧
    ⇒ (⟨ γ₁(x) ⟩, ⟨ γ₂(x) ⟩) ∈ 𝓛⟦ Σ ⊢ T ⟧ ⊆ 𝓜⟦ Σ ⊢ T ⟧
    ⇒ (γ₁(x), γ₂(x)) ∈  𝓔⟦ Σ ⊢ T ⟧
    ∎

* Case λx.M:

    Σ, Γ, x:T ⊢ M : U
    -------------------
    Σ, Γ ⊢ λx.M : T → U

    Let (γ₁, γ₂) ∈ 𝓖⟦ Σ ⊢ Γ ⟧

    Show that (γ₁(λx.M), γ₂(λx.M)) ∈ 𝓔⟦ Σ ⊢ T → U ⟧
    It's enough to show (γ₁(λx.M), γ₂(λx.M)) ∈ 𝓥⟦ Σ ⊢ T → U ⟧
    ⇐ for all Σ′, V, W such that (V, W) ∈ 𝓥⟦ Σ′ ⊢ T ⟧, (γ₁(M)[V/x], γ₂(M)[W/x]) ∈ 𝓔⟦ Σ, Σ′ ⊢ U ⟧
    ⇐ for all (γ₁′, γ₂′) ∈ 𝓖⟦ Σ, Σ′ ⊢ Γ, x:T ⟧ we have (γ₁′ (M), γ₂′ (M)) ∈ 𝓔⟦ Σ, Σ′ ⊢ U ⟧
    ⇐ by the IH
    ∎

* Case M N:

    Γ₁ ⊢ M : T → U
    Γ₂ ⊢ N : T
    ---------------
    Γ₁, Γ₂ ⊢ M N : U

    Let (γ₁, γ₂) ∈ 𝓖⟦ Σ ⊢ Γ₁, Γ₂ ⟧

    (complication due to linearity...)
    Lemma: we can split Σ = Σ′, Σ″ and γ₁ = γ₁′, γ₁″ and γ₂ = γ₂′, γ₂″
           such that (γ₁′, γ₂′) ∈ 𝓖⟦ Σ′ ⊢ Γ₁ ⟧ and (γ₁″, γ₂″) ∈ 𝓖⟦ Σ″ ⊢ Γ₂ ⟧.
           Then γᵢ(M N) = γᵢ′(M) γᵢ″ (N)

    Show that (γ₁′(M) γ₁″(N), γ₂′(M) γ₂″(N)) ∈ 𝓔⟦ Σ′, Σ″ ⊢ U ⟧

    BELOW is WRONG: we need to consider reduction sequences starting from (γ₁′(M) γ₁″(N), γ₂′(M) γ₂″(N)) to some irreducible (X, Y)

    ⇒ By induction on the typing derivation/structure of the term we obtain:  (γ₁′(M), γ₂′(M)) ∈ 𝓔⟦ Σ′ ⊢ T → U ⟧
    ⇒ (⟨ γ₁′(M) ⟩, ⟨ γ₂′(M) ⟩) ∈ 𝓜⟦ Σ′ ⊢ T → U ⟧
    ⇒ (A1) ∃ M₁, M₂ (irreducible) such that γ₁′(M) ⟶* M₁ and γ₂′(M) ⟶* M₂ with τ reductions such that (⟨ M₁ ⟩, ⟨ M₂ ⟩) ∈ 𝓛⟦ Σ′ ⊢ T → U ⟧
    ⇒ by call-by-value reduction: γ₁′(M) γ₁″(N) ⟶* M₁ γ₁″(N)  and  γ₂′(M) γ₂″(N) ⟶* M₂ γ₂″(N)
    ⇒ two cases: M₁ and M₂ are values or they are both stuck on a communication

    ** Case stuck on communication (sketchy, case term):
      "the pair (γ₁′(M) γ₁″(N), γ₂′(M) γ₂″(N)) also gets stuck on this same communication and we argue by induction on Σ′ (where either the session type gets smaller or the channel gets closed)"
      ⇒ M₁ γ₁″(N)  and   M₂ γ₂″(N) are also irreducible
      ⇒ (from A1:) Σ = Σ′, c: end! and M₁ = 𝓔₁[ term c ] and M₂ = 𝓔₂[ term c ] and (⟨ 𝓔₁[ * ] ⟩, ⟨ 𝓔₂[ * ] ⟩) ∈ 𝓜⟦ Σ′ ⊢ T → U ⟧
      ⇒ Σ = Σ′, Σ″, c: end! and (⟨ 𝓔₁[ * ] γ₁″(N) ⟩, ⟨ 𝓔₂[ * ] γ₂″(N) ⟩) ∈ 𝓜⟦ Σ′, Σ″ ⊢ U ⟧

    ** Case  M₁ and M₂ are values V₁ and V₂; then (V₁, V₂) ∈ 𝓥⟦ Σ′ ⊢ T → U ⟧
      ⇒ By induction (γ₁″(N), γ₂″(N)) ∈ 𝓔⟦ Σ″ ⊢ T ⟧
      ⇒ (⟨ γ₁″(N) ⟩, ⟨ γ₂″(N) ⟩) ∈ 𝓜⟦ Σ″ ⊢ T ⟧
      ⇒ ∃ N₁, N₂ (irreducible) such that γ₁″(N) ⟶* N₁ and γ₂″(N) ⟶* N₂ with τ reductions such that (⟨ N₁ ⟩, ⟨ N₂ ⟩) ∈ 𝓛⟦ Σ″ ⊢ T ⟧
      ⇒ by call-by-value reduction: V₁ γ₁″(N) ⟶* V₁ N₁  and  V₂ γ₂″(N) ⟶* V₂ N₂
      ⇒ two cases: N₁ and N₂ are values or they are both stuck on a communication

      ** Case stuck on communication (sketchy):
         the pair (V₁ γ₁″(N), V₂ γ₂″(N)) also gets stuck on this same communication and we argue by induction on Σ″ (where either the session type gets smaller or the channel gets closed)

      ** Case N₁ and N₂ are values (W₁, W₂) ∈ 𝓥⟦ Σ″ ⊢ T ⟧
        ⇒ As (V₁, V₂) ∈ 𝓥⟦ Σ′ ⊢ T → U ⟧
        ⇒ V₁ = λx.M₁′ , V₂ = λx.M₂′ and for all Σ″, W₁, W₂ such that (W₁, W₂) ∈ 𝓥⟦ Σ″ ⊢ T ⟧, (M₁′[W₁/x], M₂′[W₂/x]) ∈ 𝓔⟦ Σ′, Σ″ ⊢ U ⟧
        ⇒ which finally proves the claim!
    ∎


      
----------------------------------------------------------------------

* another attempt: unary logical relation

  * assume that expression processes have type 1
  * to satisfy  |Σ′| ≤ |T|

    * restrict types to nested pairs that may contain sessions
    * add effects (presence channel operations) to types: effect-free functions satisfy the assumption

  * need a distinguished thread!

P ∈ 𝓛⟦ Σ ⟧

    iff

    Σ = Σ″, c: ?T.S 
    P = 𝓟[ recv c ]
    for all Σ′, V such that V ∈ 𝓥⟦ Σ′ ⊢ T ⟧
    𝓟[ (V, c) ] ∈ 𝓜⟦ Σ′, Σ″, c: S ⟧
    ( requires |Σ′| ≤ |T| )

  or

    Σ = Σ′, Σ″, c: !T.S
    P = 𝓟[ send V c ]
    V ∈ 𝓥⟦ Σ′ ⊢ T ⟧
    𝓟[ c ] ∈ 𝓜⟦ Σ″, c: S ⟧

  or (case for term)

  or (case for wait)

  or

    Σ = ∅
    P ≈ ⟨*⟩ ∥ ⋯ ∥ ⟨*⟩

P ∈ 𝓜⟦ Σ ⟧

    iff

    ∀ P′ such that P →* P′ (τ transitions) and P′ irreducible:
    P′ ∈ 𝓛⟦ Σ ⟧
    

M ∈ 𝓥⟦ ∅ ⊢ 𝟙 ⟧ iff M = * 

M ∈ 𝓥⟦ Σ ⊢ T ⊸ U ⟧ iff M = λx.M′ and for all Σ′, V such that V ∈ 𝓥⟦ Σ′ ⊢ T ⟧, M′[V/x] ∈ 𝓔⟦ Σ, Σ′ ⊢ U ⟧

M ∈ 𝓥⟦ Σ, Σ′ ⊢ T ⊗ U ⟧ iff M = (V, V′) and V ∈ 𝓥⟦ Σ ⊢ T ⟧ and V′ ∈ 𝓥⟦ Σ′ ⊢ U ⟧

M ∈ 𝓥⟦ c: S ⊢ S ⟧ iff M = c


M ∈ 𝓔⟦ Σ ⊢ T ⟧   iff ∀ N. Σ, M ⟶λ,π* Σ′, N and irred N ⇒ N ∈ 𝓥⟦ Σ′ ⊢ T ⟧

Closing substitution
~~~~~~~~~~~~~~~~~~~~

𝓖⟦ ∅ ⊢ ∅ ⟧ = { ∅ }

𝓖⟦ Σ, Σ′ ⊢ Γ, x: T ⟧ = { γ[x ↦ V] | γ ∈ 𝓖⟦ Σ ⊢ Γ ⟧, V ∈ 𝓥⟦ Σ′ ⊢ T ⟧ }


Semantic type safety
--------------------

Σ, Γ ⊨ e : T  ⇔ ∀ γ ∈ 𝓖⟦ Σ, Γ ⟧ . γ(e) ∈ 𝓔⟦ Σ ⊢ T ⟧
