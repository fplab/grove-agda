module Grove where

open import Data.Nat hiding (_≟_; _⊔_)
open import Data.Bool hiding (_<_; _≟_)
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary
open import Relation.Nullary
open import Function.Equivalence hiding (_∘_)
open import Function using (_∘′_)
open import Level using (Level)
open import Axiom.Extensionality.Propositional
open import Data.Product
open import Function.Equality using (_⟨$⟩_)

postulate
  extensionality : {ℓ₁ ℓ₂ : Level} → Extensionality ℓ₁ ℓ₂

postulate
  Ctor : Set
  ctorRoot : Ctor
  _≟ℂ_ : (c1 c2 : Ctor) → Dec (c1 ≡ c2)
  arity : Ctor → ℕ
  arityRoot : arity ctorRoot ≡ 1

record Vertex : Set where
  constructor V
  field
    ctor : Ctor
    iden : ℕ

record Edge : Set where
  constructor E
  field
    parent : Vertex
    child : Vertex
    index : ℕ
    iden : ℕ
    .valid : iden < arity (Vertex.ctor parent)

data EdgeState : Set where
  ⊥ : EdgeState
  + : EdgeState
  - : EdgeState

_⊔_ : EdgeState → EdgeState → EdgeState
- ⊔ _ = -
_ ⊔ - = -
+ ⊔ _ = +
_ ⊔ + = +
_ ⊔ _ = ⊥

⊔-assoc : {t1 t2 t3 : EdgeState} → (t1 ⊔ (t2 ⊔ t3)) ≡ ((t1 ⊔ t2) ⊔ t3)
⊔-assoc {⊥} {⊥} {⊥} = refl
⊔-assoc {⊥} {⊥} {+} = refl
⊔-assoc {⊥} {⊥} { - } = refl
⊔-assoc {⊥} {+} {⊥} = refl
⊔-assoc {⊥} {+} {+} = refl
⊔-assoc {⊥} {+} { - } = refl
⊔-assoc {⊥} { - } {⊥} = refl
⊔-assoc {⊥} { - } {+} = refl
⊔-assoc {⊥} { - } { - } = refl
⊔-assoc {+} {⊥} {⊥} = refl
⊔-assoc {+} {⊥} {+} = refl
⊔-assoc {+} {⊥} { - } = refl
⊔-assoc {+} {+} {⊥} = refl
⊔-assoc {+} {+} {+} = refl
⊔-assoc {+} {+} { - } = refl
⊔-assoc {+} { - } {⊥} = refl
⊔-assoc {+} { - } {+} = refl
⊔-assoc {+} { - } { - } = refl
⊔-assoc { - } {⊥} {⊥} = refl
⊔-assoc { - } {⊥} {+} = refl
⊔-assoc { - } {⊥} { - } = refl
⊔-assoc { - } {+} {⊥} = refl
⊔-assoc { - } {+} {+} = refl
⊔-assoc { - } {+} { - } = refl
⊔-assoc { - } { - } {⊥} = refl
⊔-assoc { - } { - } {+} = refl
⊔-assoc { - } { - } { - } = refl

⊔-comm : {t1 t2 : EdgeState} → t1 ⊔ t2 ≡ t2 ⊔ t1
⊔-comm {⊥} {⊥} = refl
⊔-comm {⊥} {+} = refl
⊔-comm {⊥} { - } = refl
⊔-comm {+} {⊥} = refl
⊔-comm {+} {+} = refl
⊔-comm {+} { - } = refl
⊔-comm { - } {⊥} = refl
⊔-comm { - } {+} = refl
⊔-comm { - } { - } = refl

Graph : Set
Graph = Edge → EdgeState

data Action : Set where
  Action+ : Edge → Action
  Action- : Edge → Action

_≟Vertex_ : (v1 v2 : Vertex) → Dec (v1 ≡ v2)
V ctor1 iden1 ≟Vertex V ctor2 iden2 with ctor1 ≟ℂ ctor2 | iden1 Data.Nat.≟ iden2
... | yes refl | yes refl = yes refl
... | _ | no p = no (λ { refl → p refl })
... | no p | _ = no (λ { refl → p refl })

_≟Edge_ : (e1 e2 : Edge) → Dec (e1 ≡ e2)
E parent1 child1 index1 iden1 _ ≟Edge E parent2 child2 index2 iden2 _
  with parent1 ≟Vertex parent2 | child1 ≟Vertex child2 | index1 Data.Nat.≟ index2 | iden1 Data.Nat.≟ iden2
... | yes refl | yes refl | yes refl | yes refl = yes refl
... | no p | _ | _ | _ = no (λ { refl → p refl })
... | _ | no p | _ | _ = no (λ { refl → p refl })
... | _ | _ | no p | _ = no (λ { refl → p refl })
... | _ | _ | _ | no p = no (λ { refl → p refl })

{-
Edge-eta : (e : Edge) →  E (Edge.parent e) (Edge.child e) (Edge.index e) (Edge.iden e) (Edge.valid e) ≡ e
Edge-eta e = refl
-}

≟Edge-eq : (e : Edge) → does (e ≟Edge e) ≡ true
≟Edge-eq (E parent child index iden valid) with E parent child index iden valid ≟Edge E parent child index iden valid
... | yes p = refl
... | no p with p refl
... | ()

≟Edge-neq : {e1 e2 : Edge} → ¬ e1 ≡ e2  → does (e1 ≟Edge e2) ≡ false
≟Edge-neq {E parent1 child1 index1 iden1 valid1} {E parent2 child2 index2 iden2 valid2} neq with E parent1 child1 index1 iden1 valid1 ≟Edge E parent2 child2 index2 iden2 valid2
... | no p = refl
... | yes refl with neq refl
... | ()

_[_↦_] :  Graph → Edge → EdgeState → Graph
_[_↦_] f k v = λ { x → if does (x ≟Edge k) then v ⊔ f x else f x }

⟦_⟧ : Action → Graph → Graph
⟦ (Action+ e) ⟧ g = g [ e ↦ EdgeState.+ ]
⟦ (Action- e) ⟧ g = g [ e ↦ EdgeState.- ]

data ActionRel : Graph → Action → Graph → Set where
  AR : (a : Action) → (g : Graph)  → ActionRel g a (⟦ a ⟧ g)

-- TODO: idempotent: ⟦ a ⟧ ∘ ⟦ a ⟧ = ⟦ a ⟧

thm : {g g' : Graph} {a : Action} → ActionRel g a g' ⇔ g' ≡ ⟦ a ⟧ g
thm {g} {g'} {a} = equivalence to from where
  to : ActionRel g a g' → g' ≡ ⟦ a ⟧ g
  to (AR .a .g) = refl
  from : g' ≡ ⟦ a ⟧ g → ActionRel g a g'
  from refl = AR a g

ext-comm : {t1 t2 : EdgeState} {e1 e2 : Edge} {g : Graph} → ((g [ e1 ↦ t1 ]) [ e2 ↦ t2 ]) ≡ ((g [ e2 ↦ t2 ]) [ e1 ↦ t1 ])
ext-comm {t1} {t2} {e1} {e2} {g} = extensionality go where
  go : (e : Edge) → ((g [ e1 ↦ t1 ]) [ e2 ↦ t2 ]) e ≡ ((g [ e2 ↦ t2 ]) [ e1 ↦ t1 ]) e
  go e with e ≟Edge e1 | e ≟Edge e2
  ... | yes refl | yes refl rewrite ⊔-assoc {t1} {t2} {g e} | ⊔-assoc {t2} {t1} {g e} | ⊔-comm {t1} {t2} = refl
  ... | no _ | yes refl = refl
  ... | yes refl | no _ = refl
  ... | no _ | no _ = refl

comm' : (a1 a2 : Action) (g : Graph) → ⟦ a1 ⟧ (⟦ a2 ⟧ g) ≡ ⟦ a2 ⟧ (⟦ a1 ⟧ g)
comm' (Action+ e₁) (Action+ e₂) g = ext-comm {+} {+} {e₂} {e₁}
comm' (Action+ e₁) (Action- e₂) g = ext-comm { - } {+} {e₂} {e₁}
comm' (Action- e₁) (Action+ e₂) g = ext-comm {+} { - } {e₂} {e₁}
comm' (Action- e₁) (Action- e₂) g = ext-comm { - } { - } {e₂} {e₁}

comm : (a1 a2 : Action) → ⟦ a1 ⟧ ∘′ ⟦ a2 ⟧ ≡ ⟦ a2 ⟧ ∘′ ⟦ a1 ⟧
comm a1 a2 = extensionality (comm' a1 a2)

comm2 : {a1 a2 : Action} {g1 g2 g3 g2' g3' : Graph} → ActionRel g1 a1 g2 → ActionRel g2 a2 g3 → ActionRel g1 a2 g2' → ActionRel g2' a1 g3' → g3 ≡ g3'
comm2 {a1} {a2} {g1} {g2} {g3} {g2'} {g3'} ar1 ar2 ar2' ar1' = eqgg where
  eqg2 : g2 ≡ ⟦ a1 ⟧ g1
  eqg2 = Equivalence.to thm ⟨$⟩ ar1
  eqg3 : g3 ≡ ⟦ a2 ⟧ (⟦ a1 ⟧ g1)
  eqg3 with eqg2
  ... | refl = Equivalence.to thm ⟨$⟩ ar2
  eqg2' : g2' ≡ ⟦ a2 ⟧ g1
  eqg2' = Equivalence.to thm ⟨$⟩ ar2'
  eqg3' : g3' ≡ ⟦ a1 ⟧ (⟦ a2 ⟧ g1)
  eqg3' with eqg2'
  ... | refl = Equivalence.to thm ⟨$⟩ ar1'
  eqgg : g3 ≡ g3'
  eqgg with eqg3 | eqg3'
  ... | refl | refl = comm' a2 a1 g1
