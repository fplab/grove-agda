open import Axiom.Extensionality.Propositional
open import Data.Bool hiding (_<_; _≟_)
open import Data.Nat hiding (_+_; _⊔_)
open import Function.Equivalence hiding (_∘_)
open import Function hiding (_⇔_)
open import Function.Equality using (_⟨$⟩_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary

module Grove.Core.Properties.ActionCommutative
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

private
  import Grove.Core.Graph
  open module Graph = Grove.Core.Graph Ctor _≟ℂ_ arity
  import Grove.Core.CGraph
  open module CGraph = Grove.Core.CGraph Ctor _≟ℂ_ arity

_[_↦_] :  CGraph → Edge → EdgeState → CGraph
_[_↦_] f k v = λ { x → if does (x ≟Edge k) then v ⊔ f x else f x }

[↦]-comm : (s₁ s₂ : EdgeState) (e₁ e₂ : Edge) (g : CGraph)
  → (g [ e₁ ↦ s₁ ]) [ e₂ ↦ s₂ ]
  ≡ (g [ e₂ ↦ s₂ ]) [ e₁ ↦ s₁ ]
[↦]-comm s₁ s₂ e₁ e₂ g = extensionality go where
  go : (e : Edge) → ((g [ e₁ ↦ s₁ ]) [ e₂ ↦ s₂ ]) e ≡ ((g [ e₂ ↦ s₂ ]) [ e₁ ↦ s₁ ]) e
  go e with e ≟Edge e₁ | e ≟Edge e₂
  ... | yes refl | yes refl rewrite ⊔-assoc s₁ s₂ (g e) | ⊔-assoc s₂ s₁ (g e) | ⊔-comm s₁ s₂ = refl
  ... | no _ | yes refl = refl
  ... | yes refl | no _ = refl
  ... | no _ | no _ = refl

[↦]-join : (s₁ s₂ : EdgeState) (e : Edge) (g : CGraph)
  → (g [ e ↦ s₁ ]) [ e ↦ s₂ ]
  ≡ g [ e ↦ s₁ ⊔ s₂ ]
[↦]-join s₁ s₂ e g = extensionality go where
  go : (e' : Edge) → ((g [ e ↦ s₁ ]) [ e ↦ s₂ ]) e' ≡ (g [ e ↦ s₁ ⊔ s₂ ]) e'
  go e' with e' ≟Edge e
  ... | yes refl rewrite ⊔-assoc s₂ s₁ (g e) | ⊔-comm s₁ s₂ = refl
  ... | no _ = refl

----------------
-- Action
----------------

data Action : Set where
  A : Edge → EdgeState → Action
 
⟦_⟧ : Action → CGraph → CGraph
⟦ (A e s) ⟧ g = g [ e ↦ s ]

⟦⟧-comm' : (a₁ a₂ : Action) (g : CGraph)
  → ⟦ a₁ ⟧ (⟦ a₂ ⟧ g)
  ≡ ⟦ a₂ ⟧ (⟦ a₁ ⟧ g)
⟦⟧-comm' (A e₁ s₁) (A e₂ s₂) g = [↦]-comm s₂ s₁ e₂ e₁ g

⟦⟧-comm : (a₁ a₂ : Action)
  → ⟦ a₁ ⟧ ∘′ ⟦ a₂ ⟧
  ≡ ⟦ a₂ ⟧ ∘′ ⟦ a₁ ⟧
⟦⟧-comm a₁ a₂ = extensionality (⟦⟧-comm' a₁ a₂)

⟦⟧-idem' : (a : Action) (g : CGraph)
  → ⟦ a ⟧ (⟦ a ⟧ g)
  ≡ ⟦ a ⟧ g
⟦⟧-idem' (A e s) g rewrite [↦]-join s s e g with s
... | ⊥ = refl
... | + = refl
... | - = refl

⟦⟧-idem : (a : Action)
  → ⟦ a ⟧ ∘′ ⟦ a ⟧
  ≡ ⟦ a ⟧
⟦⟧-idem a = extensionality (⟦⟧-idem' a)

----------------
-- Action Relation Between CGraphs
----------------

data ActionRel : CGraph → Action → CGraph → Set where
  AR : (a : Action) → (g : CGraph) → ActionRel g a (⟦ a ⟧ g)

ActionRel-eqv : {g g' : CGraph} {a : Action}
  → ActionRel g a g' ⇔ g' ≡ ⟦ a ⟧ g
ActionRel-eqv {g} {g'} {a} = equivalence to from where
  to : ActionRel g a g' → g' ≡ ⟦ a ⟧ g
  to (AR .a .g) = refl
  from : g' ≡ ⟦ a ⟧ g → ActionRel g a g'
  from refl = AR a g

ActionRel-comm : {a₁ a₂ : Action} {g₁ g₂₁ g₃₁ g₂₂ g₃₂ : CGraph}
  → ActionRel g₁ a₁ g₂₁ → ActionRel g₂₁ a₂ g₃₁
  → ActionRel g₁ a₂ g₂₂ → ActionRel g₂₂ a₁ g₃₂
  → g₃₁ ≡ g₃₂
ActionRel-comm {a₁} {a₂} {g₁} {g₂₁} {g₃₁} {g₂₂} {g₃₂} ar₁ ar₂ ar₂₂ ar₁' = eqgg where
  eqg₂ : g₂₁ ≡ ⟦ a₁ ⟧ g₁
  eqg₂ = Equivalence.to ActionRel-eqv ⟨$⟩ ar₁
  eqg₃ : g₃₁ ≡ ⟦ a₂ ⟧ (⟦ a₁ ⟧ g₁)
  eqg₃ with eqg₂
  ... | refl = Equivalence.to ActionRel-eqv ⟨$⟩ ar₂
  eqg₂₂ : g₂₂ ≡ ⟦ a₂ ⟧ g₁
  eqg₂₂ = Equivalence.to ActionRel-eqv ⟨$⟩ ar₂₂
  eqg₃₂ : g₃₂ ≡ ⟦ a₁ ⟧ (⟦ a₂ ⟧ g₁)
  eqg₃₂ with eqg₂₂
  ... | refl = Equivalence.to ActionRel-eqv ⟨$⟩ ar₁'
  eqgg : g₃₁ ≡ g₃₂
  eqgg with eqg₃ | eqg₃₂
  ... | refl | refl = ⟦⟧-comm' a₂ a₁ g₁