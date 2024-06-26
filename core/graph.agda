-- open import prelude



module core.graph where

open import Axiom.Extensionality.Propositional
open import Data.Bool hiding (_<_; _≟_)
open import Function.Equivalence hiding (_∘_)
open import Function hiding (_⇔_)
open import Function.Equality using (_⟨$⟩_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary

postulate
  extensionality : {ℓ₁ ℓ₂ : Level} → Extensionality ℓ₁ ℓ₂






----------------
-- Constructors
----------------

postulate
  Ctor : Set
  _≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂)

----------------
-- Positions
----------------

postulate
  Pos : Set
  _≟ℙ_ : (p₁ p₂ : Pos) → Dec (p₁ ≡ p₂)
  _∈ℙ_ : Pos → Ctor → Set

----------------
-- Identifiers
----------------

postulate
  Ident : Set
  _≟𝕀_ : (i₁ i₂ : Ident) → Dec (i₁ ≡ i₂)

----------------
-- The Root Vertex
----------------

-- Note actually used in the proofs, but here it is anyway
postulate
  ctorRoot : Ctor
  posRoot : Pos
  posRoot∈ctorRoot : posRoot ∈ℙ ctorRoot
  identRoot : Ident

----------------
-- Vertex
----------------

record Vertex : Set where
  constructor V
  field
    ctor : Ctor
    ident : Ident

_≟Vertex_ : (v₁ v₂ : Vertex) → Dec (v₁ ≡ v₂)
V c₁ i₁ ≟Vertex V c₂ i₂ with c₁ ≟ℂ c₂ | i₁ ≟𝕀 i₂
... | yes refl | yes refl = yes refl
... | _        | no p     = no (λ { refl → p refl })
... | no p     | _        = no (λ { refl → p refl })

----------------
-- Edge
----------------

record Edge : Set where
  constructor E
  field
    parent : Vertex
    child : Vertex
    position : Pos
    ident : Ident
    .isValid : position ∈ℙ Vertex.ctor parent

_≟Edge_ : (e₁ e₂ : Edge) → Dec (e₁ ≡ e₂)
E parent₁ child₁ position₁ ident₁ _ ≟Edge E parent₂ child₂ position₂ ident₂ _
  with parent₁ ≟Vertex parent₂
     | child₁ ≟Vertex child₂
     | position₁ ≟ℙ position₂
     | ident₁ ≟𝕀 ident₂
... | yes refl | yes refl | yes refl | yes refl = yes refl
... | no p     | _        | _        | _        = no (λ { refl → p refl })
... | _        | no p     | _        | _        = no (λ { refl → p refl })
... | _        | _        | no p     | _        = no (λ { refl → p refl })
... | _        | _        | _        | no p     = no (λ { refl → p refl })

----------------
-- EdgeState
----------------

data EdgeState : Set where
  bot : EdgeState -- smallest -- TODO Use another symbol or bot
  + : EdgeState -- middle
  - : EdgeState -- largest

_⊔_ : EdgeState → EdgeState → EdgeState
- ⊔ _ = -
_ ⊔ - = -
+ ⊔ _ = +
_ ⊔ + = +
_ ⊔ _ = bot

⊔-assoc : (s₁ s₂ s₃ : EdgeState) → (s₁ ⊔ (s₂ ⊔ s₃)) ≡ ((s₁ ⊔ s₂) ⊔ s₃)
⊔-assoc bot bot bot = refl
⊔-assoc bot bot + = refl
⊔-assoc bot bot - = refl
⊔-assoc bot + bot = refl
⊔-assoc bot + + = refl
⊔-assoc bot + - = refl
⊔-assoc bot - bot = refl
⊔-assoc bot - + = refl
⊔-assoc bot - - = refl
⊔-assoc + bot bot = refl
⊔-assoc + bot + = refl
⊔-assoc + bot - = refl
⊔-assoc + + bot = refl
⊔-assoc + + + = refl
⊔-assoc + + - = refl
⊔-assoc + - bot = refl
⊔-assoc + - + = refl
⊔-assoc + - - = refl
⊔-assoc - bot bot = refl
⊔-assoc - bot + = refl
⊔-assoc - bot - = refl
⊔-assoc - + bot = refl
⊔-assoc - + + = refl
⊔-assoc - + - = refl
⊔-assoc - - bot = refl
⊔-assoc - - + = refl
⊔-assoc - - - = refl

⊔-comm : (s₁ s₂ : EdgeState) → s₁ ⊔ s₂ ≡ s₂ ⊔ s₁
⊔-comm bot bot = refl
⊔-comm bot + = refl
⊔-comm bot - = refl
⊔-comm + bot = refl
⊔-comm + + = refl
⊔-comm + - = refl
⊔-comm - bot = refl
⊔-comm - + = refl
⊔-comm - - = refl

⊔-idem : (s : EdgeState) → s ⊔ s ≡ s
⊔-idem bot = refl
⊔-idem + = refl
⊔-idem - = refl

----------------
-- Graph
----------------

Graph : Set
Graph = Edge → EdgeState

_[_↦_] :  Graph → Edge → EdgeState → Graph
_[_↦_] f k v = λ { x → if does (x ≟Edge k) then v ⊔ f x else f x }

[↦]-comm : (s₁ s₂ : EdgeState) (e₁ e₂ : Edge) (g : Graph)
  → (g [ e₁ ↦ s₁ ]) [ e₂ ↦ s₂ ]
  ≡ (g [ e₂ ↦ s₂ ]) [ e₁ ↦ s₁ ]
[↦]-comm s₁ s₂ e₁ e₂ g = extensionality go where
  go : (e : Edge) → ((g [ e₁ ↦ s₁ ]) [ e₂ ↦ s₂ ]) e ≡ ((g [ e₂ ↦ s₂ ]) [ e₁ ↦ s₁ ]) e
  go e with e ≟Edge e₁ | e ≟Edge e₂
  ... | yes refl | yes refl rewrite ⊔-assoc s₁ s₂ (g e) | ⊔-assoc s₂ s₁ (g e) | ⊔-comm s₁ s₂ = refl
  ... | no _ | yes refl = refl
  ... | yes refl | no _ = refl
  ... | no _ | no _ = refl

[↦]-join : (s₁ s₂ : EdgeState) (e : Edge) (g : Graph)
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
 

⟦_⟧ : Action → Graph → Graph
⟦ (A e s) ⟧ g = g [ e ↦ s ]

⟦⟧-comm' : (a₁ a₂ : Action) (g : Graph)
  → ⟦ a₁ ⟧ (⟦ a₂ ⟧ g)
  ≡ ⟦ a₂ ⟧ (⟦ a₁ ⟧ g)
⟦⟧-comm' (A e₁ s₁) (A e₂ s₂) g = [↦]-comm s₂ s₁ e₂ e₁ g

⟦⟧-comm : (a₁ a₂ : Action)
  → ⟦ a₁ ⟧ ∘′ ⟦ a₂ ⟧
  ≡ ⟦ a₂ ⟧ ∘′ ⟦ a₁ ⟧
⟦⟧-comm a₁ a₂ = extensionality (⟦⟧-comm' a₁ a₂)

⟦⟧-idem' : (a : Action) (g : Graph)
  → ⟦ a ⟧ (⟦ a ⟧ g)
  ≡ ⟦ a ⟧ g
⟦⟧-idem' (A e s) g rewrite [↦]-join s s e g with s
... | bot = refl
... | + = refl
... | - = refl

⟦⟧-idem : (a : Action)
  → ⟦ a ⟧ ∘′ ⟦ a ⟧
  ≡ ⟦ a ⟧
⟦⟧-idem a = extensionality (⟦⟧-idem' a)

----------------
-- Action Relation Between Graphs
----------------

data ActionRel : Graph → Action → Graph → Set where
  AR : (a : Action) → (g : Graph) → ActionRel g a (⟦ a ⟧ g)

ActionRel-eqv : {g g' : Graph} {a : Action}
  → ActionRel g a g' ⇔ g' ≡ ⟦ a ⟧ g
ActionRel-eqv {g} {g'} {a} = equivalence to from where
  to : ActionRel g a g' → g' ≡ ⟦ a ⟧ g
  to (AR .a .g) = refl
  from : g' ≡ ⟦ a ⟧ g → ActionRel g a g'
  from refl = AR a g

ActionRel-comm : {a₁ a₂ : Action} {g₁ g₂₁ g₃₁ g₂₂ g₃₂ : Graph}
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

 