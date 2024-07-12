
open import Axiom.Extensionality.Propositional
open import Data.Bool hiding (_<_; _≟_)
open import Data.Nat hiding (_+_; _⊔_)
open import Function.Equivalence hiding (_∘_)
open import Function hiding (_⇔_)
open import Function.Equality using (_⟨$⟩_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary

module Grove.Core.CGraph 
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

private
  import Grove.Core.Graph
  open module Graph = Grove.Core.Graph Ctor _≟ℂ_ arity


postulate
  extensionality : {ℓ₁ ℓ₂ : Level} → Extensionality ℓ₁ ℓ₂
  
data EdgeState : Set where
  ⊥ : EdgeState -- smallest
  + : EdgeState -- middle
  - : EdgeState -- largest

_⊔_ : EdgeState → EdgeState → EdgeState
- ⊔ _ = -
_ ⊔ - = -
+ ⊔ _ = +
_ ⊔ + = +
_ ⊔ _ = ⊥

⊔-assoc : (s₁ s₂ s₃ : EdgeState) → (s₁ ⊔ (s₂ ⊔ s₃)) ≡ ((s₁ ⊔ s₂) ⊔ s₃)
⊔-assoc ⊥ ⊥ ⊥ = refl
⊔-assoc ⊥ ⊥ + = refl
⊔-assoc ⊥ ⊥ - = refl
⊔-assoc ⊥ + ⊥ = refl
⊔-assoc ⊥ + + = refl
⊔-assoc ⊥ + - = refl
⊔-assoc ⊥ - ⊥ = refl
⊔-assoc ⊥ - + = refl
⊔-assoc ⊥ - - = refl
⊔-assoc + ⊥ ⊥ = refl
⊔-assoc + ⊥ + = refl
⊔-assoc + ⊥ - = refl
⊔-assoc + + ⊥ = refl
⊔-assoc + + + = refl
⊔-assoc + + - = refl
⊔-assoc + - ⊥ = refl
⊔-assoc + - + = refl
⊔-assoc + - - = refl
⊔-assoc - ⊥ ⊥ = refl
⊔-assoc - ⊥ + = refl
⊔-assoc - ⊥ - = refl
⊔-assoc - + ⊥ = refl
⊔-assoc - + + = refl
⊔-assoc - + - = refl
⊔-assoc - - ⊥ = refl
⊔-assoc - - + = refl
⊔-assoc - - - = refl

⊔-comm : (s₁ s₂ : EdgeState) → s₁ ⊔ s₂ ≡ s₂ ⊔ s₁
⊔-comm ⊥ ⊥ = refl
⊔-comm ⊥ + = refl
⊔-comm ⊥ - = refl
⊔-comm + ⊥ = refl
⊔-comm + + = refl
⊔-comm + - = refl
⊔-comm - ⊥ = refl
⊔-comm - + = refl
⊔-comm - - = refl

⊔-idem : (s : EdgeState) → s ⊔ s ≡ s
⊔-idem ⊥ = refl
⊔-idem + = refl
⊔-idem - = refl

----------------
-- Convergent Graph (CGraph)
----------------

CGraph : Set
CGraph = Edge → EdgeState