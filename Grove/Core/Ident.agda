open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr)

module Grove.Core.Ident where 

postulate
  VertexId : Set
  _≟V𝕀_ : (i₁ i₂ : VertexId) → Dec (i₁ ≡ i₂)
  _≤V𝕀_ : (i₁ i₂ : VertexId) → Set 
  _≤?V𝕀_ : (i₁ i₂ : VertexId) → Dec (i₁ ≤V𝕀 i₂) 
  ≤V𝕀-reflexive : (i : VertexId) → (i ≤V𝕀 i) 
  ≤V𝕀-antisym : (i₁ i₂ : VertexId) → (i₁ ≤V𝕀 i₂) → (i₂ ≤V𝕀 i₁) → (i₁ ≡ i₂)
  ≤V𝕀-transitive : (i₁ i₂ i₃ : VertexId) → (i₁ ≤V𝕀 i₂) → (i₂ ≤V𝕀 i₃) → (i₁ ≤V𝕀 i₃)
  ≤V𝕀-total : (i₁ i₂ : VertexId) → (i₁ ≤V𝕀 i₂) + (i₂ ≤V𝕀 i₁)
  
  EdgeId : Set
  _≟E𝕀_ : (i₁ i₂ : EdgeId) → Dec (i₁ ≡ i₂)
