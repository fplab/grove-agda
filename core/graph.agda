open import Axiom.Extensionality.Propositional
open import Data.Bool hiding (_<_; _≟_)
open import Data.Nat hiding (_⊔_; _+_)
open import Data.List
open import Data.Fin hiding(_+_)
open import Function.Equivalence hiding (_∘_)
open import Function hiding (_⇔_)
open import Function.Equality using (_⟨$⟩_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary

open import prelude
open import core.finite

module core.graph where

postulate
  
  Ctor : Set
  _≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂)
  arity : Ctor → ℕ
  
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

record Vertex : Set where
  constructor V
  field
    ctor : Ctor
    ident : VertexId

postulate 
  VertexId-uniq : (v₁ v₂ : Vertex) → (Vertex.ident v₁) ≡ (Vertex.ident v₂) → v₁ ≡ v₂  

_≟Vertex_ : (v₁ v₂ : Vertex) → Dec (v₁ ≡ v₂)
V c₁ i₁ ≟Vertex V c₂ i₂ with c₁ ≟ℂ c₂ | i₁ ≟V𝕀 i₂
... | yes refl | yes refl = yes refl
... | _        | no p     = no (λ { refl → p refl })
... | no p     | _        = no (λ { refl → p refl })

arity-v : Vertex → ℕ
arity-v (V k _) = arity k

record Source : Set where
  constructor S
  field 
    v : Vertex
    p : Fin (arity-v v)

_≟Source_ : (s₁ s₂ : Source) → Dec (s₁ ≡ s₂)
S v₁ p₁ ≟Source S v₂ p₂ with v₁ ≟Vertex v₂
S v₁ p₁ ≟Source S v₂ p₂ | yes refl with p₁ ≟Fin p₂ 
S v₁ p₁ ≟Source S v₂ p₂ | yes refl | yes refl = yes refl
S v₁ p₁ ≟Source S v₂ p₂ | yes refl | no neq = no (λ { refl → neq refl })
S v₁ p₁ ≟Source S v₂ p₂ | no neq = no (λ { refl → neq refl })

record Edge : Set where
  constructor E
  field
    source : Source
    child : Vertex
    ident : EdgeId

_≟Edge_ : (e₁ e₂ : Edge) → Dec (e₁ ≡ e₂)
E source₁ child₁ ident₁ ≟Edge E source₂ child₂ ident₂
  with source₁ ≟Source source₂
     | child₁ ≟Vertex child₂
     | ident₁ ≟E𝕀 ident₂
... | yes refl | yes refl | yes refl = yes refl
... | no p     | _        | _        = no (λ { refl → p refl })
... | _        | no p     | _        = no (λ { refl → p refl })
... | _        | _        | no p     = no (λ { refl → p refl })

Graph = List(Edge)