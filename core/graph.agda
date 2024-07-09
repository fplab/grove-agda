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

module core.graph (Ctor : Set) (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂)) (arity : Ctor → ℕ) where

postulate
  
  Ident : Set
  _≟𝕀_ : (i₁ i₂ : Ident) → Dec (i₁ ≡ i₂)
  _≤𝕀_ : (i₁ i₂ : Ident) → Set 
  _≤?𝕀_ : (i₁ i₂ : Ident) → Dec (i₁ ≤𝕀 i₂) 

  ≤𝕀-reflexive : (i : Ident) → (i ≤𝕀 i) 
  ≤𝕀-antisym : (i₁ i₂ : Ident) → (i₁ ≤𝕀 i₂) → (i₂ ≤𝕀 i₁) → (i₁ ≡ i₂)
  ≤𝕀-transitive : (i₁ i₂ i₃ : Ident) → (i₁ ≤𝕀 i₂) → (i₂ ≤𝕀 i₃) → (i₁ ≤𝕀 i₃)
  ≤𝕀-total : (i₁ i₂ : Ident) → (i₁ ≤𝕀 i₂) + (i₂ ≤𝕀 i₁)

record Vertex : Set where
  constructor V
  field
    ctor : Ctor
    ident : Ident

postulate 
  V-ident-uniq : (v₁ v₂ : Vertex) → (Vertex.ident v₁) ≡ (Vertex.ident v₂) → v₁ ≡ v₂  

_≟Vertex_ : (v₁ v₂ : Vertex) → Dec (v₁ ≡ v₂)
V c₁ i₁ ≟Vertex V c₂ i₂ with c₁ ≟ℂ c₂ | i₁ ≟𝕀 i₂
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
    ident : Ident

_≟Edge_ : (e₁ e₂ : Edge) → Dec (e₁ ≡ e₂)
E source₁ child₁ ident₁ ≟Edge E source₂ child₂ ident₂
  with source₁ ≟Source source₂
     | child₁ ≟Vertex child₂
     | ident₁ ≟𝕀 ident₂
... | yes refl | yes refl | yes refl = yes refl
... | no p     | _        | _        = no (λ { refl → p refl })
... | _        | no p     | _        = no (λ { refl → p refl })
... | _        | _        | no p     = no (λ { refl → p refl })

Graph = List(Edge)

-- Much was removed that is still important - just not on this branch
