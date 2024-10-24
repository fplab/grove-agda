open import Data.List
open import Data.Fin
open import Data.Vec
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Grove.Prelude
open import Grove.Ident

module Grove.Core.Grove 
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

private
  import Grove.Core.Graph
  open module Graph = Grove.Core.Graph Ctor _≟ℂ_ arity

mutual 
  data Term : Set where
    T : VertexId → (k : Ctor) → (Vec ChildTerm (arity k)) → Term 
    ⋎ : EdgeId → Vertex → Term 
    ↻ : EdgeId → Vertex → Term
    
  data ChildTerm : Set where 
    □ : Location → ChildTerm 
    ∶ : (EdgeId × Term) → ChildTerm
    ⋏ : Location → (List (EdgeId × Term)) → ChildTerm

Grove : Set
Grove = (List Term)
