
open import Data.List
open import Data.Fin
open import Data.Vec
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import core.ident
open import core.finite

module core.grove 
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

import core.graph
open module graph = core.graph Ctor _≟ℂ_ arity

mutual 
  data Term : Set where
    T : VertexId → (k : Ctor) → (Vec TermList (arity k)) → Term 
    ⋎ : EdgeId → Vertex → Term 
    ⤾ : EdgeId → Vertex → Term
    
  data TermList : Set where 
    □ : Source → TermList 
    ∶ : (EdgeId × Term) → TermList
    ⋏ : Source → (List (EdgeId × Term)) → TermList

-- todo: have two sorts so that holes store sources

Grove : Set
Grove = (List Term)
