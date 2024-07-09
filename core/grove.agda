
open import core.graph
open import core.finite
open import Data.List
open import Data.Vec
open import Data.Nat
open import Data.Product

module core.grove where

data Term : Set where
 T : VertexId → (k : Ctor) → (Vec (List (EdgeId × Term)) (arity k)) → Term 
 ⋎ : Vertex → Term 
 ⤾ : Vertex → Term

-- todo: have two sorts so that holes store sources

Grove : Set
Grove = (List Term)
