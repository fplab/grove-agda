
open import core.graph
open import core.finite
open import Data.List
open import Data.Fin
open import Data.Vec
open import Data.Nat
open import Data.Product

module core.grove where

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
