module core.term where

open import Data.List

open import prelude
open import core.graph
open import core.finite
open import Data.List
open import Data.Vec

data Term : Set where
 T : Ident → (k : Ctor) → (Vec (List (Ident × Term)) (arity k)) → Term 
 ⋎ : Vertex → Term 
 ⤾ : Vertex → Term

-- todo: have two sorts so that holes store sources

Θ : Set
Θ = (List Term)

record Grove : Set₁ where
  constructor γ
  field
    NP : Θ
    MP : Θ
    U : Θ 
