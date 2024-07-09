open import Data.List

open import prelude
open import core.graph
open import core.finite
open import Data.List
open import Data.Vec
open import Data.Nat

module core.grove (Ctor : Set) (arity : Ctor → ℕ) where

data Term : Set where
 T : Ident → (k : Ctor) → (Vec (List (Ident × Term)) (arity k)) → Term 
 ⋎ : Vertex → Term 
 ⤾ : Vertex → Term

-- todo: have two sorts so that holes store sources

Grove : Set
Grove = (List Term)
