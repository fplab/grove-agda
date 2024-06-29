module core.term where

open import core.graph
open import core.logic
open import core.finite
open import Data.List

{-# NO_POSITIVITY_CHECK #-}
data Term : Set₁ where
 T : Ident → Ctor → (Finite-Fun Pos (List (Ident × Term)) pos-finite) → Term 
 ⋎ : Vertex → Term 
 ⤾ : Vertex → Term

Θ : Set₁
Θ = (List Term)

record Grove : Set₁ where
  constructor γ
  field
    NP : Θ
    MP : Θ
    U : Θ 