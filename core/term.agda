module core.term where

open import Data.List

open import prelude
open import core.graph
open import core.finite

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
