module core.recomp where

open import Data.List

open import prelude
open import core.finite
open import core.graph
open import core.term
open import core.partition-graph

vertex-of-term : Term → Vertex 
vertex-of-term (T u k _) = V k u
vertex-of-term (⋎ v) = v
vertex-of-term (⤾ v) = v

{-# TERMINATING #-}
mutual 
  recomp-sub : Ctor → Ident → Pos → (Ident × Term) → List Edge
  recomp-sub k u p (u' , t) = (E (S (V k u) p) (vertex-of-term t) u') ∷ (recomp-t t)

  recomp-pos : Ident → Ctor → (Finite-Fun Pos (List (Ident × Term)) pos-finite) → Pos → (List Edge)
  recomp-pos u k ts p = concat (map (recomp-sub k u p) (apply-finite-map pos-finite ts p))

  recomp-t : Term → List(Edge)
  recomp-t (T u k ts) = concat (finite-comprehension pos-finite λ p → recomp-pos u k ts p)
  recomp-t (⋎ x) = []
  recomp-t (⤾ x) = []

recomp-ts : List(Term) → List(Edge)
recomp-ts [] = []
recomp-ts (t ∷ ts) = (recomp-t t) ++ (recomp-ts ts)
  
recomp-grove : Grove → Graph 
recomp-grove (γ NP MP U) = (recomp-ts NP) ++ (recomp-ts MP) ++ (recomp-ts U)
