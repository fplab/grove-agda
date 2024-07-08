module core.recomp where

open import Data.Nat
open import Data.List hiding(lookup)
open import Data.Fin
open import Data.Vec hiding(_++_; concat; map)

open import prelude
open import core.finite
open import core.graph
open import core.grove
open import core.classify

vertex-of-term : Term → Vertex 
vertex-of-term (T u k _) = V k u
vertex-of-term (⋎ v) = v
vertex-of-term (⤾ v) = v

mutual 
  recomp-sub : Ident → (k : Ctor) → (p : Fin (arity k)) → (Ident × Term) → List Edge
  recomp-sub u k p (u' , t) = (E (S (V k u) p) (vertex-of-term t) u') ∷ (recomp-t t)

  recomp-pos : Ident → (k : Ctor) → (p : Fin (arity k)) → (List (Ident × Term)) → (List Edge)
  recomp-pos u k p ts = concat (map (recomp-sub u k p) ts)

  {-# TERMINATING #-}
  recomp-t : Term → (List Edge)
  recomp-t (T u k ts) = concat (comprehend ts (recomp-pos u k))
  recomp-t (⋎ x) = []
  recomp-t (⤾ x) = []

recomp-grove : Grove → Graph 
recomp-grove grove = concat (map recomp-t grove)
