module core.recomp where

open import Data.Nat
open import Data.List hiding(lookup)
open import Data.Fin
open import Data.Vec hiding(_++_; concat; map)
open import Data.Unit renaming (tt to <>)
open import Data.Product hiding (map)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)

open import core.finite
open import core.graph
open import core.grove
open import core.classify

vertex-of-term : Term → Vertex 
vertex-of-term (T u k _) = V k u
vertex-of-term (⋎ _ v) = v
vertex-of-term (⤾ _ v) = v

mutual 
  recomp-sub : VertexId → (k : Ctor) → (p : Fin (arity k)) → (EdgeId × Term) → List Edge
  recomp-sub u k p (u' , t) = (E (S (V k u) p) (vertex-of-term t) u') ∷ (recomp-t t)

  recomp-pos : VertexId → (k : Ctor) → (p : Fin (arity k)) → TermList → (List Edge)
  recomp-pos u k p (□ _) = []
  recomp-pos u k p (∶ t) = recomp-sub u k p t
  recomp-pos u k p (⋏ _ ts) = concat (map (recomp-sub u k p) ts) 

  {-# TERMINATING #-}
  recomp-t : Term → (List Edge)
  recomp-t (T u k ts) = concat (comprehend ts (recomp-pos u k))
  recomp-t (⋎ _ _) = []
  recomp-t (⤾ _ _) = []

recomp-grove : Grove → Graph 
recomp-grove grove = concat (map recomp-t grove)
