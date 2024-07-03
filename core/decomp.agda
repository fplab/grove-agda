module core.decomp where

open import Data.Fin
open import Data.List
open import core.logic
open import core.finite
open import core.graph
open import core.term
open import core.partition-graph

mutual 

  {-# TERMINATING #-}
  decomp-sub : Graph → (Ident × Vertex) → (Ident × Term)
  decomp-sub G (u' , v') = (u' , decomp-v' G v')

  decomp-pos : Graph → (k : Ctor) → Ident → (p : Fin (arity k)) → List (Ident × Term)
  decomp-pos G k u p = map (decomp-sub G) (children G (S (V k u) p))

  decomp-v : Graph → Vertex → Term
  decomp-v G (V k u) = T u k (vec-of-map (decomp-pos G k u)) 

  decomp-v' : Graph → Vertex → Term 
  decomp-v' G v with classify G v [] 
  ... | NPTop = decomp-v G v -- impossible
  ... | MPTop = ⋎ v
  ... | UTop = ⤾ v
  ... | NPInner w = decomp-v G v
  ... | MPInner w = decomp-v G v
  ... | UInner w = decomp-v G v

decomp-ε : Graph → Edge → Term 
decomp-ε G (E (S v _) _ _) = decomp-v G v

-- note: in the actual implementation, this would map over vertices in G directly
decomp-εs : Graph → List(Edge) → Grove 
decomp-εs G [] = γ [] [] []
decomp-εs G (E (S v _) _ _ ∷ εs) with classify G v [] | decomp-εs G εs
... | NPTop | γ NP MP U = γ (decomp-v G v ∷ NP) MP U
... | MPTop | γ NP MP U = γ NP (decomp-v G v ∷ MP) U
... | UTop | γ NP MP U = γ NP MP (decomp-v G v ∷ U)
... | NPInner w | γ NP MP U = γ NP MP U
... | MPInner w | γ NP MP U = γ NP MP U
... | UInner w | γ NP MP U = γ NP MP U

decomp-G : Graph → Grove 
decomp-G G = decomp-εs G G