module core.decomp where

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

  decomp-pos : Graph → Ctor → Ident → Pos → List (Ident × Term)
  decomp-pos G k u p = map (decomp-sub G) (children G (S (V k u) p <>))

  decomp-v : Graph → Vertex → Term
  decomp-v G (V k u) = T u k (finite-map pos-finite (decomp-pos G k u)) 

  decomp-v' : Graph → Vertex → Term 
  decomp-v' G v with classify G [] v <> 
  ... | NPTop x = decomp-v G v -- impossible
  ... | MPTop x = ⋎ v
  ... | UTop x = ⤾ v
  ... | NPInner w x = decomp-v G v
  ... | MPInner w x = decomp-v G v
  ... | UInner w x = decomp-v G v

decomp-ε : Graph → Edge → Term 
decomp-ε G (E (S v _ _) _ _ _) = decomp-v G v

-- note: in the actual implementation, this would map over vertices in G directly
decomp-εs : Graph → List(Edge) → Grove 
decomp-εs G [] = γ [] [] []
decomp-εs G (E (S v _ _) _ _ _ ∷ εs) with classify G [] v <> | decomp-εs G εs
... | NPTop x | γ NP MP U = γ (decomp-v G v ∷ NP) MP U
... | MPTop x | γ NP MP U = γ NP (decomp-v G v ∷ MP) U
... | UTop x | γ NP MP U = γ NP MP (decomp-v G v ∷ U)
... | NPInner w x | γ NP MP U = γ NP MP U
... | MPInner w x | γ NP MP U = γ NP MP U
... | UInner w x | γ NP MP U = γ NP MP U

decomp-G : Graph → Grove 
decomp-G G = decomp-εs G G

-- WRONG!!!
-- decomp-PG : Graph → Partitioned-Graph → Grove 
-- decomp-PG G (PG NP MP U) = γ (map (decomp-ε G) NP) (map (decomp-ε G) MP) (map (decomp-ε G) U)