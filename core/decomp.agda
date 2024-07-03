module core.decomp where

open import Data.Nat
open import Data.Fin
open import Data.List

open import prelude
open import core.finite
open import core.graph
open import core.term
open import core.partition-graph

mutual 

  {-# TERMINATING #-}
  decomp-sub : ℕ → Graph → (Ident × Vertex) → (Ident × Term)
  decomp-sub fuel G (u' , v') = (u' , decomp-v' fuel G v')

  decomp-pos : ℕ → Graph → (k : Ctor) → Ident → (p : Fin (arity k)) → List (Ident × Term)
  decomp-pos fuel G k u p = map (decomp-sub fuel G) (children G (S (V k u) p))

  decomp-v : ℕ → Graph → Vertex → Term
  decomp-v zero G (V k u) = ⋎ (V k u) -- this is an arbitrary return value
  decomp-v (suc fuel) G (V k u) = T u k (vec-of-map (decomp-pos fuel G k u)) 

  decomp-v' : ℕ → Graph → Vertex → Term 
  decomp-v' fuel G v with classify fuel G v [] 
  ... | Top NP = decomp-v fuel G v -- impossible
  ... | Top MP = ⋎ v
  ... | Top U = ⤾ v
  ... | Inner X w = decomp-v fuel G v

decomp-ε : ℕ → Graph → Edge → Term 
decomp-ε fuel G (E (S v _) _ _) = decomp-v fuel G v

-- note: in the actual implementation, this would map over vertices in G directly
decomp-εs : ℕ → Graph → List(Edge) → Grove 
decomp-εs fuel G [] = γ [] [] []
decomp-εs fuel G (E (S v _) _ _ ∷ εs) with classify fuel G v [] | decomp-εs fuel G εs
... | Top NP | γ np mp u = γ (decomp-v fuel G v ∷ np) mp u
... | Top MP | γ np mp u = γ np (decomp-v fuel G v ∷ mp) u
... | Top U | γ np mp u = γ np mp (decomp-v fuel G v ∷ u)
... | Inner X w | γ np mp u = γ np mp u

decomp-G : ℕ → Graph → Grove 
decomp-G fuel G = decomp-εs fuel G G