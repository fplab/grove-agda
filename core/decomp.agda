module core.decomp where

open import Data.Nat
open import Data.Fin
open import Data.List

open import prelude
open import core.finite
open import core.graph
open import core.grove
open import core.classify

mutual 

  -- {-# TERMINATING #-}
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
  
-- -- note: in the actual implementation, this would map over vertices in G directly
decomp-εs : ℕ → Graph → (List Edge) → Grove 
decomp-εs fuel G [] = []
decomp-εs fuel G (E (S v _) _ _ ∷ εs) with classify fuel G v []
... | Top X = (decomp-v fuel G v) ∷ (decomp-εs fuel G εs)
... | Inner X w = decomp-εs fuel G εs

decomp-G : ℕ → Graph → Grove 
decomp-G fuel G = decomp-εs fuel G G 