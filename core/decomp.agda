module core.decomp where

open import Data.Nat
open import Data.Fin
open import Data.List
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

open import prelude
open import core.finite
open import core.graph
open import core.grove
open import core.classify
open import core.classify-correct

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

vertices-of-G : Graph → List Vertex 
vertices-of-G G = map (λ (E (S v _) _ _) → v) G 

some-top : Graph → Vertex → Set 
some-top G v = Σ[ X ∈ X ] top X G v

some-top-decidable :  ℕ → (G : Graph) → Decidable (some-top G)
some-top-decidable fuel G v with classify fuel G v [] | inspect (classify fuel G v) [] | classify-correct fuel G v [] <> | classify-complete fuel G v [] <>
... | Top X | _ | TopCorrect is-top | _ = yes (X , is-top)
... | Inner X w | [ eq ] | _ | Complete top-complete inner-complete = no not-top
  where 
  not-top : ¬ Σ[ X ∈ _ ] top X G v
  not-top (X , is-top) rewrite eq with top-complete is-top 
  ... | ()

decomp-G' : ℕ → Graph → Grove 
decomp-G' fuel G = map (decomp-v fuel G) (filter {P = some-top G} (some-top-decidable fuel G) (vertices-of-G G))

decomp-G : ℕ → Graph → Grove 
decomp-G fuel G = decomp-εs fuel G G 