{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Fin
open import Data.List
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Data.Unit renaming (tt to <>)
open import Data.Product hiding (map)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)

open import Grove.Ident
open import Grove.Prelude

module Grove.Core.Decomp 
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

private
  import Grove.Core.Graph
  import Grove.Core.Grove
  import Grove.Core.Classify
  import Grove.Core.ClassifyCorrect

  open module Graph = Grove.Core.Graph Ctor _≟ℂ_ arity
  open module Grove = Grove.Core.Grove Ctor _≟ℂ_ arity
  open module Classify = Grove.Core.Classify Ctor _≟ℂ_ arity
  open module ClassifyCorrect = Grove.Core.ClassifyCorrect Ctor _≟ℂ_ arity

mutual 

  -- {-# TERMINATING #-}
  decomp-sub : ℕ → Graph → (EdgeId × Vertex) → (EdgeId × Term)
  decomp-sub fuel G (u' , v') = (u' , decomp-v' fuel G v' u')

  decomp-pos : ℕ → Graph → (k : Ctor) → VertexId → (p : Fin (arity k)) → TermList
  decomp-pos fuel G k u p with map (decomp-sub fuel G) (children G (S (V k u) p))
  ... | [] = □ (S (V k u) p)
  ... | t ∷ [] = ∶ t
  ... | t1 ∷ t2 ∷ ts = ⋏ (S (V k u) p) (t1 ∷ t2 ∷ ts)

  decomp-v : ℕ → Graph → Vertex → Term
  decomp-v zero G (V k u) = {!   !}
  decomp-v (suc fuel) G (V k u) = T u k (vec-of-map (decomp-pos fuel G k u)) 

  decomp-v' : ℕ → Graph → Vertex → EdgeId → Term 
  decomp-v' fuel G v u with classify fuel G v [] 
  ... | Top NP = decomp-v fuel G v -- impossible
  ... | Top MP = ⋎ u v
  ... | Top U = ⤾ u v
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

some-top-decidable :  ℕ → (G : Graph) → (has-uniq-ids G) → Decidable (some-top G)
some-top-decidable fuel G uniq-ids v with classify fuel G v [] | inspect (classify fuel G v) [] | classify-correct fuel G uniq-ids v [] <> | classify-complete fuel G uniq-ids v [] <>
... | Top X | _ | TopCorrect is-top | _ = yes (X , is-top)
... | Inner X w | [ eq ] | _ | Complete top-complete inner-complete = no not-top
  where 
  not-top : ¬(Σ[ X ∈ _ ] top X G v)
  not-top (X , is-top) rewrite eq with top-complete is-top 
  ... | ()

decomp-G : ℕ → (G : Graph) → (has-uniq-ids G) → Grove 
decomp-G fuel G uniq-ids = map (decomp-v fuel G) (filter (some-top-decidable fuel G uniq-ids) (vertices-of-G G))
