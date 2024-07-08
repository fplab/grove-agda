{-# OPTIONS --allow-unsolved-metas #-}

module core.partition-graph where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_<_; _≟_)
open import Data.List hiding (lookup; _∷ʳ_)
open import Data.Vec
open import Data.Fin hiding(_+_; _-_)
open import Data.Maybe hiding(map) 
open import Data.Nat hiding (_+_)
open import Data.Nat.Properties
open import Data.Empty

open import prelude
open import core.finite
open import core.graph


-- -- -- this is important 
-- -- -- classify-of-parent : (G : Graph) → 
-- -- --   (v w : Vertex) → 
-- -- --   (classify G w [] ≡ NPInner v) → 
-- -- --   (v' : Vertex) → 
-- -- --   (classify-parents G v' ≡ PC-UP w) → 
-- -- --   (classify G v' [] ≡ NPInner v)
-- -- -- classify-of-parent G v w eq1 v' eq2 with classify G w [] | classify-correct G w [] <> | eq1
-- -- -- ... | NPInner .v | NPInnerCorrect .v (oa , top) | refl = let npinner' = (HOA-step eq2 oa , top) in {!   !}
-- -- -- with inspect (classify-parents G v') | eq2
-- -- -- ... | PC-NP with≡ eq | () 
-- -- -- ... | PC-MP with≡ eq | ()
-- -- -- ... | PC-UP x with≡ eq | _ rewrite eq = {!   !}


-- -- -- classify-np-top : (G : Graph) → (v : Vertex) → (eq : NP-top G v) → (classify G [] v <> ≡ NPTop eq)
-- -- -- classify-np-top G v eq with inspect (classify-parents G v)
-- -- -- classify-np-top G v eq | (PC-NP with≡ eq') = {!   !}

-- -- list-assoc-update : List (Vertex × Graph) → Vertex → Edge → List (Vertex × Graph)
-- -- list-assoc-update [] v ε = (v , ε ∷ []) ∷ []
-- -- list-assoc-update ((v? , εs) ∷ l) v ε with Dec.does (v ≟Vertex v?)
-- -- ... | true = (v , ε ∷ εs) ∷ l
-- -- ... | false = (v? , εs) ∷ list-assoc-update l v ε

-- -- record  Partitioned-Graph : Set where
-- --   constructor PG
-- --   field
-- --     NP : List (Vertex × Graph)
-- --     MP : List (Vertex × Graph)
-- --     U : List (Vertex × Graph)

-- -- partition-graph-rec : Graph → (List Edge) → Partitioned-Graph 
-- -- partition-graph-rec G [] = PG [] [] []
-- -- partition-graph-rec G (ε ∷ εs) with edge-classify G ε | partition-graph-rec G εs 
-- -- ... | NPE x | PG NP MP U = PG (list-assoc-update NP x ε) MP U
-- -- ... | MPE x | PG NP MP U = PG NP (list-assoc-update MP x ε)U  
-- -- ... | UE x | PG NP MP U = PG NP MP (list-assoc-update U x ε)
    
-- -- partition-graph : Graph → Partitioned-Graph 
-- -- partition-graph G = partition-graph-rec G G
   
-- -- unpartition-graph : Partitioned-Graph → Graph          
-- -- unpartition-graph (PG NP MP U) = (concat (map (λ (v , εs) → εs) NP)) ++ (concat (map (λ (v , εs) → εs) MP)) ++ (concat (map (λ (v , εs) → εs) U)) 
            