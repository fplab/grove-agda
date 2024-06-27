module core.redecomp where

open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)
open import Relation.Nullary hiding(¬_)
open import Data.Bool hiding (_<_; _≟_)
open import Data.List

open import core.logic
open import core.finite
open import core.graph
open import core.term
open import core.partition-graph
open import core.decomp
open import core.recomp

-- all using the old, coarse partitioning
-- redepart-rec : (G : Graph) → (εs : List Edge) → list-equiv (unpartition-graph (partition-graph-rec G εs)) εs
-- redepart-rec G [] = ListEquivRefl []
-- redepart-rec G (ε ∷ εs) with edge-classify G ε | inspect (partition-graph-rec G εs)
-- ... | NPE x | PG NP MP U with≡ eq = ListEquivCons ε (redepart-rec G εs)
-- ... | MPE x | PG NP MP U with≡ eq = ListEquivTrans (ListEquivAppCons _ _ _) (ListEquivCons ε (redepart-rec G εs))
-- ... | UE x | PG NP MP U with≡ eq = ListEquivTrans (ListEquivAppAppCons (Partitioned-Graph.NP (partition-graph-rec G εs)) _ _ ε) (ListEquivCons ε (redepart-rec G εs))

-- redepart : (G : Graph) → list-equiv (unpartition-graph (partition-graph G)) G
-- redepart G = redepart-rec G G

-- decomp-parts-rec : (G : Graph) → (εs : List Edge) → decomp-PG G (partition-graph-rec G εs) ≡ decomp-εs G εs
-- decomp-parts-rec G [] = refl
-- decomp-parts-rec G (E (S v u <>) v' u' <> ∷ εs) with edge-classify G (E (S v u <>) v' u' <>) | inspect (partition-graph-rec G εs) | classify G [] v <> | decomp-εs G εs
-- ... | NPE x | PG NP MP U with≡ eq = {!   !}
-- ... | MPE x | PG NP MP U with≡ eq = {!   !}
-- ... | UE x | PG NP MP U with≡ eq = {!   !}
 
-- decomp-parts : (G : Graph) → decomp-PG G (partition-graph G) ≡ decomp-G G
-- decomp-parts G = {!   !}

assoc : (l : List (Vertex × Graph)) → (v : Vertex) → Graph 
assoc [] v = []
assoc ((v? , εs) ∷ l) v with Dec.does (v ≟Vertex v?)
... | true = εs 
... | false = assoc l v

map-update : (l : List (Vertex × Graph)) → (v : Vertex) → (ε : Edge) → list-equiv (concat (map π2 (list-assoc-update l v ε))) (ε ∷ concat (map π2 l))
map-update [] v ε = ListEquivRefl _
map-update ((v? , εs) ∷ l) v ε with Dec.does (v ≟Vertex v?)
... | true = ListEquivRefl _ 
... | false = ListEquivTrans (ListEquivApp (ListEquivRefl _) (map-update l v ε)) (ListEquivAppCons _ _ _)

redepart-rec : (G : Graph) → (εs : List Edge) → list-equiv (unpartition-graph (partition-graph-rec G εs)) εs
redepart-rec G [] = ListEquivRefl []
redepart-rec G (ε ∷ εs) with edge-classify G ε | inspect (partition-graph-rec G εs) | redepart-rec G εs
... | NPE x | PG NP MP U with≡ eq | equiv rewrite eq = ListEquivTrans (ListEquivApp (map-update NP x ε) (ListEquivRefl _)) (ListEquivCons _ equiv)
... | MPE x | PG NP MP U with≡ eq | equiv rewrite eq = ListEquivTrans (ListEquivApp (ListEquivRefl (concat (map π2 NP))) (ListEquivApp (map-update MP x ε) (ListEquivRefl _))) (ListEquivTrans (ListEquivAppCons _ _ _) (ListEquivCons _ equiv))
... | UE x | PG NP MP U with≡ eq | equiv rewrite eq = ListEquivTrans (ListEquivApp (ListEquivRefl (concat (map π2 NP))) (ListEquivApp (ListEquivRefl (concat (map π2 MP))) (map-update U x ε))) (ListEquivTrans (ListEquivAppAppCons (concat (map π2 NP)) _ _ ε) (ListEquivCons _ equiv))

redepart : (G : Graph) → list-equiv (unpartition-graph (partition-graph G)) G
redepart G = redepart-rec G G

pieces-inversion : (G : Graph) → Set 
pieces-inversion G with (partition-graph G)
... | PG NP MP U with (NP ++ MP ++ U)
... | [] = ⊤ 
... | (v , εs) ∷ ps = list-equiv (recomp-t (decomp-v G v)) εs

-- I think this lemma is the crux
pieces-lemma : (G : Graph) → (pieces-inversion G)
pieces-lemma = {!   !}
 
redecomp : (G : Graph) → (recomp-grove (decomp-G G) ≡ G)
redecomp G = {!   !}  