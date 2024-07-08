module core.decomp-recomp where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding(¬_)
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
open import Data.Nat

open import prelude
open import core.finite
open import core.list-logic
open import core.graph
open import core.grove
open import core.classify
-- open import core.classify-lemmas
open import core.classify-correct
open import core.decomp
open import core.recomp

lem12 : (G : Graph) → (v : Vertex) → (X : X) → (ε : Edge) →
  (edge X G ε v) → (top X G v)
lem12 G v X ε (TopEdge is-top) = is-top
lem12 G v X ε (InnerEdge (_ , _ , is-top)) = is-top

edge-classify-in-G : (fuel : ℕ) → (G : Graph) → (w : Vertex) → (X : X) → (ε : Edge) →
  (edge-classify fuel G ε ≡ EC X w) → 
  list-elem w (vertices-of-G G)
edge-classify-in-G fuel G w X ε eq = {!   !}

decomp-recomp-v-sound : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (X : X) → 
  (top X G v) → 
  list-forall (λ ε → edge X G ε v) (recomp-t (decomp-v fuel G v))
decomp-recomp-v-sound = {!   !} 

decomp-recomp-v-complete : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (X : X) → (ε : Edge) →
  (top X G v) → 
  (edge X G ε v) →
  list-elem ε (recomp-t (decomp-v fuel G v))
decomp-recomp-v-complete fuel G v X ε is-top is-edge = {!   !} 

decomp-recomp-v-in-G : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (X : X) → 
  (top X G v) → 
  list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v fuel G v))
decomp-recomp-v-in-G = {!   !} 

-- decomp-recomp-v

decomp-recomp-sound : (fuel : ℕ) → (G : Graph) → list-forall (λ ε → list-elem ε G) (recomp-grove (decomp-G' fuel G))
decomp-recomp-sound fuel G = list-forall-concat {ls = (map recomp-t (decomp-G' fuel G))} 
                            (list-forall-map {l = (decomp-G' fuel G)}
                            (list-forall-map {l = (filter (some-top-decidable fuel G) (vertices-of-G G))} 
                            (list-forall-filter {l = vertices-of-G G} 
                            (list-forall-map {l = G} 
                            (list-forall-general reg-forall)))))
  where 
  reg-forall : ((E (S v _) _ _) : Edge) → 
                some-top G v → 
                list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v fuel G v))
  reg-forall (E (S v _) _ _ ) (X , is-top) = decomp-recomp-v-in-G fuel G v X is-top 
  
decomp-recomp-complete : (fuel : ℕ) → (G : Graph) → list-forall (λ ε → list-elem ε (recomp-grove (decomp-G' fuel G))) G
decomp-recomp-complete fuel G = list-forall-general general-forall
  where 
  general-forall : (ε : Edge) → list-elem ε (recomp-grove (decomp-G' fuel G))
  general-forall ε with edge-classify fuel G ε | inspect (edge-classify fuel G) ε | edge-classify-correct fuel G ε
  ... | EC X w | [ eq ] | EdgeCorrect is-edge with lem12 G w X ε is-edge 
  ... | is-top = list-elem-concat {ls = (map recomp-t (decomp-G' fuel G))} 
                (decomp-recomp-v-complete fuel G w X ε is-top is-edge) 
                (list-elem-map {a = decomp-v fuel G w} {l = decomp-G' fuel G} {f = recomp-t}  
                (list-elem-map {a = w} {l = filter (some-top-decidable fuel G) (vertices-of-G G)} {f = decomp-v fuel G} 
                (list-elem-filter {l = vertices-of-G G} {dec = some-top-decidable fuel G} (X , is-top) (edge-classify-in-G fuel G w X ε eq))))  

-- decomp-recomp : (fuel : ℕ) → (G : Graph) → (recomp-grove (decomp-G' fuel G) ≡ G)
-- decomp-recomp fuel G = {!   !}  