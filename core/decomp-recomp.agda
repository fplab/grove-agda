module core.decomp-recomp where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding(¬_)
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
open import Data.Nat
open import Data.Fin

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

parents-in-G : (G : Graph) → (v : Vertex) → list-forall (λ w → list-elem w (vertices-of-G G)) (parents G v) 
parents-in-G [] v = <>
parents-in-G ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?)
parents-in-G ((E (S w _) _ _) ∷ G) v | true = (ListElemHave _) , (list-forall-implies (parents-in-G G v) (ListElemSkip _))
parents-in-G (_ ∷ G) v | false = list-forall-implies (parents-in-G G v) (ListElemSkip _)

unique-parent-in-G : (G : Graph) → (x w : Vertex) →
  (classify-parents G x ≡ PC-UP w) → list-elem w (vertices-of-G G)
unique-parent-in-G G x w eq with parents G x | parents-in-G G x | eq
... | .w ∷ [] | (elem , _) | refl = elem

inner-in-G : (fuel : ℕ) → (G : Graph) → (v w : Vertex) → (X : X) →
    inner X G v w → 
    list-elem w (vertices-of-G G)
inner-in-G fuel G v w X (_ , (n , ws , (_ , eq , cps)) , _) with cps (fromℕ n) 
... | cp rewrite eq = unique-parent-in-G G _ w cp

edge-classify-in-G : (fuel : ℕ) → (G : Graph) → (w : Vertex) → (X : X) → (ε : Edge) →
  (list-elem ε G) →
  (edge X G ε w) → 
  list-elem w (vertices-of-G G)
edge-classify-in-G fuel G w X .(E (S w _) _ _) elem (TopEdge _) = list-elem-map elem
edge-classify-in-G fuel G w X .(E (S _ _) _ _) elem (InnerEdge is-inner) = inner-in-G fuel G _ w X is-inner

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
                            (list-forall-elem reg-forall)))))
  where 
  reg-forall : ((E (S v _) _ _) : Edge) → 
                list-elem _ _ →
                some-top G v → 
                list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v fuel G v))
  reg-forall (E (S v _) _ _ ) _ (X , is-top) = decomp-recomp-v-in-G fuel G v X is-top 
  
decomp-recomp-complete : (fuel : ℕ) → (G : Graph) → list-forall (λ ε → list-elem ε (recomp-grove (decomp-G' fuel G))) G
decomp-recomp-complete fuel G = list-forall-elem elem-forall
  where 
  elem-forall : (ε : Edge) → list-elem ε G → list-elem ε (recomp-grove (decomp-G' fuel G))
  elem-forall ε elem with edge-classify fuel G ε | edge-classify-correct fuel G ε
  ... | EC X w | EdgeCorrect is-edge with lem12 G w X ε is-edge 
  ... | is-top = list-elem-concat {ls = (map recomp-t (decomp-G' fuel G))} 
                (decomp-recomp-v-complete fuel G w X ε is-top is-edge) 
                (list-elem-map {a = decomp-v fuel G w} {l = decomp-G' fuel G} {f = recomp-t}  
                (list-elem-map {a = w} {l = filter (some-top-decidable fuel G) (vertices-of-G G)} {f = decomp-v fuel G} 
                (list-elem-filter {l = vertices-of-G G} {dec = some-top-decidable fuel G} (X , is-top) (edge-classify-in-G fuel G w X ε elem is-edge))))  

-- decomp-recomp : (fuel : ℕ) → (G : Graph) → (recomp-grove (decomp-G' fuel G) ≡ G)
-- decomp-recomp fuel G = {!   !}  