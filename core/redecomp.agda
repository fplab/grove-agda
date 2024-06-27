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

lemm : (G : Graph) → ((V k u) : Vertex) → (recomp-t (decomp-v G (V k u))) ≡ concat (finite-comprehension pos-finite (λ p → concat (map (λ (u' , t) → E (S (V k u) p _) (vertex-of-term t) u' _ ∷ recomp-t t) (apply-finite-map pos-finite (finite-map pos-finite (λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ _)))) p))))
lemm G (V k u) = refl

-- concat (finite-comprehension pos-finite (λ p → concat (map (λ (u' , t) → E (S (V k u) p _) (vertex-of-term t) u' _ ∷ recomp-t t) (apply-finite-map pos-finite (finite-map pos-finite (λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ _)))) p))))

-- concat 
      -- (finite-comprehension pos-finite 
      --   (λ p →
      --     concat
      --     (map
          
      --       (λ (u' , t) →
      --           E (S (V k u) p _)
      --           (vertex-of-term t) u' _
      --           ∷ recomp-t t)

      --       (apply-finite-map pos-finite
      --         (finite-map pos-finite
      --           (λ p₁ →
      --             map
      --             (λ (u' , v) →
      --               u' , decomp-v' G v)

      --             (children G (S (V k u) p₁ _))
      --           )
      --         )

      --         p
      --       )
      --     )
      --   )
      -- )

      -- map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p _))

vertex-of-decomp : (G : Graph) → (v : Vertex) → vertex-of-term (decomp-v G v) ≡ v 
vertex-of-decomp G (V k u) = refl

vertex-of-decomp' : (G : Graph) → (v : Vertex) → vertex-of-term (decomp-v' G v) ≡ v 
vertex-of-decomp' G (V k u) with classify G [] (V k u) <> 
... | NPTop x = refl
... | MPTop x = refl
... | UTop x = refl
... | NPInner w x = refl
... | MPInner w x = refl
... | UInner w x = refl

child-classification : (G : Graph) → (v : Vertex) → Σ[ pf ∈ _ ] (classify G [] v <> ≡ NPTop pf) → list-forall (λ (u' , v') → edge-classify G (E (S v p <>) v' u' <>) ≡ NPE v × list-forall (λ ε → edge-classify G ε ≡ NPE (V k u)) (recomp-t (decomp-v' G v'))) (children G (S (V k u) p <>))

lemma-core : (G : Graph) → ((V k u) : Vertex) → Σ[ pf ∈ _ ] (classify G [] (V k u) <> ≡ NPTop pf) → (p : Pos) → list-forall (λ (u' , v') → edge-classify G (E (S (V k u) p <>) (vertex-of-term (decomp-v' G v')) u' <>) ≡ NPE (V k u) × list-forall (λ ε → edge-classify G ε ≡ NPE (V k u)) (recomp-t (decomp-v' G v'))) (children G (S (V k u) p <>))
lemma-core G (V k u) eq p with children G (S (V k u) p <>) 
... | [] = <>
... | (u' , w) ∷ ws rewrite (vertex-of-decomp' G w) = ({!   !} , {!   !}) , {!   !} 

lemma : (G : Graph) → (v : Vertex) → Σ[ pf ∈ _ ] (classify G [] v <> ≡ NPTop pf) → list-forall (λ ε → edge-classify G ε ≡ NPE v) (recomp-t (decomp-v G v))
lemma G (V k u) eq = forall-concat-comprehension pos-finite _ _ λ p → list-forall-concat (list-forall-map (helper p))
  where
    helper : (p : Pos) → list-forall (λ (u' , t) → list-forall (λ ε → edge-classify G ε ≡ NPE (V k u)) (E (S (V k u) p _) (vertex-of-term t) u' _ ∷ recomp-t t)) (apply-finite-map pos-finite (finite-map pos-finite (λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ _)))) p)
    helper p rewrite apply-finite-map-correct pos-finite ((λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ <>)))) p = list-forall-map (lemma-core G (V k u) eq p)

  -- forall-concat-comprehension pos-finite _ _ λ p → list-forall-concat (helper p)
  -- where
  --   helper3 : (p : Pos) → list-forall (λ (u' , t) → list-forall (λ ε → edge-classify G ε ≡ NPE (V k u)) (E (S (V k u) p _) (vertex-of-term t) u' _ ∷ recomp-t t)) (map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p _)))
  --   helper3 p = list-forall-map (lemma-core G (V k u) eq p)

  --   helper2 : (p : Pos) → list-forall (λ (u' , t) → list-forall (λ ε → edge-classify G ε ≡ NPE (V k u)) (E (S (V k u) p _) (vertex-of-term t) u' _ ∷ recomp-t t)) (apply-finite-map pos-finite (finite-map pos-finite (λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ _)))) p)
  --   helper2 p rewrite apply-finite-map-correct pos-finite ((λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ _)))) p = helper3 p
    
  --   helper : (p : Pos) → list-forall (list-forall (λ ε → edge-classify G ε ≡ NPE (V k u))) (map (λ (u' , t) → E (S (V k u) p _) (vertex-of-term t) u' _ ∷ recomp-t t) (apply-finite-map pos-finite (finite-map pos-finite (λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ _)))) p))
  --   -- helper p with list-forall-map {P = (list-forall (λ ε → edge-classify G ε ≡ NPE (V k u)))} {l = (apply-finite-map pos-finite (finite-map pos-finite (λ p₁ → map (λ (u' , v) → u' , decomp-v' G v) (children G (S (V k u) p₁ _)))) p)} {f = (λ (u' , t) → E (S (V k u) p _) (vertex-of-term t) u' _ ∷ recomp-t t)} {!   !}
  --   -- ... | thing = thing
  --   helper p = list-forall-map (helper2 p)

-- NP-part : Graph → (List Edge) → Vertex → List Edge 
-- NP-part G [] v = []
-- NP-part G (ε ∷ εs) v with edge-classify G ε 
-- ... | MPE _ = NP-part G εs v
-- ... | UE _ = NP-part G εs v
-- ... | NPE v? with Dec.does (v ≟Vertex v?)
-- ... | true = ε ∷ (NP-part G εs v)
-- ... | false = NP-part G εs v

-- lemma : (G : Graph) → (v : Vertex) → Σ[ pf ∈ _ ] (classify G [] v <> ≡ NPTop pf) → list-equiv (recomp-t (decomp-v G v)) (NP-part G G v)
-- lemma G v = {!   !}

-- pieces-inversion : (G : Graph) → Set 
-- pieces-inversion G with (partition-graph G)
-- ... | PG NP MP U with (NP ++ MP ++ U)
-- ... | [] = ⊤ 
-- ... | (v , εs) ∷ ps = list-equiv (recomp-t (decomp-v G v)) εs

-- -- I think this lemma is the crux
-- pieces-lemma : (G : Graph) → (pieces-inversion G)
-- pieces-lemma G with (partition-graph G)
-- ... | PG NP MP U with (NP ++ MP ++ U)
-- ... | [] = <> 
-- ... | (v , εs) ∷ ps = {!   !}
  
redecomp : (G : Graph) → (recomp-grove (decomp-G G) ≡ G)
redecomp G = {!   !}  