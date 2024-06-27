{-# OPTIONS --allow-unsolved-metas #-}

module core.partition-graph where

open import Relation.Binary.PropositionalEquality hiding(inspect)
open import Relation.Nullary hiding(¬_)
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
open import Data.Maybe hiding(map) 
open import Data.Nat hiding (_+_)

open import core.logic
open import core.finite
open import core.graph

id-of-vertex : Vertex → Ident 
id-of-vertex (V ctor ident) = ident

id-min : Ident → Ident → Ident  
id-min u1 u2 with u1 ≤𝕀 u2 
... | true = u1
... | false = u2

-- might need to emit proofs one day
parents : Graph → Vertex → List(Vertex) 
parents [] v = [] 
parents ((E s v? _ _) ∷ G) v with Dec.does (v ≟Vertex v?)
parents ((E (S w _ _) _ _ _) ∷ G) v | true = w ∷ (parents G v) 
parents (_ ∷ G) v | false = parents G v

-- might need to emit proofs one day
children : Graph → Source → List(Ident × Vertex) 
children [] s = [] 
children ((E s? _ _ _) ∷ G) s with Dec.does (s ≟Source s?)
children ((E _ v u _) ∷ G) s | true = (u , v) ∷ (children G s) 
children (_ ∷ G) s | false = children G s

data parent-class : Graph → Vertex → Set where 
  PC-NP : ∀{G v} → parent-class G v
  PC-UP : ∀{G v} → Vertex → parent-class G v
  PC-MP : ∀{G v} → parent-class G v

classify-parents : (G : Graph) → (v : Vertex) → parent-class G v 
classify-parents G v with parents G v 
classify-parents G v | [] = PC-NP
classify-parents G v | x ∷ [] = PC-UP x
classify-parents G v | _ ∷ _ ∷ _ = PC-MP

data has-only-ancestor : Graph → Vertex → Vertex → Set where
  HOA-base : {G : Graph} → {v w : Vertex} → (classify-parents G v ≡ PC-UP w) → (has-only-ancestor G v w)
  HOA-step : {G : Graph} → {v w x : Vertex} → (classify-parents G v ≡ PC-UP w) → (has-only-ancestor G w x) → (has-only-ancestor G v x)

-- this predicate holds on G v w u if it is possible to follow a chain of only-parents 
-- from v to w, and u is the minimal vertex id encountered on that chain (excluding v, including w)
data only-ancestor-min-id : Graph → Vertex → Vertex → Ident → Set where 
  OAMI-base : {G : Graph} → {v w : Vertex} → (classify-parents G v ≡ PC-UP w) → only-ancestor-min-id G v w (id-of-vertex w) 
  OAMI-step : {G : Graph} → {v w x : Vertex} → {u : Ident} → (only-ancestor-min-id G v w u) → (classify-parents G w ≡ PC-UP x) → (only-ancestor-min-id G v x (id-min u (id-of-vertex x)))

NP-top : Graph → Vertex → Set 
NP-top G v = classify-parents G v ≡ PC-NP

MP-top : Graph → Vertex → Set 
MP-top G v = classify-parents G v ≡ PC-MP

U-top : Graph → Vertex → Set 
U-top G v = only-ancestor-min-id G v v (id-of-vertex v)

NP-inner : Graph → Vertex → Vertex → Set 
NP-inner G v w = has-only-ancestor G v w × (NP-top G w)

MP-inner : Graph → Vertex → Vertex → Set 
MP-inner G v w = has-only-ancestor G v w × (MP-top G w)

U-inner : Graph → Vertex → Vertex → Set 
U-inner G v w = has-only-ancestor G v w × (U-top G w)

data class : Graph → Vertex → Set where 
  NPTop : ∀{G v} → (NP-top G v) → class G v
  MPTop : ∀{G v} → (MP-top G v) → class G v
  UTop : ∀{G v} → (U-top G v) → class G v
  NPInner : ∀{G v} → (w : Vertex) → (NP-inner G v w) → class G v
  MPInner : ∀{G v} → (w : Vertex) → (MP-inner G v w) → class G v
  UInner : ∀{G v} → (w : Vertex) → (U-inner G v w) → class G v

only-descendants : Graph → Vertex → List(Vertex × Ident) → Set 
only-descendants G v ws = list-forall (λ (w , u) → only-ancestor-min-id G w v u) ws

locate-U :  (G : Graph) → (ws : List(Vertex × Ident)) → (v : Vertex) → (only-descendants G v ws) → (_+_ ⊤ (U-top G v))
locate-U G [] v <> = Inl <>
locate-U G ((v? , u) ∷ ws) v (od , ods) with (v ≟Vertex v?) | (u ≟𝕀 (id-of-vertex v))
... | _ because ofʸ refl | _ because ofʸ refl = Inl <>
... | _ | _ = locate-U G ws v ods

{-# TERMINATING #-} 
-- Why? because it terminates when it hits a node with 0 or multiple parents. 
-- When it's running, it's following a chain of only-parents.
-- Since G is finite, this chain will eventually meet itself again.
-- This forms a loop. When the chain reaches the minimal-id element of the loop, it will terminate.
classify : (G : Graph) → (ws : List(Vertex × Ident)) → (v : Vertex) → (only-descendants G v ws) → (class G v)
classify G ws v ods with inspect (classify-parents G v)
classify G ws v ods | (PC-NP with≡ eq) = NPTop eq
classify G ws v ods | (PC-MP with≡ eq) = MPTop eq
classify G ws v ods | (PC-UP x with≡ eq) with locate-U G ws v ods
classify G ws v ods | (PC-UP x with≡ eq) | Inr utop = UTop utop
classify G ws v ods | (PC-UP x with≡ eq) | Inl <> with classify G ((v , (id-of-vertex x)) ∷ (map (λ (w , u) → (w , id-min u (id-of-vertex x))) ws)) x (OAMI-base eq , forall-map-implies ods (λ {(w , u)} → λ oami → OAMI-step oami eq))
classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | NPTop nptop = NPInner x (HOA-base eq , nptop)
classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | MPTop mptop = MPInner x (HOA-base eq , mptop)
classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | UTop utop = UInner x (HOA-base eq , utop)
classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | NPInner r (hoa , nptop) = NPInner r ((HOA-step eq hoa) , nptop)
classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | MPInner r (hoa , mptop) = MPInner r ((HOA-step eq hoa) , mptop)
classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | UInner r (hoa , utop) = UInner r ((HOA-step eq hoa) , utop)

-- maybe this carries proofs later. e.g. NPE also holds a proof that ε is down from v, and that v is in NP-top
data edge-class : Graph → Edge → Set where 
  NPE : ∀{G ε} → Vertex → edge-class G ε
  MPE : ∀{G ε} → Vertex → edge-class G ε
  UE : ∀{G ε} → Vertex → edge-class G ε
  
-- assume ε is assigned +. In fact the whole decomp recomp thing should just consider a graph to be a set of edges, and not account for dead ones.
edge-classify : (G : Graph) → (ε : Edge) → edge-class G ε 
edge-classify G (E (S v _ _) _ _ _) with classify G [] v <>
... | NPTop x = NPE v 
... | MPTop x = MPE v
... | UTop x = UE v
... | NPInner w x = NPE w
... | MPInner w x = MPE w
... | UInner w x = UE w

-- not fine enough!
-- record Partitioned-Graph : Set where
--   constructor PG
--   field
--     NP : List Edge
--     MP : List Edge
--     U : List Edge

-- partition-graph-rec : Graph → (List Edge) → Partitioned-Graph 
-- partition-graph-rec G [] = PG [] [] []
-- partition-graph-rec G (ε ∷ εs) with edge-classify G ε | partition-graph-rec G εs 
-- ... | NPE x | PG NP MP U = PG (ε ∷ NP) MP U
-- ... | MPE x | PG NP MP U = PG NP (ε ∷ MP) U
-- ... | UE x | PG NP MP U = PG NP MP (ε ∷ U)
 
-- partition-graph : Graph → Partitioned-Graph 
-- partition-graph G = partition-graph-rec G G

-- unpartition-graph : Partitioned-Graph → Graph 
-- unpartition-graph (PG NP MP U) = NP ++ MP ++ U

list-assoc-update : List (Vertex × Graph) → Vertex → Edge → List (Vertex × Graph)
list-assoc-update [] v ε = (v , ε ∷ []) ∷ []
list-assoc-update ((v? , εs) ∷ l) v ε with Dec.does (v ≟Vertex v?)
... | true = (v , ε ∷ εs) ∷ l
... | false = (v? , εs) ∷ list-assoc-update l v ε

record  Partitioned-Graph : Set where
  constructor PG
  field
    NP : List (Vertex × Graph)
    MP : List (Vertex × Graph)
    U : List (Vertex × Graph)

partition-graph-rec : Graph → (List Edge) → Partitioned-Graph 
partition-graph-rec G [] = PG [] [] []
partition-graph-rec G (ε ∷ εs) with edge-classify G ε | partition-graph-rec G εs 
... | NPE x | PG NP MP U = PG (list-assoc-update NP x ε) MP U
... | MPE x | PG NP MP U = PG NP (list-assoc-update MP x ε)U
... | UE x | PG NP MP U = PG NP MP (list-assoc-update U x ε)
 
partition-graph : Graph → Partitioned-Graph 
partition-graph G = partition-graph-rec G G

unpartition-graph : Partitioned-Graph → Graph 
unpartition-graph (PG NP MP U) = (concat (map (λ (v , εs) → εs) NP)) ++ (concat (map (λ (v , εs) → εs) MP)) ++ (concat (map (λ (v , εs) → εs) U))