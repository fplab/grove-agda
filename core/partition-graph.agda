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

data parent : Graph → (v w : Vertex) → Set where 
  ParentHave : ∀{G v w a b c d} → parent ((E (S v a b) w c d) ∷ G) v w
  ParentSkip : ∀{G v w ε} → parent G v w → parent (ε ∷ G) v w

-- might need to emit proofs one day
parents : Graph → Vertex → List(Vertex) 
parents [] v = [] 
parents ((E s v? _ _) ∷ G) v with Dec.does (v ≟Vertex v?)
parents ((E (S w _ _) _ _ _) ∷ G) v | true = w ∷ (parents G v) 
parents (_ ∷ G) v | false = parents G v

parents-correct : (G : Graph) → (v : Vertex) → list-forall (λ w → parent G w v) (parents G v) 
parents-correct [] v = <>
parents-correct ((E s v? _ _) ∷ G) v with Dec.does (v ≟Vertex v?) | Dec.proof (v ≟Vertex v?)
parents-correct (E (S w _ _) v _ _ ∷ G) .v | true | ofʸ refl = ParentHave , list-forall-implies (parents-correct G v) (λ x → ParentSkip x)
parents-correct (_ ∷ G) v | false | _ = list-forall-implies (parents-correct G v) (λ x → ParentSkip x)

-- might need to emit proofs one day
children : Graph → Source → List(Ident × Vertex) 
children [] s = [] 
children ((E s? _ _ _) ∷ G) s with Dec.does (s ≟Source s?)
children ((E _ v u _) ∷ G) s | true = (u , v) ∷ (children G s) 
children (_ ∷ G) s | false = children G s

children-correct : (G : Graph) → (v : Vertex) → (p : Pos) → list-forall (λ (_ , w) → parent G v w) (children G (S v p <>))
children-correct [] v p = <>
children-correct ((E s? _ _ _) ∷ G) v p with Dec.does ((S v p <>) ≟Source s?) | Dec.proof ((S v p <>) ≟Source s?)
children-correct ((E _ w u _) ∷ G) v p | true | ofʸ refl = ParentHave , (list-forall-implies (children-correct G v p) (λ x → ParentSkip x))
children-correct (_ ∷ G) v p | false | _ = list-forall-implies (children-correct G v p) (λ x → ParentSkip x)

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

-- this is true and can be used, but it might be so lightweight as to be confusing. depends on what level of abstraction you want to work. 
-- NP-inner-parent : (G : Graph) → (v x w : Vertex) → (classify-parents G v ≡ PC-UP x) → (NP-inner G x w) → (NP-inner G v w)
-- NP-inner-parent G v x w eq (oa , top) = HOA-step eq oa , top

-- data class : Graph → Vertex → Set where 
--   NPTop : ∀{G v} → (NP-top G v) → class G v
--   MPTop : ∀{G v} → (MP-top G v) → class G v
--   UTop : ∀{G v} → (U-top G v) → class G v
--   NPInner : ∀{G v} → (w : Vertex) → (NP-inner G v w) → class G v
--   MPInner : ∀{G v} → (w : Vertex) → (MP-inner G v w) → class G v
--   UInner : ∀{G v} → (w : Vertex) → (U-inner G v w) → class G v

data class : Graph → Vertex → Set where 
  NPTop : ∀{G v} → class G v
  MPTop : ∀{G v} → class G v
  UTop : ∀{G v} → class G v
  NPInner : ∀{G v} → (w : Vertex) → class G v
  MPInner : ∀{G v} → (w : Vertex) → class G v
  UInner : ∀{G v} → (w : Vertex) → class G v

data class-correct : (G : Graph) → (v : Vertex) → (class G v) → Set where 
  NPTopCorrect : ∀{G v} → (NP-top G v) → class-correct G v NPTop 
  MPTopCorrect : ∀{G v} → (MP-top G v) → class-correct G v MPTop
  UTopCorrect : ∀{G v} → (U-top G v) → class-correct G v UTop
  NPInnerCorrect : ∀{G v} → (w : Vertex) → (NP-inner G v w) → class-correct G v (NPInner w)
  MPInnerCorrect : ∀{G v} → (w : Vertex) → (MP-inner G v w) → class-correct G v (MPInner w)
  UInnerCorrect : ∀{G v} → (w : Vertex) → (U-inner G v w) → class-correct G v (UInner w)

only-descendants : Graph → Vertex → List(Vertex × Ident) → Set 
only-descendants G v ws = list-forall (λ (w , u) → only-ancestor-min-id G w v u) ws

-- returns true if ( v , v.id ) appears in ws
locate-U : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → Bool
locate-U G v [] = false
locate-U G v ((v? , u) ∷ ws) with Dec.does (v ≟Vertex v?) | Dec.does (u ≟𝕀 (id-of-vertex v))
... | true | true = true
... | true | false = locate-U G v ws
... | false | _ = locate-U G v ws

locate-U-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → (locate-U G v ws ≡ true) → (U-top G v)
locate-U-correct G v [] oas () 
locate-U-correct G v ((v? , u) ∷ ws) (oa , oas) eq with Dec.does (v ≟Vertex v?) | Dec.does (u ≟𝕀 (id-of-vertex v)) | Dec.proof (v ≟Vertex v?) | Dec.proof (u ≟𝕀 (id-of-vertex v))
... | true | true | ofʸ refl | ofʸ refl = oa
... | true | false | _ | _ = locate-U-correct G v ws oas eq
... | false | _ | _ | _ = locate-U-correct G v ws oas eq

-- {-# TERMINATING #-} 
-- Why? because it terminates when it hits a node with 0 or multiple parents. 
-- When it's running, it's following a chain of only-parents.
-- Since G is finite, this chain will eventually meet itself again.
-- This forms a loop. When the chain reaches the minimal-id element of the loop, it will terminate.
-- classify : (G : Graph) → (ws : List(Vertex × Ident)) → (v : Vertex) → (only-descendants G v ws) → (class G v)
-- classify G ws v ods with inspect (classify-parents G v)
-- classify G ws v ods | (PC-NP with≡ eq) = NPTop eq
-- classify G ws v ods | (PC-MP with≡ eq) = MPTop eq
-- classify G ws v ods | (PC-UP x with≡ eq) with locate-U G ws v ods
-- classify G ws v ods | (PC-UP x with≡ eq) | Inr utop = UTop utop
-- classify G ws v ods | (PC-UP x with≡ eq) | Inl <> with classify G ((v , (id-of-vertex x)) ∷ (map (λ (w , u) → (w , id-min u (id-of-vertex x))) ws)) x (OAMI-base eq , forall-map-implies ods (λ {(w , u)} → λ oami → OAMI-step oami eq))
-- classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | NPTop nptop = NPInner x (HOA-base eq , nptop)
-- classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | MPTop mptop = MPInner x (HOA-base eq , mptop)
-- classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | UTop utop = UInner x (HOA-base eq , utop)
-- classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | NPInner r (hoa , nptop) = NPInner r ((HOA-step eq hoa) , nptop)
-- classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | MPInner r (hoa , mptop) = MPInner r ((HOA-step eq hoa) , mptop)
-- classify G ws v ods | (PC-UP x with≡ eq) | Inl <> | UInner r (hoa , utop) = UInner r ((HOA-step eq hoa) , utop)

update-ws : Vertex → List(Vertex × Ident) → Vertex → List(Vertex × Ident)
update-ws v ws x = (v , (id-of-vertex x)) ∷ (map (λ (w , u) → (w , id-min u (id-of-vertex x))) ws)

update-ws-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (x : Vertex) → (only-descendants G v ws) → (classify-parents G v ≡ PC-UP x) → (only-descendants G x (update-ws v ws x))
update-ws-correct G v ws x oas eq = OAMI-base eq , forall-map-implies oas (λ {(w , u)} → λ oa → OAMI-step oa eq)

{-# TERMINATING #-} 
classify : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (class G v)
classify G v ws with classify-parents G v
classify G v ws | PC-NP = NPTop
classify G v ws | PC-MP = MPTop
classify G v ws | PC-UP x with locate-U G v ws
classify G v ws | PC-UP x | true = UTop
classify G v ws | PC-UP x | false with classify G x (update-ws v ws x)
classify G v ws | PC-UP x | false | NPTop = NPInner x
classify G v ws | PC-UP x | false | MPTop = MPInner x
classify G v ws | PC-UP x | false | UTop = UInner x
classify G v ws | PC-UP x | false | NPInner w = NPInner w
classify G v ws | PC-UP x | false | MPInner w = MPInner w
classify G v ws | PC-UP x | false | UInner w = UInner w

{-# TERMINATING #-} 
classify-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → class-correct G v (classify G v ws)
classify-correct G v ws oas with inspect (classify-parents G v)
classify-correct G v ws oas | PC-NP with≡ eq rewrite eq = NPTopCorrect eq
classify-correct G v ws oas | PC-MP with≡ eq rewrite eq = MPTopCorrect eq
classify-correct G v ws oas | PC-UP x with≡ eq rewrite eq with inspect (locate-U G v ws)
classify-correct G v ws oas | PC-UP x with≡ eq | true with≡ eq' rewrite eq' = UTopCorrect (locate-U-correct G v ws oas eq')
classify-correct G v ws oas | PC-UP x with≡ eq | false with≡ eq' rewrite eq' with classify G x (update-ws v ws x) | classify-correct G x (update-ws v ws x) (update-ws-correct G v ws x oas eq)
classify-correct G v ws oas | PC-UP x with≡ eq | false with≡ eq' | NPTop | NPTopCorrect top = NPInnerCorrect x (HOA-base eq , top)
classify-correct G v ws oas | PC-UP x with≡ eq | false with≡ eq' | MPTop | MPTopCorrect top = MPInnerCorrect x (HOA-base eq , top)
classify-correct G v ws oas | PC-UP x with≡ eq | false with≡ eq' | UTop | UTopCorrect top = UInnerCorrect x (HOA-base eq , top)
classify-correct G v ws oas | PC-UP x with≡ eq | false with≡ eq' | NPInner w | NPInnerCorrect _ (oa , top) = NPInnerCorrect w (HOA-step eq oa , top)
classify-correct G v ws oas | PC-UP x with≡ eq | false with≡ eq' | MPInner w | MPInnerCorrect _ (oa , top) = MPInnerCorrect w (HOA-step eq oa , top)
classify-correct G v ws oas | PC-UP x with≡ eq | false with≡ eq' | UInner w | UInnerCorrect _ (oa , top) = UInnerCorrect w (HOA-step eq oa , top)

data edge-class : Graph → Edge → Set where 
  NPE : ∀{G ε} → Vertex → edge-class G ε
  MPE : ∀{G ε} → Vertex → edge-class G ε
  UE : ∀{G ε} → Vertex → edge-class G ε
  
edge-classify : (G : Graph) → (ε : Edge) → edge-class G ε 
edge-classify G (E (S v _ _) _ _ _) with classify G v []
... | NPTop = NPE v 
... | MPTop = MPE v
... | UTop = UE v
... | NPInner w = NPE w
... | MPInner w = MPE w
... | UInner w = UE w


-- classify-np-top : (G : Graph) → (v : Vertex) → (eq : NP-top G v) → (classify G [] v <> ≡ NPTop eq)
-- classify-np-top G v eq with inspect (classify-parents G v)
-- classify-np-top G v eq | (PC-NP with≡ eq') = {!   !}

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