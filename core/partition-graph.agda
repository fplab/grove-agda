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
  ParentHave : ∀{G v w a c} → parent ((E (S v a) w c) ∷ G) v w
  ParentSkip : ∀{G v w ε} → parent G v w → parent (ε ∷ G) v w

-- might need to emit proofs one day
parents : Graph → Vertex → List(Vertex) 
parents [] v = [] 
parents ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?)
parents ((E (S w _) _ _) ∷ G) v | true = w ∷ (parents G v) 
parents (_ ∷ G) v | false = parents G v

parents-correct : (G : Graph) → (v : Vertex) → list-forall (λ w → parent G w v) (parents G v) 
parents-correct [] v = <>
parents-correct ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?) | Dec.proof (v ≟Vertex v?)
parents-correct (E (S w _) v _ ∷ G) .v | true | ofʸ refl = ParentHave , list-forall-implies (parents-correct G v) (λ x → ParentSkip x)
parents-correct (_ ∷ G) v | false | _ = list-forall-implies (parents-correct G v) (λ x → ParentSkip x)

-- might need to emit proofs one day
children : Graph → Source → List(Ident × Vertex) 
children [] s = [] 
children ((E s? _ _) ∷ G) s with Dec.does (s ≟Source s?)
children ((E _ v u) ∷ G) s | true = (u , v) ∷ (children G s) 
children (_ ∷ G) s | false = children G s

children-correct : (G : Graph) → (v : Vertex) → (p : Pos) → list-forall (λ (_ , w) → parent G v w) (children G (S v p))
children-correct [] v p = <>
children-correct ((E s? _ _) ∷ G) v p with Dec.does ((S v p) ≟Source s?) | Dec.proof ((S v p) ≟Source s?)
children-correct ((E _ w u) ∷ G) v p | true | ofʸ refl = ParentHave , (list-forall-implies (children-correct G v p) (λ x → ParentSkip x))
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
  OAMI-step : {G : Graph} → {v w x : Vertex} → {u u' : Ident} → (only-ancestor-min-id G v w u) → (classify-parents G w ≡ PC-UP x) → ((id-min u (id-of-vertex x)) ≡ u') → (only-ancestor-min-id G v x u')

data X : Set where 
  NP : X 
  MP : X 
  U : X 

top : X → Graph → Vertex → Set 
top NP G v = classify-parents G v ≡ PC-NP
top MP G v = classify-parents G v ≡ PC-MP 
top U G v = only-ancestor-min-id G v v (id-of-vertex v)

inner : X → Graph → Vertex → Vertex → Set 
inner X G v w = ¬(top U G v) × has-only-ancestor G v w × (top X G w)

data class : Graph → Vertex → Set where 
  Top : ∀{G v} → (X : X) → class G v
  Inner : ∀{G v} → (X : X) → (w : Vertex) → class G v

data class-correct : (G : Graph) → (v : Vertex) → (class G v) → Set where 
  TopCorrect : ∀{X G v} → (top X G v) → class-correct G v (Top X) 
  InnerCorrect : ∀{X G v} → (w : Vertex) → (inner X G v w) → class-correct G v (Inner X w)
  
only-descendants : Graph → Vertex → List(Vertex × Ident) → Set 
only-descendants G v ws = list-forall (λ (w , u) → only-ancestor-min-id G w v u) ws

-- returns true if ( v , v.id ) appears in ws
locate-U : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → Bool
locate-U G v [] = false
locate-U G v ((v? , u) ∷ ws) with Dec.does (v ≟Vertex v?) | Dec.does (u ≟𝕀 (id-of-vertex v))
... | true | true = true
... | true | false = locate-U G v ws
... | false | _ = locate-U G v ws

locate-U-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → (locate-U G v ws ≡ true) → (top U G v)
locate-U-correct G v [] oas () 
locate-U-correct G v ((v? , u) ∷ ws) (oa , oas) eq with Dec.does (v ≟Vertex v?) | Dec.does (u ≟𝕀 (id-of-vertex v)) | Dec.proof (v ≟Vertex v?) | Dec.proof (u ≟𝕀 (id-of-vertex v))
... | true | true | ofʸ refl | ofʸ refl = oa
... | true | false | _ | _ = locate-U-correct G v ws oas eq
... | false | _ | _ | _ = locate-U-correct G v ws oas eq

update-ws : Vertex → List(Vertex × Ident) → Vertex → List(Vertex × Ident)
update-ws v ws x = (v , (id-of-vertex x)) ∷ (map (λ (w , u) → (w , id-min u (id-of-vertex x))) ws)

update-ws-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (x : Vertex) → (only-descendants G v ws) → (classify-parents G v ≡ PC-UP x) → (only-descendants G x (update-ws v ws x))
update-ws-correct G v ws x oas eq = OAMI-base eq , forall-map-implies oas (λ {(w , u)} → λ oa → OAMI-step oa eq refl)

-- {-# TERMINATING #-} 
classify : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (class G v)
classify zero G v ws = Top NP -- this is a meaningless return value
classify (suc fuel) G v ws with classify-parents G v
classify (suc fuel) G v ws | PC-NP = Top NP -- if it has no parents, it is Top NP
classify (suc fuel) G v ws | PC-MP = Top MP -- if it has multiple parents, it is Top MP
classify (suc fuel) G v ws | PC-UP x with locate-U G v ws
classify (suc fuel) G v ws | PC-UP x | true = Top U -- if it appears in the seen list with minimal id, it is Top U
classify (suc fuel) G v ws | PC-UP x | false with Dec.does (v ≟Vertex x)
classify (suc fuel) G v ws | PC-UP x | false | true = Top U -- if its parent is itself, it is Top U
classify (suc fuel) G v ws | PC-UP x | false | false with classify fuel G x (update-ws v ws x)
classify (suc fuel) G v ws | PC-UP x | false | false | Top X = Inner X x -- if its parent is Top, it is Inner
classify (suc fuel) G v ws | PC-UP x | false | false | Inner NP w = Inner NP w -- if its parent is Inner NP, it's the same
classify (suc fuel) G v ws | PC-UP x | false | false | Inner MP w = Inner MP w -- if its parent is Inner MP, it's the same
classify (suc fuel) G v ws | PC-UP x | false | false | Inner U w with Dec.does (v ≟Vertex w)
classify (suc fuel) G v ws | PC-UP x | false | false | Inner U w | true = Top U -- if its parent is Inner U rooted at itself, its Top U
classify (suc fuel) G v ws | PC-UP x | false | false | Inner U w | false = Inner U w -- if its parent is Inner U with a different root, its the same

not-utop : (G : Graph) → (v x : Vertex) → (classify-parents G v ≡ PC-UP x) → ¬(v ≡ x) → ¬(inner U G x v) → ¬(top U G v)
not-utop G v x eq neq not-inner (OAMI-base eq2) rewrite eq with eq2 
not-utop G v x eq neq not-inner (OAMI-base eq2) | refl = neq refl
not-utop G v x eq neq not-inner (OAMI-step oa eq2 eq3) = not-inner ({!   !} , {!   !})

-- {-# TERMINATING #-} 
classify-correct : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → class-correct G v (classify fuel G v ws)
classify-correct zero G v ws oas = {!   !}
classify-correct (suc fuel) G v ws oas with inspect (classify-parents G v)
classify-correct (suc fuel) G v ws oas | PC-NP with≡ eq rewrite eq = TopCorrect eq
classify-correct (suc fuel) G v ws oas | PC-MP with≡ eq rewrite eq = TopCorrect eq
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq rewrite eq with inspect (locate-U G v ws)
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | true with≡ eq' rewrite eq' = TopCorrect (locate-U-correct G v ws oas eq')
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' rewrite eq' with Dec.does (v ≟Vertex x) | Dec.proof (v ≟Vertex x)
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | true | ofʸ refl = TopCorrect (OAMI-base eq)
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | false | ofⁿ neq with classify fuel G x (update-ws v ws x) | classify-correct fuel G x (update-ws v ws x) (update-ws-correct G v ws x oas eq)
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | false | ofⁿ neq | Top X | TopCorrect top = InnerCorrect x ({!   !} , HOA-base eq , top)
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | false | ofⁿ neq | Inner NP w | InnerCorrect _ (not-utop , oa , top)= InnerCorrect w ( {!   !} , HOA-step eq oa , top)
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | false | ofⁿ neq | Inner MP w | InnerCorrect _ (not-utop , oa , top)= InnerCorrect w ( {!   !} , HOA-step eq oa , top)
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | false | ofⁿ neq | Inner U w | InnerCorrect _ (not-utop , oa , top) with Dec.does (v ≟Vertex w) | Dec.proof (v ≟Vertex w) 
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | false | ofⁿ neq | Inner U w | InnerCorrect _ (not-utop , oa , top) | true | ofʸ refl = TopCorrect top 
classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | false | ofⁿ neq | Inner U w | InnerCorrect _ (not-utop , oa , top) | false | ofⁿ neq' = InnerCorrect w ( {!   !} , HOA-step eq oa , top)

-- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | NPTop | NPTopCorrect top = InnerCorrect NP x (HOA-base eq , top)
-- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | MPTop | MPTopCorrect top = InnerCorrect MP x (HOA-base eq , top)
-- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | UTop | UTopCorrect top = InnerCorrect U x (HOA-base eq , top)
-- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | NPInner w | NPInnerCorrect _ (oa , top) = InnerCorrect NP w (HOA-step eq oa , top)
-- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | MPInner w | MPInnerCorrect _ (oa , top) = InnerCorrect MP w (HOA-step eq oa , top)
-- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | UInner w | UInnerCorrect _ (oa , top) = InnerCorrect U w (HOA-step eq oa , top)

-- -- this typechecks for me... I have no idea how
-- classify-correct-nptop : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → (classify G v ws ≡ NPTop) → (NP-top G v)
-- classify-correct-nptop G v ws oas ()

-- -- I broke it
-- silly : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → (classify G v ws ≡ NPTop) → ⊥
-- silly G v ws oas ()

-- postulate 
--   k : Ctor 
--   u : Ident 

-- absurd : ⊥ 
-- absurd = silly [] (V k u) [] <> refl

-- -- this is important 
-- -- classify-of-parent : (G : Graph) → 
-- --   (v w : Vertex) → 
-- --   (classify G w [] ≡ NPInner v) → 
-- --   (v' : Vertex) → 
-- --   (classify-parents G v' ≡ PC-UP w) → 
-- --   (classify G v' [] ≡ NPInner v)
-- -- classify-of-parent G v w eq1 v' eq2 with classify G w [] | classify-correct G w [] <> | eq1
-- -- ... | NPInner .v | NPInnerCorrect .v (oa , top) | refl = let npinner' = (HOA-step eq2 oa , top) in {!   !}
-- -- with inspect (classify-parents G v') | eq2
-- -- ... | PC-NP with≡ eq | () 
-- -- ... | PC-MP with≡ eq | ()
-- -- ... | PC-UP x with≡ eq | _ rewrite eq = {!   !}

-- data edge-class : Graph → Edge → Set where 
--   NPE : ∀{G ε} → Vertex → edge-class G ε
--   MPE : ∀{G ε} → Vertex → edge-class G ε
--   UE : ∀{G ε} → Vertex → edge-class G ε
  
-- edge-classify : (G : Graph) → (ε : Edge) → edge-class G ε 
-- edge-classify G (E (S v _) _ _) with classify G v []
-- ... | NPTop = NPE v 
-- ... | MPTop = MPE v
-- ... | UTop = UE v
-- ... | NPInner w = NPE w
-- ... | MPInner w = MPE w
-- ... | UInner w = UE w


-- -- classify-np-top : (G : Graph) → (v : Vertex) → (eq : NP-top G v) → (classify G [] v <> ≡ NPTop eq)
-- -- classify-np-top G v eq with inspect (classify-parents G v)
-- -- classify-np-top G v eq | (PC-NP with≡ eq') = {!   !}

-- list-assoc-update : List (Vertex × Graph) → Vertex → Edge → List (Vertex × Graph)
-- list-assoc-update [] v ε = (v , ε ∷ []) ∷ []
-- list-assoc-update ((v? , εs) ∷ l) v ε with Dec.does (v ≟Vertex v?)
-- ... | true = (v , ε ∷ εs) ∷ l
-- ... | false = (v? , εs) ∷ list-assoc-update l v ε

-- record  Partitioned-Graph : Set where
--   constructor PG
--   field
--     NP : List (Vertex × Graph)
--     MP : List (Vertex × Graph)
--     U : List (Vertex × Graph)

-- partition-graph-rec : Graph → (List Edge) → Partitioned-Graph 
-- partition-graph-rec G [] = PG [] [] []
-- partition-graph-rec G (ε ∷ εs) with edge-classify G ε | partition-graph-rec G εs 
-- ... | NPE x | PG NP MP U = PG (list-assoc-update NP x ε) MP U
-- ... | MPE x | PG NP MP U = PG NP (list-assoc-update MP x ε)U  
-- ... | UE x | PG NP MP U = PG NP MP (list-assoc-update U x ε)
    
-- partition-graph : Graph → Partitioned-Graph 
-- partition-graph G = partition-graph-rec G G
 
-- unpartition-graph : Partitioned-Graph → Graph          
-- unpartition-graph (PG NP MP U) = (concat (map (λ (v , εs) → εs) NP)) ++ (concat (map (λ (v , εs) → εs) MP)) ++ (concat (map (λ (v , εs) → εs) U)) 