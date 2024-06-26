module core.partition-graph where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding(¬_)
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
open import Data.Maybe hiding(map) 
open import Data.Nat hiding (_+_)

open import core.logic
open import core.graph
open import core.graph-functions

id-of-vertex : Vertex → Ident 
id-of-vertex (V ctor ident) = ident

id-min : Ident → Ident → Ident  
id-min u1 u2 with u1 ≤𝕀 u2 
... | true = u1
... | false = u2

forall-map-implies : {A B : Set} → {P1 : A → Set} → {P2 : B → Set} → {l : List A} → {f : A → B} → list-forall P1 l → ({a : A} → (P1 a) → (P2 (f a))) → list-forall P2 (map f l)
forall-map-implies {A} {B} {P1} {P2} {[]} {f} fa i = <>
forall-map-implies {A} {B} {P1} {P2} {x ∷ l} {f} (p , fa) i = i p , forall-map-implies {A} {B} {P1} {P2} {l} {f} fa i

data parent-class : Graph → Vertex → Set where 
  PC-NP : ∀{G v} → parent-class G v
  PC-UP : ∀{G v} → Vertex → parent-class G v
  PC-MP : ∀{G v} → parent-class G v

classify-parents : (G : Graph) → (v : Vertex) → parent-class G v 
classify-parents G v with parents v G 
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
classify G ws v ods with (classify-parents G v) -- in eq
classify G ws v ods | PC-NP = NPTop {!   !}
classify G ws v ods | PC-MP = MPTop {!   !}
classify G ws v ods | PC-UP x with locate-U G ws v ods
classify G ws v ods | PC-UP x | Inr utop = UTop utop
classify G ws v ods | PC-UP x | Inl <> with classify G ((v , (id-of-vertex x)) ∷ (map (λ (w , u) → (w , id-min u (id-of-vertex x))) ws)) x (OAMI-base {!  !} , forall-map-implies ods (λ {(w , u)} → λ oami → OAMI-step oami {!   !}))
classify G ws v ods | PC-UP x | Inl <> | NPTop nptop = NPInner x (HOA-base {!   !} , nptop)
classify G ws v ods | PC-UP x | Inl <> | MPTop mptop = MPInner x (HOA-base {!   !} , mptop)
classify G ws v ods | PC-UP x | Inl <> | UTop utop = UInner x (HOA-base {!   !}, utop)
classify G ws v ods | PC-UP x | Inl <> | NPInner r (hoa , nptop) = NPInner r ((HOA-step {!   !} hoa) , nptop)
classify G ws v ods | PC-UP x | Inl <> | MPInner r (hoa , mptop) = MPInner r ((HOA-step {!   !} hoa) , mptop)
classify G ws v ods | PC-UP x | Inl <> | UInner r (hoa , utop) = UInner r ((HOA-step {!   !} hoa) , utop)