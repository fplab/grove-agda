{-# OPTIONS --allow-unsolved-metas #-}

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
open import Data.Unit renaming (tt to <>)
open import Data.Product hiding (map)

open import core.ident
open import core.finite
open import core.list-logic

module core.classify 
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

import core.graph
open module graph = core.graph Ctor _≟ℂ_ arity

data parent : Graph → (v w : Vertex) → Set where 
  ParentHave : ∀{G v w a c} → parent ((E (S v a) w c) ∷ G) v w
  ParentSkip : ∀{G v w ε} → parent G v w → parent (ε ∷ G) v w

-- might need to emit proofs one day
parents : Graph → Vertex → List(Vertex) 
parents [] v = [] 
parents ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?)
parents ((E (S w _) _ _) ∷ G) v | true = w ∷ (parents G v) 
parents (_ ∷ G) v | false = parents G v

children : Graph → Source → List(EdgeId × Vertex) 
children [] s = [] 
children ((E s? _ _) ∷ G) s with Dec.does (s ≟Source s?)
children ((E _ v u) ∷ G) s | true = (u , v) ∷ (children G s) 
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

only-ancestor : Graph → (v w : Vertex) → (n : ℕ) → (Vec Vertex (suc (suc n))) → Set 
only-ancestor G v w n ws = 
    (lookup ws zero ≡ v) × 
    (lookup ws (fromℕ (suc n)) ≡ w) × 
    ((i : Fin (suc n)) → classify-parents G (lookup ws (cast-up i)) ≡ PC-UP (lookup ws (suc i)))

nat-only-ancestor : Graph → (v w : Vertex) → (n : ℕ) → Set 
nat-only-ancestor G v w n = 
  Σ[ ws ∈ (Vec Vertex (suc (suc n))) ] 
  (only-ancestor G v w n ws)

is-only-ancestor : Graph → (v w : Vertex) → Set 
is-only-ancestor G v w = 
  Σ[ n ∈ ℕ ] 
  (nat-only-ancestor G v w n)

id-of-vertex : Vertex → VertexId 
id-of-vertex (V ctor ident) = ident

id-min : VertexId → VertexId → VertexId  
id-min u1 u2 with Dec.does (u1 ≤?V𝕀 u2)
... | true = u1
... | false = u2

min-id : {m : ℕ} → Vec Vertex m → VertexId → Set
min-id {zero} ws u = ⊤
min-id {suc m} ws u = (i : Fin m) → u ≤V𝕀 id-of-vertex (lookup ws (suc i))

is-only-ancestor-min-id : Graph → (v w : Vertex) → (u : VertexId) → Set 
is-only-ancestor-min-id G v w u = 
  Σ[ n ∈ ℕ ] 
  Σ[ ws ∈ (Vec Vertex (suc (suc n))) ] 
  ((only-ancestor G v w n ws) × 
  min-id ws u)

data X : Set where 
  NP : X 
  MP : X 
  U : X 

top : X → Graph → Vertex → Set 
top NP G v = classify-parents G v ≡ PC-NP
top MP G v = classify-parents G v ≡ PC-MP 
top U G v = is-only-ancestor-min-id G v v (id-of-vertex v)

inner : X → Graph → Vertex → Vertex → Set 
inner X G v w = ¬(top U G v) × (is-only-ancestor G v w) × (top X G w)

data class : Graph → Vertex → Set where 
  Top : ∀{G v} → (X : X) → class G v
  Inner : ∀{G v} → (X : X) → (w : Vertex) → class G v
  
only-descendants : Graph → Vertex → List(Vertex × VertexId) → Set 
only-descendants G v ws = list-forall (λ (w , u) → is-only-ancestor-min-id G w v u) ws

-- returns true if ( v , v.id ) appears in ws
locate-U : (G : Graph) → (v : Vertex) → (ws : List(Vertex × VertexId)) → Bool
locate-U G v [] = false
locate-U G v ((v? , u) ∷ ws) with Dec.does (v ≟Vertex v?) | Dec.does (u ≟V𝕀 (id-of-vertex v))
... | true | true = true
... | true | false = locate-U G v ws
... | false | _ = locate-U G v ws

update-ws : Vertex → List(Vertex × VertexId) → Vertex → List(Vertex × VertexId)
update-ws v ws x = (v , (id-of-vertex x)) ∷ (Data.List.map (λ (w , u) → (w , id-min u (id-of-vertex x))) ws)
  
classify : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (ws : List(Vertex × VertexId)) → (class G v)
classify zero G v ws = {!   !}
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

data edge : X → Graph → Edge → Vertex → Set where 
  TopEdge : ∀{X G v u1 x u2} → (top X G v) → edge X G (E (S v u1) x u2) v
  InnerEdge : ∀{X G v u1 x u2 w} → (inner X G v w) → edge X G (E (S v u1) x u2) w

data edge-class : Graph → Edge → Set where 
  EC : ∀{G ε} → (X : X) → (w : Vertex) → edge-class G ε
  
edge-classify : (fuel : ℕ) → (G : Graph) → (ε : Edge) → edge-class G ε 
edge-classify fuel G (E (S v _) _ _) with classify fuel G v []
... | Top X = EC X v 
... | Inner X w = EC X w