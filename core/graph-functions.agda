module core.graph-functions where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
open import Data.Maybe hiding(map)
open import Data.Nat
open import Relation.Nullary


open import core.graph
open import core.logic

edges : Graph → List(Edge) 
edges [] = [] 
edges ((e , +) ∷ G) = e ∷ (edges G)
edges ((e , -) ∷ G) = edges G

sources : Graph → List(Source) 
sources [] = [] 
sources ((E s v u , +) ∷ G) = s ∷ (sources G) 
sources ((e , -) ∷ G) = sources G 

outedges : Source → Graph → List(Edge) 
outedges s [] = [] 
outedges s ((E s' v u , +) ∷ G) with Dec.does (s ≟Source s')
outedges s ((E s' v u , +) ∷ G) | true = (E s' v u) ∷ (outedges s G) 
outedges s ((E s' v u , +) ∷ G) | false = outedges s G
outedges s ((e , -) ∷ G) = outedges s G

inedges : Vertex → Graph → List(Edge) 
inedges v [] = [] 
inedges v ((E s v' u , +) ∷ G) with Dec.does (v ≟Vertex v')
inedges v ((E s v' u , +) ∷ G) | true = (E s v' u) ∷ (inedges v G) 
inedges v ((E s v' u , +) ∷ G) | false = inedges v G
inedges v ((e , -) ∷ G) = inedges v G

ingraph : Vertex → Graph → Graph 
ingraph v [] = [] 
ingraph v ((E s v' u , Ge) ∷ G) with Dec.does (v ≟Vertex v')
ingraph v ((E s v' u , Ge) ∷ G) | true = ((E s v' u) , Ge) ∷ (ingraph v G) 
ingraph v ((E s v' u , Ge) ∷ G) | false = ingraph v G

parents : Vertex → Graph → List(Vertex) 
parents v [] = [] 
parents v ((E s v' u , +) ∷ G) with Dec.does (v ≟Vertex v')
parents v ((E (S w _) v' u , +) ∷ G) | true = w ∷ (parents v G) 
parents v ((E s v' u , +) ∷ G) | false = parents v G
parents v ((e , -) ∷ G) = parents v G

-- uses fuel
ancestors-helper : Vertex → Graph → ℕ → List(Vertex)
ancestors-helper v G zero = []
ancestors-helper v G (suc fuel) = 
  let parents = parents v G in
  let grand-ancestors = map (λ parent → ancestors-helper parent G fuel) parents in 
  parents ++ (concat grand-ancestors)

ancestors : Vertex → Graph → List(Vertex)
ancestors v G = ancestors-helper v G (length G)

min : List(Vertex) → Maybe(Vertex) 
min [] = nothing 
min (V k u ∷ vs) with min vs 
... | nothing = just (V k u)
... | just (V k' u') with (u ≤𝕀 u')
... | true = just (V k u)
... | false = just (V k' u')

is-own-min-ancestor : Vertex → Graph → Bool 
is-own-min-ancestor v G with min (ancestors v G)
... | nothing = false 
... | just v' = Dec.does (v ≟Vertex v')


-- data _∈-ancestors_,_ : Vertex → Graph → Vertex → Set where 
--   AncestorParent : ∀{G v₁ v₂} → v₁ ∈-parents G , v₂ → v₁ ∈-ancestors G , v₂ 
--   AncestorGrand : ∀{G v₁ v₂ v₃} → v₁ ∈-parents G , v₂ → v₂ ∈-ancestors G , v₃ → v₁ ∈-ancestors G , v₃ 
  
-- _is-min_ : Vertex → (Vertex → Set) → Set 
-- v is-min (_∈S) = (w : Vertex) → (w ∈S) → (Vertex.ident v) ≤𝕀 (Vertex.ident w)
