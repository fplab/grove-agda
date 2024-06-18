module core.graph_functions where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_<_; _≟_)

open import core.graph
open import core.logic

_∈-sources_ : Source → Graph → Set 
s ∈-sources G = Σ[ (E s' _ _) ∈ Edge ] (s ≡ s')

_∈-inedges_ : Edge → Graph → Set 
e ∈-inedges G = (G e) ≡ +

_∈-outedges_,_ : Edge → Graph → Source → Set 
(E s v u) ∈-outedges G , s' = (s ≡ s' × (E s' v u) ∈-inedges G)

_∈-inedges_,_ : Edge → Graph → Vertex → Set 
(E s v u) ∈-inedges G , v' = (v ≡ v')

ingraph : Graph → Vertex → Graph 
ingraph G v (E s v' u) with Dec.does (v ≟Vertex v')
... | true = G (E s v' u)
... | false = bot

_∈-parents_,_ : Vertex → Graph → Vertex → Set 
v₁ ∈-parents G , v₂ = Σ[ (E (S v₃ _ _) v₄ _) ∈ Edge ] (v₁ ≡ v₃ × v₂ ≡ v₄)

data _∈-ancestors_,_ : Vertex → Graph → Vertex → Set where 
  AncestorParent : ∀{G v₁ v₂} → v₁ ∈-parents G , v₂ → v₁ ∈-ancestors G , v₂ 
  AncestorGrand : ∀{G v₁ v₂ v₃} → v₁ ∈-parents G , v₂ → v₂ ∈-ancestors G , v₃ → v₁ ∈-ancestors G , v₃ 
  

