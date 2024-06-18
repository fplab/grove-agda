module core.grove where

open import Relation.Binary.PropositionalEquality
open import core.graph
open import core.graph_functions
open import core.term
open import core.logic
open import core.sets

----------------
-- Groves
----------------

θ : Set₁
θ = Term → Set

record Grove : Set₁ where
  constructor γ
  field
    NP : θ
    MP : θ
    U : θ

-- _ : Grove
-- _ = γ empty empty empty

edge-decomp : Edge → Term 
edge-decomp = {!   !}

decomp : Graph → Grove
Grove.NP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edge-decomp (E s v u) ≡ t × is_empty {Edge} (λ e → (e ∈-inedges G , v))) 
Grove.MP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edge-decomp (E s v u) ≡ t × is_multiple {Edge} (λ e → (e ∈-inedges G , v))) 
Grove.U (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edge-decomp (E s v u) ≡ t × is_singleton {Edge} (λ e → (e ∈-inedges G , v)) × v is-min (λ w → (w ∈-ancestors G , v)))