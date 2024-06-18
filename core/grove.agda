module core.grove where

open import core.graph
open import core.term
open import core.logic

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

decomp : (G : Graph) → Grove
Grove.NP (decomp G) t = Σ[ (E _ v _) ∈ Edge ] {! (inedges v)  !} 
Grove.MP (decomp G) = {!   !} 
Grove.U (decomp G) = {!   !} 