module core.grove where

open import Relation.Binary.PropositionalEquality
open import core.graph
open import core.graph_functions
open import core.var
open import core.exp
open import core.pat
open import core.typ
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

edecomp' : Vertex → Pos → Exp 
edecomp' v p with ∈-outedges

-- this combines the edecomp, pdecomp, and tdecomp
-- this e stands for edge, not expression
edecomp : Graph → Edge → Term 
edecomp G (E s (V (Exp-var x) u) u') = 
  let Gv = ingraph G (V (Exp-var x) u) in 
  TermExp ((` Gv) x)
edecomp G (E s (V Exp-lam u) u') = 
  let Gv = ingraph G (V Exp-lam u) in 
  {!   !}
  -- let q = edecomp' (E s (V Exp-lam u) u') Param
edecomp G (E s (V Exp-app u) u') = {!   !}
edecomp G (E s (V Exp-plus u) u') = {!   !}
edecomp G (E s (V Exp-times u) u') = {!   !}
edecomp G (E s (V (Exp-num x) u) u') = {!   !}
edecomp G (E s (V (Pat-var x) u) u') = {!   !}
edecomp G (E s (V Typ-arrow u) u') = {!   !}
edecomp G (E s (V Typ-num u) u') = {!   !}
-- Unreachable?
edecomp G (E s (V Root u) u') = {!   !}

-- pdecomp : Graph → Edge → Pat 
-- pdecomp = {!   !}

-- tdecomp : Graph → Edge → Typ 
-- tdecomp = {!   !}

-- edge-decomp : Graph → Edge → Term 
-- edge-decomp G e with e  
-- edge-decomp G e | (E s (V k u) u') with (sort k)
-- ... | SortExp = TermExp (edecomp G e)
-- ... | SortPat = TermPat (pdecomp G e)
-- ... | SortType = TermTyp (tdecomp G e)

decomp : Graph → Grove
Grove.NP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_empty {Edge} (λ e → (e ∈-inedges G , v)))  
Grove.MP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_multiple {Edge} (λ e → (e ∈-inedges G , v))) 
Grove.U (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_singleton {Edge} (λ e → (e ∈-inedges G , v)) × v is-min (λ w → (w ∈-ancestors G , v)))