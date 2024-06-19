module core.grove where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
open import Data.Bool
open import core.graph
open import core.graph-functions
open import core.var
open import core.hole
open import core.exp
open import core.pat
open import core.typ
open import core.term
open import core.logic

----------------
-- Groves
----------------

θ : Set
θ = List(Term)

record Grove : Set₁ where
  constructor γ
  field
    NP : θ
    MP : θ
    U : θ

mutual 
  edecomp' : Graph → Edge → Pos → Exp 
  edecomp' G (E s v u) p with outedges (S v p) G 
  edecomp' G (E s v u) p | [] = `☐ (H _ ((S v p)))
  edecomp' G (E s v u) p | e1 ∷ e2 ∷ es = `⟨ map (edecomp G) (e1 ∷ e2 ∷ es) ⟩
  edecomp' G (E s v u) p | (E s' v' u') ∷ [] with inedges v' G
  edecomp' G (E s v u) p | (E s' v' u') ∷ [] | [] = _ -- impossible
  edecomp' G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ _ ∷ _ = `⋎ₑ (E s' v' u')
  edecomp' G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = `⤾ₑ (E s' v' u')
  ... | false = edecomp G (E s' v' u')

  edecomp : Graph → Edge → Exp 
  edecomp G (E s (V (Exp-var x) u) u') =
    let Gv = ingraph (V (Exp-var x) u) G in 
    ((` Gv) x)
  edecomp G (E s (V Exp-lam u) u') =
    let Gv = ingraph (V Exp-lam u) G in 
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

edge-decomp : Graph → Edge → Term 
edge-decomp G e with e  
edge-decomp G e | (E s (V k u) u') with (sort k)
... | SortExp = TermExp (edecomp G e)
... | SortPat = TermPat {!   !} --(pdecomp G e)
... | SortType = TermTyp {!   !} --(tdecomp G e)

-- the first graph is the outer, static argument. the second is inducted on.
decomp-helper : Graph → Graph → Grove
decomp-helper GG [] = γ [] [] [] 
decomp-helper GG ((E s v u , Ge) ∷ G) with decomp-helper GG G | inedges v GG
decomp-helper GG ((E s v u , Ge) ∷ G) | γ NP MP U | [] = γ ((edge-decomp GG (E s v u)) ∷ NP) MP U
decomp-helper GG ((E s v u , Ge) ∷ G) | γ NP MP U | _ ∷ _ ∷ _ = γ NP ((edge-decomp GG (E s v u)) ∷ MP) U
decomp-helper GG ((E s v u , Ge) ∷ G) | γ NP MP U | _ ∷ [] with is-own-min-ancestor v GG
... | true = γ NP MP ((edge-decomp GG (E s v u)) ∷ U)
... | false = γ NP MP U

decomp : Graph → Grove
decomp G = decomp-helper G G 


-- Grove.NP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_empty {Edge} (λ e → (e ∈-inedges G , v)))  
-- Grove.MP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_multiple {Edge} (λ e → (e ∈-inedges G , v)))   
-- Grove.U (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_singleton {Edge} (λ e → (e ∈-inedges G , v)) × v is-min (λ w → (w ∈-ancestors G , v)))