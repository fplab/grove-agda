module core.grove where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
open import Data.Bool
open import Data.Nat hiding (_+_)
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

Θ : Set
Θ = List(Term)

record Grove : Set₁ where
  constructor γ
  field
    NP : Θ
    MP : Θ
    U : Θ

default_exp : Exp 
default_exp = `⟨ [] ⟩ 

default_pat : Pat 
default_pat = ⟨ [] ⟩` 

default_typ : Typ 
default_typ = ⟨ [] ⟩

mutual 
  pdecomp' : Graph → (ε : Edge) → (p : Pos) → (well-sorted-source (Edge.child ε) p) → Pat
  pdecomp' G (E s v u ws) p wsa with outedges (S v p wsa) G 
  pdecomp' G (E s v u ws) p wsa | [] = ☐` (H ((S v p wsa)))
  pdecomp' G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs  = ⟨ map (pdecomp G) (ε1 ∷ ε2 ∷ εs) ⟩`
  pdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] with inedges v' G
  pdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | [] = default_pat -- impossible
  pdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ _ ∷ _ = ⋎ₑ` (E s' v' u' ws')
  pdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = ⤾ₑ` (E s' v' u' ws')
  ... | false = pdecomp G (E s' v' u' ws')

  pdecomp : Graph → Edge → Pat
  pdecomp G (E s (V (Pat-var x) u) u' ws) =
    let Gv = ingraph (V (Pat-var x) u) G in 
    (Gv `) x
  -- impossible
  pdecomp G (E s (V Root u) u' ws) = default_pat
  pdecomp G (E s (V (Exp-var x) u) u' ws) = default_pat
  pdecomp G (E s (V Exp-lam u) u' ws) = default_pat
  pdecomp G (E s (V Exp-app u) u' ws) = default_pat
  pdecomp G (E s (V Exp-plus u) u' ws) = default_pat
  pdecomp G (E s (V Exp-times u) u' ws) = default_pat
  pdecomp G (E s (V (Exp-num x) u) u' ws) = default_pat
  pdecomp G (E s (V Typ-arrow u) u' ws) = default_pat
  pdecomp G (E s (V Typ-num u) u' ws) = default_pat

mutual  
  {-# TERMINATING #-}
  tdecomp' : Graph → (ε : Edge) → (p : Pos) → (well-sorted-source (Edge.child ε) p) → Typ
  tdecomp' G (E s v u ws) p wsa with outedges (S v p wsa) G 
  tdecomp' G (E s v u ws) p wsa | [] = ☐ (H ((S v p wsa)))
  tdecomp' G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs = ⟨ map (tdecomp G) (ε1 ∷ ε2 ∷ εs) ⟩
  tdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] with inedges v' G
  tdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | [] = default_typ -- impossible
  tdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ _ ∷ _ = ⋎ₑ (E s' v' u' ws')
  tdecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = ⤾ₑ (E s' v' u' ws')
  ... | false = tdecomp G (E s' v' u' ws')

  tdecomp : Graph → Edge → Typ
  tdecomp G (E s (V Typ-arrow u) u' ws) = 
    let ε =  (E s (V Typ-arrow u) u' ws) in
    let Gv = ingraph (V Typ-arrow u) G in
    let τ1 = tdecomp' G ε Domain (SortType , ArityArrowDomain) in 
    let τ2 = tdecomp' G ε Return (SortType , ArityArrowReturn) in 
    _-→_ Gv τ1 τ2
  tdecomp G (E s (V Typ-num u) u' ws) =
    let Gv = ingraph (V Typ-num u) G in
    num Gv
  -- impossible 
  tdecomp G (E s (V Root u) u' ws) = default_typ
  tdecomp G (E s (V (Exp-var x) u) u' ws) = default_typ
  tdecomp G (E s (V Exp-lam u) u' ws) = default_typ
  tdecomp G (E s (V Exp-app u) u' ws) = default_typ
  tdecomp G (E s (V Exp-plus u) u' ws) = default_typ
  tdecomp G (E s (V Exp-times u) u' ws) = default_typ
  tdecomp G (E s (V (Exp-num x) u) u' ws) = default_typ
  tdecomp G (E s (V (Pat-var x) u) u' ws) = default_typ

mutual 
  {-# TERMINATING #-}
  edecomp' : Graph → (ε : Edge) → (p : Pos) → (well-sorted-source (Edge.child ε) p) → Exp 
  edecomp' G (E s v u ws) p wsa with outedges (S v p wsa) G 
  edecomp' G (E s v u ws) p wsa | [] = `☐ (H ((S v p wsa)))
  edecomp' G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs = `⟨ map (edecomp G) (ε1 ∷ ε2 ∷ εs) ⟩
  edecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] with inedges v' G
  edecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | [] = default_exp -- impossible
  edecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ _ ∷ _ = `⋎ₑ (E s' v' u' ws')
  edecomp' G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = `⤾ₑ (E s' v' u' ws')
  ... | false = edecomp G (E s' v' u' ws')

  edecomp : Graph → Edge → Exp 
  edecomp G (E s (V (Exp-var x) u) u' ws) = 
    let Gv = ingraph (V (Exp-var x) u) G in 
    (Gv ` x)
  edecomp G (E s (V Exp-lam u) u' ws) =
    let ε = (E s (V Exp-lam u) u' ws) in
    let Gv = ingraph (V Exp-lam u) G in 
    let q = pdecomp' G ε Param (SortPat , ArityLamParam) in 
    let τ = tdecomp' G ε Type (SortType , ArityLamType) in 
    let e = edecomp' G ε Body (SortExp , ArityLamBody) in 
    Gv `λ q ∶ τ ∙ e
  edecomp G (E s (V Exp-app u) u' ws) =
    let ε = (E s (V Exp-app u) u' ws) in
    let Gv = ingraph (V Exp-app u) G in 
    let e1 = edecomp' G ε Fun (SortExp , ArityAppFun) in 
    let e2 = edecomp' G ε Arg (SortExp , ArityAppArg) in 
    Gv ` e1 ∙ e2
  edecomp G (E s (V Exp-plus u) u' ws) =
    let ε = (E s (V Exp-plus u) u' ws) in
    let Gv = ingraph (V Exp-plus u) G in 
    let e1 = edecomp' G ε Left (SortExp , ArityPlusLeft) in 
    let e2 = edecomp' G ε Right (SortExp , ArityPlusRight) in 
    _`_+_ Gv e1 e2
  edecomp G (E s (V Exp-times u) u' ws) =
    let ε = (E s (V Exp-times u) u' ws) in
    let Gv = ingraph (V Exp-times u) G in 
    let e1 = edecomp' G ε Left (SortExp , ArityTimesLeft) in 
    let e2 = edecomp' G ε Right (SortExp , ArityTimesRight) in 
    _`_*_ Gv e1 e2
  edecomp G (E s (V (Exp-num n) u) u' ws) =
    let Gv = ingraph (V (Exp-num n) u) G in 
    Gv `ℕ n
  -- impossible
  edecomp G (E s (V (Pat-var x) u) u' ws) = default_exp
  edecomp G (E s (V Typ-arrow u) u' ws) = default_exp
  edecomp G (E s (V Typ-num u) u' ws) = default_exp
  edecomp G (E s (V Root u) u' ws) = default_exp

edge-decomp : Graph → Edge → Term 
edge-decomp G ε with ε  
edge-decomp G ε | (E s (V k u) u' ws) with (sort k)
edge-decomp G ε | (E s (V k u) u' ws) | SortExp = (TermExp (edecomp G ε))
edge-decomp G ε | (E s (V k u) u' ws) | SortPat = (TermPat (pdecomp G ε))
edge-decomp G ε | (E s (V k u) u' ws) | SortTyp = (TermTyp (tdecomp G ε))

-- the first graph is the outer, static argument. the second is inducted on.
decomp-helper : Graph → Graph → Grove
decomp-helper GG [] = γ [] [] []
decomp-helper GG ((E s v u ws , Ge) ∷ G) with decomp-helper GG G | inedges v GG
decomp-helper GG ((E s v u ws , Ge) ∷ G) | γ NP MP U | [] = γ ((edge-decomp GG (E s v u ws)) ∷ NP) MP U
decomp-helper GG ((E s v u ws , Ge) ∷ G) | γ NP MP U | _ ∷ _ ∷ _ = γ NP (edge-decomp GG (E s v u ws) ∷ MP) U
decomp-helper GG ((E s v u ws , Ge) ∷ G) | γ NP MP U | _ ∷ [] with is-own-min-ancestor v GG
... | false = γ NP MP U
... | true = γ NP MP (edge-decomp GG (E s v u ws) ∷ U) 
 
decomp : Graph → Grove 
decomp G = decomp-helper G G 

Θ-recomp : Θ → Graph 
Θ-recomp [] = []
Θ-recomp (x ∷ l) = unionG (term-recomp x) (Θ-recomp l)

recomp : Grove → Graph  
recomp (γ NP MP U) = unionG (Θ-recomp NP) (unionG (Θ-recomp MP) (Θ-recomp U))