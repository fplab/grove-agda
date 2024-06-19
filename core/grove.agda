module core.grove where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
open import Data.Bool
open import Data.Nat
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

-- bound invariant : if F(bound,...) = (term, bound'), then bound <= indices in term < bound'

mutual 
  edecomp' : ℕ → Graph → Edge → Pos → (Exp × ℕ)
  edecomp' bound G (E s v u) p with outedges (S v p) G 
  edecomp' bound G (E s v u) p | [] = `☐ (H bound ((S v p))) , suc bound
  edecomp' bound G (E s v u) p | ε1 ∷ ε2 ∷ εs with map-folder bound G (ε1 ∷ ε2 ∷ εs)
    where
      map-folder : ℕ → Graph → List(Edge) → (List(Exp) × ℕ) 
      map-folder bound G [] = ([] , bound)
      map-folder bound G (ε ∷ εs) with edecomp bound G ε 
      ... | e , bound' with map-folder bound' G εs 
      ... | es , bound'' = (e ∷ es) , bound''
  edecomp' bound G (E s v u) p | ε1 ∷ ε2 ∷ εs | (es , bound') = `⟨ es ⟩ , bound'
  edecomp' bound G (E s v u) p | (E s' v' u') ∷ [] with inedges v' G
  edecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | [] = `⟨ [] ⟩ , zero -- impossible
  edecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ _ ∷ _ = `⋎ₑ (E s' v' u') , bound
  edecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = `⤾ₑ (E s' v' u') , bound
  ... | false = edecomp bound G (E s' v' u')

  edecomp : ℕ → Graph → Edge → (Exp × ℕ)
  edecomp bound G (E s (V (Exp-var x) u) u') = 
    let Gv = ingraph (V (Exp-var x) u) G in 
    (Gv ` x) , bound
  edecomp bound G (E s (V Exp-lam u) u') =
    let ε = (E s (V Exp-lam u) u') in
    let Gv = ingraph (V Exp-lam u) G in 
    let q , bound' = pdecomp' bound G ε Param in 
    let τ , bound'' = tdecomp' bound' G ε Type in 
    let e , bound''' = edecomp' bound'' G ε Body in 
    Gv `λ q ∶ τ ∙ e , bound'''
  edecomp bound G (E s (V Exp-app u) u') = {!   !}
  edecomp bound G (E s (V Exp-plus u) u') = {!   !}
  edecomp bound G (E s (V Exp-times u) u') = {!   !}
  edecomp bound G (E s (V (Exp-num x) u) u') = {!   !}
  -- impossible
  edecomp bound G (E s (V (Pat-var x) u) u') = {!   !}
  edecomp bound G (E s (V Typ-arrow u) u') = {!   !}
  edecomp bound G (E s (V Typ-num u) u') = {!   !}
  edecomp bound G (E s (V Root u) u') = {!   !}

  -- edecomp G (E s (V (Exp-var x) u) u') =
  --   let Gv = ingraph (V (Exp-var x) u) G in 
  --   ((` Gv) x)
  -- edecomp G (E s (V Exp-lam u) u') =
  --   let Gv = ingraph (V Exp-lam u) G in 
  --   {!   !}
  --   -- let q = edecomp' (E s (V Exp-lam u) u') Param
  -- edecomp G (E s (V Exp-app u) u') = {!   !}
  -- edecomp G (E s (V Exp-plus u) u') = {!   !}
  -- edecomp G (E s (V Exp-times u) u') = {!   !}
  -- edecomp G (E s (V (Exp-num x) u) u') = {!   !}
  -- -- these are unreachable because of when edecomp is called
  -- edecomp G (E s (V (Pat-var x) u) u') = {!   !}
  -- edecomp G (E s (V Typ-arrow u) u') = {!   !}
  -- edecomp G (E s (V Typ-num u) u') = {!   !}
  -- edecomp G (E s (V Root u) u') = {!   !}

  -- pdecomp : Graph → Edge → Pat 
  -- pdecomp G (E s (V (Pat-var x) u) u') =
  --   let Gv = ingraph (V (Pat-var x) u) G in 
  --   ((` Gv) x)
  -- pdecomp G (E s (V k u) u') = {!   !}

  pdecomp' : ℕ → Graph → Edge → Pos → (Pat × ℕ)
  pdecomp' bound G (E s v u) p with outedges (S v p) G 
  pdecomp' bound G (E s v u) p | [] = ☐` (H bound ((S v p))) , suc bound
  pdecomp' bound G (E s v u) p | ε1 ∷ ε2 ∷ εs with map-folder bound G (ε1 ∷ ε2 ∷ εs)
    where
      map-folder : ℕ → Graph → List(Edge) → (List(Pat) × ℕ) 
      map-folder bound G [] = ([] , bound)
      map-folder bound G (ε ∷ εs) with pdecomp bound G ε 
      ... | e , bound' with map-folder bound' G εs 
      ... | es , bound'' = (e ∷ es) , bound''
  pdecomp' bound G (E s v u) p | ε1 ∷ ε2 ∷ εs | (es , bound') = ⟨ es ⟩` , bound'
  pdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] with inedges v' G
  pdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | [] = ⟨ [] ⟩` , zero -- impossible
  pdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ _ ∷ _ = ⋎ₑ` (E s' v' u') , bound
  pdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = ⤾ₑ` (E s' v' u') , bound
  ... | false = pdecomp bound G (E s' v' u')

  pdecomp : ℕ → Graph → Edge → (Pat × ℕ)
  pdecomp = {!   !}

  tdecomp' : ℕ → Graph → Edge →  Pos → (Typ × ℕ)
  tdecomp' bound G (E s v u) p with outedges (S v p) G 
  tdecomp' bound G (E s v u) p | [] = ☐ (H bound ((S v p))) , suc bound
  tdecomp' bound G (E s v u) p | ε1 ∷ ε2 ∷ εs with map-folder bound G (ε1 ∷ ε2 ∷ εs)
    where
      map-folder : ℕ → Graph → List(Edge) → (List(Typ) × ℕ) 
      map-folder bound G [] = ([] , bound)
      map-folder bound G (ε ∷ εs) with tdecomp bound G ε 
      ... | e , bound' with map-folder bound' G εs 
      ... | es , bound'' = (e ∷ es) , bound''
  tdecomp' bound G (E s v u) p | ε1 ∷ ε2 ∷ εs | (es , bound') = ⟨ es ⟩ , bound'
  tdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] with inedges v' G
  tdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | [] = ⟨ [] ⟩ , zero -- impossible
  tdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ _ ∷ _ = ⋎ₑ (E s' v' u') , bound
  tdecomp' bound G (E s v u) p | (E s' v' u') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = ⤾ₑ (E s' v' u') , bound
  ... | false = tdecomp bound G (E s' v' u')

  tdecomp : ℕ → Graph → Edge → (Typ × ℕ)
  tdecomp = {!   !}

edge-decomp : ℕ → Graph → Edge → (Term × ℕ)
edge-decomp bound G ε with ε  
edge-decomp bound G ε | (E s (V k u) u') with (sort k)
edge-decomp bound G ε | (E s (V k u) u') | SortExp with edecomp bound G ε
edge-decomp bound G ε | (E s (V k u) u') | SortExp | (e , bound') = (TermExp e , bound')
edge-decomp bound G ε | (E s (V k u) u') | SortPat with pdecomp bound G ε
edge-decomp bound G ε | (E s (V k u) u') | SortPat | (q , bound') = (TermPat q , bound')
edge-decomp bound G ε | (E s (V k u) u') | SortTyp with tdecomp bound G ε
edge-decomp bound G ε | (E s (V k u) u') | SortTyp | (τ , bound') = (TermTyp τ , bound')

-- the first graph is the outer, static argument. the second is inducted on.
decomp-helper : ℕ → Graph → Graph → (Grove × ℕ)
decomp-helper bound GG [] = γ [] [] [] , bound
decomp-helper bound GG ((E s v u , Ge) ∷ G) with decomp-helper bound GG G | inedges v GG
decomp-helper bound GG ((E s v u , Ge) ∷ G) | (γ NP MP U , bound') | [] with edge-decomp bound' GG (E s v u)
decomp-helper bound GG ((E s v u , Ge) ∷ G) | (γ NP MP U , bound') | [] | (t , bound'') = γ (t ∷ NP) MP U , bound''
decomp-helper bound GG ((E s v u , Ge) ∷ G) | (γ NP MP U , bound') | _ ∷ _ ∷ _ with edge-decomp bound' GG (E s v u)
decomp-helper bound GG ((E s v u , Ge) ∷ G) | (γ NP MP U , bound') | _ ∷ _ ∷ _ | (t , bound'') = γ NP (t ∷ MP) U , bound''
decomp-helper bound GG ((E s v u , Ge) ∷ G) | (γ NP MP U , bound') | _ ∷ [] with is-own-min-ancestor v GG
... | false = γ NP MP U , bound'
... | true with edge-decomp bound' GG (E s v u) 
... | (t , bound'') = γ NP MP (t ∷ U) , bound'' 

decomp : Graph → Grove
decomp G with decomp-helper zero G G 
... | (grove , _) = grove


-- Grove.NP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_empty {Edge} (λ e → (e ∈-inedges G , v)))  
-- Grove.MP (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_multiple {Edge} (λ e → (e ∈-inedges G , v)))   
-- Grove.U (decomp G) t = Σ[ (E s v u) ∈ Edge ] (edecomp G (E s v u) ≡ t × is_singleton {Edge} (λ e → (e ∈-inedges G , v)) × v is-min (λ w → (w ∈-ancestors G , v)))