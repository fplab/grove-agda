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

θ : Set
θ = List(Term)

record Grove : Set₁ where
  constructor γ
  field
    NP : θ
    MP : θ
    U : θ

-- bound invariant : if F(bound,...) = (term, bound'), then bound <= indices in term < bound'

default_exp : Exp 
default_exp = `⟨ [] ⟩ 

default_pat : Pat 
default_pat = ⟨ [] ⟩` 

default_typ : Typ 
default_typ = ⟨ [] ⟩

mutual 
  pdecomp' : ℕ → Graph → (ε : Edge) → (p : Pos) → (well-sorted-source (Edge.child ε) p) → (Pat × ℕ)
  pdecomp' bound G (E s v u ws) p wsa with outedges (S v p wsa) G 
  pdecomp' bound G (E s v u ws) p wsa | [] = ☐` (H ((S v p wsa))) , suc bound
  pdecomp' bound G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs with map-folder bound G (ε1 ∷ ε2 ∷ εs)
    where
      map-folder : ℕ → Graph → List(Edge) → (List(Pat) × ℕ) 
      map-folder bound G [] = ([] , bound)
      map-folder bound G (ε ∷ εs) with pdecomp bound G ε 
      ... | e , bound' with map-folder bound' G εs 
      ... | es , bound'' = (e ∷ es) , bound''
  pdecomp' bound G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs | (es , bound') = ⟨ es ⟩` , bound'
  pdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] with inedges v' G
  pdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | [] = default_pat , zero -- impossible
  pdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ _ ∷ _ = ⋎ₑ` (E s' v' u' ws') , bound
  pdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = ⤾ₑ` (E s' v' u' ws') , bound
  ... | false = pdecomp bound G (E s' v' u' ws')

  pdecomp : ℕ → Graph → Edge → (Pat × ℕ)
  pdecomp bound G (E s (V (Pat-var x) u) u' ws) =
    let Gv = ingraph (V (Pat-var x) u) G in 
    (Gv `) x , bound
  -- impossible
  pdecomp bound G (E s (V Root u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V (Exp-var x) u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V Exp-lam u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V Exp-app u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V Exp-plus u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V Exp-times u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V (Exp-num x) u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V Typ-arrow u) u' ws) = default_pat , zero
  pdecomp bound G (E s (V Typ-num u) u' ws) = default_pat , zero

mutual  
  {-# TERMINATING #-}
  tdecomp' : ℕ → Graph → (ε : Edge) → (p : Pos) → (well-sorted-source (Edge.child ε) p) → (Typ × ℕ)
  tdecomp' bound G (E s v u ws) p wsa with outedges (S v p wsa) G 
  tdecomp' bound G (E s v u ws) p wsa | [] = ☐ (H ((S v p wsa))) , suc bound
  tdecomp' bound G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs with map-folder bound G (ε1 ∷ ε2 ∷ εs)
    where
      map-folder : ℕ → Graph → List(Edge) → (List(Typ) × ℕ) 
      map-folder bound G [] = ([] , bound)
      map-folder bound G (ε ∷ εs) with tdecomp bound G ε 
      ... | e , bound' with map-folder bound' G εs 
      ... | es , bound'' = (e ∷ es) , bound''
  tdecomp' bound G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs | (es , bound') = ⟨ es ⟩ , bound'
  tdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] with inedges v' G
  tdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | [] = ⟨ [] ⟩ , zero -- impossible
  tdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ _ ∷ _ = ⋎ₑ (E s' v' u' ws') , bound
  tdecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = ⤾ₑ (E s' v' u' ws') , bound
  ... | false = tdecomp bound G (E s' v' u' ws')

  tdecomp : ℕ → Graph → Edge → (Typ × ℕ)
  tdecomp bound G (E s (V Typ-arrow u) u' ws) = 
    let ε =  (E s (V Typ-arrow u) u' ws) in
    let Gv = ingraph (V Typ-arrow u) G in
    let τ1 , bound' = tdecomp' bound G ε Domain (SortType , ArityArrowDomain) in 
    let τ2 , bound'' = tdecomp' bound' G ε Return (SortType , ArityArrowReturn) in 
    _-→_ Gv τ1 τ2 ,  bound''
  tdecomp bound G (E s (V Typ-num u) u' ws) =
    let Gv = ingraph (V Typ-num u) G in
    num Gv , bound
  -- impossible 
  tdecomp bound G (E s (V Root u) u' ws) = default_typ , zero
  tdecomp bound G (E s (V (Exp-var x) u) u' ws) = default_typ , zero
  tdecomp bound G (E s (V Exp-lam u) u' ws) = default_typ , zero
  tdecomp bound G (E s (V Exp-app u) u' ws) = default_typ , zero
  tdecomp bound G (E s (V Exp-plus u) u' ws) = default_typ , zero
  tdecomp bound G (E s (V Exp-times u) u' ws) = default_typ , zero
  tdecomp bound G (E s (V (Exp-num x) u) u' ws) = default_typ , zero
  tdecomp bound G (E s (V (Pat-var x) u) u' ws) = default_typ , zero

mutual 
  {-# TERMINATING #-}
  edecomp' : ℕ → Graph → (ε : Edge) → (p : Pos) → (well-sorted-source (Edge.child ε) p) → (Exp × ℕ)
  edecomp' bound G (E s v u ws) p wsa with outedges (S v p wsa) G 
  edecomp' bound G (E s v u ws) p wsa | [] = `☐ (H ((S v p wsa))) , suc bound
  edecomp' bound G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs with map-folder bound G (ε1 ∷ ε2 ∷ εs)
    where
      map-folder : ℕ → Graph → List(Edge) → (List(Exp) × ℕ) 
      map-folder bound G [] = ([] , bound)
      map-folder bound G (ε ∷ εs) with edecomp bound G ε 
      ... | e , bound' with map-folder bound' G εs 
      ... | es , bound'' = (e ∷ es) , bound''
  edecomp' bound G (E s v u ws) p wsa | ε1 ∷ ε2 ∷ εs | (es , bound') = `⟨ es ⟩ , bound'
  edecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] with inedges v' G
  edecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | [] = default_exp , zero -- impossible
  edecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ _ ∷ _ = `⋎ₑ (E s' v' u' ws') , bound
  edecomp' bound G (E s v u ws) p wsa | (E s' v' u' ws') ∷ [] | _ ∷ [] with is-own-min-ancestor v' G
  ... | true = `⤾ₑ (E s' v' u' ws') , bound
  ... | false = edecomp bound G (E s' v' u' ws')

  edecomp : ℕ → Graph → Edge → (Exp × ℕ)
  edecomp bound G (E s (V (Exp-var x) u) u' ws) = 
    let Gv = ingraph (V (Exp-var x) u) G in 
    (Gv ` x) , bound
  edecomp bound G (E s (V Exp-lam u) u' ws) =
    let ε = (E s (V Exp-lam u) u' ws) in
    let Gv = ingraph (V Exp-lam u) G in 
    let q , bound' = pdecomp' bound G ε Param (SortPat , ArityLamParam) in 
    let τ , bound'' = tdecomp' bound' G ε Type (SortType , ArityLamType) in 
    let e , bound''' = edecomp' bound'' G ε Body (SortExp , ArityLamBody) in 
    Gv `λ q ∶ τ ∙ e , bound'''
  edecomp bound G (E s (V Exp-app u) u' ws) =
    let ε = (E s (V Exp-app u) u' ws) in
    let Gv = ingraph (V Exp-app u) G in 
    let e1 , bound' = edecomp' bound G ε Fun (SortExp , ArityAppFun) in 
    let e2 , bound'' = edecomp' bound' G ε Arg (SortExp , ArityAppArg) in 
    Gv ` e1 ∙ e2 , bound''
  edecomp bound G (E s (V Exp-plus u) u' ws) =
    let ε = (E s (V Exp-plus u) u' ws) in
    let Gv = ingraph (V Exp-plus u) G in 
    let e1 , bound' = edecomp' bound G ε Left (SortExp , ArityPlusLeft) in 
    let e2 , bound'' = edecomp' bound' G ε Right (SortExp , ArityPlusRight) in 
    _`_+_ Gv e1 e2 , bound''
  edecomp bound G (E s (V Exp-times u) u' ws) =
    let ε = (E s (V Exp-times u) u' ws) in
    let Gv = ingraph (V Exp-times u) G in 
    let e1 , bound' = edecomp' bound G ε Left (SortExp , ArityTimesLeft) in 
    let e2 , bound'' = edecomp' bound' G ε Right (SortExp , ArityTimesRight) in 
    _`_*_ Gv e1 e2 , bound''
  edecomp bound G (E s (V (Exp-num n) u) u' ws) =
    let Gv = ingraph (V (Exp-num n) u) G in 
    Gv `ℕ n , bound
  -- impossible
  edecomp bound G (E s (V (Pat-var x) u) u' ws) = default_exp , zero
  edecomp bound G (E s (V Typ-arrow u) u' ws) = default_exp , zero
  edecomp bound G (E s (V Typ-num u) u' ws) = default_exp , zero
  edecomp bound G (E s (V Root u) u' ws) = default_exp , zero

edge-decomp : ℕ → Graph → Edge → (Term × ℕ)
edge-decomp bound G ε with ε  
edge-decomp bound G ε | (E s (V k u) u' ws) with (sort k)
edge-decomp bound G ε | (E s (V k u) u' ws) | SortExp with edecomp bound G ε
edge-decomp bound G ε | (E s (V k u) u' ws) | SortExp | (e , bound') = (TermExp e , bound')
edge-decomp bound G ε | (E s (V k u) u' ws) | SortPat with pdecomp bound G ε
edge-decomp bound G ε | (E s (V k u) u' ws) | SortPat | (q , bound') = (TermPat q , bound')
edge-decomp bound G ε | (E s (V k u) u' ws) | SortTyp with tdecomp bound G ε
edge-decomp bound G ε | (E s (V k u) u' ws) | SortTyp | (τ , bound') = (TermTyp τ , bound')

-- the first graph is the outer, static argument. the second is inducted on.
decomp-helper : ℕ → Graph → Graph → (Grove × ℕ)
decomp-helper bound GG [] = γ [] [] [] , bound
decomp-helper bound GG ((E s v u ws , Ge) ∷ G) with decomp-helper bound GG G | inedges v GG
decomp-helper bound GG ((E s v u ws , Ge) ∷ G) | (γ NP MP U , bound') | [] with edge-decomp bound' GG (E s v u ws)
decomp-helper bound GG ((E s v u ws , Ge) ∷ G) | (γ NP MP U , bound') | [] | (t , bound'') = γ (t ∷ NP) MP U , bound''
decomp-helper bound GG ((E s v u ws , Ge) ∷ G) | (γ NP MP U , bound') | _ ∷ _ ∷ _ with edge-decomp bound' GG (E s v u ws)
decomp-helper bound GG ((E s v u ws , Ge) ∷ G) | (γ NP MP U , bound') | _ ∷ _ ∷ _ | (t , bound'') = γ NP (t ∷ MP) U , bound''
decomp-helper bound GG ((E s v u ws , Ge) ∷ G) | (γ NP MP U , bound') | _ ∷ [] with is-own-min-ancestor v GG
... | false = γ NP MP U , bound'
... | true with edge-decomp bound' GG (E s v u ws) 
... | (t , bound'') = γ NP MP (t ∷ U) , bound'' 
 
decomp : Graph → Grove 
decomp G with decomp-helper zero G G 
... | (grove , _) = grove

θ-recomp : θ → Graph 
θ-recomp [] = []
θ-recomp (x ∷ l) = unionG (term-recomp x) (θ-recomp l)

recomp : Grove → Graph  
recomp (γ NP MP U) = unionG (θ-recomp NP) (unionG (θ-recomp MP) (θ-recomp U))