module core.term where

-- open import prelude
open import core.var
open import core.typ
open import core.graph
open import core.exp
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

----------------
-- Set of Terms
----------------

data Term : Set where
  e : Exp → Term
  τ : Typ → Term
 
data θ : Set where
  empty  : θ
  insert : Term → θ → θ


recomp : (t : Term) → Graph
recomp (e x)  = erecomp x
recomp (τ x)  =  trecomp x


decomp : (G : Graph) → Term
decomp G = {!   !}

-- TODO: Define recomp and decomp to work with edge sets
-- TODO: Need a helper from edge set → graph

-- ! Define decomp using a graph and a set of edges (inedges in G (plus)) → term (ignore -, bot)



_≟t_ : (t₁ t₂ : Term) → Dec (t₁ ≡ t₂)
_≟t_ t₁ t₂ = {!   !}


-- TODO: Define edge set as a data type and define decomp and recomp in terms of edge sets


  -- ! What about duplicates in θ?
  -- TODO: Create zippered terms along with cursor in a separate file?


  -- ? Use a list and define well-formedness to include no dups in list
  -- ? Or pair a list with a proof that it contains no dups
  -- TODO : Need decidable equality of exps, typs, and terms to show this

  -- TODO: Use the IDs instead of term equality to check for dups in þteta





