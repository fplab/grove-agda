module core.decomp-recomp where

open import Relation.Binary.PropositionalEquality hiding ([_])
-- open import Data.List
-- open import Data.Bool
-- open import Data.Nat hiding (_+_)
-- open import core.var
-- open import core.hole
-- open import core.exp
-- open import core.pat
-- open import core.typ
-- open import core.term
open import core.logic
open import core.graph
open import core.graph-functions
open import core.grove

-- I know we'll need custom equivalence to account for the list rep
decomp-recomp : (G : Graph) → (recomp(decomp(G)) ≡ G)
decomp-recomp G = {!   !}