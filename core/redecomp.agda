module core.redecomp where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List

open import core.logic
open import core.finite
open import core.graph
open import core.term
open import core.partition-graph
open import core.decomp
open import core.recomp

redecomp : (G : Graph) → (recomp-grove(decomp-G(G)) ≡ G)
redecomp G = {!   !}  