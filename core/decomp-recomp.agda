module core.decomp-recomp where

open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)
open import Relation.Nullary hiding(¬_)
open import Data.Bool hiding (_<_; _≟_)
open import Data.List

open import prelude
open import core.finite
open import core.graph
open import core.grove
open import core.classify
-- open import core.classify-lemmas
open import core.classify-correct
open import core.decomp
open import core.recomp

decomp-recomp-v-sound : (G : Graph) → (v : Vertex) → (top X v) → list-forall ? (recomp (decomp v))
decomp-recomp-v-sound = ? 

decomp-recomp : (G : Graph) → (recomp-grove (decomp-G G) ≡ G)
decomp-recomp G = {!   !}  