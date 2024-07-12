open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary using (Decidable)

module Grove.Core
  (Ctor : Set)
  (_≟ℂ_ : Decidable (_≡_ {A = Ctor}))
  (arity : Ctor → ℕ)
  where

  import Grove.Core.Graph
  import Grove.Core.Grove
  import Grove.Core.Classify
  import Grove.Core.ClassifyLemmas
  import Grove.Core.ClassifyCorrect
  import Grove.Core.Decomp
  import Grove.Core.Recomp
  import Grove.Core.CGraph

  import Grove.Core.Properties.Recomposability
  import Grove.Core.Properties.ActionCommutative

  open module Graph = Grove.Core.Graph Ctor _≟ℂ_ arity public
  open module Grove = Grove.Core.Grove Ctor _≟ℂ_ arity public
  open module Classify = Grove.Core.Classify Ctor _≟ℂ_ arity
  open module ClassifyLemmas = Grove.Core.ClassifyLemmas Ctor _≟ℂ_ arity
  open module ClassifyCorrect = Grove.Core.ClassifyCorrect Ctor _≟ℂ_ arity
  open module Decomp = Grove.Core.Decomp Ctor _≟ℂ_ arity
  open module Recomp = Grove.Core.Recomp Ctor _≟ℂ_ arity
  open module CGraph = Grove.Core.CGraph Ctor _≟ℂ_ arity

  open module Recomposability = Grove.Core.Properties.Recomposability Ctor _≟ℂ_ arity
  open module ActionCommutative = Grove.Core.Properties.ActionCommutative Ctor _≟ℂ_ arity
