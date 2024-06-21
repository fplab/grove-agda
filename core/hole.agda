module core.hole where

open import core.graph
open import Data.Nat

record Hole : Set where
    constructor H
    field
        source : Source

