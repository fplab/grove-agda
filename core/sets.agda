module core.sets where

open import core.logic
open import Relation.Binary.PropositionalEquality

is_empty : {A : Set} → (A → Set) → Set 
is_empty {A} (_∈S) = (a : A) → ¬(a ∈S)

is_singleton : {A : Set} → (A → Set) → Set
is_singleton {A} (_∈S) =  Σ[ a ∈ A ] ((b : A) → a ≡ b)

is_multiple : {A : Set} → (A → Set) → Set
is_multiple {A} S = ¬(is_empty S) × ¬(is_singleton S) 