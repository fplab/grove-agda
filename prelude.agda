module prelude where

open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- unit
data ⊤ {ℓ} : Set ℓ where
  <> : ⊤

-- pairs
infixr 1 _,_
record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (lmax ℓ₁ ℓ₂) where
  constructor _,_
  field
    π1 : A
    π2 : B π1
open Σ public

-- Sigma types, or dependent pairs, with nice notation.
syntax Σ A (\ x -> B) = Σ[ x ∈ A ] B

_×_ : (Set ℓ₁) → (Set ℓ₂) → Set (lmax ℓ₁ ℓ₂)
A × B = Σ A λ _ → B

-- sums
data _+_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (lmax ℓ₁ ℓ₂) where
  Inl : A → A + B
  Inr : B → A + B

infixr 1 _×_
infixr 1 _+_