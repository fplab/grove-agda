module core.logic where

open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)
open import Data.List

-- empty type
data ⊥ : Set where

-- from false, derive whatever
abort : ∀ {C : Set} → ⊥ → C
abort ()

-- negation 
open import Agda.Primitive using (Level)
¬_ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → ⊥

-- unit
data ⊤ : Set where
  <> : ⊤

-- pairs
infixr 1 _,_
record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (lmax l1 l2) where
  constructor _,_
  field
    π1 : A
    π2 : B π1
open Σ public

-- Sigma types, or dependent pairs, with nice notation.
syntax Σ A (\ x -> B) = Σ[ x ∈ A ] B

_×_ : {l1 : Level} {l2 : Level} → (Set l1) → (Set l2) → Set (lmax l1 l2)
A × B = Σ A λ _ → B

-- sums
data _+_ (A B : Set) : Set where
  Inl : A → A + B
  Inr : B → A + B

infixr 1 _×_
infixr 1 _+_

list-forall : {A : Set} → (A → Set) → (List A) → Set 
list-forall P [] = ⊤
list-forall P (a ∷ l) = (P a) × (list-forall P l)