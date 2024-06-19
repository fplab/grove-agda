module core.pat where

open import core.hole
open import core.graph
open import core.var
open import Data.List


data Pat : Set where 
  `_  : (G : Graph) → (x : Var)  → Pat
  ☐    : (u : Hole)  → Pat
  ⋎ₑ   : (ε : Edge)  → Pat
  ⤾ₑ   : (ε : Edge)  → Pat
  ⟨_⟩  : List Pat    → Pat

precomp : (p : Pat) → Graph
precomp ((` G) x) = G
precomp (☐ u) = λ _ → bot
precomp (⋎ₑ ε) = λ _ → +
precomp (⤾ₑ ε) = λ _ → +
precomp ⟨ [] ⟩ = λ _ →  bot
precomp ⟨ x ∷ xs ⟩ = unionG (precomp x) (precomp ⟨ xs ⟩)