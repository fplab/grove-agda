{-# OPTIONS --allow-unsolved-metas #-}
module core.typ where

open import core.graph
open import core.hole
open import core.logic
open import Data.List
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary



data Typ : Set where
  num  : (G : Graph) → Typ
  ☐    : (u : Hole)  → Typ
  _-→_ : (G : Graph) → Typ → Typ → Typ
  ⋎ₑ   : (ε : Edge)  → Typ
  ⤾ₑ   : (ε : Edge)  → Typ
  ⟨_⟩  : List Typ    → Typ

infixr 25 _-→_



trecomp : (τ : Typ) → Graph
trecomp (num G) = G
trecomp (☐ u) = []
trecomp ((G -→ τ₁) τ₂) = (G ∪G trecomp(τ₁)) ∪G trecomp(τ₂)
trecomp (⋎ₑ ε) = [ (ε , +) ] 
trecomp (⤾ₑ ε) = [ (ε , +) ] 
trecomp ⟨ [] ⟩ = []
trecomp ⟨ x ∷ xs ⟩ = unionG (trecomp x) (trecomp ⟨ xs ⟩)

_≟τ_ : (τ₁ τ₂ : Typ) → Dec (τ₁ ≡ τ₂)
_≟τ_ τ₁ τ₂ = {!   !}
