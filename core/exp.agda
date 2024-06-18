{-# OPTIONS --allow-unsolved-metas #-}
module core.exp where



open import core.hole
open import core.graph
open import core.var
open import core.typ
open import Data.Nat
open import Data.List
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

----------------
-- Syntax of Expressions
----------------
data Exp : Set where
 `☐      : (u : Hole)  → Exp
 `_      : (G : Graph) → (x : Var)  → Exp
 `λ_∶_∙_ : (G : Graph) → (x : Var)  → (τ : Typ)  → (e : Exp) → Exp 
 `_∙_    : (G : Graph) → (e1 : Exp) → (e2 : Exp) → Exp
 `ℕ_     : (G : Graph) → (n : ℕ)    → Exp
 `_+_    : (G : Graph) → (e1 : Exp) → (e2 : Exp) → Exp
 `_*_    : (G : Graph) → (e1 : Exp) → (e2 : Exp) → Exp
 `⋎ₑ     : (ε : Edge)  → Exp
 `⤾ₑ     : (ε : Edge)  → Exp
 `⟨_⟩    : List Exp    → Exp



erecomp : (e : Exp) → Graph
erecomp (`☐ u) = λ _ → bot 
erecomp ((` G) x) = G
erecomp ((`λ G ∶ x ∙ τ) e) = (G ∪G trecomp(τ)) ∪G erecomp(e)
erecomp ((` G ∙ e₁) e₂) = (G ∪G erecomp(e₁)) ∪G erecomp(e₂)
erecomp ((`ℕ G) n) = G
erecomp ((` G + e₁) e₂) = (G ∪G erecomp(e₁)) ∪G erecomp(e₂)
erecomp ((` G * e₁) e₂) = (G ∪G erecomp(e₁)) ∪G erecomp(e₂)
erecomp (`⋎ₑ ε) = λ _ → +
erecomp (`⤾ₑ ε) = λ _ → +
erecomp `⟨ [] ⟩ = λ _ →  bot
erecomp `⟨ x ∷ xs ⟩ = unionG (erecomp x) (erecomp `⟨ xs ⟩)


-- TODO : Fix this to map recomp on the list
 
-- TODO Need a way to 'union' graphs together


_≟e_ : (e₁ e₂ : Exp) → Dec (e₁ ≡ e₂)
does (e₁ ≟e e₂) = {!   !}
proof (e₁ ≟e e₂) = {!   !}