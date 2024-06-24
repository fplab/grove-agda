{-# OPTIONS --allow-unsolved-metas #-}

module core.term where

-- open import prelude
open import core.var
open import core.exp
open import core.pat
open import core.typ
open import core.graph
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

----------------
-- Set of Terms
----------------

data Term : Set where
  TermExp : Exp → Term
  TermPat : Pat → Term
  TermTyp : Typ → Term


term-recomp : (t : Term) → Graph
term-recomp (TermExp x) = erecomp x
term-recomp (TermPat x) = precomp x
term-recomp (TermTyp x) = trecomp x


-- TODO: Define recomp and decomp to work with edge sets
-- TODO: Need a helper from edge set → graph

-- ! Define decomp using a graph and a set of edges (inedges in G (plus)) → term (ignore -, bot)

_≟t_ : (t₁ t₂ : Term) → Dec (t₁ ≡ t₂)
_≟t_ t₁ t₂ = {!   !}


-- TODO: Define edge set as a data type and define decomp and recomp in terms of edge sets


  -- ! What about duplicates in θ?
  -- TODO: Create zippered terms along with cursor in a separate file?


  -- ? Use a list and define well-formedness to include no dups in list
  -- ? Or pair a list with a proof that it contains no dups
  -- TODO : Need decidable equality of exps, typs, and terms to show this

  -- TODO: Use the IDs instead of term equality to check for dups in þteta





