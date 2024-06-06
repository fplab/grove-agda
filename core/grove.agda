module core.grove where

-- open import prelude
open import core.var
open import core.graph
open import Data.Nat


----------------
-- Syntax of Terms
----------------
-- TODO Annotate exps, typs, pat_vars with graphs, refs with edges, and empty holes with local sources
-- TODO figure out conflicts and references

data Typ : Set where
  num : Typ
  unknown : Typ --TODO: Use question mark or some other character ?
  _-→_ : Typ → Typ → Typ
  -- TODO: Multiparent, unicycle, conflicts, empty holes

data Exp : Set where
 `_ : (x : Var) → Exp
 `λ_∶_∙_ : (q : PatVar) → (τ : Typ) → (e : Exp) → Exp -- '\:'
 `_∙_ : (e1 : Exp) → (e2 : Exp) → Exp
 `ℕ_ : (n : ℕ) → Exp
 `_+_ : (e1 : Exp) → (e2 : Exp) → Exp
 `_*_ : (e1 : Exp) → (e2 : Exp) → Exp
 -- curlyveedownarrow
 -- TODO multiparent, unicycle, conflicts, empty holes

----------------
-- Set of Terms
----------------

data Term : Set where
  e : Exp → Term
  τ : Typ → Term
  q : PatVar → Term
 
data θ : Set where
  empty  : θ
  insert : Term → θ → θ

-- ? Is this a good representation


----------------
-- Groves
----------------


record Grove : Set where
  constructor γ
  field
    NP : θ
    MP : θ
    U : θ