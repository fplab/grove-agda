module core.grove where

open import core.term


----------------
-- Groves
----------------

record Grove : Set where
  constructor γ
  field
    NP : θ
    MP : θ
    U : θ




_ : Grove
_ = γ empty empty empty