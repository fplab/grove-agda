open import Data.List using (List)

open import Grove.Ident
open import Grove.Marking.Typ
open import Grove.Marking.Ctx

module Grove.Marking.MultiParents where
  data Mode : Set where
    Syn : Mode
    Ana : (τ : Typ) → Mode

  record MultiParentCtx : Set where
    constructor ⟨_,_,_⟩
    field
      u : VertexId
      Γ : Ctx
      m : Mode

  MultiParents = List MultiParentCtx
