open import marking.prelude

open import marking.id
open import marking.typ
open import marking.ctx

module marking.multiparents where
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
