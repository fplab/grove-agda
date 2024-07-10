open import Data.List using (List)

open import Grove.Ident
open import Grove.Marking.Typ
open import Grove.Marking.Ctx

open import Grove.Marking.Grove using (Vertex; Source)

module Grove.Marking.MultiParents where
  data Mode : Set where
    Syn : Mode
    Ana : (τ : Typ) → Mode

  record MultiParentCtx : Set where
    constructor ⟨_,_,_,_⟩
    field
      v : Vertex
      w : EdgeId
      Γ : Ctx
      m : Mode

  MultiParents = List MultiParentCtx
