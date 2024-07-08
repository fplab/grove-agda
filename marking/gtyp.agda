open import marking.prelude
open import marking.id
open import marking.typ

-- graph types
module marking.gtyp where
  mutual
    data GTyp : Set where
      num^_  : (u : VertexId) → GTyp
      _-→_^_ : (σ₁ : GSubTyp) → (σ₂ : GSubTyp) → (u : VertexId) → GTyp
      ⋎^_    : (u : VertexId) → GTyp
      ↻^_    : (u : VertexId) → GTyp

    data GSubTyp : Set where
      □^_^_ : (u  : VertexId) → (p : Position) → GSubTyp
      ∶_    : (σ  : GSubTyp') → GSubTyp
      ⋏_    : (σ* : List GSubTyp') → GSubTyp

    GSubTyp' = EdgeId × GTyp

    _△ : GTyp → Typ
    (num^ u)       △ = num
    (σ₁ -→ σ₂ ^ u) △ = (σ₁ △s) -→ (σ₂ △s)
    (⋎^ u)         △ = unknown
    (↻^ u)         △ = unknown

    _△s : GSubTyp → Typ
    (□^ u ^ p)    △s = unknown
    (∶ ⟨ w , σ ⟩) △s = σ △
    (⋏ σ*)        △s = unknown
