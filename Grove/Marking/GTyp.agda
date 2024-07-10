open import Data.List using (List)
open import Data.Product using (_×_; _,_)

open import Grove.Ident
open import Grove.Marking.Typ

open import Grove.Marking.Grove using (Vertex; Source)

-- graph types
module Grove.Marking.GTyp where
  mutual
    data GTyp : Set where
      num^_  : (u : VertexId) → GTyp
      _-→_^_ : (τ₁ : GSubTyp) → (τ₂ : GSubTyp) → (u : VertexId) → GTyp
      ⋎^_^_  : (w : EdgeId) → (v : Vertex) → GTyp
      ↻^_^_  : (w : EdgeId) → (v : Vertex) → GTyp

    data GSubTyp : Set where
      □ : (s : Source) → GSubTyp
      ∶ : (τ : GSubTyp') → GSubTyp
      ⋏ : (s : Source) → (τ* : List GSubTyp') → GSubTyp

    GSubTyp' = EdgeId × GTyp

    _△ : GTyp → Typ
    (num^ u)       △ = num
    (τ₁ -→ τ₂ ^ u) △ = (τ₁ △s) -→ (τ₂ △s)
    (⋎^ w ^ v)     △ = unknown
    (↻^ w ^ v)     △ = unknown

    _△s : GSubTyp → Typ
    (□ s)       △s = unknown
    (∶ (w , τ)) △s = τ △
    (⋏ s τ*)    △s = unknown
