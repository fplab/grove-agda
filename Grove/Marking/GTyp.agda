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
      _-→_^_ : (τ₁ : GChildTyp) → (τ₂ : GChildTyp) → (u : VertexId) → GTyp
      ⋎^_^_  : (w : EdgeId) → (v : Vertex) → GTyp
      ↻^_^_  : (w : EdgeId) → (v : Vertex) → GTyp

    data GChildTyp : Set where
      □ : (s : Source) → GChildTyp
      ∶ : (τ : GChildTyp') → GChildTyp
      ⋏ : (s : Source) → (τ* : List GChildTyp') → GChildTyp

    GChildTyp' = EdgeId × GTyp

    _△ : GTyp → Typ
    (num^ u)       △ = num
    (τ₁ -→ τ₂ ^ u) △ = (τ₁ △s) -→ (τ₂ △s)
    (⋎^ w ^ v)     △ = unknown
    (↻^ w ^ v)     △ = unknown

    _△s : GChildTyp → Typ
    (□ s)       △s = unknown
    (∶ (w , τ)) △s = τ △
    (⋏ s τ*)    △s = unknown
