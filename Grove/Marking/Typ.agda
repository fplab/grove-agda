open import Data.List using (List)
open import Data.Product using (_×_; _,_)

open import Grove.Ident
open import Grove.Marking.STyp

open import Grove.Marking.Grove using (Vertex; Location)

-- graph types
module Grove.Marking.Typ where
  mutual
    data Typ : Set where
      num^_  : (u : VertexId) → Typ
      _-→_^_ : (τ₁ : ChildTyp) → (τ₂ : ChildTyp) → (u : VertexId) → Typ
      ⋎^_^_  : (w : EdgeId) → (v : Vertex) → Typ
      ↻^_^_  : (w : EdgeId) → (v : Vertex) → Typ

    data ChildTyp : Set where
      □ : (s : Location) → ChildTyp
      ∶ : (τ : ChildTyp') → ChildTyp
      ⋏ : (s : Location) → (τ* : List ChildTyp') → ChildTyp

    ChildTyp' = EdgeId × Typ

    _△ : Typ → STyp
    (num^ u)       △ = num
    (τ₁ -→ τ₂ ^ u) △ = (τ₁ △s) -→ (τ₂ △s)
    (⋎^ w ^ v)     △ = unknown
    (↻^ w ^ v)     △ = unknown

    _△s : ChildTyp → STyp
    (□ s)       △s = unknown
    (∶ (w , τ)) △s = τ △
    (⋏ s τ*)    △s = unknown
