open import Data.List using (List)
open import Data.Product using (_×_; _,_)

open import Grove.Marking.Ident
open import Grove.Marking.Typ

-- graph types
module Grove.Marking.GTyp where
  mutual
    data GTyp : Set where
      num^_  : (u : VertexId) → GTyp
      _-→_^_ : (τ₁ : GSubTyp) → (τ₂ : GSubTyp) → (u : VertexId) → GTyp
      ⋎^_    : (u : VertexId) → GTyp
      ↻^_    : (u : VertexId) → GTyp

    data GSubTyp : Set where
      -- TODO fix u, p into s
      □^_^_ : (u  : VertexId) → (p : VertexId) → GSubTyp
      ∶_    : (τ  : GSubTyp') → GSubTyp
      ⋏_    : (τ* : List GSubTyp') → GSubTyp

    GSubTyp' = EdgeId × GTyp

    _△ : GTyp → Typ
    (num^ u)       △ = num
    (τ₁ -→ τ₂ ^ u) △ = (τ₁ △s) -→ (τ₂ △s)
    (⋎^ u)         △ = unknown
    (↻^ u)         △ = unknown

    _△s : GSubTyp → Typ
    (□^ u ^ p)  △s = unknown
    (∶ (w , τ)) △s = τ △
    (⋏ τ*)      △s = unknown
