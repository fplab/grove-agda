open import marking.prelude

open import marking.typ
open import marking.id
open import marking.var
open import marking.ctx

-- unmarked expressions
module marking.uexp where
  infix  4 _⊢_⇒_
  infix  4 _⊢_⇐_

  data UExp : Set where
    -⦇-⦈^_    : (u : VertexId) → UExp
    -_^_      : (x : Var) → (u : VertexId) → UExp
    -λ_∶_∙_^_ : (x : Var) → (τ : Typ) → (e : UExp) → (u : VertexId) → UExp
    -_∙_^_    : (e₁ : UExp) → (e₂ : UExp) → (u : VertexId) → UExp
    -ℕ_^_     : (n : ℕ) → (u : VertexId) → UExp
    -_+_^_    : (e₁ : UExp) → (e₂ : UExp) → (u : VertexId) → UExp

  data USubsumable : UExp → Set where
    USuHole : ∀ {u}
      → USubsumable (-⦇-⦈^ u)

    USuVar : ∀ {x u}
      → USubsumable (- x ^ u)

    USuAp : ∀ {e₁ e₂ u}
      → USubsumable (- e₁ ∙ e₂ ^ u)

    USuNum : ∀ {n u}
      → USubsumable (-ℕ n ^ u)

    USuPlus : ∀ {e₁ e₂ u}
      → USubsumable (- e₁ + e₂ ^ u)

  mutual
    -- synthesis
    data _⊢_⇒_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      USHole : ∀ {Γ u}
        → Γ ⊢ -⦇-⦈^ u  ⇒ unknown

      USVar : ∀ {Γ x u τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ⇒ τ

      USLam : ∀ {Γ x τ e u τ′}
        → (e⇒τ′ :  Γ , x ∶ τ ⊢ e ⇒ τ′)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ⇒ τ -→ τ′

      USAp : ∀ {Γ e₁ e₂ u τ τ₁ τ₂}
        → (e₁⇒τ : Γ ⊢ e₁ ⇒ τ)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₁⇐τ₁ : Γ ⊢ e₂ ⇐ τ₁)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ⇒ τ₂

      USNum : ∀ {Γ n u}
        → Γ ⊢ -ℕ n ^ u ⇒ num

      USPlus : ∀ {Γ e₁ e₂ u}
        → (e₁⇐num : Γ ⊢ e₁ ⇐ num)
        → (e₂⇐num : Γ ⊢ e₂ ⇐ num)
        → Γ ⊢ - e₁ + e₂ ^ u ⇒ num

    -- analysis
    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x τ e u τ₁ τ₂ τ₃}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → (e⇐τ₂ : Γ , x ∶ τ ⊢ e ⇐ τ₂)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ⇐ τ₃

      UASubsume : ∀ {Γ e τ τ′}
        → (e⇒τ′ : Γ ⊢ e ⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : USubsumable e)
        → Γ ⊢ e ⇐ τ
