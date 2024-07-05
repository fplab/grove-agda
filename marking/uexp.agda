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
    -⦇-⦈^_  : (u : VertexId) → UExp
    -_      : (x : Var) → UExp
    -λ_∶_∙_ : (x : Var) → (τ : Typ) → (e : UExp) → UExp
    -_∙_    : (e₁ : UExp) → (e₂ : UExp) → UExp
    -ℕ_     : (n : ℕ) → UExp
    -_+_    : (e₁ : UExp) → (e₂ : UExp) → UExp

  data USubsumable : UExp → Set where
    USuHole : ∀ {u}
      → USubsumable (-⦇-⦈^ u)

    USuVar : ∀ {x}
      → USubsumable (- x)

    USuAp : ∀ {e₁ e₂}
      → USubsumable (- e₁ ∙ e₂)

    USuNum : ∀ {n}
      → USubsumable (-ℕ n)

    USuPlus : ∀ {e₁ e₂}
      → USubsumable (- e₁ + e₂)

  mutual
    -- synthesis
    data _⊢_⇒_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      USHole : ∀ {Γ u}
        → Γ ⊢ -⦇-⦈^ u  ⇒ unknown

      USVar : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ⇒ τ

      USLam : ∀ {Γ x τ e τ′}
        → (e⇒τ′ :  Γ , x ∶ τ ⊢ e ⇒ τ′)
        → Γ ⊢ -λ x ∶ τ ∙ e ⇒ τ -→ τ′

      USAp : ∀ {Γ e₁ e₂ τ τ₁ τ₂}
        → (e₁⇒τ : Γ ⊢ e₁ ⇒ τ)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₁⇐τ₁ : Γ ⊢ e₂ ⇐ τ₁)
        → Γ ⊢ - e₁ ∙ e₂ ⇒ τ₂

      USNum : ∀ {Γ n}
        → Γ ⊢ -ℕ n ⇒ num

      USPlus : ∀ {Γ e₁ e₂}
        → (e₁⇐num : Γ ⊢ e₁ ⇐ num)
        → (e₂⇐num : Γ ⊢ e₂ ⇐ num)
        → Γ ⊢ - e₁ + e₂ ⇒ num

    -- analysis
    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → (e⇐τ₂ : Γ , x ∶ τ ⊢ e ⇐ τ₂)
        → Γ ⊢ -λ x ∶ τ ∙ e ⇐ τ₃

      UASubsume : ∀ {Γ e τ τ′}
        → (e⇒τ′ : Γ ⊢ e ⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : USubsumable e)
        → Γ ⊢ e ⇐ τ
