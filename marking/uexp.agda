open import marking.prelude

open import marking.typ
open import marking.id
open import marking.var
open import marking.ctx

-- unmarked expressions
module marking.uexp where
  infix  4 _⊢_⇒_
  infix  4 _⊢_⇐_
  infix  4 _⊢s_⇒_
  infix  4 _⊢s_⇐_

  mutual
    data UExp : Set where
      -⦇-⦈^_    : (u : VertexId) → UExp
      -_^_      : (x : Var) → (u : VertexId) → UExp
      -λ_∶_∙_^_ : (x : Var) → (τ : Typ) → (e : USubExp) → (u : VertexId) → UExp
      -_∙_^_    : (e₁ : USubExp) → (e₂ : USubExp) → (u : VertexId) → UExp
      -ℕ_^_     : (n : ℕ) → (u : VertexId) → UExp
      -_+_^_    : (e₁ : USubExp) → (e₂ : USubExp) → (u : VertexId) → UExp

    data USubExp : Set where
      -□_ : (w  : EdgeId) → USubExp
      -_  : (ė  : USubExp') → USubExp
      -*_ : (ė* : List USubExp') → USubExp

    USubExp' = EdgeId × UExp

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
        → Γ ⊢ -⦇-⦈^ u ⇒ unknown

      USVar : ∀ {Γ x u τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ⇒ τ

      USLam : ∀ {Γ x τ e u τ′}
        → (e⇒τ′ : Γ , x ∶ τ ⊢s e ⇒ τ′)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ⇒ τ -→ τ′

      USAp : ∀ {Γ e₁ e₂ u τ τ₁ τ₂}
        → (e₁⇒τ : Γ ⊢s e₁ ⇒ τ)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₁⇐τ₁ : Γ ⊢s e₂ ⇐ τ₁)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ⇒ τ₂

      USNum : ∀ {Γ n u}
        → Γ ⊢ -ℕ n ^ u ⇒ num

      USPlus : ∀ {Γ e₁ e₂ u}
        → (e₁⇐num : Γ ⊢s e₁ ⇐ num)
        → (e₂⇐num : Γ ⊢s e₂ ⇐ num)
        → Γ ⊢ - e₁ + e₂ ^ u ⇒ num

    data _⊢s_⇒_ : (Γ : Ctx) (e : USubExp) (τ : Typ) → Set where
      USubSHole : ∀ {Γ w}
        → Γ ⊢s -□ w ⇒ unknown

      USubSJust : ∀ {Γ w e τ}
        → (e⇒τ : Γ ⊢ e ⇒ τ)
        → Γ ⊢s - ⟨ w , e ⟩ ⇒ τ

      -- TODO synthesize meet
      USubSConflict : ∀ {Γ ė*}
        -- → (ė⇒* : Γ ⊢s* ė*)
        → (ė⇒* : All (λ (⟨ w , e ⟩) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
        → Γ ⊢s -* ė* ⇒ unknown

    -- analysis
    data _⊢s_⇐_ : (Γ : Ctx) (e : USubExp) (τ : Typ) → Set where
      USubASubsume : ∀ {Γ e τ τ′} 
        → (e⇒τ′ : Γ ⊢s e ⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → Γ ⊢s e ⇐ τ

    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x τ e u τ₁ τ₂ τ₃}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → (e⇐τ₂ : Γ , x ∶ τ ⊢s e ⇐ τ₂)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ⇐ τ₃

      UASubsume : ∀ {Γ e τ τ′}
        → (e⇒τ′ : Γ ⊢ e ⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : USubsumable e)
        → Γ ⊢ e ⇐ τ
