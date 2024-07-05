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
    data UTyp : Set where
      num^_  : (u : VertexId) → UTyp
      _-→_^_ : (σ₁ : USubTyp) → (σ₂ : USubTyp) → (u : VertexId) → UTyp

    data USubTyp : Set where
      □^_^_ : (u  : VertexId) → (p : Position) → USubTyp
      ∶_    : (σ  : USubTyp') → USubTyp
      *_    : (σ* : List USubTyp') → USubTyp

    USubTyp' = EdgeId × UTyp

    _▲ : UTyp → Typ
    (num^ u)       ▲ = num
    (σ₁ -→ σ₂ ^ u) ▲ = (σ₁ ▲s) -→ (σ₂ ▲s)

    _▲s : USubTyp → Typ
    (□^ u ^ p)    ▲s = unknown
    (∶ ⟨ w , σ ⟩) ▲s = σ ▲
    (* σ*)        ▲s = unknown

  mutual
    -- TODO multiparent + unicycle conflicts
    data UExp : Set where
      -_^_      : (x : Var) → (u : VertexId) → UExp
      -λ_∶_∙_^_ : (x : Var) → (σ : UTyp) → (e : USubExp) → (u : VertexId) → UExp
      -_∙_^_    : (e₁ : USubExp) → (e₂ : USubExp) → (u : VertexId) → UExp
      -ℕ_^_     : (n : ℕ) → (u : VertexId) → UExp
      -_+_^_    : (e₁ : USubExp) → (e₂ : USubExp) → (u : VertexId) → UExp

    data USubExp : Set where
      -□^_^_ : (w  : EdgeId) → (p : Position) → USubExp
      -∶_    : (ė  : USubExp') → USubExp
      -*_    : (ė* : List USubExp') → USubExp

    USubExp' = EdgeId × UExp

  data USubsumable : UExp → Set where
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
      USVar : ∀ {Γ x u τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ⇒ τ

      USLam : ∀ {Γ x σ e u τ′}
        → (e⇒τ′ : Γ , x ∶ (σ ▲) ⊢s e ⇒ τ′)
        → Γ ⊢ -λ x ∶ σ ∙ e ^ u ⇒ (σ ▲) -→ τ′

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
      USubSHole : ∀ {Γ w p}
        → Γ ⊢s -□^ w ^ p ⇒ unknown

      USubSJust : ∀ {Γ w e τ}
        → (e⇒τ : Γ ⊢ e ⇒ τ)
        → Γ ⊢s -∶ ⟨ w , e ⟩ ⇒ τ

      -- TODO synthesize meet
      USubSConflict : ∀ {Γ ė*}
        -- → (ė⇒* : Γ ⊢s* ė*)
        → (ė⇒* : All (λ (⟨ w , e ⟩) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
        → Γ ⊢s -* ė* ⇒ unknown

    -- analysis
    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x σ e u τ₁ τ₂ τ₃}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (σ ▲) ~ τ₁)
        → (e⇐τ₂ : Γ , x ∶ (σ ▲) ⊢s e ⇐ τ₂)
        → Γ ⊢ -λ x ∶ σ ∙ e ^ u ⇐ τ₃

      UASubsume : ∀ {Γ e τ τ′}
        → (e⇒τ′ : Γ ⊢ e ⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : USubsumable e)
        → Γ ⊢ e ⇐ τ

    data _⊢s_⇐_ : (Γ : Ctx) (e : USubExp) (τ : Typ) → Set where
      USubASubsume : ∀ {Γ e τ τ′} 
        → (e⇒τ′ : Γ ⊢s e ⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → Γ ⊢s e ⇐ τ
