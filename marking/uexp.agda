open import marking.prelude

open import marking.id
open import marking.var
open import marking.typ
open import marking.gtyp
open import marking.ctx

-- unmarked expressions
module marking.uexp where
  infix  4 _⊢_⇒_
  infix  4 _⊢_⇐_
  infix  4 _⊢s_⇒_
  infix  4 _⊢s_⇐_

  mutual
    data UExp : Set where
      -_^_      : (x : Var) → (u : VertexId) → UExp
      -λ_∶_∙_^_ : (x : Var) → (σ : GTyp) → (e : USubExp) → (u : VertexId) → UExp
      -_∙_^_    : (e₁ : USubExp) → (e₂ : USubExp) → (u : VertexId) → UExp
      -ℕ_^_     : (n : ℕ) → (u : VertexId) → UExp
      -_+_^_    : (e₁ : USubExp) → (e₂ : USubExp) → (u : VertexId) → UExp
      -⋎^_      : (u : VertexId) → UExp
      -↻^_      : (u : VertexId) → UExp

    data USubExp : Set where
      -□^_^_ : (w  : EdgeId) → (p : Position) → USubExp
      -∶_    : (ė  : USubExp') → USubExp
      -⋏_    : (ė* : List USubExp') → USubExp

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

    USuMultiParent : ∀ {u}
      → USubsumable (-⋎^ u)

    USuUnicycle : ∀ {u}
      → USubsumable (-↻^ u)

  mutual
    -- synthesis
    data _⊢_⇒_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      USVar : ∀ {Γ x u τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ⇒ τ

      USLam : ∀ {Γ x σ e u τ′}
        → (e⇒τ′ : Γ , x ∶ (σ △) ⊢s e ⇒ τ′)
        → Γ ⊢ -λ x ∶ σ ∙ e ^ u ⇒ (σ △) -→ τ′

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

      USMultiParent : ∀ {Γ u}
        → Γ ⊢ -⋎^ u ⇒ unknown

      USUnicycle : ∀ {Γ u}
        → Γ ⊢ -↻^ u ⇒ unknown

    data _⊢s_⇒_ : (Γ : Ctx) (e : USubExp) (τ : Typ) → Set where
      USubSHole : ∀ {Γ w p}
        → Γ ⊢s -□^ w ^ p ⇒ unknown

      USubSJust : ∀ {Γ w e τ}
        → (e⇒τ : Γ ⊢ e ⇒ τ)
        → Γ ⊢s -∶ ⟨ w , e ⟩ ⇒ τ

      -- TODO synthesize meet
      USubSConflict : ∀ {Γ ė*}
        → (ė⇒* : All (λ (⟨ w , e ⟩) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
        → Γ ⊢s -⋏ ė* ⇒ unknown

    -- analysis
    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x σ e u τ₁ τ₂ τ₃}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (σ △) ~ τ₁)
        → (e⇐τ₂ : Γ , x ∶ (σ △) ⊢s e ⇐ τ₂)
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

  -- synthesis unicity
  mutual
    ⇒-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ}
              → Γ ⊢ e ⇒ τ₁
              → Γ ⊢ e ⇒ τ₂
              → τ₁ ≡ τ₂
    ⇒-unicity (USVar ∋x)             (USVar ∋x′)              = ∋→τ-≡ ∋x ∋x′
    ⇒-unicity (USLam e⇒τ₁)           (USLam e⇒τ₂)
      rewrite ⇒s-unicity e⇒τ₁ e⇒τ₂                            = refl
    ⇒-unicity (USAp e₁⇒τ₁ τ▸ e₂⇐τ₂)  (USAp e₁⇒τ₁′ τ▸′ e₂⇐τ₂′)
      rewrite ⇒s-unicity e₁⇒τ₁ e₁⇒τ₁′
      with refl ← ▸-→-unicity τ▸ τ▸′                          = refl
    ⇒-unicity USNum                  USNum                    = refl
    ⇒-unicity (USPlus e₁⇐num e₂⇐num) (USPlus e₁⇐num′ e₂⇐num′) = refl
    ⇒-unicity USMultiParent          USMultiParent            = refl
    ⇒-unicity USUnicycle             USUnicycle               = refl

    ⇒s-unicity : ∀ {Γ : Ctx} {e : USubExp} {τ₁ τ₂ : Typ}
               → Γ ⊢s e ⇒ τ₁
               → Γ ⊢s e ⇒ τ₂
               → τ₁ ≡ τ₂
    ⇒s-unicity USubSHole           USubSHole            = refl
    ⇒s-unicity (USubSJust e⇒τ)     (USubSJust e⇒τ′)
      rewrite ⇒-unicity e⇒τ e⇒τ′                        = refl
    ⇒s-unicity (USubSConflict ė⇒*) (USubSConflict ė⇒*′) = refl
