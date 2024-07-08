open import marking.prelude

open import marking.id
open import marking.var
open import marking.typ
open import marking.gtyp
open import marking.ctx

-- instrinsically typed marked expressions
module marking.mexp where
  infix  4 _⊢⇒_
  infix  4 _⊢⇐_
  infix  4 _⊢⇒s_
  infix  4 _⊢⇐s_

  mutual
    -- synthesis
    data _⊢⇒_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSVar
      ⊢_^_ : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → (u : VertexId)
        → Γ ⊢⇒ τ

      -- MSLam
      ⊢λ_∶_∙_^_ : ∀ {Γ τ'}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇒s τ')
        → (u : VertexId)
        → Γ ⊢⇒ (τ △) -→ τ'

      -- MSAp1
      ⊢_∙_[_]^_ : ∀ {Γ τ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒s τ)
        → (ě₂ : Γ ⊢⇐s τ₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (u : VertexId)
        → Γ ⊢⇒ τ₂

      -- MSAp2
      ⊢⸨_⸩∙_[_]^_ : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇒s τ)
        → (ě₂ : Γ ⊢⇐s unknown)
        → (τ!▸ : τ !▸-→)
        → (u : VertexId)
        → Γ ⊢⇒ unknown

      -- MSNum
      ⊢ℕ_^_ : ∀ {Γ}
        → (n : ℕ)
        → (u : VertexId)
        → Γ ⊢⇒ num

      -- MSPlus
      ⊢_+_^_ : ∀ {Γ}
        → (ě₁ : Γ ⊢⇐s num)
        → (ě₂ : Γ ⊢⇐s num)
        → (u : VertexId)
        → Γ ⊢⇒ num

      -- MSFree
      ⊢⟦_⟧^_ : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → (u : VertexId)
        → Γ ⊢⇒ unknown

      ⊢⋎^_ : ∀ {Γ}
        → (u : VertexId)
        → Γ ⊢⇒ unknown

      ⊢↻^_ : ∀ {Γ}
        → (u : VertexId)
        → Γ ⊢⇒ unknown

    data _⊢⇒s_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSubSHole: \vdash\sq^_^_
      ⊢□^_^_ : ∀ {Γ}
        → (w : EdgeId)
        → (p : Position)
        → Γ ⊢⇒s unknown

      -- MSubSJust
      ⊢∶ : ∀ {Γ τ}
        → (ė : EdgeId × Γ ⊢⇒ τ)
        → Γ ⊢⇒s τ

      -- MSubSConflict: \vdash\curlywedge_
      -- TODO synthesize meet?
      ⊢⋏_ : ∀ {Γ}
        → (ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ))
        → Γ ⊢⇒s unknown

    data MSubsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      MSuVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → MSubsumable {Γ} (⊢ ∋x ^ u)

      MSuAp1 : ∀ {Γ u τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MSubsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MSuAp2 : ∀ {Γ u τ}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s unknown}
        → {τ!▸ : τ !▸-→}
        → MSubsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u)

      MSuNum : ∀ {Γ u}
        → {n : ℕ}
        → MSubsumable {Γ} (⊢ℕ n ^ u)

      MSuPlus : ∀ {Γ u}
        → {ě₁ : Γ ⊢⇐s num}
        → {ě₂ : Γ ⊢⇐s num}
        → MSubsumable {Γ} (⊢ ě₁ + ě₂ ^ u)

      MSuFree : ∀ {Γ y u}
        → {∌y : Γ ∌ y}
        → MSubsumable {Γ} (⊢⟦ ∌y ⟧^ u)

      MSuMultiParent : ∀ {Γ u}
        → MSubsumable {Γ} (⊢⋎^ u)

      MSuUnicycle : ∀ {Γ u}
        → MSubsumable {Γ} (⊢↻^ u)

    -- analysis
    data _⊢⇐_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MALam1
      ⊢λ_∶_∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇐s τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △) ~ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃

      -- MALam2
      ⊢⸨λ_∶_∙_⸩[_]^_ : ∀ {Γ τ'}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇐s unknown)
        → (τ'!▸ : τ' !▸-→)
        → (u : VertexId)
        → Γ ⊢⇐ τ'

      -- MALam3
      ⊢λ_∶⸨_⸩∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇐s τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ △) ~̸ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒ τ')
        → (τ~̸τ' : τ ~̸ τ')
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ

      -- MASubsume
      ⊢∙_[_∙_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒ τ')
        → (τ~τ' : τ ~ τ')
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ

    data _⊢⇐s_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSubASubsume
      ⊢∙_[_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒s τ')
        → (τ~τ' : τ ~ τ')
        → Γ ⊢⇐s τ

      -- MSubAInconsistentTypes
      ⊢⸨_⸩[_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒s τ')
        → (τ~̸τ' : τ ~̸ τ')
        → Γ ⊢⇐s τ

  mutual
    data Markless⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → Set where
      MLSVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → Markless⇒ {Γ} (⊢ ∋x ^ u)

      MLSLam : ∀ {Γ τ' x τ u}
        → {ě : Γ , x ∶ (τ △) ⊢⇒s τ'}
        → (less : Markless⇒s ě)
        → Markless⇒ {Γ} (⊢λ x ∶ τ ∙ ě ^ u)

      MLSAp : ∀ {Γ τ τ₁ τ₂ u}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (less₁ : Markless⇒s ě₁)
        → (less₂ : Markless⇐s ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MLSNum : ∀ {Γ n u}
        → Markless⇒ {Γ} (⊢ℕ n ^ u)

      MLSPlus : ∀ {Γ u}
        → {ě₁ : Γ ⊢⇐s num}
        → {ě₂ : Γ ⊢⇐s num}
        → (less₁ : Markless⇐s ě₁)
        → (less₂ : Markless⇐s ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ + ě₂ ^ u)

    data Markless⇒s : ∀ {Γ τ} → (ě : Γ ⊢⇒s τ) → Set where
      MLSubSHole : ∀ {Γ w p}
        → Markless⇒s {Γ} (⊢□^ w ^ p)

      MLSubSJust : ∀ {Γ w τ}
        → {ě : Γ ⊢⇒ τ}
        → (less : Markless⇒ ě)
        → Markless⇒s {Γ} (⊢∶ ⟨ w , ě ⟩)

      -- TODO maybe this is a mark?
      MLSubSConflict : ∀ {Γ}
        → {ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)}
        → (less* : All (λ { ⟨ _ , ⟨ _ , ě ⟩ ⟩ → Markless⇒ ě }) ė*)
        → Markless⇒s {Γ} (⊢⋏ ė*)

    data Markless⇐ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → Set where
      MLALam : ∀ {Γ τ₁ τ₂ τ₃ x τ u}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : (τ △) ~ τ₁}
        → (less : Markless⇐s ě)
        → Markless⇐ {Γ} (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)

      MLASubsume : ∀ {Γ τ τ'}
        → {ě : Γ ⊢⇒ τ'}
        → {τ~τ' : τ ~ τ'}
        → {su : MSubsumable ě}
        → (less : Markless⇒ ě)
        → Markless⇐ {Γ} (⊢∙ ě [ τ~τ' ∙ su ])

    data Markless⇐s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → Set where
      MLSubASubsume : ∀ {Γ τ τ'}
        → {ě : Γ ⊢⇒s τ'}
        → {τ~τ' : τ ~ τ'}
        → (less : Markless⇒s ě)
        → Markless⇐s {Γ} (⊢∙ ě [ τ~τ' ])
