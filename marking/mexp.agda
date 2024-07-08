open import marking.prelude

open import marking.typ
open import marking.id
open import marking.var
open import marking.ctx

-- instrinsically typed marked expressions
module marking.mexp where
  infix  4 _⊢⇒_
  infix  4 _⊢⇐_

  mutual
    -- synthesis
    data _⊢⇒_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSVar
      ⊢_^_ : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → (u : VertexId)
        → Γ ⊢⇒ τ

      -- MSLam
      ⊢λ_∶_∙_^_ : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇒ τ′)
        → (u : VertexId)
        → Γ ⊢⇒ τ -→ τ′

      -- MSAp1
      ⊢_∙_[_]^_ : ∀ {Γ τ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ τ₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (u : VertexId)
        → Γ ⊢⇒ τ₂

      -- MSAp2
      ⊢⸨_⸩∙_[_]^_ : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ unknown)
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
        → (ě₁ : Γ ⊢⇐ num)
        → (ě₂ : Γ ⊢⇐ num)
        → (u : VertexId)
        → Γ ⊢⇒ num

      -- MSFree
      ⊢⟦_⟧^_ : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → (u : VertexId)
        → Γ ⊢⇒ unknown

    data MSubsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      MSuVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → MSubsumable {Γ} (⊢ ∋x ^ u)

      MSuAp1 : ∀ {Γ u τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MSubsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MSuAp2 : ∀ {Γ u τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸-→}
        → MSubsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u)

      MSuNum : ∀ {Γ u}
        → {n : ℕ}
        → MSubsumable {Γ} (⊢ℕ n ^ u)

      MSuPlus : ∀ {Γ u}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → MSubsumable {Γ} (⊢ ě₁ + ě₂ ^ u)

      MSuFree : ∀ {Γ y u}
        → {∌y : Γ ∌ y}
        → MSubsumable {Γ} (⊢⟦ ∌y ⟧^ u)

    -- analysis
    data _⊢⇐_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MALam1
      ⊢λ_∶_∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃

      -- MALam2
      ⊢⸨λ_∶_∙_⸩[_]^_ : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ unknown)
        → (τ′!▸ : τ′ !▸-→)
        → (u : VertexId)
        → Γ ⊢⇐ τ′

      -- MALam3
      ⊢λ_∶⸨_⸩∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : τ ~̸ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_]^_ : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → (τ~̸τ′ : τ ~̸ τ′)
        → (su : MSubsumable ě)
        → (u : VertexId)
        → Γ ⊢⇐ τ

      -- MAMSubsume
      ⊢∙_[_∙_]^_ : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : MSubsumable ě)
        → (u : VertexId)
        → Γ ⊢⇐ τ

  mutual
    data Markless⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → Set where
      MLSVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → Markless⇒ {Γ} (⊢ ∋x ^ u)

      MLSLam : ∀ {Γ τ′ x τ u}
        → {ě : Γ , x ∶ τ ⊢⇒ τ′}
        → (less : Markless⇒ ě)
        → Markless⇒ {Γ} (⊢λ x ∶ τ ∙ ě ^ u)

      MLSAp : ∀ {Γ τ τ₁ τ₂ u}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (less₁ : Markless⇒ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MLSNum : ∀ {Γ n u}
        → Markless⇒ {Γ} (⊢ℕ n ^ u)

      MLSPlus : ∀ {Γ u}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (less₁ : Markless⇐ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ + ě₂ ^ u)

    data Markless⇐ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → Set where
      MLALam : ∀ {Γ τ₁ τ₂ τ₃ x τ u}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → (less : Markless⇐ ě)
        → Markless⇐ {Γ} (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)

      MLASubsume : ∀ {Γ τ τ′ u}
        → {ě : Γ ⊢⇒ τ′}
        → {τ~τ′ : τ ~ τ′}
        → {su : MSubsumable ě}
        → (less : Markless⇒ ě)
        → Markless⇐ {Γ} (⊢∙ ě [ τ~τ′ ∙ su ]^ u)
