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
      -- MSHole
      ⊢⦇-⦈^_ : ∀ {Γ}
        → (u : VertexId)
        → Γ ⊢⇒ unknown

      -- MSVar
      ⊢_ : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢⇒ τ

      -- MSLam
      ⊢λ_∶_∙_ : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇒ τ′)
        → Γ ⊢⇒ τ -→ τ′

      -- MSAp1
      ⊢_∙_[_] : ∀ {Γ τ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ τ₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → Γ ⊢⇒ τ₂

      -- MSAp2
      ⊢⸨_⸩∙_[_] : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ unknown)
        → (τ!▸ : τ !▸-→)
        → Γ ⊢⇒ unknown

      -- MSNum
      ⊢ℕ_ : ∀ {Γ}
        → (n : ℕ)
        → Γ ⊢⇒ num

      -- MSPlus
      ⊢_+_ : ∀ {Γ}
        → (ě₁ : Γ ⊢⇐ num)
        → (ě₂ : Γ ⊢⇐ num)
        → Γ ⊢⇒ num

      -- MSFree
      ⊢⟦_⟧ : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → Γ ⊢⇒ unknown

    data MSubsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      MSuHole : ∀ {Γ}
        → {u : VertexId} 
        → MSubsumable {Γ} (⊢⦇-⦈^ u)

      MSuVar : ∀ {Γ x τ}
        → {∋x : Γ ∋ x ∶ τ}
        → MSubsumable {Γ} (⊢ ∋x)

      MSuAp1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MSubsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ])

      MSuAp2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸-→}
        → MSubsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ])

      MSuNum : ∀ {Γ}
        → {n : ℕ}
        → MSubsumable {Γ} (⊢ℕ n)

      MSuPlus : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → MSubsumable {Γ} (⊢ ě₁ + ě₂)

      MSuFree : ∀ {Γ y}
        → {∌y : Γ ∌ y}
        → MSubsumable {Γ} (⊢⟦ ∌y ⟧)

    -- analysis
    data _⊢⇐_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MALam1
      ⊢λ_∶_∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → Γ ⊢⇐ τ₃

      -- MALam2
      ⊢⸨λ_∶_∙_⸩[_] : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ unknown)
        → (τ′!▸ : τ′ !▸-→)
        → Γ ⊢⇐ τ′

      -- MALam3
      ⊢λ_∶⸨_⸩∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : τ ~̸ τ₁)
        → Γ ⊢⇐ τ₃

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → (τ~̸τ′ : τ ~̸ τ′)
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ

      -- MAMSubsume
      ⊢∙_[_∙_] : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ

  mutual
    data Markless⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → Set where
      MLSHole : ∀ {Γ u}
        → Markless⇒ {Γ} (⊢⦇-⦈^ u)

      MLSVar : ∀ {Γ x τ}
        → {∋x : Γ ∋ x ∶ τ}
        → Markless⇒ {Γ} (⊢ ∋x)

      MLSLam : ∀ {Γ τ′ x τ}
        → {ě : Γ , x ∶ τ ⊢⇒ τ′}
        → (less : Markless⇒ ě)
        → Markless⇒ {Γ} (⊢λ x ∶ τ ∙ ě)

      MLSAp : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (less₁ : Markless⇒ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ])

      MLSNum : ∀ {Γ n}
        → Markless⇒ {Γ} (⊢ℕ n)

      MLSPlus : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (less₁ : Markless⇐ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ + ě₂)

    data Markless⇐ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → Set where
      MLALam : ∀ {Γ τ₁ τ₂ τ₃ x τ}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → (less : Markless⇐ ě)
        → Markless⇐ {Γ} (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ])

      MLASubsume : ∀ {Γ τ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → {τ~τ′ : τ ~ τ′}
        → {su : MSubsumable ě}
        → (less : Markless⇒ ě)
        → Markless⇐ {Γ} (⊢∙ ě [ τ~τ′ ∙ su ])
