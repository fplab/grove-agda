open import marking.prelude
open import marking.definitions

module marking.theorems.marking where
  infix 4 _⊢_↬⇒_
  infix 4 _⊢_↬⇐_

  -- mark insertion
  mutual
    -- synthesis
    data _⊢_↬⇒_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇒ τ) → Set where
      MKSHole : ∀ {Γ u}
        → Γ ⊢ ‵⦇-⦈^ u ↬⇒ ⊢⦇-⦈^ u

      MKSVar : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ ‵ x ↬⇒ ⊢ ∋x

      MKSFree : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → Γ ⊢ ‵ y ↬⇒ ⊢⟦ ∌y ⟧

      MKSLam : ∀ {Γ x τ e τ₁}
        → {ě : Γ , x ∶ τ ⊢⇒ τ₁}
        → (e↬⇒ě : Γ , x ∶ τ ⊢ e ↬⇒ ě)
        → Γ ⊢ ‵λ x ∶ τ ∙ e ↬⇒ ⊢λ x ∶ τ ∙ ě

      MKSAp1 : ∀ {Γ e₁ e₂ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → (e₁↬⇒ě₁ : Γ ⊢ e₁ ↬⇒ ě₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → Γ ⊢ ‵ e₁ ∙ e₂ ↬⇒ ⊢ ě₁ ∙ ě₂ [ τ▸ ]

      MKSAp2 : ∀ {Γ e₁ e₂ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → (e₁↬⇒ě₁ : Γ ⊢ e₁ ↬⇒ ě₁)
        → (τ!▸ : τ !▸-→)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → Γ ⊢ ‵ e₁ ∙ e₂ ↬⇒ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]

      MKSNum : ∀ {Γ n}
        → Γ ⊢ ‵ℕ n ↬⇒ ⊢ℕ n

      MKSPlus : ∀ {Γ e₁ e₂}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (e₁↬⇐ě₁ : Γ ⊢ e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → Γ ⊢ ‵ e₁ + e₂ ↬⇒ ⊢ ě₁ + ě₂

    USu→MSu : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {ě : Γ ⊢⇒ τ} → USubsumable e → Γ ⊢ e ↬⇒ ě → MSubsumable ě
    USu→MSu {ě = ⊢⦇-⦈^ u}             USuHole  _ = MSuHole
    USu→MSu {ě = ⊢_ {x = x} ∋x}       USuVar   _ = MSuVar
    USu→MSu {ě = ⊢⟦ x ⟧}              USuVar   _ = MSuFree
    USu→MSu {ě = ⊢ ě₁ ∙ ě₂ [ τ▸ ]}    USuAp    _ = MSuAp1
    USu→MSu {ě = ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]} USuAp    _ = MSuAp2
    USu→MSu {ě = ⊢ℕ n}                USuNum   _ = MSuNum
    USu→MSu {ě = ⊢ ě₁ + ě₂}           USuPlus  _ = MSuPlus

    -- analysis
    data _⊢_↬⇐_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇐ τ) → Set where
      MKALam1 : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → Γ , x ∶ τ ⊢ e ↬⇐ ě
        → Γ ⊢ (‵λ x ∶ τ ∙ e) ↬⇐ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ])

      MKALam2 : ∀ {Γ x τ e τ′}
        → {ě : Γ , x ∶ τ ⊢⇐ unknown}
        → (τ′!▸ : τ′ !▸-→)
        → Γ , x ∶ τ ⊢ e ↬⇐ ě
        → Γ ⊢ (‵λ x ∶ τ ∙ e) ↬⇐ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ])

      MKALam3 : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : τ ~̸ τ₁)
        → Γ , x ∶ τ ⊢ e ↬⇐ ě
        → Γ ⊢ (‵λ x ∶ τ ∙ e) ↬⇐ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ])

      MKAInconsistentTypes : ∀ {Γ e τ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~̸τ′ : τ ~̸ τ′)
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ′ ∙ USu→MSu s e↬⇒ě ]

      MKASubsume : ∀ {Γ e τ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~τ′ : τ ~ τ′)
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢∙ ě [ τ~τ′ ∙ USu→MSu s e↬⇒ě ]
