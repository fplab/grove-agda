open import marking.prelude
open import marking.id
open import marking.typ
open import marking.gtyp
open import marking.ctx
open import marking.multiparents
open import marking.uexp
open import marking.mexp

module marking.marking where
  infix 4 _⊢_↬⇒_
  infix 4 _⊢_↬⇐_
  infix 4 _⊢s_↬⇒_
  infix 4 _⊢s_↬⇐_

  -- mark insertion
  mutual
    -- synthesis
    data _⊢_↬⇒_ : {τ : Typ} {𝕞 : MultiParents} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇒ τ ∣ 𝕞) → Set where
      MKSVar : ∀ {Γ x τ u}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ↬⇒ ⊢ ∋x ^ u

      MKSFree : ∀ {Γ y u}
        → (∌y : Γ ∌ y)
        → Γ ⊢ - y ^ u ↬⇒ ⊢⟦ ∌y ⟧^ u

      MKSLam : ∀ {Γ x τ e τ₁ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇒s τ₁ ∣ 𝕞}
        → (e↬⇒ě : Γ , x ∶ (τ △) ⊢s e ↬⇒ ě)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ↬⇒ ⊢λ x ∶ τ ∙ ě ^ u

      MKSAp1 : ∀ {Γ e₁ e₂ τ τ₁ τ₂ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇒s τ ∣ 𝕞₁}
        → {ě₂ : Γ ⊢⇐s τ₁ ∣ 𝕞₂}
        → (e₁↬⇒ě₁ : Γ ⊢s e₁ ↬⇒ ě₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ↬⇒ ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u

      MKSAp2 : ∀ {Γ e₁ e₂ τ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇒s τ ∣ 𝕞₁}
        → {ě₂ : Γ ⊢⇐s unknown ∣ 𝕞₂}
        → (e₁↬⇒ě₁ : Γ ⊢s e₁ ↬⇒ ě₁)
        → (τ!▸ : τ !▸-→)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ↬⇒ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u

      MKSNum : ∀ {Γ n u}
        → Γ ⊢ -ℕ n ^ u ↬⇒ ⊢ℕ n ^ u

      MKSPlus : ∀ {Γ e₁ e₂ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇐s num ∣ 𝕞₁}  
        → {ě₂ : Γ ⊢⇐s num ∣ 𝕞₂}
        → (e₁↬⇐ě₁ : Γ ⊢s e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂)
        → Γ ⊢ - e₁ + e₂ ^ u ↬⇒ ⊢ ě₁ + ě₂ ^ u

      MKSMultiParent : ∀ {Γ u}
        → Γ ⊢ -⋎^ u ↬⇒ ⊢⋎^ u

      MKSUnicycle : ∀ {Γ u}
        → Γ ⊢ -↻^ u ↬⇒ ⊢↻^ u

    MKSubSConflictChildren : ∀ {Γ} {ė* : List USubExp'}
      → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] ∃[ 𝕞 ] Σ[ ě ∈ Γ ⊢⇒ τ ∣ 𝕞 ] Γ ⊢ e ↬⇒ ě) ė*)
      → List (EdgeId × ∃[ τ ] ∃[ 𝕞 ] Γ ⊢⇒ τ ∣ 𝕞)
    MKSubSConflictChildren [] = []
    MKSubSConflictChildren (_∷_ {⟨ w , _ ⟩} ⟨ τ , ⟨ 𝕞 , ⟨ ě , _ ⟩ ⟩ ⟩ ė↬⇒ě*) = ⟨ w , ⟨ τ , ⟨ 𝕞 , ě ⟩ ⟩ ⟩ ∷ (MKSubSConflictChildren ė↬⇒ě*)

    data _⊢s_↬⇒_ : {τ : Typ} {𝕞 : MultiParents} (Γ : Ctx) → (e : USubExp) → (Γ ⊢⇒s τ ∣ 𝕞) → Set where
      MKSubSHole : ∀ {Γ w p}
        → Γ ⊢s -□^ w ^ p ↬⇒ ⊢□^ w ^ p

      MKSubSJust : ∀ {Γ w e τ 𝕞}
        → {ě : Γ ⊢⇒ τ ∣ 𝕞} 
        → (e↬⇒ě : Γ  ⊢ e ↬⇒ ě)
        → Γ ⊢s -∶ ⟨ w , e ⟩ ↬⇒ ⊢∶ ⟨ w , ě ⟩

      MKSubSConflict : ∀ {Γ ė*}
        → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] ∃[ 𝕞 ] Σ[ ě ∈ Γ ⊢⇒ τ ∣ 𝕞 ] Γ ⊢ e ↬⇒ ě) ė*)
        → Γ ⊢s -⋏ ė* ↬⇒ ⊢⋏ (MKSubSConflictChildren ė↬⇒ě*)

    USu→MSu : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {𝕞 : MultiParents} {ě : Γ ⊢⇒ τ ∣ 𝕞} → USubsumable e → Γ ⊢ e ↬⇒ ě → MSubsumable ě
    USu→MSu {ě = ⊢_^_ {x = x} ∋x u}      USuVar          _ = MSuVar
    USu→MSu {ě = ⊢⟦ x ⟧^ u}              USuVar          _ = MSuFree
    USu→MSu {ě = ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u}    USuAp           _ = MSuAp1
    USu→MSu {ě = ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u} USuAp           _ = MSuAp2
    USu→MSu {ě = ⊢ℕ n ^ u}               USuNum          _ = MSuNum
    USu→MSu {ě = ⊢ ě₁ + ě₂ ^ u}          USuPlus         _ = MSuPlus
    USu→MSu {ě = ⊢⋎^ u}                  USuMultiParent  _ = MSuMultiParent
    USu→MSu {ě = ⊢↻^ u}                  USuUnicycle     _ = MSuUnicycle

    -- analysis
    data _⊢_↬⇐_ : {τ : Typ} {𝕞 : MultiParents} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇐ τ ∣ 𝕞) → Set where
      MKALam1 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂ ∣ 𝕞}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △) ~ τ₁)
        → (e↬⇐ě : Γ , x ∶ (τ △) ⊢s e ↬⇐ ě)
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)

      MKALam2 : ∀ {Γ x τ e τ' u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s unknown ∣ 𝕞}
        → (τ'!▸ : τ' !▸-→)
        → (e↬⇐ě : Γ , x ∶ (τ △) ⊢s e ↬⇐ ě)
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u)

      MKALam3 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂ ∣ 𝕞}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ △) ~̸ τ₁)
        → (e↬⇐ě : Γ , x ∶ (τ △) ⊢s e ↬⇐ ě)
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u)

      MKASubsume : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒ τ' ∣ 𝕞}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~τ' : τ ~ τ')
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢∙ ě [ τ~τ' ∙ USu→MSu s e↬⇒ě ]

      MKAInconsistentTypes : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒ τ' ∣ 𝕞}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~̸τ' : τ ~̸ τ')
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ∙ USu→MSu s e↬⇒ě ]

    data _⊢s_↬⇐_ : {τ : Typ} {𝕞 : MultiParents} (Γ : Ctx) → (e : USubExp) → (Γ ⊢⇐s τ ∣ 𝕞) → Set where
      MKSubASubsume : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒s τ' ∣ 𝕞}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě )
        → (τ~τ' : τ ~ τ')
        → Γ ⊢s e ↬⇐ ⊢∙ ě [ τ~τ' ]

      MKSubAInconsistentTypes : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒s τ' ∣ 𝕞}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě)
        → (τ~̸τ' : τ ~̸ τ')
        → Γ ⊢s e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ]
