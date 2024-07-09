open import marking.prelude
open import marking.id
open import marking.typ
open import marking.gtyp
open import marking.ctx
open import marking.multiparents
open import marking.uexp
open import marking.mexp

module marking.marking where
  infix 4 _⊢_↬⇒_∣_
  infix 4 _⊢_↬⇐_∣_
  infix 4 _⊢s_↬⇒_∣_
  infix 4 _⊢s_↬⇐_∣_

  -- mark insertion
  mutual
    -- synthesis
    data _⊢_↬⇒_∣_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇒ τ) → (𝕞 : MultiParents) → Set where
      MKSVar : ∀ {Γ x τ u}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ↬⇒ ⊢ ∋x ^ u ∣ []

      MKSFree : ∀ {Γ y u}
        → (∌y : Γ ∌ y)
        → Γ ⊢ - y ^ u ↬⇒ ⊢⟦ ∌y ⟧^ u ∣ []

      MKSLam : ∀ {Γ x τ e τ₁ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇒s τ₁}
        → (e↬⇒ě : Γ , x ∶ (τ △) ⊢s e ↬⇒ ě ∣ 𝕞)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ↬⇒ ⊢λ x ∶ τ ∙ ě ^ u ∣ 𝕞

      MKSAp1 : ∀ {Γ e₁ e₂ τ τ₁ τ₂ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s τ₁}
        → (e₁↬⇒ě₁ : Γ ⊢s e₁ ↬⇒ ě₁ ∣ 𝕞₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂ ∣ 𝕞₂)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ↬⇒ ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u ∣ 𝕞₁ ++ 𝕞₂

      MKSAp2 : ∀ {Γ e₁ e₂ τ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s unknown}
        → (e₁↬⇒ě₁ : Γ ⊢s e₁ ↬⇒ ě₁ ∣ 𝕞₁)
        → (τ!▸ : τ !▸-→)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂ ∣ 𝕞₂)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ↬⇒ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u ∣ 𝕞₁ ++ 𝕞₂

      MKSNum : ∀ {Γ n u}
        → Γ ⊢ -ℕ n ^ u ↬⇒ ⊢ℕ n ^ u ∣ []

      MKSPlus : ∀ {Γ e₁ e₂ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇐s num}  
        → {ě₂ : Γ ⊢⇐s num}
        → (e₁↬⇐ě₁ : Γ ⊢s e₁ ↬⇐ ě₁ ∣ 𝕞₁)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂ ∣ 𝕞₂)
        → Γ ⊢ - e₁ + e₂ ^ u ↬⇒ ⊢ ě₁ + ě₂ ^ u ∣ 𝕞₁ ++ 𝕞₂

      MKSMultiParent : ∀ {Γ u}
        → Γ ⊢ -⋎^ u ↬⇒ ⊢⋎^ u ∣ ∣[ ⟨ u , Γ , Syn ⟩ ]

      MKSUnicycle : ∀ {Γ u}
        → Γ ⊢ -↻^ u ↬⇒ ⊢↻^ u ∣ ∣[ ⟨ u , Γ , Syn ⟩ ]

    MKSubSConflictChildren : ∀ {Γ} {ė* : List USubExp'}
      → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*)
      → List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)
    MKSubSConflictChildren [] = []
    MKSubSConflictChildren (_∷_ {⟨ w , _ ⟩} ⟨ τ , ⟨ ě , _ ⟩ ⟩ ė↬⇒ě*) = ⟨ w , ⟨ τ , ě ⟩ ⟩ ∷ (MKSubSConflictChildren ė↬⇒ě*)

    MKSubSConflictMultiParents : ∀ {Γ} {ė* : List USubExp'}
      → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*)
      → MultiParents
    MKSubSConflictMultiParents [] = []
    MKSubSConflictMultiParents (⟨ _ , ⟨ _ , ⟨ 𝕞 , _ ⟩ ⟩ ⟩ ∷ ė↬⇒ě*) = 𝕞 ++ MKSubSConflictMultiParents ė↬⇒ě*

    data _⊢s_↬⇒_∣_ : {τ : Typ} (Γ : Ctx) → (e : USubExp) → (Γ ⊢⇒s τ) → (𝕞 : MultiParents) → Set where
      MKSubSHole : ∀ {Γ w p}
        → Γ ⊢s -□^ w ^ p ↬⇒ ⊢□^ w ^ p ∣ []

      MKSubSJust : ∀ {Γ w e τ 𝕞}
        → {ě : Γ ⊢⇒ τ} 
        → (e↬⇒ě : Γ  ⊢ e ↬⇒ ě ∣ 𝕞)
        → Γ ⊢s -∶ ⟨ w , e ⟩ ↬⇒ ⊢∶ ⟨ w , ě ⟩ ∣ 𝕞

      MKSubSConflict : ∀ {Γ ė*}
        → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*)
        → Γ ⊢s -⋏ ė* ↬⇒ ⊢⋏ (MKSubSConflictChildren ė↬⇒ě*) ∣ (MKSubSConflictMultiParents ė↬⇒ě*)

    USu→MSu : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {ě : Γ ⊢⇒ τ} {𝕞 : MultiParents} → USubsumable e → Γ ⊢ e ↬⇒ ě ∣ 𝕞 → MSubsumable ě
    USu→MSu {ě = ⊢_^_ {x = x} ∋x u}      USuVar          _ = MSuVar
    USu→MSu {ě = ⊢⟦ x ⟧^ u}              USuVar          _ = MSuFree
    USu→MSu {ě = ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u}    USuAp           _ = MSuAp1
    USu→MSu {ě = ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u} USuAp           _ = MSuAp2
    USu→MSu {ě = ⊢ℕ n ^ u}               USuNum          _ = MSuNum
    USu→MSu {ě = ⊢ ě₁ + ě₂ ^ u}          USuPlus         _ = MSuPlus
    USu→MSu {ě = ⊢⋎^ u}                  USuMultiParent  _ = MSuMultiParent
    USu→MSu {ě = ⊢↻^ u}                  USuUnicycle     _ = MSuUnicycle

    -- analysis
    data _⊢_↬⇐_∣_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇐ τ) → (𝕞 : MultiParents) → Set where
      MKALam1 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △) ~ τ₁)
        → Γ , x ∶ (τ △) ⊢s e ↬⇐ ě ∣ 𝕞
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u) ∣ 𝕞

      MKALam2 : ∀ {Γ x τ e τ' u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s unknown}
        → (τ'!▸ : τ' !▸-→)
        → Γ , x ∶ (τ △) ⊢s e ↬⇐ ě ∣ 𝕞
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u) ∣ 𝕞

      MKALam3 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ △) ~̸ τ₁)
        → Γ , x ∶ (τ △) ⊢s e ↬⇐ ě ∣ 𝕞
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u) ∣ 𝕞

      MKASubsume : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒ τ'}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě ∣ 𝕞)
        → (τ~τ' : τ ~ τ')
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢∙ ě [ τ~τ' ∙ USu→MSu s e↬⇒ě ] ∣ 𝕞

      MKAInconsistentTypes : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒ τ'}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě ∣ 𝕞)
        → (τ~̸τ' : τ ~̸ τ')
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ∙ USu→MSu s e↬⇒ě ] ∣ 𝕞

    data _⊢s_↬⇐_∣_ : {τ : Typ} (Γ : Ctx) → (e : USubExp) → (Γ ⊢⇐s τ) → (𝕞 : MultiParents) → Set where
      MKSubASubsume : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒s τ'}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě ∣ 𝕞)
        → (τ~τ' : τ ~ τ')
        → Γ ⊢s e ↬⇐ ⊢∙ ě [ τ~τ' ] ∣ 𝕞

      MKSubAInconsistentTypes : ∀ {Γ e τ τ' 𝕞}
        → {ě : Γ ⊢⇒s τ'}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě ∣ 𝕞)
        → (τ~̸τ' : τ ~̸ τ')
        → Γ ⊢s e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ] ∣ 𝕞
