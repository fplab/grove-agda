open import marking.prelude
open import marking.definitions

module marking.theorems.totality where
  mutual
    -- TODO make context implicit
    ↬⇒-totality : (Γ : Ctx)
                → (e : UExp)
                → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] (Γ ⊢ e ↬⇒ ě ∣ 𝕞)
    ↬⇒-totality Γ (- x ^ u)
      with Γ ∋?? x
    ...  | yes (Z {τ = τ})         = ⟨ τ       , ⟨ ⊢ Z ^ u           , ⟨ _ , MKSVar Z           ⟩ ⟩ ⟩
    ...  | yes (S {τ = τ} x≢x' ∋x) = ⟨ τ       , ⟨ ⊢ (S x≢x' ∋x) ^ u , ⟨ _ , MKSVar (S x≢x' ∋x) ⟩ ⟩ ⟩
    ...  | no  ∌x                  = ⟨ unknown , ⟨ ⊢⟦ ∌x ⟧^ u        , ⟨ _ , MKSFree ∌x         ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-λ x ∶ τ ∙ e ^ u)
      with ⟨ τ' , ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒s-totality (Γ , x ∶ (τ △)) e
         = ⟨ (τ △) -→ τ' , ⟨ ⊢λ x ∶ τ ∙ ě ^ u , ⟨ _ , MKSLam e↬⇒ě ⟩ ⟩ ⟩
    ↬⇒-totality Γ (- e₁ ∙ e₂ ^ u)
      with ↬⇒s-totality Γ e₁
    ...  | ⟨ τ , ⟨ ě₁ , ⟨ _ , e₁↬⇒ě₁ ⟩ ⟩ ⟩
             with τ ▸-→?
    ...         | no τ!▸
                    with ⟨ ě₂ , ⟨ _ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇐s-totality Γ unknown e₂
                       = ⟨ unknown , ⟨ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u , ⟨ _ , MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂ ⟩ ⟩ ⟩
    ...         | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩
                    with ⟨ ě₂ , ⟨ _ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇐s-totality Γ τ₁ e₂
                       = ⟨ τ₂ , ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ]^ u , ⟨ _ , MKSAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂ ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-ℕ n ^ u) = ⟨ num , ⟨ ⊢ℕ n ^ u , ⟨ _ , MKSNum ⟩ ⟩ ⟩
    ↬⇒-totality Γ (- e₁ + e₂ ^ u)
      with ⟨ ě₁ , ⟨ _ , e₁↬⇐ě₁ ⟩ ⟩ ← ↬⇐s-totality Γ num e₁
         | ⟨ ě₂ , ⟨ _ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇐s-totality Γ num e₂
         = ⟨ num , ⟨ ⊢ ě₁ + ě₂ ^ u , ⟨ _ , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-⋎^ u) = ⟨ unknown , ⟨ ⊢⋎^ u , ⟨ _ , MKSMultiParent ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-↻^ u) = ⟨ unknown , ⟨ ⊢↻^ u , ⟨ _ , MKSUnicycle ⟩ ⟩ ⟩

    ↬⇒s-totality : (Γ : Ctx)
                 → (e : USubExp)
                 → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒s τ ] ∃[ 𝕞 ] (Γ ⊢s e ↬⇒ ě ∣ 𝕞)
    ↬⇒s-totality Γ (-□^ w ^ p) = ⟨ unknown , ⟨ ⊢□^ w ^ p , ⟨ _ , MKSubSHole ⟩ ⟩ ⟩
    ↬⇒s-totality Γ (-∶ ⟨ w , e ⟩)
      with ⟨ τ' , ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ⟨ τ' , ⟨ ⊢∶ ⟨ w , ě ⟩ , ⟨ _ , MKSubSJust e↬⇒ě ⟩ ⟩ ⟩
    ↬⇒s-totality Γ (-⋏ ė*)
      with ė↬⇒ě* ← ↬⇒s-totality* Γ ė*
         = ⟨ unknown , ⟨ ⊢⋏ MKSubSConflictChildren ė↬⇒ě* , ⟨ _ , MKSubSConflict ė↬⇒ě* ⟩ ⟩ ⟩

    ↬⇒s-totality* : (Γ : Ctx)
                  → (ė* : List USubExp')
                  → All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*
    ↬⇒s-totality* Γ []               = []
    ↬⇒s-totality* Γ (⟨ w , e ⟩ ∷ ė*) = ↬⇒-totality Γ e ∷ ↬⇒s-totality* Γ ė*

    ↬⇐-subsume : ∀ {Γ e τ 𝕞}
               → (ě : Γ ⊢⇒ τ)
               → (τ' : Typ)
               → (e↬⇒ě : Γ ⊢ e ↬⇒ ě ∣ 𝕞)
               → (s : USubsumable e)
               → Σ[ ě ∈ Γ ⊢⇐ τ' ] ∃[ 𝕞' ] (Γ ⊢ e ↬⇐ ě ∣ 𝕞')
    ↬⇐-subsume {τ = τ} ě τ' e↬⇒ě s with τ' ~? τ
    ...   | yes τ'~τ = ⟨ ⊢∙ ě  [ τ'~τ ∙ USu→MSu s e↬⇒ě ] , ⟨ _ , MKASubsume e↬⇒ě τ'~τ s ⟩ ⟩
    ...   | no  τ'~̸τ = ⟨ ⊢⸨ ě ⸩[ τ'~̸τ ∙ USu→MSu s e↬⇒ě ] , ⟨ _ , MKAInconsistentTypes e↬⇒ě τ'~̸τ s ⟩ ⟩

    ↬⇐s-subsume : ∀ {Γ e τ 𝕞}
                → (ě : Γ ⊢⇒s τ)
                → (τ' : Typ)
                → (e↬⇒ě : Γ ⊢s e ↬⇒ ě ∣ 𝕞)
                → Σ[ ě ∈ Γ ⊢⇐s τ' ] ∃[ 𝕞' ] (Γ ⊢s e ↬⇐ ě ∣ 𝕞')
    ↬⇐s-subsume {τ = τ} ě τ' e↬⇒ě  with τ' ~? τ
    ...   | yes τ'~τ = ⟨ ⊢∙ ě  [ τ'~τ ] , ⟨ _ , MKSubASubsume e↬⇒ě τ'~τ ⟩ ⟩
    ...   | no  τ'~̸τ = ⟨ ⊢⸨ ě ⸩[ τ'~̸τ ] , ⟨ _ , MKSubAInconsistentTypes e↬⇒ě τ'~̸τ ⟩ ⟩

    ↬⇐-totality : (Γ : Ctx)
                → (τ' : Typ)
                → (e : UExp)
                → Σ[ ě ∈ Γ ⊢⇐ τ' ] ∃[ 𝕞 ] (Γ ⊢ e ↬⇐ ě ∣ 𝕞)
    ↬⇐-totality Γ τ' e@(- x ^ u)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⟦ ∌x ⟧^ u) , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ...  | ⟨ τ        , ⟨ ě@(⊢ ∋x ^ u)   , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
      with τ' ▸-→?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ'▸ ⟩ ⟩
             with (τ △) ~? τ₁
    ...         | yes τ~τ₁
                    with ⟨ ě' , ⟨ _ , e'↬⇐ě' ⟩ ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) τ₂ e'
                       = ⟨ ⊢λ x ∶ τ ∙ ě' [ τ'▸ ∙ τ~τ₁ ]^ u , ⟨ _ , MKALam1 τ'▸ τ~τ₁ e'↬⇐ě' ⟩ ⟩
    ...         | no  τ~̸τ₁
                    with ⟨ ě' , ⟨ _ , e'↬⇐ě' ⟩ ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) τ₂ e'
                       = ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě' [ τ'▸ ∙ τ~̸τ₁ ]^ u , ⟨ _ , MKALam3 τ'▸ τ~̸τ₁ e'↬⇐ě' ⟩ ⟩
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
         | no τ'!▸
             with ⟨ ě' , ⟨ _ , e'↬⇐ě' ⟩ ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) unknown e'
                = ⟨ ⊢⸨λ x ∶ τ ∙ ě' ⸩[ τ'!▸ ]^ u , ⟨ _ , MKALam2 τ'!▸ e'↬⇐ě' ⟩ ⟩
    ↬⇐-totality Γ τ' e@(- _ ∙ _ ^ u)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⸨ _ ⸩∙ _ [ _ ]^ u) , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ...  | ⟨ _        , ⟨ ě@(⊢  _  ∙ _ [ _ ]^ u) , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ↬⇐-totality Γ τ' e@(-ℕ _ ^ u)
      with ⟨ _ , ⟨ ě@(⊢ℕ _ ^ u) , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuNum
    ↬⇐-totality Γ τ' e@(- _ + _ ^ u)
      with ⟨ _ , ⟨ ě@(⊢ _ + _ ^ u) , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuPlus
    ↬⇐-totality Γ τ' e@(-⋎^ u)
      with ⟨ _ , ⟨ ě@(⊢⋎^ u) , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuMultiParent
    ↬⇐-totality Γ τ' e@(-↻^ u)
      with ⟨ _ , ⟨ ě@(⊢↻^ u) , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuUnicycle

    ↬⇐s-totality : (Γ : Ctx)
                 → (τ' : Typ)
                 → (e : USubExp)
                 → Σ[ ě ∈ Γ ⊢⇐s τ' ] ∃[ 𝕞 ] (Γ ⊢s e ↬⇐ ě ∣ 𝕞)
    ↬⇐s-totality Γ τ' e
      with ⟨ _ , ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒s-totality Γ e
         = ↬⇐s-subsume ě τ' e↬⇒ě
