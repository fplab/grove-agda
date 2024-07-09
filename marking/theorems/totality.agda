open import marking.prelude
open import marking.definitions

module marking.theorems.totality where
  mutual
    -- TODO make context implicit
    ↬⇒-totality : (Γ : Ctx)
                → (e : UExp)
                → Σ[ τ ∈ Typ ] ∃[ 𝕞 ] Σ[ ě ∈ Γ ⊢⇒ τ ∣ 𝕞 ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (- x ^ u)
      with Γ ∋?? x
    ...  | yes (Z {τ = τ})         = ⟨ τ       , ⟨ _ , ⟨ ⊢ Z ^ u           , MKSVar Z           ⟩ ⟩ ⟩
    ...  | yes (S {τ = τ} x≢x' ∋x) = ⟨ τ       , ⟨ _ , ⟨ ⊢ (S x≢x' ∋x) ^ u , MKSVar (S x≢x' ∋x) ⟩ ⟩ ⟩
    ...  | no  ∌x                  = ⟨ unknown , ⟨ _ , ⟨ ⊢⟦ ∌x ⟧^ u        , MKSFree ∌x         ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-λ x ∶ τ ∙ e ^ u)
      with ⟨ τ' , ⟨ _ , ⟨ ě , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒s-totality (Γ , x ∶ (τ △)) e
         = ⟨ (τ △) -→ τ' , ⟨ _ , ⟨ ⊢λ x ∶ τ ∙ ě ^ u , MKSLam e↬⇒ě ⟩ ⟩ ⟩
    ↬⇒-totality Γ (- e₁ ∙ e₂ ^ u)
      with ↬⇒s-totality Γ e₁
    ...  | ⟨ τ , ⟨ _ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩ ⟩
             with τ ▸-→?
    ...         | no τ!▸
                    with ⟨ _ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇐s-totality Γ unknown e₂
                       = ⟨ unknown , ⟨ _ , ⟨ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u , MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂ ⟩ ⟩ ⟩
    ...         | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩
                    with ⟨ _ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇐s-totality Γ τ₁ e₂
                       = ⟨ τ₂ , ⟨ _ , ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ]^ u , MKSAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂ ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-ℕ n ^ u) = ⟨ num , ⟨ _ , ⟨ ⊢ℕ n ^ u , MKSNum ⟩ ⟩ ⟩
    ↬⇒-totality Γ (- e₁ + e₂ ^ u)
      with ⟨ _ , ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ⟩ ← ↬⇐s-totality Γ num e₁
         | ⟨ _ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇐s-totality Γ num e₂
         = ⟨ num , ⟨ _ , ⟨ ⊢ ě₁ + ě₂ ^ u , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-⋎^ u) = ⟨ unknown , ⟨ _ , ⟨ ⊢⋎^ u , MKSMultiParent ⟩ ⟩ ⟩
    ↬⇒-totality Γ (-↻^ u) = ⟨ unknown , ⟨ _ , ⟨ ⊢↻^ u , MKSUnicycle ⟩ ⟩ ⟩

    ↬⇒s-totality : (Γ : Ctx)
                 → (e : USubExp)
                 → Σ[ τ ∈ Typ ] ∃[ 𝕞 ] Σ[ ě ∈ Γ ⊢⇒s τ ∣ 𝕞 ] (Γ ⊢s e ↬⇒ ě)
    ↬⇒s-totality Γ (-□^ w ^ p) = ⟨ unknown , ⟨ _ , ⟨ ⊢□^ w ^ p , MKSubSHole ⟩ ⟩ ⟩
    ↬⇒s-totality Γ (-∶ ⟨ w , e ⟩)
      with ⟨ τ' , ⟨ _ , ⟨ ě , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ⟨ τ' , ⟨ _ , ⟨ ⊢∶ ⟨ w , ě ⟩ , MKSubSJust e↬⇒ě ⟩ ⟩ ⟩
    ↬⇒s-totality Γ (-⋏ ė*)
      with ė↬⇒ě* ← ↬⇒s-totality* Γ ė*
         = ⟨ unknown , ⟨ _ , ⟨ ⊢⋏ MKSubSConflictChildren ė↬⇒ě* , MKSubSConflict ė↬⇒ě* ⟩ ⟩ ⟩

    ↬⇒s-totality* : (Γ : Ctx)
                  → (ė* : List USubExp')
                  → All (λ (⟨ _ , e ⟩) → ∃[ τ ] ∃[ 𝕞 ] Σ[ ě ∈ Γ ⊢⇒ τ ∣ 𝕞 ] Γ ⊢ e ↬⇒ ě) ė*
    ↬⇒s-totality* Γ []               = []
    ↬⇒s-totality* Γ (⟨ w , e ⟩ ∷ ė*) = ↬⇒-totality Γ e ∷ ↬⇒s-totality* Γ ė*

    ↬⇐-subsume : ∀ {Γ e τ 𝕞}
               → (ě : Γ ⊢⇒ τ ∣ 𝕞)
               → (τ' : Typ)
               → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
               → (s : USubsumable e)
               →  ∃[ 𝕞' ] Σ[ ě ∈ Γ ⊢⇐ τ' ∣ 𝕞' ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-subsume {τ = τ} ě τ' e↬⇒ě s with τ' ~? τ
    ...   | yes τ'~τ = ⟨ _ , ⟨ ⊢∙ ě  [ τ'~τ ∙ USu→MSu s e↬⇒ě ] , MKASubsume e↬⇒ě τ'~τ s ⟩ ⟩
    ...   | no  τ'~̸τ = ⟨ _ , ⟨ ⊢⸨ ě ⸩[ τ'~̸τ ∙ USu→MSu s e↬⇒ě ] , MKAInconsistentTypes e↬⇒ě τ'~̸τ s ⟩ ⟩

    ↬⇐s-subsume : ∀ {Γ e τ 𝕞}
                → (ě : Γ ⊢⇒s τ ∣ 𝕞)
                → (τ' : Typ)
                → (e↬⇒ě : Γ ⊢s e ↬⇒ ě)
                → ∃[ 𝕞' ] Σ[ ě ∈ Γ ⊢⇐s τ' ∣ 𝕞' ] (Γ ⊢s e ↬⇐ ě)
    ↬⇐s-subsume {τ = τ} ě τ' e↬⇒ě  with τ' ~? τ
    ...   | yes τ'~τ = ⟨ _ , ⟨ ⊢∙ ě  [ τ'~τ ] , MKSubASubsume e↬⇒ě τ'~τ ⟩ ⟩
    ...   | no  τ'~̸τ = ⟨ _ , ⟨ ⊢⸨ ě ⸩[ τ'~̸τ ] , MKSubAInconsistentTypes e↬⇒ě τ'~̸τ ⟩ ⟩

    ↬⇐-totality : (Γ : Ctx)
                → (τ' : Typ)
                → (e : UExp)
                → ∃[ 𝕞 ] Σ[ ě ∈ Γ ⊢⇐ τ' ∣ 𝕞 ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ' e@(- x ^ u)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ _ , ⟨ ě@(⊢⟦ ∌x ⟧^ u) , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ...  | ⟨ τ        , ⟨ _ , ⟨ ě@(⊢ ∋x ^ u)   , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
      with τ' ▸-→?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ'▸ ⟩ ⟩
             with (τ △) ~? τ₁
    ...         | yes τ~τ₁
                    with ⟨ _ , ⟨ ě' , e'↬⇐ě' ⟩ ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) τ₂ e'
                       = ⟨ _ , ⟨ ⊢λ x ∶ τ ∙ ě' [ τ'▸ ∙ τ~τ₁ ]^ u , MKALam1 τ'▸ τ~τ₁ e'↬⇐ě' ⟩ ⟩
    ...         | no  τ~̸τ₁
                    with ⟨ _ , ⟨ ě' , e'↬⇐ě' ⟩ ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) τ₂ e'
                       = ⟨ _ , ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě' [ τ'▸ ∙ τ~̸τ₁ ]^ u , MKALam3 τ'▸ τ~̸τ₁ e'↬⇐ě' ⟩ ⟩
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
         | no τ'!▸
             with ⟨ _ , ⟨ ě' , e'↬⇐ě' ⟩ ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) unknown e'
                = ⟨ _ , ⟨ ⊢⸨λ x ∶ τ ∙ ě' ⸩[ τ'!▸ ]^ u , MKALam2 τ'!▸ e'↬⇐ě' ⟩ ⟩
    ↬⇐-totality Γ τ' e@(- _ ∙ _ ^ u)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ _ , ⟨ ě@(⊢⸨ _ ⸩∙ _ [ _ ]^ u) , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ...  | ⟨ _        , ⟨ _ , ⟨ ě@(⊢  _  ∙ _ [ _ ]^ u) , e↬⇒ě ⟩ ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ↬⇐-totality Γ τ' e@(-ℕ _ ^ u)
      with ⟨ _ , ⟨ _ , ⟨ ě@(⊢ℕ _ ^ u) , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuNum
    ↬⇐-totality Γ τ' e@(- _ + _ ^ u)
      with ⟨ _ , ⟨ _ , ⟨ ě@(⊢ _ + _ ^ u) , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuPlus
    ↬⇐-totality Γ τ' e@(-⋎^ u)
      with ⟨ _ , ⟨ _ , ⟨ ě@(⊢⋎^ u) , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuMultiParent
    ↬⇐-totality Γ τ' e@(-↻^ u)
      with ⟨ _ , ⟨ _ , ⟨ ě@(⊢↻^ u) , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuUnicycle

    ↬⇐s-totality : (Γ : Ctx)
                 → (τ' : Typ)
                 → (e : USubExp)
                 → ∃[ 𝕞 ] Σ[ ě ∈ Γ ⊢⇐s τ' ∣ 𝕞 ] (Γ ⊢s e ↬⇐ ě)
    ↬⇐s-totality Γ τ' e
      with ⟨ _ , ⟨ _ , ⟨ ě , e↬⇒ě ⟩ ⟩ ⟩ ← ↬⇒s-totality Γ e
         = ↬⇐s-subsume ě τ' e↬⇒ě
