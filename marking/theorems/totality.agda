open import marking.prelude
open import marking.definitions

module marking.theorems.totality where
  mutual
    -- TODO make context implicit
    ↬⇒-totality : (Γ : Ctx)
                → (e : UExp)
                → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (- x ^ u)
      with Γ ∋?? x
    ...  | yes (Z {τ = τ})         = ⟨ τ       , ⟨ ⊢ Z ^ u           , MKSVar Z           ⟩ ⟩
    ...  | yes (S {τ = τ} x≢x' ∋x) = ⟨ τ       , ⟨ ⊢ (S x≢x' ∋x) ^ u , MKSVar (S x≢x' ∋x) ⟩ ⟩
    ...  | no  ∌x                  = ⟨ unknown , ⟨ ⊢⟦ ∌x ⟧^ u        , MKSFree ∌x         ⟩ ⟩
    ↬⇒-totality Γ (-λ x ∶ τ ∙ e ^ u)
      with ⟨ τ' , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒s-totality (Γ , x ∶ (τ △)) e
         = ⟨ (τ △) -→ τ' , ⟨ ⊢λ x ∶ τ ∙ ě ^ u , MKSLam e↬⇒ě ⟩ ⟩
    ↬⇒-totality Γ (- e₁ ∙ e₂ ^ u)
      with ↬⇒s-totality Γ e₁
    ...  | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩
             with τ ▸-→?
    ...         | no τ!▸
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐s-totality Γ unknown e₂
                       = ⟨ unknown , ⟨ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u , MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂ ⟩ ⟩
    ...         | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐s-totality Γ τ₁ e₂
                       = ⟨ τ₂ , ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ]^ u , MKSAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ (-ℕ n ^ u) = ⟨ num , ⟨ ⊢ℕ n ^ u , MKSNum ⟩ ⟩
    ↬⇒-totality Γ (- e₁ + e₂ ^ u)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐s-totality Γ num e₁
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐s-totality Γ num e₂
         = ⟨ num , ⟨ ⊢ ě₁ + ě₂ ^ u , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ (-⋎^ u) = ⟨ unknown , ⟨ ⊢⋎^ u , MKSMultiParent ⟩ ⟩
    ↬⇒-totality Γ (-↻^ u) = ⟨ unknown , ⟨ ⊢↻^ u , MKSUnicycle ⟩ ⟩

    ↬⇒s-totality : (Γ : Ctx)
                 → (e : USubExp)
                 → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒s τ ] (Γ ⊢s e ↬⇒ ě)
    ↬⇒s-totality Γ (-□^ w ^ p) = ⟨ unknown , ⟨ ⊢□^ w ^ p , MKSubSHole ⟩ ⟩
    ↬⇒s-totality Γ (-∶ ⟨ w , e ⟩)
      with ⟨ τ' , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ⟨ τ' , ⟨ ⊢∶ ⟨ w , ě ⟩ , MKSubSJust e↬⇒ě ⟩ ⟩
    ↬⇒s-totality Γ (-⋏ ė*) = ⟨ unknown , {! ⟨ ⊢⋏ {! !} , MKSubSConflict {! !} ⟩ !} ⟩

    ↬⇐-subsume : ∀ {Γ e τ}
               → (ě : Γ ⊢⇒ τ)
               → (τ' : Typ)
               → (Γ ⊢ e ↬⇒ ě)
               → (s : USubsumable e)
               → Σ[ ě ∈ Γ ⊢⇐ τ' ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-subsume {τ = τ} ě τ' e↬⇒ě s with τ' ~? τ
    ...   | yes τ'~τ = ⟨ ⊢∙ ě  [ τ'~τ ∙ USu→MSu s e↬⇒ě ] , MKASubsume e↬⇒ě τ'~τ s ⟩
    ...   | no  τ'~̸τ = ⟨ ⊢⸨ ě ⸩[ τ'~̸τ ∙ USu→MSu s e↬⇒ě ] , MKAInconsistentTypes e↬⇒ě τ'~̸τ s ⟩

    ↬⇐s-subsume : ∀ {Γ e τ}
                → (ě : Γ ⊢⇒s τ)
                → (τ' : Typ)
                → (Γ ⊢s e ↬⇒ ě)
                → Σ[ ě ∈ Γ ⊢⇐s τ' ] (Γ ⊢s e ↬⇐ ě)

    ↬⇐-totality : (Γ : Ctx)
                → (τ' : Typ)
                → (e : UExp)
                → Σ[ ě ∈ Γ ⊢⇐ τ' ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ' e@(- x ^ u)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⟦ ∌x ⟧^ u) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ...  | ⟨ τ        , ⟨ ě@(⊢ ∋x ^ u)   , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
      with τ' ▸-→?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ'▸ ⟩ ⟩
             with (τ △) ~? τ₁
    ...         | yes τ~τ₁
                    with ⟨ ě' , e'↬⇐ě' ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) τ₂ e'
                       = ⟨ ⊢λ x ∶ τ ∙ ě' [ τ'▸ ∙ τ~τ₁ ]^ u , MKALam1 τ'▸ τ~τ₁ e'↬⇐ě' ⟩
    ...         | no  τ~̸τ₁
                    with ⟨ ě' , e'↬⇐ě' ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) τ₂ e'
                       = ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě' [ τ'▸ ∙ τ~̸τ₁ ]^ u , MKALam3 τ'▸ τ~̸τ₁ e'↬⇐ě' ⟩
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
         | no τ'!▸
             with ⟨ ě' , e'↬⇐ě' ⟩ ← ↬⇐s-totality (Γ , x ∶ (τ △)) unknown e'
                = ⟨ ⊢⸨λ x ∶ τ ∙ ě' ⸩[ τ'!▸ ]^ u , MKALam2 τ'!▸ e'↬⇐ě' ⟩
    ↬⇐-totality Γ τ' e@(- _ ∙ _ ^ u)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⸨ _ ⸩∙ _ [ _ ]^ u) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ...  | ⟨ _        , ⟨ ě@(⊢  _  ∙ _ [ _ ]^ u) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ↬⇐-totality Γ τ' e@(-ℕ _ ^ u)
      with ⟨ _ , ⟨ ě@(⊢ℕ _ ^ u) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuNum
    ↬⇐-totality Γ τ' e@(- _ + _ ^ u)
      with ⟨ _ , ⟨ ě@(⊢ _ + _ ^ u) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuPlus
    ↬⇐-totality Γ τ' e@(-⋎^ u)
      with ⟨ _ , ⟨ ě@(⊢⋎^ u) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuMultiParent
    ↬⇐-totality Γ τ' e@(-↻^ u)
      with ⟨ _ , ⟨ ě@(⊢↻^ u) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuUnicycle

    ↬⇐s-totality : (Γ : Ctx)
                 → (τ' : Typ)
                 → (e : USubExp)
                 → Σ[ ě ∈ Γ ⊢⇐s τ' ] (Γ ⊢s e ↬⇐ ě)
    ↬⇐s-totality Γ τ' e
      with ⟨ _ , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒s-totality Γ e
         = ↬⇐s-subsume ě τ' e↬⇒ě
