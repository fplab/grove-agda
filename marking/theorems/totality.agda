open import marking.prelude
open import marking.definitions

module marking.theorems.totality where
  mutual
    ↬⇒-totality : (Γ : Ctx)
                → (e : UExp)
                → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (-⦇-⦈^ x)        = ⟨ unknown , ⟨ ⊢⦇-⦈^ x , MKSHole ⟩ ⟩
    ↬⇒-totality Γ (- x)
      with Γ ∋?? x
    ...  | yes (Z {τ = τ})         = ⟨ τ       , ⟨ ⊢ Z           , MKSVar Z           ⟩ ⟩
    ...  | yes (S {τ = τ} x≢x′ ∋x) = ⟨ τ       , ⟨ ⊢ (S x≢x′ ∋x) , MKSVar (S x≢x′ ∋x) ⟩ ⟩
    ...  | no  ∌x                  = ⟨ unknown , ⟨ ⊢⟦ ∌x ⟧       , MKSFree ∌x         ⟩ ⟩
    ↬⇒-totality Γ (-λ x ∶ τ ∙ e)
      with ⟨ τ′ , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality (Γ , x ∶ τ) e
         = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě , MKSLam e↬⇒ě ⟩ ⟩
    ↬⇒-totality Γ (- e₁ ∙ e₂)
      with ↬⇒-totality Γ e₁
    ...  | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩
             with τ ▸-→?
    ...         | no τ!▸
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ unknown e₂
                       = ⟨ unknown , ⟨ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] , MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂ ⟩ ⟩
    ...         | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ τ₁ e₂
                       = ⟨ τ₂ , ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ] , MKSAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ (-ℕ n) = ⟨ num , ⟨ ⊢ℕ n , MKSNum ⟩ ⟩
    ↬⇒-totality Γ (- e₁ + e₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ num e₁
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ num e₂
         = ⟨ num , ⟨ ⊢ ě₁ + ě₂ , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩

    ↬⇐-subsume : ∀ {Γ e τ}
               → (ě : Γ ⊢⇒ τ)
               → (τ′ : Typ)
               → (Γ ⊢ e ↬⇒ ě)
               → (s : USubsumable e)
               → Σ[ ě ∈ Γ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-subsume {τ = τ} ě τ′ e↬⇒ě s with τ′ ~? τ
    ...   | yes τ′~τ = ⟨ ⊢∙ ě  [ τ′~τ ∙ USu→MSu s e↬⇒ě ] , MKASubsume e↬⇒ě τ′~τ s ⟩
    ...   | no  τ′~̸τ = ⟨ ⊢⸨ ě ⸩[ τ′~̸τ ∙ USu→MSu s e↬⇒ě ] , MKAInconsistentTypes e↬⇒ě τ′~̸τ s ⟩

    ↬⇐-totality : (Γ : Ctx)
                → (τ′ : Typ)
                → (e : UExp)
                → Σ[ ě ∈ Γ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ′ e@(-⦇-⦈^ u)
      with ⟨ .unknown , ⟨ ě@(⊢⦇-⦈^ _) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuHole
    ↬⇐-totality Γ τ′ e@(- x)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⟦ ∌x ⟧) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuVar
    ...  | ⟨ τ        , ⟨ ě@(⊢ ∋x) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuVar
    ↬⇐-totality Γ τ′ e@(-λ x ∶ τ ∙ e′)
      with τ′ ▸-→?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩
             with τ ~? τ₁
    ...         | yes τ~τ₁
                    with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
                       = ⟨ ⊢λ x ∶ τ ∙ ě′ [ τ′▸ ∙ τ~τ₁ ] , MKALam1 τ′▸ τ~τ₁ e′↬⇐ě′ ⟩
    ...         | no  τ~̸τ₁
                    with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
                       = ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě′ [ τ′▸ ∙ τ~̸τ₁ ] , MKALam3 τ′▸ τ~̸τ₁ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(-λ x ∶ τ ∙ e′)
         | no τ′!▸
             with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) unknown e′
                = ⟨ ⊢⸨λ x ∶ τ ∙ ě′ ⸩[ τ′!▸ ] , MKALam2 τ′!▸ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(- _ ∙ _)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⸨ _ ⸩∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuAp
    ...  | ⟨ _        , ⟨ ě@(⊢  _  ∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuAp
    ↬⇐-totality Γ τ′ e@(-ℕ _)
      with ⟨ _ , ⟨ ě@(⊢ℕ _) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuNum
    ↬⇐-totality Γ τ′ e@(- _ + _)
      with ⟨ _ , ⟨ ě@(⊢ _ + _) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuPlus
