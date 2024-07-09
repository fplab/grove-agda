open import marking.prelude
open import marking.definitions

module marking.theorems.wellformed where
  mutual
    -- marking preserves syntactic structure
    ↬⇒□ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ} {𝕞 : MultiParents}
        → Γ ⊢ e ↬⇒ ě ∣ 𝕞
        → ě ⇒□ ≡ e
    ↬⇒□ (MKSVar ∋x)       = refl
    ↬⇒□ (MKSFree ∌x)      = refl
    ↬⇒□ (MKSLam e↬⇒ě)
      rewrite ↬⇒□s e↬⇒ě   = refl
    ↬⇒□ (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂)
      rewrite ↬⇒□s e₁↬⇒ě₁
            | ↬⇐□s e₂↬⇐ě₂ = refl
    ↬⇒□ (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂)
      rewrite ↬⇒□s e₁↬⇒ě₁
            | ↬⇐□s e₂↬⇐ě₂ = refl
    ↬⇒□ MKSNum            = refl
    ↬⇒□ (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
      rewrite ↬⇐□s e₁↬⇐ě₁
            | ↬⇐□s e₂↬⇐ě₂ = refl
    ↬⇒□ MKSMultiParent    = refl
    ↬⇒□ MKSUnicycle       = refl

    ↬⇒□s : ∀ {Γ : Ctx} {e : USubExp} {τ : Typ} {ě : Γ ⊢⇒s τ} {𝕞 : MultiParents}
        → Γ ⊢s e ↬⇒ ě ∣ 𝕞
        → ě ⇒□s ≡ e
    ↬⇒□s MKSubSHole = refl
    ↬⇒□s (MKSubSJust e↬⇒ě) rewrite ↬⇒□ e↬⇒ě = refl
    ↬⇒□s (MKSubSConflict ė↬⇒ě*)
      with eqv ← ↬⇒□s* ė↬⇒ě* rewrite eqv    = refl

    ↬⇒□s* : ∀ {Γ ė*}
          → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*)
          → ((MKSubSConflictChildren ė↬⇒ě*) ⇒□s*) ≡ ė*
    ↬⇒□s* [] = refl
    ↬⇒□s* (_∷_ {⟨ w , e ⟩} {ė*} ⟨ τ , ⟨ ě , ⟨ 𝕞 , e↬⇒ě ⟩ ⟩ ⟩ ė↬⇒ě*)
      with refl ← ↬⇒□ e↬⇒ě
         | eqv ← ↬⇒□s* ė↬⇒ě* rewrite eqv = refl

    ↬⇐□ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ} {𝕞 : MultiParents}
        → Γ ⊢ e ↬⇐ ě ∣ 𝕞
        → ě ⇐□ ≡ e
    ↬⇐□ (MKALam1 τ₁▸ τ~τ₁ e↬⇐ě)
      rewrite ↬⇐□s e↬⇐ě  = refl
    ↬⇐□ (MKALam2 τ₁!▸ e↬⇐ě)
      rewrite ↬⇐□s e↬⇐ě  = refl
    ↬⇐□ (MKALam3 τ₁▸ τ~̸τ₁ e↬⇐ě)
      rewrite ↬⇐□s e↬⇐ě  = refl
    ↬⇐□ (MKAInconsistentTypes e↬⇒ě τ~̸τ' s)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇐□ (MKASubsume e↬⇒ě τ~τ' s)
      rewrite ↬⇒□ e↬⇒ě   = refl

    ↬⇐□s : ∀ {Γ : Ctx} {e : USubExp} {τ : Typ} {ě : Γ ⊢⇐s τ} {𝕞 : MultiParents}
        → Γ ⊢s e ↬⇐ ě ∣ 𝕞
        → ě ⇐□s ≡ e
    ↬⇐□s (MKSubASubsume e↬⇒ě τ~τ')
      rewrite ↬⇒□s e↬⇒ě = refl
    ↬⇐□s (MKSubAInconsistentTypes e↬⇒ě τ~̸τ')
      rewrite ↬⇒□s e↬⇒ě = refl

  mutual
    -- well-typed unmarked expressions are marked into marked expressions of the same type
    ⇒τ→↬⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇒ τ
           → Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞
    ⇒τ→↬⇒τ {e = - x ^ u}            (USVar ∋x)       = ⟨ ⊢ ∋x ^ u , ⟨ _ , MKSVar ∋x ⟩ ⟩
    ⇒τ→↬⇒τ {e = -λ x ∶ τ ∙ e ^ u}   (USLam e⇒τ)
      with ⟨ ě  , ⟨ _ , e↬⇒ě ⟩ ⟩ ← ⇒sτ→↬⇒sτ e⇒τ      = ⟨ ⊢λ x ∶ τ ∙ ě ^ u , ⟨ _ , MKSLam e↬⇒ě ⟩ ⟩
    ⇒τ→↬⇒τ {e = - e₁ ∙ e₂ ^ u} (USAp e₁⇒τ τ▸ e₂⇐τ₂)
      with ⟨ ě₁ , ⟨ _ , e₁↬⇒ě₁ ⟩ ⟩ ← ⇒sτ→↬⇒sτ e₁⇒τ
         | ⟨ ě₂ , ⟨ _ , e₂↬⇐ě₂ ⟩ ⟩ ← ⇐sτ→↬⇐sτ e₂⇐τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u , ⟨ _ , MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂ ⟩ ⟩
    ⇒τ→↬⇒τ {e = -ℕ n ^ u}           USNum            = ⟨ ⊢ℕ n ^ u , ⟨ _ , MKSNum ⟩ ⟩
    ⇒τ→↬⇒τ {e = - e₁ + e₂ ^ u}      (USPlus e₁⇐num e₂⇐num)
      with ⟨ ě₁ , ⟨ _ , e₁↬⇐ě₁ ⟩ ⟩ ← ⇐sτ→↬⇐sτ e₁⇐num
         | ⟨ ě₂ , ⟨ _ , e₂↬⇐ě₂ ⟩ ⟩ ← ⇐sτ→↬⇐sτ e₂⇐num = ⟨ ⊢ ě₁ + ě₂ ^ u , ⟨ _ , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩
    ⇒τ→↬⇒τ {e = -⋎^ u}              USMultiParent    = ⟨ ⊢⋎^ u , ⟨ _ , MKSMultiParent ⟩ ⟩
    ⇒τ→↬⇒τ {e = -↻^ u}              USUnicycle       = ⟨ ⊢↻^ u , ⟨ _ , MKSUnicycle ⟩ ⟩

    ⇒sτ→↬⇒sτ : ∀ {Γ : Ctx} {e : USubExp} {τ : Typ}
             → Γ ⊢s e ⇒ τ
             → Σ[ ě ∈ Γ ⊢⇒s τ ] ∃[ 𝕞 ] Γ ⊢s e ↬⇒ ě ∣ 𝕞
    ⇒sτ→↬⇒sτ {e = -□^ w ^ p}     USubSHole   = ⟨ ⊢□^ w ^ p , ⟨ _ , MKSubSHole ⟩ ⟩
    ⇒sτ→↬⇒sτ {e = -∶ ⟨ w , e ⟩} (USubSJust e⇒τ) 
      with ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ← ⇒τ→↬⇒τ e⇒τ = ⟨ ⊢∶ ⟨ w , ě ⟩ , ⟨ _ , MKSubSJust e↬⇒ě ⟩ ⟩
    ⇒sτ→↬⇒sτ {e = -⋏ ė*}        (USubSConflict ė⇒*)
      with ė↬⇒ě* ← ⇒sτ→↬⇒sτ* ė⇒*             = ⟨ ⊢⋏ MKSubSConflictChildren ė↬⇒ě* , ⟨ _ , MKSubSConflict ė↬⇒ě* ⟩ ⟩

    ⇒sτ→↬⇒sτ* : ∀ {Γ : Ctx} {ė* : List USubExp'}
              → (ė⇒* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
              → All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*
    ⇒sτ→↬⇒sτ* []                 = []
    ⇒sτ→↬⇒sτ* (⟨ τ , e⇒ ⟩ ∷ ė⇒*) = ⟨ τ , ⇒τ→↬⇒τ e⇒ ⟩ ∷ ⇒sτ→↬⇒sτ* ė⇒*

    ⇐τ→↬⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇐ τ
           → Σ[ ě ∈ Γ ⊢⇐ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇐ ě ∣ 𝕞
    ⇐τ→↬⇐τ {e = -λ x ∶ τ ∙ e ^ u}   (UALam τ₃▸ τ~τ₁ e⇐τ₂)
      with ⟨ ě , ⟨ _ , e↬⇐ě ⟩ ⟩ ← ⇐sτ→↬⇐sτ e⇐τ₂
         = ⟨ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u , ⟨ _ , MKALam1 τ₃▸ τ~τ₁ e↬⇐ě ⟩ ⟩
    ⇐τ→↬⇐τ {e = e}              (UASubsume e⇒τ' τ~τ' su)
      with ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ← ⇒τ→↬⇒τ e⇒τ'
         = ⟨ ⊢∙ ě [ τ~τ' ∙ USu→MSu su e↬⇒ě ] , ⟨ _ , MKASubsume e↬⇒ě τ~τ' su ⟩ ⟩

    ⇐sτ→↬⇐sτ : ∀ {Γ : Ctx} {e : USubExp} {τ : Typ}
             → Γ ⊢s e ⇐ τ
             → Σ[ ě ∈ Γ ⊢⇐s τ ] ∃[ 𝕞 ] Γ ⊢s e ↬⇐ ě ∣ 𝕞
    ⇐sτ→↬⇐sτ (USubASubsume e⇒τ' τ~τ')
      with ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ← ⇒sτ→↬⇒sτ e⇒τ'
         = ⟨ ⊢∙ ě [ τ~τ' ] , ⟨ _ , MKSubASubsume e↬⇒ě τ~τ' ⟩ ⟩

  mutual
    -- marking synthesizes the same type as synthesis
    ⇒-↬-≡ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {τ' : Typ} {ě : Γ ⊢⇒ τ'} {𝕞 : MultiParents}
           → Γ ⊢ e ⇒ τ
           → Γ ⊢ e ↬⇒ ě ∣ 𝕞
           → τ ≡ τ'
    ⇒-↬-≡ (USVar ∋x)         (MKSVar ∋x')                = ∋→τ-≡ ∋x ∋x'
    ⇒-↬-≡ (USVar {τ = τ} ∋x) (MKSFree ∌y)                = ⊥-elim (∌y ⟨ τ , ∋x ⟩)
    ⇒-↬-≡ (USLam e⇒τ) (MKSLam e↬⇒ě)
      rewrite ⇒s-↬s-≡ e⇒τ e↬⇒ě                           = refl
    ⇒-↬-≡ (USAp e⇒τ τ▸ e₁⇐τ₁) (MKSAp1 e↬⇒ě τ▸' e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e⇒τ e↬⇒ě
      with refl ← ▸-→-unicity τ▸ τ▸'                     = refl
    ⇒-↬-≡ (USAp {τ₁ = τ₁} {τ₂ = τ₂} e⇒τ τ▸ e₁⇐τ₁) (MKSAp2 e↬⇒ě τ!▸ e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e⇒τ e↬⇒ě                       = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ⇒-↬-≡ USNum                  MKSNum                  = refl
    ⇒-↬-≡ (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) = refl
    ⇒-↬-≡ USMultiParent          MKSMultiParent          = refl
    ⇒-↬-≡ USUnicycle             MKSUnicycle             = refl

    ⇒s-↬s-≡ : ∀ {Γ e τ τ'} {ě : Γ ⊢⇒s τ'} {𝕞 : MultiParents}
            → Γ ⊢s e ⇒ τ
            → Γ ⊢s e ↬⇒ ě ∣ 𝕞
            → τ ≡ τ'
    ⇒s-↬s-≡ USubSHole           MKSubSHole             = refl
    ⇒s-↬s-≡ (USubSJust e⇒τ)     (MKSubSJust e↬⇒ě)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě                       = refl
    ⇒s-↬s-≡ (USubSConflict ė⇒*) (MKSubSConflict ė↬⇒ě*) = refl

  mutual
    -- marking well-typed terms produces no marks
    ⇒τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ} {𝕞 : MultiParents}
                → Γ ⊢ e ⇒ τ
                → Γ ⊢ e ↬⇒ ě ∣ 𝕞
                → Markless⇒ ě
    ⇒τ→markless (USVar ∋x) (MKSVar ∋x')
         = MLSVar
    ⇒τ→markless (USVar ∋x) (MKSFree ∌y)
         = ⊥-elim (∌y ⟨ unknown , ∋x ⟩)
    ⇒τ→markless (USLam e⇒τ) (MKSLam e↬⇒ě)
         = MLSLam (⇒sτ→markless e⇒τ e↬⇒ě)
    ⇒τ→markless (USAp e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp1 e₁↬⇒ě₁ τ▸'  e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e₁⇒τ e₁↬⇒ě₁
      with refl ← ▸-→-unicity τ▸ τ▸'
         = MLSAp (⇒sτ→markless e₁⇒τ e₁↬⇒ě₁) (⇐sτ→markless e₂⇐τ₁ e₂↬⇐ě₂)
    ⇒τ→markless (USAp {τ₁ = τ₁} e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp2 e₁↬⇒ě₁ τ!▸' e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e₁⇒τ e₁↬⇒ě₁
         = ⊥-elim (τ!▸' ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ⇒τ→markless USNum MKSNum
         = MLSNum
    ⇒τ→markless (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
         = MLSPlus (⇐sτ→markless e₁⇐num e₁↬⇐ě₁) (⇐sτ→markless e₂⇐num e₂↬⇐ě₂)
    ⇒τ→markless USMultiParent MKSMultiParent
         = MLSMultiParent
    ⇒τ→markless USUnicycle MKSUnicycle
         = MLSUnicycle

    ⇒sτ→markless : ∀ {Γ e τ} {ě : Γ ⊢⇒s τ} {𝕞 : MultiParents}
                 → Γ ⊢s e ⇒ τ
                 → Γ ⊢s e ↬⇒ ě ∣ 𝕞
                 → Markless⇒s ě
    ⇒sτ→markless USubSHole MKSubSHole = MLSubSHole
    ⇒sτ→markless (USubSJust e⇒τ) (MKSubSJust e↬⇒ě)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě      = MLSubSJust (⇒τ→markless e⇒τ e↬⇒ě)
    ⇒sτ→markless (USubSConflict ė⇒*) (MKSubSConflict ė↬⇒ě*) = MLSubSConflict (⇒sτ→markless* ė⇒* ė↬⇒ě*)

    ⇒sτ→markless* : ∀ {Γ ė*}
                  → (ė⇒* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
                  → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*)
                  → All (λ { ⟨ _ , ⟨ _ , ě ⟩ ⟩ → Markless⇒ ě }) (MKSubSConflictChildren ė↬⇒ě*)
    ⇒sτ→markless* [] [] = []
    ⇒sτ→markless* (⟨ _ , e⇒ ⟩ ∷ ė⇒*) (⟨ _ , ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ∷ ė↬⇒ě*)
      with refl ← ⇒-↬-≡ e⇒ e↬⇒ě
         = ⇒τ→markless e⇒ e↬⇒ě ∷ ⇒sτ→markless* ė⇒* ė↬⇒ě*

    ⇐τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ} {𝕞 : MultiParents}
                → Γ ⊢ e ⇐ τ
                → Γ ⊢ e ↬⇐ ě ∣ 𝕞
                → Markless⇐ ě
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam1 τ₃▸' τ~τ₁' e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸'
         = MLALam (⇐sτ→markless e⇐τ e↬⇐ě)
    ⇐τ→markless (UALam {τ₁ = τ₁} {τ₂ = τ₂} τ₃▸ τ~τ₁ e⇐τ) (MKALam2 τ₃!▸ e↬⇐ě)
         = ⊥-elim (τ₃!▸ ⟨ τ₁ , ⟨ τ₂ , τ₃▸ ⟩ ⟩)
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam3 τ₃▸' τ~̸τ₁ e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸'
         = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ⇐τ→markless (UASubsume e⇒τ' τ~τ' su) (MKAInconsistentTypes e↬⇒ě τ~̸τ' su')
      with refl ← ⇒-↬-≡ e⇒τ' e↬⇒ě
         = ⊥-elim (τ~̸τ' τ~τ')
    ⇐τ→markless (UASubsume e⇒τ' τ~τ' su) (MKASubsume e↬⇒ě τ~τ'' su')
      with refl ← ⇒-↬-≡ e⇒τ' e↬⇒ě
         = MLASubsume (⇒τ→markless e⇒τ' e↬⇒ě)

    ⇐sτ→markless : ∀ {Γ e τ} {ě : Γ ⊢⇐s τ} {𝕞 : MultiParents}
                 → Γ ⊢s e ⇐ τ
                 → Γ ⊢s e ↬⇐ ě ∣ 𝕞
                 → Markless⇐s ě
    ⇐sτ→markless (USubASubsume e⇒τ' τ~τ') (MKSubASubsume e↬⇒ě τ~τ'')
      with refl ← ⇒s-↬s-≡ e⇒τ' e↬⇒ě
         = MLSubASubsume (⇒sτ→markless e⇒τ' e↬⇒ě)
    ⇐sτ→markless (USubASubsume e⇒τ' τ~τ') (MKSubAInconsistentTypes e↬⇒ě τ~̸τ')
      with refl ← ⇒s-↬s-≡ e⇒τ' e↬⇒ě
         = ⊥-elim (τ~̸τ' τ~τ')

  mutual
    -- synthetically marking an expression into a markless expression and a type implies the original synthesizes that type
    ↬⇒τ-markless→⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ} {𝕞 : MultiParents}
                    → Γ ⊢ e ↬⇒ ě ∣ 𝕞
                    → Markless⇒ ě
                    → Γ ⊢ e ⇒ τ
    ↬⇒τ-markless→⇒τ (MKSVar ∋x) less = USVar ∋x
    ↬⇒τ-markless→⇒τ (MKSLam e↬⇒ě) (MLSLam less)
      with e⇒τ ← ↬⇒sτ-markless→⇒sτ e↬⇒ě less
         = USLam e⇒τ
    ↬⇒τ-markless→⇒τ (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MLSAp less₁ less₂)
      with e₁⇒τ  ← ↬⇒sτ-markless→⇒sτ e₁↬⇒ě₁ less₁
         | e₂⇐τ₁ ← ↬⇐sτ-markless→⇐sτ e₂↬⇐ě₂ less₂
         = USAp e₁⇒τ τ▸ e₂⇐τ₁
    ↬⇒τ-markless→⇒τ MKSNum MLSNum = USNum
    ↬⇒τ-markless→⇒τ (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MLSPlus less₁ less₂)
      with e₁⇐τ₁ ← ↬⇐sτ-markless→⇐sτ e₁↬⇐ě₁ less₁
         | e₂⇐τ₂ ← ↬⇐sτ-markless→⇐sτ e₂↬⇐ě₂ less₂
         = USPlus e₁⇐τ₁ e₂⇐τ₂
    ↬⇒τ-markless→⇒τ MKSMultiParent MLSMultiParent = USMultiParent
    ↬⇒τ-markless→⇒τ MKSUnicycle    MLSUnicycle    = USUnicycle

    ↬⇒sτ-markless→⇒sτ : ∀ {Γ e τ} {ě : Γ ⊢⇒s τ} {𝕞 : MultiParents}
                    → Γ ⊢s e ↬⇒ ě ∣ 𝕞
                    → Markless⇒s ě
                    → Γ ⊢s e ⇒ τ
    ↬⇒sτ-markless→⇒sτ MKSubSHole             MLSubSHole             = USubSHole
    ↬⇒sτ-markless→⇒sτ (MKSubSJust e↬⇒ě)      (MLSubSJust less)      = USubSJust (↬⇒τ-markless→⇒τ e↬⇒ě less)
    ↬⇒sτ-markless→⇒sτ (MKSubSConflict ė↬⇒ě*) (MLSubSConflict less*) = USubSConflict (↬⇒sτ-markless→⇒sτ* ė↬⇒ě* less*)

    ↬⇒sτ-markless→⇒sτ* : ∀ {Γ ė*}
                       → (ė↬⇒ě* : All (λ (⟨ _ , e ⟩) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] ∃[ 𝕞 ] Γ ⊢ e ↬⇒ ě ∣ 𝕞) ė*)
                       → (less* : All (λ { ⟨ _ , ⟨ _ , ě ⟩ ⟩ → Markless⇒ ě }) (MKSubSConflictChildren ė↬⇒ě*))
                       → All (λ (⟨ _ , e ⟩) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*
    ↬⇒sτ-markless→⇒sτ* []                                     []             = []
    ↬⇒sτ-markless→⇒sτ* (⟨ τ , ⟨ ě , ⟨ _ , e↬⇒ě ⟩ ⟩ ⟩ ∷ ė↬⇒ě*) (less ∷ less*) = ⟨ τ , ↬⇒τ-markless→⇒τ e↬⇒ě less ⟩ ∷ ↬⇒sτ-markless→⇒sτ* ė↬⇒ě* less*

    -- analytically marking an expression into a markless expression against a type implies the original analyzes against type
    ↬⇐τ-markless→⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ} {𝕞 : MultiParents}
                    → Γ ⊢ e ↬⇐ ě ∣ 𝕞
                    → Markless⇐ ě
                    → Γ ⊢ e ⇐ τ
    ↬⇐τ-markless→⇐τ (MKALam1 τ₃▸ τ~τ₁ e↬⇐ě) (MLALam less)
      with e⇐τ₂ ← ↬⇐sτ-markless→⇐sτ e↬⇐ě less
         = UALam τ₃▸ τ~τ₁ e⇐τ₂
    ↬⇐τ-markless→⇐τ (MKASubsume e↬⇒ě τ~τ' su) (MLASubsume less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = UASubsume e⇒τ τ~τ' su

    ↬⇐sτ-markless→⇐sτ : ∀ {Γ e τ} {ě : Γ ⊢⇐s τ} {𝕞 : MultiParents}
                    → Γ ⊢s e ↬⇐ ě ∣ 𝕞
                    → Markless⇐s ě
                    → Γ ⊢s e ⇐ τ
    ↬⇐sτ-markless→⇐sτ (MKSubASubsume e↬⇒ě τ~τ') (MLSubASubsume less)
      with e⇒τ ← ↬⇒sτ-markless→⇒sτ e↬⇒ě less = USubASubsume e⇒τ τ~τ'

  mutual
    -- ill-typed expressions are marked into non-markless expressions
    ¬⇒τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ' : Typ} {ě : Γ ⊢⇒ τ'} {𝕞 : MultiParents}
                  → ¬ (Σ[ τ ∈ Typ ] Γ ⊢ e ⇒ τ)
                  → Γ ⊢ e ↬⇒ ě ∣ 𝕞
                  → ¬ (Markless⇒ ě)
    ¬⇒τ→¬markless {τ' = τ'} ¬e⇒τ e↬⇒ě less = ¬e⇒τ ⟨ τ' , ↬⇒τ-markless→⇒τ e↬⇒ě less ⟩

    ¬⇐τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ' : Typ} {ě : Γ ⊢⇐ τ'} {𝕞 : MultiParents}
                  → ¬ (Σ[ τ ∈ Typ ] Γ ⊢ e ⇐ τ)
                  → Γ ⊢ e ↬⇐ ě ∣ 𝕞
                  → ¬ (Markless⇐ ě)
    ¬⇐τ→¬markless {τ' = τ'} ¬e⇐τ e↬⇐ě less = ¬e⇐τ ⟨ τ' , ↬⇐τ-markless→⇐τ e↬⇐ě less ⟩
