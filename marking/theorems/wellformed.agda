open import marking.prelude
open import marking.definitions

module marking.theorems.wellformed where
  mutual
    -- marking preserves syntactic structure
    ↬⇒□ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ}
        → Γ ⊢ e ↬⇒ ě
        → ě ⇒□ ≡ e
    ↬⇒□ MKSHole          = refl
    ↬⇒□ (MKSVar ∋x)      = refl
    ↬⇒□ (MKSFree ∌x)     = refl
    ↬⇒□ (MKSLam e↬⇒ě)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇒□ (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ MKSNum           = refl
    ↬⇒□ (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl

    ↬⇐□ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ}
        → Γ ⊢ e ↬⇐ ě
        → ě ⇐□ ≡ e
    ↬⇐□ (MKALam1 τ₁▸ τ~τ₁ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (MKALam2 τ₁!▸ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (MKALam3 τ₁▸ τ~̸τ₁ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (MKAInconsistentTypes e↬⇒ě τ~̸τ′ s)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇐□ (MKASubsume e↬⇒ě τ~τ′ s)
      rewrite ↬⇒□ e↬⇒ě   = refl

  mutual
    -- well-typed unmarked expression are marked into marked expressions of the same type
    ⇒τ→↬⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇒ τ
           → Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě
    ⇒τ→↬⇒τ {e = -⦇-⦈^ u}        USHole     = ⟨ ⊢⦇-⦈^ u , MKSHole ⟩
    ⇒τ→↬⇒τ {e = - x}            (USVar ∋x) = ⟨ ⊢ ∋x , MKSVar ∋x ⟩
    ⇒τ→↬⇒τ {e = -λ x ∶ τ ∙ e}   (USLam e⇒τ)
      with ⟨ ě  , e↬⇒ě   ⟩ ← ⇒τ→↬⇒τ e⇒τ    = ⟨ ⊢λ x ∶ τ ∙ ě , MKSLam e↬⇒ě ⟩
    ⇒τ→↬⇒τ {e = - e₁ ∙ e₂} (USAp e₁⇒τ τ▸ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸ ] , MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂ ⟩
    ⇒τ→↬⇒τ {e = -ℕ n}           USNum      = ⟨ ⊢ℕ n , MKSNum ⟩
    ⇒τ→↬⇒τ {e = - e₁ + e₂}      (USPlus e₁⇐num e₂⇐num)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐num
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐num = ⟨ ⊢ ě₁ + ě₂ , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩

    ⇐τ→↬⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇐ τ
           → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě
    ⇐τ→↬⇐τ {e = -λ x ∶ τ ∙ e}   (UALam τ₃▸ τ~τ₁ e⇐τ₂)
      with ⟨ ě , e↬⇐ě ⟩ ← ⇐τ→↬⇐τ e⇐τ₂     = ⟨ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] , MKALam1 τ₃▸ τ~τ₁ e↬⇐ě ⟩
    ⇐τ→↬⇐τ {e = e}              (UASubsume e⇒τ′ τ~τ′ su)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ′     = ⟨ ⊢∙ ě [ τ~τ′ ∙ USu→MSu su e↬⇒ě ] , MKASubsume e↬⇒ě τ~τ′ su ⟩

  -- marking synthesizes the same type as synthesis
  ⇒-↬-≡ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {τ′ : Typ} {ě : Γ ⊢⇒ τ′}
         → Γ ⊢ e ⇒ τ
         → Γ ⊢ e ↬⇒ ě
         → τ ≡ τ′
  ⇒-↬-≡ USHole MKSHole
       = refl
  ⇒-↬-≡ (USVar ∋x) (MKSVar ∋x′)
       = ∋→τ-≡ ∋x ∋x′
  ⇒-↬-≡ (USVar {τ = τ} ∋x) (MKSFree ∌y)
       = ⊥-elim (∌y ⟨ τ , ∋x ⟩)
  ⇒-↬-≡ (USLam e⇒τ) (MKSLam e↬⇒ě)
    rewrite ⇒-↬-≡ e⇒τ e↬⇒ě
       = refl
  ⇒-↬-≡ (USAp e⇒τ τ▸ e₁⇐τ₁) (MKSAp1 e↬⇒ě τ▸′ e₂↬⇐ě₂)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
    with refl ← ▸-→-unicity τ▸ τ▸′
       = refl
  ⇒-↬-≡ (USAp {τ₁ = τ₁} {τ₂ = τ₂} e⇒τ τ▸ e₁⇐τ₁) (MKSAp2 e↬⇒ě τ!▸ e₂↬⇐ě₂)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
       = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ⇒-↬-≡ USNum MKSNum
       = refl
  ⇒-↬-≡ (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
       = refl

  mutual
    -- marking well-typed terms produces no marks
    ⇒τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ}
                → Γ ⊢ e ⇒ τ
                → Γ ⊢ e ↬⇒ ě
                → Markless⇒ ě
    ⇒τ→markless USHole MKSHole
         = MLSHole
    ⇒τ→markless (USVar ∋x) (MKSVar ∋x′)
         = MLSVar
    ⇒τ→markless (USVar ∋x) (MKSFree ∌y)
         = ⊥-elim (∌y ⟨ unknown , ∋x ⟩)
    ⇒τ→markless (USLam e⇒τ) (MKSLam e↬⇒ě)
         = MLSLam (⇒τ→markless e⇒τ e↬⇒ě)
    ⇒τ→markless (USAp e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp1 e₁↬⇒ě₁ τ▸′  e₂↬⇐ě₂)
      with refl ← ⇒-↬-≡ e₁⇒τ e₁↬⇒ě₁
      with refl ← ▸-→-unicity τ▸ τ▸′
         = MLSAp (⇒τ→markless e₁⇒τ e₁↬⇒ě₁) (⇐τ→markless e₂⇐τ₁ e₂↬⇐ě₂)
    ⇒τ→markless (USAp {τ₁ = τ₁} e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp2 e₁↬⇒ě₁ τ!▸′ e₂↬⇐ě₂)
      with refl ← ⇒-↬-≡ e₁⇒τ e₁↬⇒ě₁
         = ⊥-elim (τ!▸′ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ⇒τ→markless USNum MKSNum
         = MLSNum
    ⇒τ→markless (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
         = MLSPlus (⇐τ→markless e₁⇐num e₁↬⇐ě₁) (⇐τ→markless e₂⇐num e₂↬⇐ě₂)

    ⇐τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ}
                → Γ ⊢ e ⇐ τ
                → Γ ⊢ e ↬⇐ ě
                → Markless⇐ ě
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam1 τ₃▸′ τ~τ₁′ e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸′
         = MLALam (⇐τ→markless e⇐τ e↬⇐ě)
    ⇐τ→markless (UALam {τ₁ = τ₁} {τ₂ = τ₂} τ₃▸ τ~τ₁ e⇐τ) (MKALam2 τ₃!▸ e↬⇐ě)
         = ⊥-elim (τ₃!▸ ⟨ τ₁ , ⟨ τ₂ , τ₃▸ ⟩ ⟩)
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam3 τ₃▸′ τ~̸τ₁ e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸′
         = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ⇐τ→markless (UASubsume e⇒τ′ τ~τ′ su) (MKAInconsistentTypes e↬⇒ě τ~̸τ′ su′)
      with refl ← ⇒-↬-≡ e⇒τ′ e↬⇒ě
         = ⊥-elim (τ~̸τ′ τ~τ′)
    ⇐τ→markless (UASubsume e⇒τ′ τ~τ′ su) (MKASubsume e↬⇒ě τ~τ′′ su′)
      with refl ← ⇒-↬-≡ e⇒τ′ e↬⇒ě
         = MLASubsume (⇒τ→markless e⇒τ′ e↬⇒ě)

  mutual
    -- synthetically marking an expression into a markless expression and a type implies the original synthesizes that type
    ↬⇒τ-markless→⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ}
                    → Γ ⊢ e ↬⇒ ě
                    → Markless⇒ ě
                    → Γ ⊢ e ⇒ τ
    ↬⇒τ-markless→⇒τ MKSHole less = USHole
    ↬⇒τ-markless→⇒τ (MKSVar ∋x) less = USVar ∋x
    ↬⇒τ-markless→⇒τ (MKSLam e↬⇒ě) (MLSLam less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = USLam e⇒τ
    ↬⇒τ-markless→⇒τ (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MLSAp less₁ less₂)
      with e₁⇒τ  ← ↬⇒τ-markless→⇒τ e₁↬⇒ě₁ less₁
         | e₂⇐τ₁ ← ↬⇐τ-markless→⇐τ e₂↬⇐ě₂ less₂
         = USAp e₁⇒τ τ▸ e₂⇐τ₁
    ↬⇒τ-markless→⇒τ MKSNum MLSNum = USNum
    ↬⇒τ-markless→⇒τ (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MLSPlus less₁ less₂)
      with e₁⇐τ₁ ← ↬⇐τ-markless→⇐τ e₁↬⇐ě₁ less₁
         | e₂⇐τ₂ ← ↬⇐τ-markless→⇐τ e₂↬⇐ě₂ less₂
         = USPlus e₁⇐τ₁ e₂⇐τ₂

    -- analytically marking an expression into a markless expression against a type implies the original analyzes against type
    ↬⇐τ-markless→⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ}
                    → Γ ⊢ e ↬⇐ ě
                    → Markless⇐ ě
                    → Γ ⊢ e ⇐ τ
    ↬⇐τ-markless→⇐τ (MKALam1 τ₃▸ τ~τ₁ e↬⇐ě) (MLALam less)
      with e⇐τ₂ ← ↬⇐τ-markless→⇐τ e↬⇐ě less
         = UALam τ₃▸ τ~τ₁ e⇐τ₂
    ↬⇐τ-markless→⇐τ (MKASubsume e↬⇒ě τ~τ′ su) (MLASubsume less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = UASubsume e⇒τ τ~τ′ su

  mutual
    -- ill-typed expressions are marked into non-markless expressions
    ¬⇒τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ′ : Typ} {ě : Γ ⊢⇒ τ′}
                  → ¬ (Σ[ τ ∈ Typ ] Γ ⊢ e ⇒ τ)
                  → Γ ⊢ e ↬⇒ ě
                  → ¬ (Markless⇒ ě)
    ¬⇒τ→¬markless {τ′ = τ′} ¬e⇒τ e↬⇒ě less = ¬e⇒τ ⟨ τ′ , ↬⇒τ-markless→⇒τ e↬⇒ě less ⟩

    ¬⇐τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ′ : Typ} {ě : Γ ⊢⇐ τ′}
                  → ¬ (Σ[ τ ∈ Typ ] Γ ⊢ e ⇐ τ)
                  → Γ ⊢ e ↬⇐ ě
                  → ¬ (Markless⇐ ě)
    ¬⇐τ→¬markless {τ′ = τ′} ¬e⇐τ e↬⇐ě less = ¬e⇐τ ⟨ τ′ , ↬⇐τ-markless→⇐τ e↬⇐ě less ⟩
