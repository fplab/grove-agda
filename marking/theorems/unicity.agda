open import marking.prelude
open import marking.definitions

open import marking.theorems.marking

module marking.theorems.unicity where
  ↬⇒-τ-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : Γ ⊢⇒ τ₁} {ě₂ : Γ ⊢⇒ τ₂}
               → Γ ⊢ e ↬⇒ ě₁
               → Γ ⊢ e ↬⇒ ě₂
               → τ₁ ≡ τ₂
  ↬⇒-τ-unicity           MKSHole      MKSHole       = refl
  ↬⇒-τ-unicity           (MKSVar ∋x)  (MKSVar ∋x′)  = ∋→τ-≡ ∋x ∋x′
  ↬⇒-τ-unicity {τ₁ = τ₁} (MKSVar ∋x)  (MKSFree ∌x)  = ⊥-elim (∌x ⟨ τ₁ , ∋x ⟩)
  ↬⇒-τ-unicity {τ₂ = τ₂} (MKSFree ∌x) (MKSVar ∋x)   = ⊥-elim (∌x ⟨ τ₂ , ∋x ⟩)
  ↬⇒-τ-unicity           (MKSFree ∌x) (MKSFree ∌x′) = refl
  ↬⇒-τ-unicity (MKSLam e↬⇒ě) (MKSLam e↬⇒ě′)
    rewrite ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = refl
  ↬⇒-τ-unicity (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp1 e₁↬⇒ě₁′ τ′▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = proj₂ (-→-inj (▸-→-unicity τ▸ τ′▸))
  ↬⇒-τ-unicity (MKSAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁′ τ▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′) = refl
  ↬⇒-τ-unicity MKSNum                  MKSNum                    = refl
  ↬⇒-τ-unicity (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MKSPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′) = refl

  mutual
    ↬⇒-ě-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě₁ : Γ ⊢⇒ τ} {ě₂ : Γ ⊢⇒ τ}
                 → Γ ⊢ e ↬⇒ ě₁
                 → Γ ⊢ e ↬⇒ ě₂
                 → ě₁ ≡ ě₂
    ↬⇒-ě-unicity MKSHole MKSHole = refl
    ↬⇒-ě-unicity (MKSVar ∋x) (MKSVar ∋x′)
      rewrite ∋-≡ ∋x ∋x′ = refl
    ↬⇒-ě-unicity (MKSVar ∋x) (MKSFree ∌x) = ⊥-elim (∌x ⟨ unknown , ∋x ⟩)
    ↬⇒-ě-unicity (MKSFree ∌x) (MKSVar ∋x) = ⊥-elim (∌x ⟨ unknown , ∋x ⟩)
    ↬⇒-ě-unicity (MKSFree ∌x) (MKSFree ∌x′)
      rewrite assimilation ∌x ∌x′ = refl
    ↬⇒-ě-unicity (MKSLam e↬⇒ě) (MKSLam e↬⇒ě′)
      rewrite ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′ = refl
    ↬⇒-ě-unicity (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp1 e₁↬⇒ě₁′ τ▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ▸-→-unicity τ▸ τ▸′
      with refl ← ▸-→-≡ τ▸ τ▸′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇒-ě-unicity (MKSAp1 {τ₁ = τ₁} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp1 {τ₁ = τ₁} e₁↬⇒ě₁′ τ▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′
            | !▸-→-≡ τ!▸ τ!▸′ = refl
    ↬⇒-ě-unicity MKSNum MKSNum = refl
    ↬⇒-ě-unicity (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MKSPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′)
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl

    USu→MSu-unicity : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {ě : Γ ⊢⇒ τ}
                      → (s : USubsumable e)
                      → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
                      → (e↬⇒ě′ : Γ ⊢ e ↬⇒ ě)
                      → USu→MSu s e↬⇒ě ≡ USu→MSu s e↬⇒ě′
    USu→MSu-unicity USuHole  MKSHole         _ = refl
    USu→MSu-unicity USuVar   (MKSVar _)      _ = refl
    USu→MSu-unicity USuVar   (MKSFree _)     _ = refl
    USu→MSu-unicity USuAp    (MKSAp1 _ _ _)  _ = refl
    USu→MSu-unicity USuAp    (MKSAp2 _ _ _)  _ = refl
    USu→MSu-unicity USuNum   MKSNum          _ = refl
    USu→MSu-unicity USuPlus  (MKSPlus _ _)   _ = refl

    ↬⇐-ě-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě₁ : Γ ⊢⇐ τ} {ě₂ : Γ ⊢⇐ τ}
                 → Γ ⊢ e ↬⇐ ě₁
                 → Γ ⊢ e ↬⇐ ě₂
                 → ě₁ ≡ ě₂
    ↬⇐-ě-unicity (MKALam1 τ▸ τ₁~τ₂ e↬⇐ě) (MKALam1 τ▸′ τ₁~τ₂′ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′
      rewrite ▸-→-≡ τ▸ τ▸′
            | ~-≡ τ₁~τ₂ τ₁~τ₂′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (MKALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě) (MKALam2 τ!▸ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam1 τ▸ τ~τ₁ e↬⇐ě) (MKALam3 τ▸′ τ~̸τ₁ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′ = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam2 τ!▸′ e↬⇐ě′)
      rewrite !▸-→-≡ τ!▸ τ!▸′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam3 τ▸ τ~̸τ₁ e↬⇐ě) (MKALam1 τ▸′ τ~τ₁ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′ = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (MKALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě) (MKALam2 τ!▸ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam3 τ▸ τ~̸τ₁ e↬⇐ě) (MKALam3 τ▸′ τ~̸τ₁′ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′
      rewrite ▸-→-≡ τ▸ τ▸′
            | ~̸-≡ τ~̸τ₁ τ~̸τ₁′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuHole) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuHole)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuHole e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuVar) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuVar e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuAp) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuAp e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuNum) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuNum e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuPlus) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuPlus e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ s) (MKASubsume e↬⇒ě′ τ~τ′ s′)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = ⊥-elim (τ~̸τ′ τ~τ′)
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ s) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′ s′)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = ⊥-elim (τ~̸τ′ τ~τ′)
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuHole) (MKASubsume e↬⇒ě′ τ~τ′′ USuHole)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuHole e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuVar) (MKASubsume e↬⇒ě′ τ~τ′′ USuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuVar e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuAp) (MKASubsume e↬⇒ě′ τ~τ′′ USuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuAp e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuNum) (MKASubsume e↬⇒ě′ τ~τ′′ USuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuNum e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuPlus) (MKASubsume e↬⇒ě′ τ~τ′′ USuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuPlus e↬⇒ě e↬⇒ě′ = refl

  ↬⇒-unicity-sig : ∀ {Γ : Ctx} {τ₁ τ₂ : Typ} → τ₁ ≡ τ₂ → Γ ⊢⇒ τ₁ → Γ ⊢⇒ τ₂ → Set
  ↬⇒-unicity-sig refl e₁ e₂ = e₁ ≡ e₂

  ↬⇒-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : Γ ⊢⇒ τ₁} {ě₂ : Γ ⊢⇒ τ₂}
             → (e↬⇒ě₁ : Γ ⊢ e ↬⇒ ě₁)
             → (e↬⇒ě₂ : Γ ⊢ e ↬⇒ ě₂)
             → Σ[ τ₁≡τ₂ ∈ τ₁ ≡ τ₂ ] ↬⇒-unicity-sig τ₁≡τ₂ ě₁ ě₂
  ↬⇒-unicity e↬⇒ě₁ e↬⇒ě₂
    with refl ← ↬⇒-τ-unicity e↬⇒ě₁ e↬⇒ě₂
       = ⟨ refl , ↬⇒-ě-unicity e↬⇒ě₁ e↬⇒ě₂ ⟩

  ↬⇐-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě₁ : Γ ⊢⇐ τ} {ě₂ : Γ ⊢⇐ τ}
             → Γ ⊢ e ↬⇐ ě₁
             → Γ ⊢ e ↬⇐ ě₂
             → ě₁ ≡ ě₂
  ↬⇐-unicity = ↬⇐-ě-unicity
