open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax; Σ-syntax)

open import Grove.Prelude
open import Grove.Marking.STyp
open import Grove.Marking.Ctx
open import Grove.Marking.UExp
open import Grove.Marking.MExp
open import Grove.Marking.Marking

module Grove.Marking.Properties.Unicity where
  mutual
    ↬⇒-τ-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : STyp} {ě₁ : Γ ⊢⇒ τ₁} {ě₂ : Γ ⊢⇒ τ₂}
                 → Γ ⊢ e ↬⇒ ě₁
                 → Γ ⊢ e ↬⇒ ě₂
                 → τ₁ ≡ τ₂
    ↬⇒-τ-unicity           (MKSVar ∋x)  (MKSVar ∋x')  = ∋→τ-≡ ∋x ∋x'
    ↬⇒-τ-unicity {τ₁ = τ₁} (MKSVar ∋x)  (MKSFree ∌x)  = ⊥-elim (∌x (τ₁ , ∋x))
    ↬⇒-τ-unicity {τ₂ = τ₂} (MKSFree ∌x) (MKSVar ∋x)   = ⊥-elim (∌x (τ₂ , ∋x))
    ↬⇒-τ-unicity           (MKSFree ∌x) (MKSFree ∌x') = refl
    ↬⇒-τ-unicity (MKSLam e↬⇒ě) (MKSLam e↬⇒ě')
      rewrite ↬⇒s-τ-unicity e↬⇒ě e↬⇒ě' = refl
    ↬⇒-τ-unicity (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp1 e₁↬⇒ě₁' τ'▸ e₂↬⇐ě₂')
      with refl ← ↬⇒s-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁' = proj₂ (-→-inj (▸-→-unicity τ▸ τ'▸))
    ↬⇒-τ-unicity (MKSAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁' τ!▸ e₂↬⇐ě₂')
      with refl ← ↬⇒s-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁' = ⊥-elim (τ!▸ (τ₁ , τ₂ , τ▸))
    ↬⇒-τ-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁' τ▸ e₂↬⇐ě₂')
      with refl ← ↬⇒s-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁' = ⊥-elim (τ!▸ (τ₁ , τ₂ , τ▸))
    ↬⇒-τ-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁' τ!▸' e₂↬⇐ě₂') = refl
    ↬⇒-τ-unicity MKSNum                  MKSNum                    = refl
    ↬⇒-τ-unicity (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MKSPlus e₁↬⇐ě₁' e₂↬⇐ě₂') = refl
    ↬⇒-τ-unicity MKSMultiLocationConflict          MKSMultiLocationConflict            = refl
    ↬⇒-τ-unicity MKSCycleLocationConflict             MKSCycleLocationConflict               = refl

    ↬⇒s-τ-unicity : ∀ {Γ : Ctx} {e : UChildExp} {τ₁ τ₂ : STyp} {ě₁ : Γ ⊢⇒s τ₁} {ě₂ : Γ ⊢⇒s τ₂}
                  → Γ ⊢s e ↬⇒ ě₁
                  → Γ ⊢s e ↬⇒ ě₂
                  → τ₁ ≡ τ₂
    ↬⇒s-τ-unicity MKSHole             MKSHole              = refl
    ↬⇒s-τ-unicity (MKSOnly e↬⇒ě)      (MKSOnly e↬⇒ě')
      rewrite ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'                            = refl
    ↬⇒s-τ-unicity (MKSLocalConflict ė↬⇒ě*) (MKSLocalConflict ė↬⇒ě*₁) = refl

  mutual
    ↬⇒-ě-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě₁ : Γ ⊢⇒ τ} {ě₂ : Γ ⊢⇒ τ}
                 → Γ ⊢ e ↬⇒ ě₁
                 → Γ ⊢ e ↬⇒ ě₂
                 → ě₁ ≡ ě₂
    ↬⇒-ě-unicity (MKSVar ∋x) (MKSVar ∋x')
      rewrite ∋-≡ ∋x ∋x' = refl
    ↬⇒-ě-unicity (MKSVar ∋x) (MKSFree ∌x) = ⊥-elim (∌x (unknown , ∋x))
    ↬⇒-ě-unicity (MKSFree ∌x) (MKSVar ∋x) = ⊥-elim (∌x (unknown , ∋x))
    ↬⇒-ě-unicity (MKSFree ∌x) (MKSFree ∌x')
      rewrite assimilation ∌x ∌x' = refl
    ↬⇒-ě-unicity (MKSLam e↬⇒ě) (MKSLam e↬⇒ě')
      rewrite ↬⇒s-ě-unicity e↬⇒ě e↬⇒ě' = refl
    ↬⇒-ě-unicity (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp1 e₁↬⇒ě₁' τ▸' e₂↬⇐ě₂')
      with refl ← ↬⇒s-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁'
      with refl ← ▸-→-unicity τ▸ τ▸'
      with refl ← ▸-→-≡ τ▸ τ▸'
      rewrite ↬⇒s-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁'
            | ↬⇐s-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂' = refl
    ↬⇒-ě-unicity (MKSAp1 {τ₁ = τ₁} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁' τ!▸ e₂↬⇐ě₂')
      with refl ← ↬⇒s-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁' = ⊥-elim (τ!▸ (τ₁ , unknown , τ▸))
    ↬⇒-ě-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp1 {τ₁ = τ₁} e₁↬⇒ě₁' τ▸ e₂↬⇐ě₂')
      with refl ← ↬⇒s-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁' = ⊥-elim (τ!▸ (τ₁ , unknown , τ▸))
    ↬⇒-ě-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁' τ!▸' e₂↬⇐ě₂')
      with refl ← ↬⇒s-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁'
      rewrite ↬⇒s-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁'
            | ↬⇐s-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂'
            | !▸-→-≡ τ!▸ τ!▸' = refl
    ↬⇒-ě-unicity MKSNum MKSNum = refl
    ↬⇒-ě-unicity (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MKSPlus e₁↬⇐ě₁' e₂↬⇐ě₂')
      rewrite ↬⇐s-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁'
            | ↬⇐s-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂' = refl
    ↬⇒-ě-unicity MKSMultiLocationConflict MKSMultiLocationConflict = refl
    ↬⇒-ě-unicity MKSCycleLocationConflict    MKSCycleLocationConflict    = refl

    ↬⇒s-ě-unicity : ∀ {Γ : Ctx} {e : UChildExp} {τ : STyp} {ě₁ : Γ ⊢⇒s τ} {ě₂ : Γ ⊢⇒s τ}
                  → Γ ⊢s e ↬⇒ ě₁
                  → Γ ⊢s e ↬⇒ ě₂
                  → ě₁ ≡ ě₂
    ↬⇒s-ě-unicity MKSHole             MKSHole = refl
    ↬⇒s-ě-unicity (MKSOnly e↬⇒ě)      (MKSOnly e↬⇒ě')
      rewrite ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'               = refl
    ↬⇒s-ě-unicity (MKSLocalConflict ė↬⇒ě*) (MKSLocalConflict ė↬⇒ě*')
      rewrite ↬⇒s-ě-unicity* ė↬⇒ě* ė↬⇒ě*'           = refl

    ↬⇒s-ě-unicity* : ∀ {Γ} {ė* : List UChildExp'}
                   → (ė↬⇒ě*  : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
                   → (ė↬⇒ě*' : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
                   → MKSLocalConflictChildren ė↬⇒ě* ≡ MKSLocalConflictChildren ė↬⇒ě*'
    ↬⇒s-ě-unicity* [] [] = refl
    ↬⇒s-ě-unicity* ((τ , ě , e↬⇒ě) ∷ ė↬⇒ě*) ((τ' , ě' , e↬⇒ě') ∷ ė↬⇒ě*')
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
      rewrite ↬⇒s-ě-unicity* ė↬⇒ě* ė↬⇒ě*'
           = refl

    USu→MSu-unicity : ∀ {e : UExp} {Γ : Ctx} {τ : STyp} {ě : Γ ⊢⇒ τ}
                      → (s : USubsumable e)
                      → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
                      → (e↬⇒ě' : Γ ⊢ e ↬⇒ ě)
                      → USu→MSu s e↬⇒ě ≡ USu→MSu s e↬⇒ě'
    USu→MSu-unicity USuVar          (MKSVar _)      _ = refl
    USu→MSu-unicity USuVar          (MKSFree _)     _ = refl
    USu→MSu-unicity USuAp           (MKSAp1 _ _ _)  _ = refl
    USu→MSu-unicity USuAp           (MKSAp2 _ _ _)  _ = refl
    USu→MSu-unicity USuNum          MKSNum          _ = refl
    USu→MSu-unicity USuPlus         (MKSPlus _ _)   _ = refl

    ↬⇐-ě-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě₁ : Γ ⊢⇐ τ} {ě₂ : Γ ⊢⇐ τ}
                 → Γ ⊢ e ↬⇐ ě₁
                 → Γ ⊢ e ↬⇐ ě₂
                 → ě₁ ≡ ě₂
    ↬⇐-ě-unicity (MKALam1 τ▸ τ₁~τ₂ e↬⇐ě) (MKALam1 τ▸' τ₁~τ₂' e↬⇐ě')
      with refl ← ▸-→-unicity τ▸ τ▸'
      rewrite ▸-→-≡ τ▸ τ▸'
            | ~-≡ τ₁~τ₂ τ₁~τ₂'
            | ↬⇐s-ě-unicity e↬⇐ě e↬⇐ě' = refl
    ↬⇐-ě-unicity (MKALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě) (MKALam2 τ!▸ e↬⇐ě') = ⊥-elim (τ!▸ (τ₁ , τ₂ , τ▸))
    ↬⇐-ě-unicity (MKALam1 τ▸ τ~τ₁ e↬⇐ě) (MKALam3 τ▸' τ~̸τ₁ e↬⇐ě')
      with refl ← ▸-→-unicity τ▸ τ▸' = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě') = ⊥-elim (τ!▸ (τ₁ , τ₂ , τ▸))
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam2 τ!▸' e↬⇐ě')
      rewrite !▸-→-≡ τ!▸ τ!▸'
            | ↬⇐s-ě-unicity e↬⇐ě e↬⇐ě' = refl
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě') = ⊥-elim (τ!▸ (τ₁ , τ₂ , τ▸))
    ↬⇐-ě-unicity (MKALam3 τ▸ τ~̸τ₁ e↬⇐ě) (MKALam1 τ▸' τ~τ₁ e↬⇐ě')
      with refl ← ▸-→-unicity τ▸ τ▸' = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (MKALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě) (MKALam2 τ!▸ e↬⇐ě') = ⊥-elim (τ!▸ (τ₁ , τ₂ , τ▸))
    ↬⇐-ě-unicity (MKALam3 τ▸ τ~̸τ₁ e↬⇐ě) (MKALam3 τ▸' τ~̸τ₁' e↬⇐ě')
      with refl ← ▸-→-unicity τ▸ τ▸'
      rewrite ▸-→-≡ τ▸ τ▸'
            | ~̸-≡ τ~̸τ₁ τ~̸τ₁'
            | ↬⇐s-ě-unicity e↬⇐ě e↬⇐ě' = refl
    ↬⇐-ě-unicity MKAMultiLocationConflict MKAMultiLocationConflict = refl
    ↬⇐-ě-unicity MKACycleLocationConflict MKACycleLocationConflict = refl
    ↬⇐-ě-unicity (MKAInconsistentSTypes e↬⇒ě τ~̸τ' USuVar) (MKAInconsistentSTypes e↬⇒ě' τ~̸τ'' USuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~̸-≡ τ~̸τ' τ~̸τ''
      rewrite USu→MSu-unicity USuVar e↬⇒ě e↬⇒ě' = refl
    ↬⇐-ě-unicity (MKAInconsistentSTypes e↬⇒ě τ~̸τ' USuAp) (MKAInconsistentSTypes e↬⇒ě' τ~̸τ'' USuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~̸-≡ τ~̸τ' τ~̸τ''
      rewrite USu→MSu-unicity USuAp e↬⇒ě e↬⇒ě' = refl
    ↬⇐-ě-unicity (MKAInconsistentSTypes e↬⇒ě τ~̸τ' USuNum) (MKAInconsistentSTypes e↬⇒ě' τ~̸τ'' USuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~̸-≡ τ~̸τ' τ~̸τ''
      rewrite USu→MSu-unicity USuNum e↬⇒ě e↬⇒ě' = refl
    ↬⇐-ě-unicity (MKAInconsistentSTypes e↬⇒ě τ~̸τ' USuPlus) (MKAInconsistentSTypes e↬⇒ě' τ~̸τ'' USuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~̸-≡ τ~̸τ' τ~̸τ''
      rewrite USu→MSu-unicity USuPlus e↬⇒ě e↬⇒ě' = refl
    ↬⇐-ě-unicity (MKAInconsistentSTypes e↬⇒ě τ~̸τ' s) (MKASubsume e↬⇒ě' τ~τ' s')
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě' = ⊥-elim (τ~̸τ' τ~τ')
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ' s) (MKAInconsistentSTypes e↬⇒ě' τ~̸τ' s')
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě' = ⊥-elim (τ~̸τ' τ~τ')
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ' USuVar) (MKASubsume e↬⇒ě' τ~τ'' USuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~-≡ τ~τ' τ~τ''
      rewrite USu→MSu-unicity USuVar e↬⇒ě e↬⇒ě' = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ' USuAp) (MKASubsume e↬⇒ě' τ~τ'' USuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~-≡ τ~τ' τ~τ''
      rewrite USu→MSu-unicity USuAp e↬⇒ě e↬⇒ě' = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ' USuNum) (MKASubsume e↬⇒ě' τ~τ'' USuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~-≡ τ~τ' τ~τ''
      rewrite USu→MSu-unicity USuNum e↬⇒ě e↬⇒ě' = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ' USuPlus) (MKASubsume e↬⇒ě' τ~τ'' USuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě'
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě'
         | refl ← ~-≡ τ~τ' τ~τ''
      rewrite USu→MSu-unicity USuPlus e↬⇒ě e↬⇒ě' = refl

    ↬⇐s-ě-unicity : ∀ {Γ : Ctx} {e : UChildExp} {τ : STyp} {ě₁ : Γ ⊢⇐s τ} {ě₂ : Γ ⊢⇐s τ}
                 → Γ ⊢s e ↬⇐ ě₁
                 → Γ ⊢s e ↬⇐ ě₂
                 → ě₁ ≡ ě₂
    ↬⇐s-ě-unicity MKAHole             MKAHole = refl
    ↬⇐s-ě-unicity (MKAOnly e↬⇐ě)      (MKAOnly e↬⇐ě')
      rewrite ↬⇐-ě-unicity e↬⇐ě e↬⇐ě'               = refl
    ↬⇐s-ě-unicity (MKALocalConflict ė↬⇐ě*) (MKALocalConflict ė↬⇐ě*')
      rewrite ↬⇐s-ě-unicity* ė↬⇐ě* ė↬⇐ě*'           = refl

    ↬⇐s-ě-unicity* : ∀ {Γ τ} {ė* : List UChildExp'}
                   → (ė↬⇐ě*  : All (λ (_ , e) → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě) ė*)
                   → (ė↬⇐ě*' : All (λ (_ , e) → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě) ė*)
                   → MKALocalConflictChildren ė↬⇐ě* ≡ MKALocalConflictChildren ė↬⇐ě*'
    ↬⇐s-ě-unicity* [] [] = refl
    ↬⇐s-ě-unicity* ((ě , e↬⇐ě) ∷ ė↬⇐ě*) ((ě' , e↬⇐ě') ∷ ė↬⇐ě*')
      with refl ← ↬⇐-ě-unicity e↬⇐ě e↬⇐ě'
      rewrite ↬⇐s-ě-unicity* ė↬⇐ě* ė↬⇐ě*'
           = refl

  ↬⇒-unicity-sig : ∀ {Γ : Ctx} {τ₁ τ₂ : STyp} → τ₁ ≡ τ₂ → Γ ⊢⇒ τ₁ → Γ ⊢⇒ τ₂ → Set
  ↬⇒-unicity-sig refl e₁ e₂ = e₁ ≡ e₂

  ↬⇒-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : STyp} {ě₁ : Γ ⊢⇒ τ₁} {ě₂ : Γ ⊢⇒ τ₂}
             → (e↬⇒ě₁ : Γ ⊢ e ↬⇒ ě₁)
             → (e↬⇒ě₂ : Γ ⊢ e ↬⇒ ě₂)
             → Σ[ τ₁≡τ₂ ∈ τ₁ ≡ τ₂ ] ↬⇒-unicity-sig τ₁≡τ₂ ě₁ ě₂
  ↬⇒-unicity e↬⇒ě₁ e↬⇒ě₂
    with refl ← ↬⇒-τ-unicity e↬⇒ě₁ e↬⇒ě₂
       = refl , ↬⇒-ě-unicity e↬⇒ě₁ e↬⇒ě₂

  ↬⇐-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě₁ : Γ ⊢⇐ τ} {ě₂ : Γ ⊢⇐ τ}
             → Γ ⊢ e ↬⇐ ě₁
             → Γ ⊢ e ↬⇐ ě₂
             → ě₁ ≡ ě₂
  ↬⇐-unicity = ↬⇐-ě-unicity
