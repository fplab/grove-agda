open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (¬_)

open import Grove.Marking.STyp
open import Grove.Marking.Ctx
open import Grove.Marking.UExp
open import Grove.Marking.MExp
open import Grove.Marking.Erasure
open import Grove.Marking.Marking

module Grove.Marking.Properties.WellFormed where
  mutual
    -- marking preserves syntactic structure
    ↬⇒□ : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě : Γ ⊢⇒ τ}
        → Γ ⊢ e ↬⇒ ě
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
    ↬⇒□ MKSMultiLocationConflict    = refl
    ↬⇒□ MKSCycleLocationConflict       = refl

    ↬⇒□s : ∀ {Γ : Ctx} {e : UChildExp} {τ : STyp} {ě : Γ ⊢⇒s τ}
        → Γ ⊢s e ↬⇒ ě
        → ě ⇒□s ≡ e
    ↬⇒□s MKSHole = refl
    ↬⇒□s (MKSOnly e↬⇒ě) rewrite ↬⇒□ e↬⇒ě = refl
    ↬⇒□s (MKSLocalConflict ė↬⇒ě*)
      with eqv ← ↬⇒□s* ė↬⇒ě* rewrite eqv    = refl

    ↬⇒□s* : ∀ {Γ ė*}
          → (ė↬⇒ě* : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
          → ((MKSLocalConflictChildren ė↬⇒ě*) ⇒□s*) ≡ ė*
    ↬⇒□s* All.[] = refl
    ↬⇒□s* (All._∷_ {w , e} {ė*} (τ , ě , e↬⇒ě) ė↬⇒ě*)
      with refl ← ↬⇒□ e↬⇒ě | eqv ← ↬⇒□s* ė↬⇒ě* rewrite eqv = refl

    ↬⇐□ : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě : Γ ⊢⇐ τ}
        → Γ ⊢ e ↬⇐ ě
        → ě ⇐□ ≡ e
    ↬⇐□ (MKALam1 τ₁▸ τ~τ₁ e↬⇐ě)
      rewrite ↬⇐□s e↬⇐ě  = refl
    ↬⇐□ (MKALam2 τ₁!▸ e↬⇐ě)
      rewrite ↬⇐□s e↬⇐ě  = refl
    ↬⇐□ (MKALam3 τ₁▸ τ~̸τ₁ e↬⇐ě)
      rewrite ↬⇐□s e↬⇐ě  = refl
    ↬⇐□ MKAMultiLocationConflict = refl
    ↬⇐□ MKACycleLocationConflict = refl
    ↬⇐□ (MKAInconsistentSTypes e↬⇒ě τ~̸τ' s)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇐□ (MKASubsume e↬⇒ě τ~τ' s)
      rewrite ↬⇒□ e↬⇒ě   = refl

    ↬⇐□s : ∀ {Γ : Ctx} {e : UChildExp} {τ : STyp} {ě : Γ ⊢⇐s τ}
        → Γ ⊢s e ↬⇐ ě
        → ě ⇐□s ≡ e
    ↬⇐□s MKAHole = refl
    ↬⇐□s (MKAOnly e↬⇐ě) rewrite ↬⇐□ e↬⇐ě = refl
    ↬⇐□s (MKALocalConflict ė↬⇐ě*)
      with eqv ← ↬⇐□s* ė↬⇐ě* rewrite eqv    = refl

    ↬⇐□s* : ∀ {Γ τ ė*}
          → (ė↬⇐ě* : All (λ (_ , e) → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě) ė*)
          → ((MKALocalConflictChildren ė↬⇐ě*) ⇐□s*) ≡ ė*
    ↬⇐□s* All.[] = refl
    ↬⇐□s* (All._∷_ {w , e} {ė*} (ě , e↬⇐ě) ė↬⇐ě*)
      with refl ← ↬⇐□ e↬⇐ě | eqv ← ↬⇐□s* ė↬⇐ě* rewrite eqv = refl

  mutual
    -- well-typed unmarked expressions are marked into marked expressions of the same type
    ⇒τ→↬⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : STyp}
           → Γ ⊢ e ⇒ τ
           → Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě
    ⇒τ→↬⇒τ {e = - x ^ u}            (USVar ∋x)    = ⊢ ∋x ^ u , MKSVar ∋x
    ⇒τ→↬⇒τ {e = -λ x ∶ τ ∙ e ^ u}   (USLam e⇒τ)
      with ě  , e↬⇒ě   ← ⇒sτ→↬⇒sτ e⇒τ             = ⊢λ x ∶ τ ∙ ě ^ u , MKSLam e↬⇒ě
    ⇒τ→↬⇒τ {e = - e₁ ∙ e₂ ^ u} (USAp e₁⇒τ τ▸ e₂⇐τ₂)
      with ě₁ , e₁↬⇒ě₁ ← ⇒sτ→↬⇒sτ e₁⇒τ
         | ě₂ , e₂↬⇐ě₂ ← ⇐sτ→↬⇐sτ e₂⇐τ₂           = ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u , MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂
    ⇒τ→↬⇒τ {e = -ℕ n ^ u}           USNum         = ⊢ℕ n ^ u , MKSNum
    ⇒τ→↬⇒τ {e = - e₁ + e₂ ^ u}      (USPlus e₁⇐num e₂⇐num)
      with ě₁ , e₁↬⇐ě₁ ← ⇐sτ→↬⇐sτ e₁⇐num
         | ě₂ , e₂↬⇐ě₂ ← ⇐sτ→↬⇐sτ e₂⇐num          = ⊢ ě₁ + ě₂ ^ u , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂
    ⇒τ→↬⇒τ {e = -⋎^ w ^ v}          USMultiLocationConflict = ⊢⋎^ w ^ v , MKSMultiLocationConflict
    ⇒τ→↬⇒τ {e = -↻^ w ^ v}          USCycleLocationConflict    = ⊢↻^ w ^ v , MKSCycleLocationConflict

    ⇒sτ→↬⇒sτ : ∀ {Γ : Ctx} {e : UChildExp} {τ : STyp}
             → Γ ⊢s e ⇒ τ
             → Σ[ ě ∈ Γ ⊢⇒s τ ] Γ ⊢s e ↬⇒ ě
    ⇒sτ→↬⇒sτ {e = -□ s}       USHole = ⊢□ s , MKSHole
    ⇒sτ→↬⇒sτ {e = -∶ (w , e)} (USOnly e⇒τ) 
      with ě , e↬⇒ě ← ⇒τ→↬⇒τ e⇒τ        = ⊢∶ (w , ě) , MKSOnly e↬⇒ě
    ⇒sτ→↬⇒sτ {e = -⋏ s ė*}    (USLocalConflict ė⇒*)
      with ė↬⇒ě* ← ⇒sτ→↬⇒sτ* ė⇒*        = ⊢⋏ s (MKSLocalConflictChildren ė↬⇒ě*) , MKSLocalConflict ė↬⇒ě*

    ⇒sτ→↬⇒sτ* : ∀ {Γ : Ctx} {ė* : List UChildExp'}
              → (ė⇒* : All (λ (_ , e) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
              → All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*
    ⇒sτ→↬⇒sτ* []             = []
    ⇒sτ→↬⇒sτ* ((τ , e⇒) ∷ ė⇒*) = (τ , ⇒τ→↬⇒τ e⇒) ∷ ⇒sτ→↬⇒sτ* ė⇒*

    ⇐τ→↬⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : STyp}
           → Γ ⊢ e ⇐ τ
           → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě
    ⇐τ→↬⇐τ {e = -λ x ∶ τ ∙ e ^ u} (UALam τ₃▸ τ~τ₁ e⇐τ₂)
      with ě , e↬⇐ě ← ⇐sτ→↬⇐sτ e⇐τ₂ = ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u , MKALam1 τ₃▸ τ~τ₁ e↬⇐ě
    ⇐τ→↬⇐τ {e = -⋎^ w ^ v} UAMultiLocationConflict = ⊢⋎^ w ^ v , MKAMultiLocationConflict
    ⇐τ→↬⇐τ {e = -↻^ w ^ v} UACycleLocationConflict = ⊢↻^ w ^ v , MKACycleLocationConflict
    ⇐τ→↬⇐τ {e = e}                (UASubsume e⇒τ' τ~τ' su)
      with ě , e↬⇒ě ← ⇒τ→↬⇒τ e⇒τ'   = ⊢∙ ě [ τ~τ' ∙ USu→MSu su e↬⇒ě ] , MKASubsume e↬⇒ě τ~τ' su

    ⇐sτ→↬⇐sτ : ∀ {Γ : Ctx} {e : UChildExp} {τ : STyp}
             → Γ ⊢s e ⇐ τ
             → Σ[ ě ∈ Γ ⊢⇐s τ ] Γ ⊢s e ↬⇐ ě
    ⇐sτ→↬⇐sτ {e = -□ s}       UAHole = ⊢□ s , MKAHole
    ⇐sτ→↬⇐sτ {e = -∶ (w , e)} (UAOnly e⇐τ) 
      with ě , e↬⇐ě ← ⇐τ→↬⇐τ e⇐τ        = ⊢∶ (w , ě) , MKAOnly e↬⇐ě
    ⇐sτ→↬⇐sτ {e = -⋏ s ė*}    (UALocalConflict ė⇐*)
      with ė↬⇐ě* ← ⇐sτ→↬⇐sτ* ė⇐*        = ⊢⋏ s (MKALocalConflictChildren ė↬⇐ě*) , MKALocalConflict ė↬⇐ě*

    ⇐sτ→↬⇐sτ* : ∀ {Γ : Ctx} {τ : STyp} {ė* : List UChildExp'}
              → (ė⇐* : All (λ (_ , e) → Γ ⊢ e ⇐ τ) ė*)
              → All (λ (_ , e) → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě) ė*
    ⇐sτ→↬⇐sτ* []             = []
    ⇐sτ→↬⇐sτ* (e⇐ ∷ ė⇐*) = ⇐τ→↬⇐τ e⇐ ∷ ⇐sτ→↬⇐sτ* ė⇐*

  mutual
    -- marking synthesizes the same type as synthesis
    ⇒-↬-≡ : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {τ' : STyp} {ě : Γ ⊢⇒ τ'}
           → Γ ⊢ e ⇒ τ
           → Γ ⊢ e ↬⇒ ě
           → τ ≡ τ'
    ⇒-↬-≡ (USVar ∋x) (MKSVar ∋x')
         = ∋→τ-≡ ∋x ∋x'
    ⇒-↬-≡ (USVar {τ = τ} ∋x) (MKSFree ∌y)
         = ⊥-elim (∌y (τ , ∋x))
    ⇒-↬-≡ (USLam e⇒τ) (MKSLam e↬⇒ě)
      rewrite ⇒s-↬s-≡ e⇒τ e↬⇒ě
         = refl
    ⇒-↬-≡ (USAp e⇒τ τ▸ e₁⇐τ₁) (MKSAp1 e↬⇒ě τ▸' e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e⇒τ e↬⇒ě
      with refl ← ▸-→-unicity τ▸ τ▸'
         = refl
    ⇒-↬-≡ (USAp {τ₁ = τ₁} {τ₂ = τ₂} e⇒τ τ▸ e₁⇐τ₁) (MKSAp2 e↬⇒ě τ!▸ e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e⇒τ e↬⇒ě
         = ⊥-elim (τ!▸ (τ₁ , τ₂ , τ▸))
    ⇒-↬-≡ USNum MKSNum
         = refl
    ⇒-↬-≡ (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
         = refl
    ⇒-↬-≡ USMultiLocationConflict MKSMultiLocationConflict
         = refl
    ⇒-↬-≡ USCycleLocationConflict MKSCycleLocationConflict
         = refl

    ⇒s-↬s-≡ : ∀ {Γ e τ τ'} {ě : Γ ⊢⇒s τ'}
            → Γ ⊢s e ⇒ τ
            → Γ ⊢s e ↬⇒ ě
            → τ ≡ τ'
    ⇒s-↬s-≡ USHole           MKSHole             = refl
    ⇒s-↬s-≡ (USOnly e⇒τ)     (MKSOnly e↬⇒ě)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě                       = refl
    ⇒s-↬s-≡ (USLocalConflict ė⇒*) (MKSLocalConflict ė↬⇒ě*) = refl

  mutual
    -- marking well-typed terms produces no marks
    ⇒τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě : Γ ⊢⇒ τ}
                → Γ ⊢ e ⇒ τ
                → Γ ⊢ e ↬⇒ ě
                → Markless⇒ ě
    ⇒τ→markless (USVar ∋x) (MKSVar ∋x')
         = MLSVar
    ⇒τ→markless (USVar ∋x) (MKSFree ∌y)
         = ⊥-elim (∌y (unknown , ∋x))
    ⇒τ→markless (USLam e⇒τ) (MKSLam e↬⇒ě)
         = MLSLam (⇒sτ→markless e⇒τ e↬⇒ě)
    ⇒τ→markless (USAp e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp1 e₁↬⇒ě₁ τ▸'  e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e₁⇒τ e₁↬⇒ě₁
      with refl ← ▸-→-unicity τ▸ τ▸'
         = MLSAp (⇒sτ→markless e₁⇒τ e₁↬⇒ě₁) (⇐sτ→markless e₂⇐τ₁ e₂↬⇐ě₂)
    ⇒τ→markless (USAp {τ₁ = τ₁} e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp2 e₁↬⇒ě₁ τ!▸' e₂↬⇐ě₂)
      with refl ← ⇒s-↬s-≡ e₁⇒τ e₁↬⇒ě₁
         = ⊥-elim (τ!▸' (τ₁ , unknown , τ▸))
    ⇒τ→markless USNum MKSNum
         = MLSNum
    ⇒τ→markless (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
         = MLSPlus (⇐sτ→markless e₁⇐num e₁↬⇐ě₁) (⇐sτ→markless e₂⇐num e₂↬⇐ě₂)
    ⇒τ→markless USMultiLocationConflict MKSMultiLocationConflict
         = MLSMultiLocationConflict
    ⇒τ→markless USCycleLocationConflict MKSCycleLocationConflict
         = MLSCycleLocationConflict

    ⇒sτ→markless : ∀ {Γ e τ} {ě : Γ ⊢⇒s τ}
                 → Γ ⊢s e ⇒ τ
                 → Γ ⊢s e ↬⇒ ě
                 → Markless⇒s ě
    ⇒sτ→markless USHole MKSHole = MLSHole
    ⇒sτ→markless (USOnly e⇒τ) (MKSOnly e↬⇒ě)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě      = MLSOnly (⇒τ→markless e⇒τ e↬⇒ě)
    ⇒sτ→markless (USLocalConflict ė⇒*) (MKSLocalConflict ė↬⇒ě*) = MLSLocalConflict (⇒sτ→markless* ė⇒* ė↬⇒ě*)

    ⇒sτ→markless* : ∀ {Γ ė*}
                  → (ė⇒* : All (λ (_ , e) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
                  → (ė↬⇒ě* : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
                  → All (λ { (_ , _ , ě) → Markless⇒ ě }) (MKSLocalConflictChildren ė↬⇒ě*)
    ⇒sτ→markless* [] [] = []
    ⇒sτ→markless* ((_ , e⇒) ∷ ė⇒*) ((_ , ě , e↬⇒ě) ∷ ė↬⇒ě*)
      with refl ← ⇒-↬-≡ e⇒ e↬⇒ě
         = ⇒τ→markless e⇒ e↬⇒ě ∷ ⇒sτ→markless* ė⇒* ė↬⇒ě*

    ⇐τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě : Γ ⊢⇐ τ}
                → Γ ⊢ e ⇐ τ
                → Γ ⊢ e ↬⇐ ě
                → Markless⇐ ě
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam1 τ₃▸' τ~τ₁' e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸'
         = MLALam (⇐sτ→markless e⇐τ e↬⇐ě)
    ⇐τ→markless (UALam {τ₁ = τ₁} {τ₂ = τ₂} τ₃▸ τ~τ₁ e⇐τ) (MKALam2 τ₃!▸ e↬⇐ě)
         = ⊥-elim (τ₃!▸ (τ₁ , τ₂ , τ₃▸))
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam3 τ₃▸' τ~̸τ₁ e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸'
         = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ⇐τ→markless UAMultiLocationConflict MKAMultiLocationConflict = MLAMultiLocationConflict
    ⇐τ→markless UACycleLocationConflict MKACycleLocationConflict = MLACycleLocationConflict
    ⇐τ→markless (UASubsume e⇒τ' τ~τ' su) (MKAInconsistentSTypes e↬⇒ě τ~̸τ' su')
      with refl ← ⇒-↬-≡ e⇒τ' e↬⇒ě
         = ⊥-elim (τ~̸τ' τ~τ')
    ⇐τ→markless (UASubsume e⇒τ' τ~τ' su) (MKASubsume e↬⇒ě τ~τ'' su')
      with refl ← ⇒-↬-≡ e⇒τ' e↬⇒ě
         = MLASubsume (⇒τ→markless e⇒τ' e↬⇒ě)

    ⇐sτ→markless : ∀ {Γ e τ} {ě : Γ ⊢⇐s τ}
                 → Γ ⊢s e ⇐ τ
                 → Γ ⊢s e ↬⇐ ě
                 → Markless⇐s ě
    ⇐sτ→markless UAHole MKAHole = MLAHole
    ⇐sτ→markless (UAOnly e⇐τ) (MKAOnly e↬⇐ě) = MLAOnly (⇐τ→markless e⇐τ e↬⇐ě)
    ⇐sτ→markless (UALocalConflict ė⇐*) (MKALocalConflict ė↬⇐ě*) = MLALocalConflict (⇐sτ→markless* ė⇐* ė↬⇐ě*)

    ⇐sτ→markless* : ∀ {Γ τ ė*}
                  → (ė⇐* : All (λ (_ , e) → Γ ⊢ e ⇐ τ) ė*)
                  → (ė↬⇐ě* : All (λ (_ , e) → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě) ė*)
                  → All (λ { (_ , ě) → Markless⇐ ě }) (MKALocalConflictChildren ė↬⇐ě*)
    ⇐sτ→markless* [] [] = []
    ⇐sτ→markless* (e⇐ ∷ ė⇐*) ((ě , e↬⇐ě) ∷ ė↬⇐ě*) = ⇐τ→markless e⇐ e↬⇐ě ∷ ⇐sτ→markless* ė⇐* ė↬⇐ě*

  mutual
    -- synthetically marking an expression into a markless expression and a type implies the original synthesizes that type
    ↬⇒τ-markless→⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě : Γ ⊢⇒ τ}
                    → Γ ⊢ e ↬⇒ ě
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
    ↬⇒τ-markless→⇒τ MKSMultiLocationConflict MLSMultiLocationConflict = USMultiLocationConflict
    ↬⇒τ-markless→⇒τ MKSCycleLocationConflict MLSCycleLocationConflict = USCycleLocationConflict

    ↬⇒sτ-markless→⇒sτ : ∀ {Γ e τ} {ě : Γ ⊢⇒s τ}
                    → Γ ⊢s e ↬⇒ ě
                    → Markless⇒s ě
                    → Γ ⊢s e ⇒ τ
    ↬⇒sτ-markless→⇒sτ MKSHole             MLSHole             = USHole
    ↬⇒sτ-markless→⇒sτ (MKSOnly e↬⇒ě)      (MLSOnly less)      = USOnly (↬⇒τ-markless→⇒τ e↬⇒ě less)
    ↬⇒sτ-markless→⇒sτ (MKSLocalConflict ė↬⇒ě*) (MLSLocalConflict less*) = USLocalConflict (↬⇒sτ-markless→⇒sτ* ė↬⇒ě* less*)

    ↬⇒sτ-markless→⇒sτ* : ∀ {Γ ė*}
                       → (ė↬⇒ě* : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
                       → (less* : All (λ { (_ , _ , ě) → Markless⇒ ě }) (MKSLocalConflictChildren ė↬⇒ě*))
                       → All (λ (_ , e) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*
    ↬⇒sτ-markless→⇒sτ* []                       []             = []
    ↬⇒sτ-markless→⇒sτ* ((τ , ě , e↬⇒ě) ∷ ė↬⇒ě*) (less ∷ less*) = (τ , ↬⇒τ-markless→⇒τ e↬⇒ě less) ∷ ↬⇒sτ-markless→⇒sτ* ė↬⇒ě* less*

    -- analytically marking an expression into a markless expression against a type implies the original analyzes against type
    ↬⇐τ-markless→⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : STyp} {ě : Γ ⊢⇐ τ}
                    → Γ ⊢ e ↬⇐ ě
                    → Markless⇐ ě
                    → Γ ⊢ e ⇐ τ
    ↬⇐τ-markless→⇐τ (MKALam1 τ₃▸ τ~τ₁ e↬⇐ě) (MLALam less)
      with e⇐τ₂ ← ↬⇐sτ-markless→⇐sτ e↬⇐ě less
         = UALam τ₃▸ τ~τ₁ e⇐τ₂
    ↬⇐τ-markless→⇐τ MKAMultiLocationConflict MLAMultiLocationConflict = UAMultiLocationConflict
    ↬⇐τ-markless→⇐τ MKACycleLocationConflict MLACycleLocationConflict = UACycleLocationConflict
    ↬⇐τ-markless→⇐τ (MKASubsume e↬⇒ě τ~τ' su) (MLASubsume less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = UASubsume e⇒τ τ~τ' su

    ↬⇐sτ-markless→⇐sτ : ∀ {Γ e τ} {ě : Γ ⊢⇐s τ}
                    → Γ ⊢s e ↬⇐ ě
                    → Markless⇐s ě
                    → Γ ⊢s e ⇐ τ
    ↬⇐sτ-markless→⇐sτ MKAHole             MLAHole             = UAHole
    ↬⇐sτ-markless→⇐sτ (MKAOnly e↬⇐ě)      (MLAOnly less)      = UAOnly (↬⇐τ-markless→⇐τ e↬⇐ě less)
    ↬⇐sτ-markless→⇐sτ (MKALocalConflict ė↬⇐ě*) (MLALocalConflict less*) = UALocalConflict (↬⇐sτ-markless→⇐sτ* ė↬⇐ě* less*)

    ↬⇐sτ-markless→⇐sτ* : ∀ {Γ τ ė*}
                       → (ė↬⇐ě* : All (λ (_ , e) → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě) ė*)
                       → (less* : All (λ { (_ , ě) → Markless⇐ ě }) (MKALocalConflictChildren ė↬⇐ě*))
                       → All (λ (_ , e) → Γ ⊢ e ⇐ τ) ė*
    ↬⇐sτ-markless→⇐sτ* []                   []             = []
    ↬⇐sτ-markless→⇐sτ* ((ě , e↬⇐ě) ∷ ė↬⇐ě*) (less ∷ less*) = ↬⇐τ-markless→⇐τ e↬⇐ě less ∷ ↬⇐sτ-markless→⇐sτ* ė↬⇐ě* less*

  mutual
    -- ill-typed expressions are marked into non-markless expressions
    ¬⇒τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ' : STyp} {ě : Γ ⊢⇒ τ'}
                  → ¬ (Σ[ τ ∈ STyp ] Γ ⊢ e ⇒ τ)
                  → Γ ⊢ e ↬⇒ ě
                  → ¬ (Markless⇒ ě)
    ¬⇒τ→¬markless {τ' = τ'} ¬e⇒τ e↬⇒ě less = ¬e⇒τ (τ' , ↬⇒τ-markless→⇒τ e↬⇒ě less)

    ¬⇐τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ' : STyp} {ě : Γ ⊢⇐ τ'}
                  → ¬ (Σ[ τ ∈ STyp ] Γ ⊢ e ⇐ τ)
                  → Γ ⊢ e ↬⇐ ě
                  → ¬ (Markless⇐ ě)
    ¬⇐τ→¬markless {τ' = τ'} ¬e⇐τ e↬⇐ě less = ¬e⇐τ (τ' , ↬⇐τ-markless→⇐τ e↬⇐ě less)
