open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Nullary using (Dec; yes; no)

open import Grove.Marking.STyp
open import Grove.Marking.Typ
open import Grove.Marking.Ctx
open import Grove.Marking.UExp
open import Grove.Marking.MExp
open import Grove.Marking.Marking

module Grove.Marking.Properties.Totality where
  mutual
    ↬⇒-totality : (Γ : Ctx)
                → (e : UExp)
                → Σ[ τ ∈ STyp ] Σ[ ě ∈ Γ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (- x ^ u)
      with Γ ∋? x
    ...  | yes (_ , Z {τ = τ})         = τ       , ⊢ Z ^ u           , MKSVar Z          
    ...  | yes (_ , S {τ = τ} x≢x' ∋x) = τ       , ⊢ (S x≢x' ∋x) ^ u , MKSVar (S x≢x' ∋x)
    ...  | no  ∌x                  = unknown , ⊢⟦ ∌x ⟧^ u        , MKSFree ∌x        
    ↬⇒-totality Γ (-λ x ∶ τ ∙ e ^ u)
      with τ' , ě , e↬⇒ě ← ↬⇒s-totality (_,_∶_ Γ x (τ △s)) e
         = (τ △s) -→ τ' , ⊢λ x ∶ τ ∙ ě ^ u , MKSLam e↬⇒ě
    ↬⇒-totality Γ (- e₁ ∙ e₂ ^ u)
      with ↬⇒s-totality Γ e₁
    ...  | τ , ě₁ , e₁↬⇒ě₁
             with τ ▸-→?
    ...         | no τ!▸
                    with ě₂ , e₂↬⇐ě₂ ← ↬⇐s-totality Γ unknown e₂
                       = unknown , ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u , MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂
    ...         | yes (τ₁ , τ₂ , τ▸τ₁-→τ₂)
                    with ě₂ , e₂↬⇐ě₂ ← ↬⇐s-totality Γ τ₁ e₂
                       = τ₂ , ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ]^ u , MKSAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂
    ↬⇒-totality Γ (-ℕ n ^ u) = num , ⊢ℕ n ^ u , MKSNum
    ↬⇒-totality Γ (- e₁ + e₂ ^ u)
      with ě₁ , e₁↬⇐ě₁ ← ↬⇐s-totality Γ num e₁
         | ě₂ , e₂↬⇐ě₂ ← ↬⇐s-totality Γ num e₂
         = num , ⊢ ě₁ + ě₂ ^ u , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂
    ↬⇒-totality Γ (-⋎^ w ^ v) = unknown , ⊢⋎^ w ^ v , MKSMultiLocationConflict
    ↬⇒-totality Γ (-↻^ w ^ v) = unknown , ⊢↻^ w ^ v , MKSCycleLocationConflict

    ↬⇒s-totality : (Γ : Ctx)
                 → (e : UChildExp)
                 → Σ[ τ ∈ STyp ] Σ[ ě ∈ Γ ⊢⇒s τ ] (Γ ⊢s e ↬⇒ ě)
    ↬⇒s-totality Γ (-□ s) = unknown , ⊢□ s , MKSHole
    ↬⇒s-totality Γ (-∶ (w , e))
      with τ' , ě , e↬⇒ě ← ↬⇒-totality Γ e
         = τ' , ⊢∶ (w , ě) , MKSOnly e↬⇒ě
    ↬⇒s-totality Γ (-⋏ s ė*)
      with ė↬⇒ě* ← ↬⇒s-totality* Γ ė*
         = unknown , ⊢⋏ s (MKSLocalConflictChildren ė↬⇒ě*) , MKSLocalConflict ė↬⇒ě*

    ↬⇒s-totality* : (Γ : Ctx)
                  → (ė* : List UChildExp')
                  → All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*
    ↬⇒s-totality* Γ []             = All.[]
    ↬⇒s-totality* Γ ((w , e) ∷ ė*) = All._∷_ (↬⇒-totality Γ e) (↬⇒s-totality* Γ ė*)

    ↬⇐-subsume : ∀ {Γ e τ}
               → (ě : Γ ⊢⇒ τ)
               → (τ' : STyp)
               → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
               → (s : USubsumable e)
               → Σ[ ě ∈ Γ ⊢⇐ τ' ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-subsume {τ = τ} ě τ' e↬⇒ě s with τ' ~? τ
    ...   | yes τ'~τ = ⊢∙ ě  [ τ'~τ ∙ USu→MSu s e↬⇒ě ] , MKASubsume e↬⇒ě τ'~τ s
    ...   | no  τ'~̸τ = ⊢⸨ ě ⸩[ τ'~̸τ ∙ USu→MSu s e↬⇒ě ] , MKAInconsistentSTypes e↬⇒ě τ'~̸τ s

    ↬⇐-totality : (Γ : Ctx)
                → (τ' : STyp)
                → (e : UExp)
                → Σ[ ě ∈ Γ ⊢⇐ τ' ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ' e@(- x ^ u)
      with ↬⇒-totality Γ e
    ...  | .unknown , ě@(⊢⟦ ∌x ⟧^ u) , e↬⇒ě = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ...  | τ        , ě@(⊢ ∋x ^ u)   , e↬⇒ě = ↬⇐-subsume ě τ' e↬⇒ě USuVar
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
      with τ' ▸-→?
    ...  | yes (τ₁ , τ₂ , τ'▸)
             with (τ △s) ~? τ₁
    ...         | yes τ~τ₁
                    with ě' , e'↬⇐ě' ← ↬⇐s-totality (_,_∶_ Γ x (τ △s)) τ₂ e'
                       = ⊢λ x ∶ τ ∙ ě' [ τ'▸ ∙ τ~τ₁ ]^ u , MKALam1 τ'▸ τ~τ₁ e'↬⇐ě'
    ...         | no  τ~̸τ₁
                    with ě' , e'↬⇐ě' ← ↬⇐s-totality (_,_∶_ Γ x (τ △s)) τ₂ e'
                       = ⊢λ x ∶⸨ τ ⸩∙ ě' [ τ'▸ ∙ τ~̸τ₁ ]^ u , MKALam3 τ'▸ τ~̸τ₁ e'↬⇐ě'
    ↬⇐-totality Γ τ' e@(-λ x ∶ τ ∙ e' ^ u)
         | no τ'!▸
             with ě' , e'↬⇐ě' ← ↬⇐s-totality (_,_∶_ Γ x (τ △s)) unknown e'
                = ⊢⸨λ x ∶ τ ∙ ě' ⸩[ τ'!▸ ]^ u , MKALam2 τ'!▸ e'↬⇐ě'
    ↬⇐-totality Γ τ' e@(- _ ∙ _ ^ u)
      with ↬⇒-totality Γ e
    ...  | .unknown , ě@(⊢⸨ _ ⸩∙ _ [ _ ]^ u) , e↬⇒ě = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ...  | _        , ě@(⊢  _  ∙ _ [ _ ]^ u) , e↬⇒ě = ↬⇐-subsume ě τ' e↬⇒ě USuAp
    ↬⇐-totality Γ τ' e@(-ℕ _ ^ u)
      with _ , ě@(⊢ℕ _ ^ u) , e↬⇒ě ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuNum
    ↬⇐-totality Γ τ' e@(- _ + _ ^ u)
      with _ , ě@(⊢ _ + _ ^ u) , e↬⇒ě ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ' e↬⇒ě USuPlus
    ↬⇐-totality Γ τ' e@(-⋎^ w ^ v) = (⊢⋎^ w ^ v) , MKAMultiLocationConflict
    ↬⇐-totality Γ τ' e@(-↻^ w ^ v) = (⊢↻^ w ^ v) , MKACycleLocationConflict

    ↬⇐s-totality : (Γ : Ctx)
                 → (τ' : STyp)
                 → (e : UChildExp)
                 → Σ[ ě ∈ Γ ⊢⇐s τ' ] (Γ ⊢s e ↬⇐ ě)
    ↬⇐s-totality Γ τ' (-□ s) = (⊢□ s) , MKAHole
    ↬⇐s-totality Γ τ' (-∶ (w , e))
      with ě , e↬⇐ě ← ↬⇐-totality Γ τ' e = (⊢∶ (w , ě)) , MKAOnly e↬⇐ě
    ↬⇐s-totality Γ τ' (-⋏ s ė*)
      with ė↬⇐ě* ← ↬⇐s-totality* Γ τ' ė*
         = ⊢⋏ s (MKALocalConflictChildren ė↬⇐ě*) , MKALocalConflict ė↬⇐ě*

    ↬⇐s-totality* : (Γ : Ctx) (τ' : STyp)
                  → (ė* : List UChildExp')
                  → All (λ (_ , e) → Σ[ ě ∈ Γ ⊢⇐ τ' ] Γ ⊢ e ↬⇐ ě) ė*
    ↬⇐s-totality* Γ τ' []             = All.[]
    ↬⇐s-totality* Γ τ' ((w , e) ∷ ė*) = All._∷_ (↬⇐-totality Γ τ' e) (↬⇐s-totality* Γ τ' ė*)
