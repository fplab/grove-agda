open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)

open import marking.id
open import marking.typ
open import marking.gtyp
open import marking.ctx
open import marking.uexp
open import marking.mexp

module marking.marking where
  infix 4 _⊢_↬⇒_
  infix 4 _⊢_↬⇐_
  infix 4 _⊢s_↬⇒_
  infix 4 _⊢s_↬⇐_

  -- mark insertion
  mutual
    -- synthesis
    data _⊢_↬⇒_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇒ τ) → Set where
      MKSVar : ∀ {Γ x τ u}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ↬⇒ ⊢ ∋x ^ u

      MKSFree : ∀ {Γ y u}
        → (∌y : Γ ∌ y)
        → Γ ⊢ - y ^ u ↬⇒ ⊢⟦ ∌y ⟧^ u

      MKSLam : ∀ {Γ x τ e τ₁ u}
        → {ě : Γ , x ∶ (τ △) ⊢⇒s τ₁}
        → (e↬⇒ě : Γ , x ∶ (τ △) ⊢s e ↬⇒ ě)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ↬⇒ ⊢λ x ∶ τ ∙ ě ^ u

      MKSAp1 : ∀ {Γ e₁ e₂ τ τ₁ τ₂ u}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s τ₁}
        → (e₁↬⇒ě₁ : Γ ⊢s e₁ ↬⇒ ě₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ↬⇒ ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u

      MKSAp2 : ∀ {Γ e₁ e₂ τ u}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s unknown}
        → (e₁↬⇒ě₁ : Γ ⊢s e₁ ↬⇒ ě₁)
        → (τ!▸ : τ !▸-→)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ↬⇒ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u

      MKSNum : ∀ {Γ n u}
        → Γ ⊢ -ℕ n ^ u ↬⇒ ⊢ℕ n ^ u

      MKSPlus : ∀ {Γ e₁ e₂ u}
        → {ě₁ : Γ ⊢⇐s num}
        → {ě₂ : Γ ⊢⇐s num}
        → (e₁↬⇐ě₁ : Γ ⊢s e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢s e₂ ↬⇐ ě₂)
        → Γ ⊢ - e₁ + e₂ ^ u ↬⇒ ⊢ ě₁ + ě₂ ^ u

      MKSMultiParent : ∀ {Γ u}
        → Γ ⊢ -⋎^ u ↬⇒ ⊢⋎^ u

      MKSUnicycle : ∀ {Γ u}
        → Γ ⊢ -↻^ u ↬⇒ ⊢↻^ u

    MKSubSConflictChildren : ∀ {Γ} {ė* : List USubExp'}
      → (ė↬⇒ě* : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
      → List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)
    MKSubSConflictChildren All.[]                              = []
    MKSubSConflictChildren (All._∷_ {w , _} (τ , ě , _) ė↬⇒ě*) = (w , τ , ě) ∷ (MKSubSConflictChildren ė↬⇒ě*)

    data _⊢s_↬⇒_ : {τ : Typ} (Γ : Ctx) → (e : USubExp) → (Γ ⊢⇒s τ) → Set where
      MKSubSHole : ∀ {Γ w p}
        → Γ ⊢s -□^ w ^ p ↬⇒ ⊢□^ w ^ p

      MKSubSJust : ∀ {Γ w e τ}
        → {ě : Γ ⊢⇒ τ} 
        → (e↬⇒ě : Γ  ⊢ e ↬⇒ ě)
        → Γ ⊢s -∶ (w , e) ↬⇒ ⊢∶ (w , ě)

      MKSubSConflict : ∀ {Γ ė*}
        → (ė↬⇒ě* : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
        → Γ ⊢s -⋏ ė* ↬⇒ ⊢⋏ (MKSubSConflictChildren ė↬⇒ě*)

    USu→MSu : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {ě : Γ ⊢⇒ τ} → USubsumable e → Γ ⊢ e ↬⇒ ě → MSubsumable ě
    USu→MSu {ě = ⊢_^_ {x = x} ∋x u}      USuVar          _ = MSuVar
    USu→MSu {ě = ⊢⟦ x ⟧^ u}              USuVar          _ = MSuFree
    USu→MSu {ě = ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u}    USuAp           _ = MSuAp1
    USu→MSu {ě = ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u} USuAp           _ = MSuAp2
    USu→MSu {ě = ⊢ℕ n ^ u}               USuNum          _ = MSuNum
    USu→MSu {ě = ⊢ ě₁ + ě₂ ^ u}          USuPlus         _ = MSuPlus
    USu→MSu {ě = ⊢⋎^ u}                  USuMultiParent  _ = MSuMultiParent
    USu→MSu {ě = ⊢↻^ u}                  USuUnicycle     _ = MSuUnicycle

    -- analysis
    data _⊢_↬⇐_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇐ τ) → Set where
      MKALam1 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △) ~ τ₁)
        → Γ , x ∶ (τ △) ⊢s e ↬⇐ ě
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)

      MKALam2 : ∀ {Γ x τ e τ' u}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s unknown}
        → (τ'!▸ : τ' !▸-→)
        → Γ , x ∶ (τ △) ⊢s e ↬⇐ ě
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u)

      MKALam3 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ △) ~̸ τ₁)
        → Γ , x ∶ (τ △) ⊢s e ↬⇐ ě
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u)

      MKASubsume : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒ τ'}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~τ' : τ ~ τ')
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢∙ ě [ τ~τ' ∙ USu→MSu s e↬⇒ě ]

      MKAInconsistentTypes : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒ τ'}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~̸τ' : τ ~̸ τ')
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ∙ USu→MSu s e↬⇒ě ]

    data _⊢s_↬⇐_ : {τ : Typ} (Γ : Ctx) → (e : USubExp) → (Γ ⊢⇐s τ) → Set where
      MKSubASubsume : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒s τ'}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě)
        → (τ~τ' : τ ~ τ')
        → Γ ⊢s e ↬⇐ ⊢∙ ě [ τ~τ' ]

      MKSubAInconsistentTypes : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒s τ'}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě)
        → (τ~̸τ' : τ ~̸ τ')
        → Γ ⊢s e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ]
