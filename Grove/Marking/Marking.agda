open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)

open import Grove.Ident
open import Grove.Marking.Typ
open import Grove.Marking.GTyp
open import Grove.Marking.Ctx
open import Grove.Marking.UExp
open import Grove.Marking.MExp

module Grove.Marking.Marking where
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
        → {ě : Γ , x ∶ (τ △s) ⊢⇒s τ₁}
        → (e↬⇒ě : Γ , x ∶ (τ △s) ⊢s e ↬⇒ ě)
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

      MKSMultiParent : ∀ {Γ w v}
        → Γ ⊢ -⋎^ w ^ v ↬⇒ ⊢⋎^ w ^ v

      MKSUnicycle : ∀ {Γ w v}
        → Γ ⊢ -↻^ w ^ v ↬⇒ ⊢↻^ w ^ v

    MKChildSConflictChildren : ∀ {Γ} {ė* : List UChildExp'}
      → (ė↬⇒ě* : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
      → List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)
    MKChildSConflictChildren All.[]                              = []
    MKChildSConflictChildren (All._∷_ {w , _} (τ , ě , _) ė↬⇒ě*) = (w , τ , ě) ∷ (MKChildSConflictChildren ė↬⇒ě*)

    data _⊢s_↬⇒_ : {τ : Typ} (Γ : Ctx) → (e : UChildExp) → (Γ ⊢⇒s τ) → Set where
      MKChildSHole : ∀ {Γ s}
        → Γ ⊢s -□ s ↬⇒ ⊢□ s

      MKChildSOnly : ∀ {Γ w e τ}
        → {ě : Γ ⊢⇒ τ} 
        → (e↬⇒ě : Γ  ⊢ e ↬⇒ ě)
        → Γ ⊢s -∶ (w , e) ↬⇒ ⊢∶ (w , ě)

      MKChildSConflict : ∀ {Γ s ė*}
        → (ė↬⇒ě* : All (λ (_ , e) → ∃[ τ ] Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě) ė*)
        → Γ ⊢s -⋏ s ė* ↬⇒ ⊢⋏ s (MKChildSConflictChildren ė↬⇒ě*)

    USu→MSu : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {ě : Γ ⊢⇒ τ} → UChildsumable e → Γ ⊢ e ↬⇒ ě → MChildsumable ě
    USu→MSu {ě = ⊢_^_ {x = x} ∋x u}      USuVar          _ = MSuVar
    USu→MSu {ě = ⊢⟦ x ⟧^ u}              USuVar          _ = MSuFree
    USu→MSu {ě = ⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u}    USuAp           _ = MSuAp1
    USu→MSu {ě = ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u} USuAp           _ = MSuAp2
    USu→MSu {ě = ⊢ℕ n ^ u}               USuNum          _ = MSuNum
    USu→MSu {ě = ⊢ ě₁ + ě₂ ^ u}          USuPlus         _ = MSuPlus
    USu→MSu {ě = ⊢⋎^ w ^ p}              USuMultiParent  _ = MSuMultiParent
    USu→MSu {ě = ⊢↻^ w ^ p}              USuUnicycle     _ = MSuUnicycle

    -- analysis
    data _⊢_↬⇐_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇐ τ) → Set where
      MKALam1 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u}
        → {ě : Γ , x ∶ (τ △s) ⊢⇐s τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △s) ~ τ₁)
        → Γ , x ∶ (τ △s) ⊢s e ↬⇐ ě
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)

      MKALam2 : ∀ {Γ x τ e τ' u}
        → {ě : Γ , x ∶ (τ △s) ⊢⇐s unknown}
        → (τ'!▸ : τ' !▸-→)
        → Γ , x ∶ (τ △s) ⊢s e ↬⇐ ě
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u)

      MKALam3 : ∀ {Γ x τ e τ₁ τ₂ τ₃ u}
        → {ě : Γ , x ∶ (τ △s) ⊢⇐s τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ △s) ~̸ τ₁)
        → Γ , x ∶ (τ △s) ⊢s e ↬⇐ ě
        → Γ ⊢ (-λ x ∶ τ ∙ e ^ u) ↬⇐ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u)

      MKASubsume : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒ τ'}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~τ' : τ ~ τ')
        → (s : UChildsumable e)
        → Γ ⊢ e ↬⇐ ⊢∙ ě [ τ~τ' ∙ USu→MSu s e↬⇒ě ]

      MKAInconsistentTypes : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒ τ'}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~̸τ' : τ ~̸ τ')
        → (s : UChildsumable e)
        → Γ ⊢ e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ∙ USu→MSu s e↬⇒ě ]

    data _⊢s_↬⇐_ : {τ : Typ} (Γ : Ctx) → (e : UChildExp) → (Γ ⊢⇐s τ) → Set where
      MKChildASubsume : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒s τ'}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě)
        → (τ~τ' : τ ~ τ')
        → Γ ⊢s e ↬⇐ ⊢∙ ě [ τ~τ' ]

      MKChildAInconsistentTypes : ∀ {Γ e τ τ'}
        → {ě : Γ ⊢⇒s τ'}
        → (e↬⇒ě : Γ ⊢s e ↬⇒ ě)
        → (τ~̸τ' : τ ~̸ τ')
        → Γ ⊢s e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ' ]
