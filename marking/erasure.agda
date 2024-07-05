open import marking.prelude

open import marking.typ
open import marking.uexp
open import marking.mexp

module marking.erasure where
  mutual
    _⇒□ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → UExp
    (⊢⦇-⦈^ u)                     ⇒□ = ‵⦇-⦈^ u
    ⊢_ {x = x} ∋x                 ⇒□ = ‵ x
    (⊢λ x ∶ τ ∙ ě)                ⇒□ = ‵λ x ∶ τ ∙ (ě ⇒□)
    ⊢ ě₁ ∙ ě₂ [ τ▸ ]              ⇒□ = ‵ (ě₁ ⇒□) ∙ (ě₂ ⇐□)
    ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]           ⇒□ = ‵ (ě₁ ⇒□) ∙ (ě₂ ⇐□)
    (⊢ℕ n)                        ⇒□ = ‵ℕ n
    (⊢ ě₁ + ě₂)                   ⇒□ = ‵ (ě₁ ⇐□) + (ě₂ ⇐□)
    ⊢⟦_⟧ {y = y} ∌y               ⇒□ = ‵ y

    _⇐□ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → UExp
    ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]   ⇐□ = ‵λ x ∶ τ ∙ (ě ⇐□)
    ⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ]       ⇐□ = ‵λ x ∶ τ ∙ (ě ⇐□)
    ⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] ⇐□ = ‵λ x ∶ τ ∙ (ě ⇐□)
    ⊢⸨ ě ⸩[ τ~̸τ′ ∙ su ]           ⇐□ = ě ⇒□
    ⊢∙ ě [ τ~τ′ ∙ su ]            ⇐□ = ě ⇒□
