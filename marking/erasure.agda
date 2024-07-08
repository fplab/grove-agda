open import marking.prelude

open import marking.id
open import marking.typ
open import marking.gtyp
open import marking.uexp
open import marking.mexp

module marking.erasure where
  mutual
    _⇒□ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → UExp
    (⊢_^_ {x = x} ∋x u)      ⇒□ = - x ^ u
    (⊢λ x ∶ τ ∙ ě ^ u)       ⇒□ = -λ x ∶ τ ∙ (ě ⇒□s) ^ u
    (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)    ⇒□ = - (ě₁ ⇒□s) ∙ (ě₂ ⇐□s) ^ u
    (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u) ⇒□ = - (ě₁ ⇒□s) ∙ (ě₂ ⇐□s) ^ u
    (⊢ℕ n ^ u)               ⇒□ = -ℕ n ^ u
    (⊢ ě₁ + ě₂ ^ u)          ⇒□ = - (ě₁ ⇐□s) + (ě₂ ⇐□s) ^ u
    (⊢⟦_⟧^_ {y = y} ∌y u)    ⇒□ = - y ^ u
    (⊢⋎^ u)                  ⇒□ = -⋎^ u
    (⊢↻^ u)                  ⇒□ = -↻^ u

    _⇒□s : ∀ {Γ τ} → (ě : Γ ⊢⇒s τ) → USubExp
    (⊢□^ w ^ p)    ⇒□s = -□^ w ^ p
    (⊢∶ ⟨ w , ě ⟩) ⇒□s = -∶ (⟨ w , ě ⇒□ ⟩)
    (⊢⋏ ė*)        ⇒□s = -⋏ (ė* ⇒□s*)

    _⇒□s* : ∀ {Γ} → (ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)) → List USubExp'
    []                       ⇒□s* = []
    (⟨ w , ⟨ _ , ě ⟩ ⟩ ∷ ė*) ⇒□s* = ⟨ w , ě ⇒□ ⟩ ∷ (ė* ⇒□s*)

    _⇐□ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → UExp
    (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)   ⇐□ = -λ x ∶ τ ∙ (ě ⇐□s) ^ u
    (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u)       ⇐□ = -λ x ∶ τ ∙ (ě ⇐□s) ^ u
    (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u) ⇐□ = -λ x ∶ τ ∙ (ě ⇐□s) ^ u
    ⊢⸨ ě ⸩[ τ~̸τ' ∙ su ]                ⇐□ = ě ⇒□
    ⊢∙ ě [ τ~τ' ∙ su ]                 ⇐□ = ě ⇒□

    _⇐□s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → USubExp
    ⊢∙ ě [ τ~τ' ] ⇐□s  = ě ⇒□s
    ⊢⸨ ě ⸩[ τ~̸τ' ] ⇐□s = ě ⇒□s

  mutual
    ⊢⇐-⊢⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → ∃[ τ' ] Σ[ ě' ∈ Γ ⊢⇒ τ' ] ě ⇐□ ≡ ě' ⇒□
    ⊢⇐-⊢⇒ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)
      with ⟨ τ' , ⟨ ě' , eq ⟩ ⟩ ← ⊢⇐s-⊢⇒s ě rewrite eq
         = ⟨ (τ △) -→ τ' , ⟨ ⊢λ x ∶ τ ∙ ě' ^ u , refl ⟩ ⟩
    ⊢⇐-⊢⇒ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u)
      with ⟨ τ' , ⟨ ě' , eq ⟩ ⟩ ← ⊢⇐s-⊢⇒s ě rewrite eq
         = ⟨ (τ △) -→ τ' , ⟨ ⊢λ x ∶ τ ∙ ě' ^ u , refl ⟩ ⟩
    ⊢⇐-⊢⇒ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u)
      with ⟨ τ' , ⟨ ě' , eq ⟩ ⟩ ← ⊢⇐s-⊢⇒s ě rewrite eq
         = ⟨ (τ △) -→ τ' , ⟨ ⊢λ x ∶ τ ∙ ě' ^ u , refl ⟩ ⟩
    ⊢⇐-⊢⇒ (⊢⸨_⸩[_∙_] {τ' = τ'} ě τ~̸τ' su) = ⟨ τ' , ⟨ ě , refl ⟩ ⟩
    ⊢⇐-⊢⇒ (⊢∙_[_∙_]  {τ' = τ'} ě τ~τ' su) = ⟨ τ' , ⟨ ě , refl ⟩ ⟩

    ⊢⇐s-⊢⇒s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → ∃[ τ' ] Σ[ ě' ∈ Γ ⊢⇒s τ' ] ě ⇐□s ≡ ě' ⇒□s
    ⊢⇐s-⊢⇒s (⊢∙_[_]  {τ' = τ'} ě τ~τ') = ⟨ τ' , ⟨ ě , refl ⟩ ⟩
    ⊢⇐s-⊢⇒s (⊢⸨_⸩[_] {τ' = τ'} ě τ~τ') = ⟨ τ' , ⟨ ě , refl ⟩ ⟩

  private
    ⊢⇒-⊢⇐-subsume : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒ τ) → (su : MSubsumable ě) → Σ[ ě' ∈ Γ ⊢⇐ τ' ] ě ⇒□ ≡ ě' ⇐□
    ⊢⇒-⊢⇐-subsume {τ = τ} {τ' = τ'} ě su
      with τ' ~? τ 
    ...  | yes τ'~τ = ⟨ ⊢∙ ě [ τ'~τ ∙ su ] , refl ⟩
    ...  | no  τ'~̸τ = ⟨ ⊢⸨ ě ⸩[ τ'~̸τ ∙ su ] , refl ⟩

    ⊢⇒s-⊢⇐s-subsume : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒s τ) → Σ[ ě' ∈ Γ ⊢⇐s τ' ] ě ⇒□s ≡ ě' ⇐□s
    ⊢⇒s-⊢⇐s-subsume {τ = τ} {τ' = τ'} ě
      with τ' ~? τ 
    ...  | yes τ'~τ = ⟨ ⊢∙ ě [ τ'~τ ] , refl ⟩
    ...  | no  τ'~̸τ = ⟨ ⊢⸨ ě ⸩[ τ'~̸τ ] , refl ⟩

  mutual
    ⊢⇒-⊢⇐ : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒ τ) → Σ[ ě' ∈ Γ ⊢⇐ τ' ] ě ⇒□ ≡ ě' ⇐□
    ⊢⇒-⊢⇐ ě@(⊢ ∋x ^ u)                        = ⊢⇒-⊢⇐-subsume ě MSuVar
    ⊢⇒-⊢⇐ {τ' = τ'} (⊢λ x ∶ τ ∙ ě ^ u)
      with τ' ▸-→?
    ...  | no  τ'!▸ with ⟨ ě' , eq ⟩ ← ⊢⇒s-⊢⇐s ě rewrite eq
         = ⟨ ⊢⸨λ x ∶ τ ∙ ě' ⸩[ τ'!▸ ]^ u , refl ⟩
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ'▸ ⟩ ⟩ with (τ △) ~? τ₁
    ...    | yes τ~τ₁ with ⟨ ě' , eq ⟩ ← ⊢⇒s-⊢⇐s ě rewrite eq
           = ⟨ ⊢λ x ∶ τ ∙ ě' [ τ'▸ ∙ τ~τ₁ ]^ u , refl ⟩
    ...    | no  τ~̸τ₁ with ⟨ ě' , eq ⟩ ← ⊢⇒s-⊢⇐s ě rewrite eq
           = ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě' [ τ'▸ ∙ τ~̸τ₁ ]^ u , refl ⟩
    ⊢⇒-⊢⇐ ě@(⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)    = ⊢⇒-⊢⇐-subsume ě MSuAp1
    ⊢⇒-⊢⇐ ě@(⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u) = ⊢⇒-⊢⇐-subsume ě MSuAp2
    ⊢⇒-⊢⇐ ě@(⊢ℕ n ^ u)               = ⊢⇒-⊢⇐-subsume ě MSuNum
    ⊢⇒-⊢⇐ ě@(⊢ ě₁ + ě₂ ^ u)          = ⊢⇒-⊢⇐-subsume ě MSuPlus
    ⊢⇒-⊢⇐ ě@(⊢⟦ ∌y ⟧^ u)             = ⊢⇒-⊢⇐-subsume ě MSuFree
    ⊢⇒-⊢⇐ ě@(⊢⋎^ u)                  = ⊢⇒-⊢⇐-subsume ě MSuMultiParent
    ⊢⇒-⊢⇐ ě@(⊢↻^ u)                  = ⊢⇒-⊢⇐-subsume ě MSuUnicycle

    ⊢⇒s-⊢⇐s : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒s τ) → Σ[ ě' ∈ Γ ⊢⇐s τ' ] ě ⇒□s ≡ ě' ⇐□s
    ⊢⇒s-⊢⇐s ě = ⊢⇒s-⊢⇐s-subsume ě
