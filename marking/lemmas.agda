open import marking.prelude

open import marking.typ
open import marking.ctx
open import marking.uexp
open import marking.mexp
open import marking.erasure

module marking.lemmas where
  -- membership type equality
  ∋→τ-≡ : ∀ {Γ x τ₁ τ₂}
        → (Γ ∋ x ∶ τ₁)
        → (Γ ∋ x ∶ τ₂)
        → τ₁ ≡ τ₂
  ∋→τ-≡ Z         Z         = refl
  ∋→τ-≡ Z         (S x≢x _) = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S x≢x _) Z         = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S _ ∋x)  (S _ ∋x′) = ∋→τ-≡ ∋x ∋x′

  -- membership derivation equality
  ∋-≡ : ∀ {Γ x τ}
      → (∋x : Γ ∋ x ∶ τ)
      → (∋x′ : Γ ∋ x ∶ τ)
      → ∋x ≡ ∋x′
  ∋-≡ Z           Z         = refl
  ∋-≡ Z           (S x≢x _) = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x _)   Z         = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x′ ∋x) (S x≢x′′ ∋x′)
    rewrite ¬-≡ x≢x′ x≢x′′
          | ∋-≡ ∋x ∋x′ = refl

  -- non-membership derivation equality
  ∌-≡ : ∀ {Γ y}
      → (∌y : Γ ∌ y)
      → (∌y′ : Γ ∌ y)
      → ∌y ≡ ∌y′
  ∌-≡ ∌y ∌y′ = assimilation ∌y ∌y′

  -- unmarked synthesis unicity
  ⇒-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ}
            → Γ ⊢ e ⇒ τ₁
            → Γ ⊢ e ⇒ τ₂
            → τ₁ ≡ τ₂
  ⇒-unicity USHole                 USHole                   = refl
  ⇒-unicity (USVar ∋x)             (USVar ∋x′)              = ∋→τ-≡ ∋x ∋x′
  ⇒-unicity (USLam e⇒τ₁)           (USLam e⇒τ₂)
    rewrite ⇒-unicity e⇒τ₁ e⇒τ₂                             = refl
  ⇒-unicity (USAp e₁⇒τ₁ τ▸ e₂⇐τ₂)  (USAp e₁⇒τ₁′ τ▸′ e₂⇐τ₂′)
    rewrite ⇒-unicity e₁⇒τ₁ e₁⇒τ₁′
    with refl ← ▸-→-unicity τ▸ τ▸′                          = refl
  ⇒-unicity USNum                  USNum                    = refl
  ⇒-unicity (USPlus e₁⇐num e₂⇐num) (USPlus e₁⇐num′ e₂⇐num′) = refl

  -- an expression that synthesizes a type may be analyzed against a consistent type
  -- note that this NOT true with a lub (where the unknown type is the top of the imprecision partial order) definition
  ⇒-~-⇐ : ∀ {Γ : Ctx} {e : UExp} {τ τ′ : Typ} → Γ ⊢ e ⇒ τ → τ′ ~ τ → Γ ⊢ e ⇐ τ′
  ⇒-~-⇐ USHole τ′~τ = UASubsume USHole ~-unknown₂ USuHole
  ⇒-~-⇐ (USVar ∋x) τ′~τ = UASubsume (USVar ∋x) τ′~τ USuVar
  ⇒-~-⇐ (USLam e⇒τ₂) τ′~τ
    with ⟨ τ₁′ , ⟨ τ₂′ , τ′▸ ⟩ ⟩ ← ~→▸-→ τ′~τ
    with TCArr τ₁″~τ₁′ τ₂″~τ₂′ ← ~-▸-→→~ τ′~τ τ′▸
    with e⇐τ₂′ ← ⇒-~-⇐ e⇒τ₂ (~-sym τ₂″~τ₂′)
       = UALam τ′▸ τ₁″~τ₁′ e⇐τ₂′
  ⇒-~-⇐ (USAp e₁⇒τ τ▸ e₂⇐τ₁) τ′~τ₂ = UASubsume (USAp e₁⇒τ τ▸ e₂⇐τ₁) τ′~τ₂ USuAp
  ⇒-~-⇐ USNum τ′~num = UASubsume USNum τ′~num USuNum
  ⇒-~-⇐ (USPlus e₁⇐num e₂⇐num) τ′~num = UASubsume (USPlus e₁⇐num e₂⇐num) τ′~num USuPlus

  -- synthesis totality
  ⊢⇐-⊢⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → ∃[ τ′ ] Σ[ ě′ ∈ Γ ⊢⇒ τ′ ] ě ⇐□ ≡ ě′ ⇒□
  ⊢⇐-⊢⇒ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]
    with ⟨ τ′ , ⟨ ě′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě rewrite eq
       = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě′ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ ⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ]
    with ⟨ τ′ , ⟨ ě′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě rewrite eq
       = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě′ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ ⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]
    with ⟨ τ′ , ⟨ ě′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě rewrite eq
       = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě′ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ (⊢⸨_⸩[_∙_] {τ′ = τ′} ě τ~̸τ′ su) = ⟨ τ′ , ⟨ ě , refl ⟩ ⟩
  ⊢⇐-⊢⇒ (⊢∙_[_∙_]  {τ′ = τ′} ě τ~τ′ su) = ⟨ τ′ , ⟨ ě , refl ⟩ ⟩

  -- analysis totality
  private
    ⊢⇒-⊢⇐-subsume : ∀ {Γ τ τ′} → (ě : Γ ⊢⇒ τ) → (su : MSubsumable ě) → Σ[ ě′ ∈ Γ ⊢⇐ τ′ ] ě ⇒□ ≡ ě′ ⇐□
    ⊢⇒-⊢⇐-subsume {τ = τ} {τ′ = τ′} ě su
      with τ′ ~? τ 
    ...  | yes τ′~τ = ⟨ ⊢∙ ě [ τ′~τ ∙ su ] , refl ⟩
    ...  | no  τ′~̸τ = ⟨ ⊢⸨ ě ⸩[ τ′~̸τ ∙ su ] , refl ⟩

  ⊢⇒-⊢⇐ : ∀ {Γ τ τ′} → (ě : Γ ⊢⇒ τ) → Σ[ ě′ ∈ Γ ⊢⇐ τ′ ] ě ⇒□ ≡ ě′ ⇐□
  ⊢⇒-⊢⇐ (⊢⦇-⦈^ u)                       = ⟨ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] , refl ⟩
  ⊢⇒-⊢⇐ ě@(⊢ ∋x)                        = ⊢⇒-⊢⇐-subsume ě MSuVar
  ⊢⇒-⊢⇐ {τ′ = τ′} (⊢λ x ∶ τ ∙ ě)
    with τ′ ▸-→?
  ...  | no  τ′!▸
           with ⟨ ě′ , eq ⟩ ← ⊢⇒-⊢⇐ ě rewrite eq
              = ⟨ ⊢⸨λ x ∶ τ ∙ ě′ ⸩[ τ′!▸ ] , refl ⟩
  ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩
           with τ ~? τ₁
  ...         | yes τ~τ₁
                  with ⟨ ě′ , eq ⟩ ← ⊢⇒-⊢⇐ ě rewrite eq
                     = ⟨ ⊢λ x ∶ τ ∙ ě′ [ τ′▸ ∙ τ~τ₁ ] , refl ⟩
  ...         | no  τ~̸τ₁
                  with ⟨ ě′ , eq ⟩ ← ⊢⇒-⊢⇐ ě rewrite eq
                     = ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě′ [ τ′▸ ∙ τ~̸τ₁ ] , refl ⟩
  ⊢⇒-⊢⇐ ě@(⊢ ě₁ ∙ ě₂ [ τ▸ ])                  = ⊢⇒-⊢⇐-subsume ě MSuAp1
  ⊢⇒-⊢⇐ ě@(⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ])               = ⊢⇒-⊢⇐-subsume ě MSuAp2
  ⊢⇒-⊢⇐ ě@(⊢ℕ n)                              = ⊢⇒-⊢⇐-subsume ě MSuNum
  ⊢⇒-⊢⇐ ě@(⊢ ě₁ + ě₂)                         = ⊢⇒-⊢⇐-subsume ě MSuPlus
  ⊢⇒-⊢⇐ ě@(⊢⟦ ∌y ⟧)                           = ⊢⇒-⊢⇐-subsume ě MSuFree
