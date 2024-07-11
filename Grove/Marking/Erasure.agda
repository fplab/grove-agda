open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (yes; no)

open import Grove.Ident
open import Grove.Marking.Typ
open import Grove.Marking.GTyp
open import Grove.Marking.UExp
open import Grove.Marking.MExp

module Grove.Marking.Erasure where
  mutual
    _⇒□ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → UExp
    (⊢_^_ {x = x} ∋x u)      ⇒□ = - x ^ u
    (⊢λ x ∶ τ ∙ ě ^ u)       ⇒□ = -λ x ∶ τ ∙ (ě ⇒□s) ^ u
    (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)    ⇒□ = - (ě₁ ⇒□s) ∙ (ě₂ ⇐□s) ^ u
    (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u) ⇒□ = - (ě₁ ⇒□s) ∙ (ě₂ ⇐□s) ^ u
    (⊢ℕ n ^ u)               ⇒□ = -ℕ n ^ u
    (⊢ ě₁ + ě₂ ^ u)          ⇒□ = - (ě₁ ⇐□s) + (ě₂ ⇐□s) ^ u
    (⊢⟦_⟧^_ {y = y} ∌y u)    ⇒□ = - y ^ u
    (⊢⋎^ w ^ v)              ⇒□ = -⋎^ w ^ v
    (⊢↻^ w ^ v)              ⇒□ = -↻^ w ^ v

    _⇒□s : ∀ {Γ τ} → (ě : Γ ⊢⇒s τ) → UChildExp
    (⊢□ s)       ⇒□s = -□ s
    (⊢∶ (w , ě)) ⇒□s = -∶ (w , ě ⇒□)
    (⊢⋏ s ė*)    ⇒□s = -⋏ s (ė* ⇒□s*)

    _⇒□s* : ∀ {Γ} → (ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)) → List UChildExp'
    []                 ⇒□s* = []
    ((w , _ , ě) ∷ ė*) ⇒□s* = (w , ě ⇒□) ∷ (ė* ⇒□s*)

    _⇐□ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → UExp
    (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)   ⇐□ = -λ x ∶ τ ∙ (ě ⇐□s) ^ u
    (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u)       ⇐□ = -λ x ∶ τ ∙ (ě ⇐□s) ^ u
    (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u) ⇐□ = -λ x ∶ τ ∙ (ě ⇐□s) ^ u
    ⊢⸨ ě ⸩[ τ~̸τ' ∙ su ]                ⇐□ = ě ⇒□
    ⊢∙ ě [ τ~τ' ∙ su ]                 ⇐□ = ě ⇒□

    _⇐□s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → UChildExp
    ⊢∙ ě [ τ~τ' ] ⇐□s  = ě ⇒□s
    ⊢⸨ ě ⸩[ τ~̸τ' ] ⇐□s = ě ⇒□s

  mutual
    ⊢⇐-⊢⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → ∃[ τ' ] Σ[ ě' ∈ Γ ⊢⇒ τ' ] ě ⇐□ ≡ ě' ⇒□
    ⊢⇐-⊢⇒ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)
      with τ' , ě' , eq ← ⊢⇐s-⊢⇒s ě rewrite eq
         = (τ △s) -→ τ' , ⊢λ x ∶ τ ∙ ě' ^ u , refl
    ⊢⇐-⊢⇒ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ'!▸ ]^ u)
      with τ' , ě' , eq ← ⊢⇐s-⊢⇒s ě rewrite eq
         = (τ △s) -→ τ' , ⊢λ x ∶ τ ∙ ě' ^ u , refl
    ⊢⇐-⊢⇒ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]^ u)
      with τ' , ě' , eq ← ⊢⇐s-⊢⇒s ě rewrite eq
         = (τ △s) -→ τ' , ⊢λ x ∶ τ ∙ ě' ^ u , refl
    ⊢⇐-⊢⇒ (⊢⸨_⸩[_∙_] {τ' = τ'} ě τ~̸τ' su) = τ' , ě , refl
    ⊢⇐-⊢⇒ (⊢∙_[_∙_]  {τ' = τ'} ě τ~τ' su) = τ' , ě , refl

    ⊢⇐s-⊢⇒s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → ∃[ τ' ] Σ[ ě' ∈ Γ ⊢⇒s τ' ] ě ⇐□s ≡ ě' ⇒□s
    ⊢⇐s-⊢⇒s (⊢∙_[_]  {τ' = τ'} ě τ~τ') = τ' , ě , refl
    ⊢⇐s-⊢⇒s (⊢⸨_⸩[_] {τ' = τ'} ě τ~τ') = τ' , ě , refl

  private
    ⊢⇒-⊢⇐-subsume : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒ τ) → (su : MChildsumable ě) → Σ[ ě' ∈ Γ ⊢⇐ τ' ] ě ⇒□ ≡ ě' ⇐□
    ⊢⇒-⊢⇐-subsume {τ = τ} {τ' = τ'} ě su
      with τ' ~? τ 
    ...  | yes τ'~τ = ⊢∙ ě [ τ'~τ ∙ su ]  , refl
    ...  | no  τ'~̸τ = ⊢⸨ ě ⸩[ τ'~̸τ ∙ su ] , refl

    ⊢⇒s-⊢⇐s-subsume : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒s τ) → Σ[ ě' ∈ Γ ⊢⇐s τ' ] ě ⇒□s ≡ ě' ⇐□s
    ⊢⇒s-⊢⇐s-subsume {τ = τ} {τ' = τ'} ě
      with τ' ~? τ 
    ...  | yes τ'~τ = ⊢∙ ě [ τ'~τ ]  , refl
    ...  | no  τ'~̸τ = ⊢⸨ ě ⸩[ τ'~̸τ ] , refl

  mutual
    ⊢⇒-⊢⇐ : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒ τ) → Σ[ ě' ∈ Γ ⊢⇐ τ' ] ě ⇒□ ≡ ě' ⇐□
    ⊢⇒-⊢⇐ ě@(⊢ ∋x ^ u)                        = ⊢⇒-⊢⇐-subsume ě MSuVar
    ⊢⇒-⊢⇐ {τ' = τ'} (⊢λ x ∶ τ ∙ ě ^ u)
      with τ' ▸-→?
    ...  | no  τ'!▸ with ě' , eq ← ⊢⇒s-⊢⇐s ě rewrite eq
         = ⊢⸨λ x ∶ τ ∙ ě' ⸩[ τ'!▸ ]^ u , refl
    ...  | yes (τ₁ , τ₂ , τ'▸) with (τ △s) ~? τ₁
    ...    | yes τ~τ₁ with ě' , eq ← ⊢⇒s-⊢⇐s ě rewrite eq
           = ⊢λ x ∶ τ ∙ ě' [ τ'▸ ∙ τ~τ₁ ]^ u , refl
    ...    | no  τ~̸τ₁ with ě' , eq ← ⊢⇒s-⊢⇐s ě rewrite eq
           = ⊢λ x ∶⸨ τ ⸩∙ ě' [ τ'▸ ∙ τ~̸τ₁ ]^ u , refl
    ⊢⇒-⊢⇐ ě@(⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)    = ⊢⇒-⊢⇐-subsume ě MSuAp1
    ⊢⇒-⊢⇐ ě@(⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u) = ⊢⇒-⊢⇐-subsume ě MSuAp2
    ⊢⇒-⊢⇐ ě@(⊢ℕ n ^ u)               = ⊢⇒-⊢⇐-subsume ě MSuNum
    ⊢⇒-⊢⇐ ě@(⊢ ě₁ + ě₂ ^ u)          = ⊢⇒-⊢⇐-subsume ě MSuPlus
    ⊢⇒-⊢⇐ ě@(⊢⟦ ∌y ⟧^ u)             = ⊢⇒-⊢⇐-subsume ě MSuFree
    ⊢⇒-⊢⇐ ě@(⊢⋎^ w ^ v)              = ⊢⇒-⊢⇐-subsume ě MSuMultiParent
    ⊢⇒-⊢⇐ ě@(⊢↻^ w ^ v)              = ⊢⇒-⊢⇐-subsume ě MSuCycleLocationConflict

    ⊢⇒s-⊢⇐s : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒s τ) → Σ[ ě' ∈ Γ ⊢⇐s τ' ] ě ⇒□s ≡ ě' ⇐□s
    ⊢⇒s-⊢⇐s ě = ⊢⇒s-⊢⇐s-subsume ě
