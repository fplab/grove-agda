open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (yes; no)

open import Grove.Ident
open import Grove.Marking.STyp
open import Grove.Marking.Typ
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
    (⊢⋎^ w ^ v)                        ⇐□ = -⋎^ w ^ v
    (⊢↻^ w ^ v)                        ⇐□ = -↻^ w ^ v
    ⊢⸨ ě ⸩[ τ~̸τ' ∙ su ]                ⇐□ = ě ⇒□
    ⊢∙ ě [ τ~τ' ∙ su ]                 ⇐□ = ě ⇒□

    _⇐□s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → UChildExp
    (⊢□ s)       ⇐□s = -□ s
    (⊢∶ (w , ě)) ⇐□s = -∶ (w , ě ⇐□)
    (⊢⋏ s ė*)    ⇐□s = -⋏ s (ė* ⇐□s*)

    _⇐□s* : ∀ {Γ τ} → (ė* : List (EdgeId × Γ ⊢⇐ τ)) → List UChildExp'
    []             ⇐□s* = []
    ((w , ě) ∷ ė*) ⇐□s* = (w , ě ⇐□) ∷ (ė* ⇐□s*)

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
    ⊢⇐-⊢⇒ (⊢⋎^ w ^ v)                     = unknown , (⊢⋎^ w ^ v) , refl
    ⊢⇐-⊢⇒ (⊢↻^ w ^ v)                     = unknown , (⊢↻^ w ^ v) , refl
    ⊢⇐-⊢⇒ (⊢⸨_⸩[_∙_] {τ' = τ'} ě τ~̸τ' su) = τ' , ě , refl
    ⊢⇐-⊢⇒ (⊢∙_[_∙_]  {τ' = τ'} ě τ~τ' su) = τ' , ě , refl

    ⊢⇐s-⊢⇒s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → ∃[ τ' ] Σ[ ě' ∈ Γ ⊢⇒s τ' ] ě ⇐□s ≡ ě' ⇒□s
    ⊢⇐s-⊢⇒s (⊢□ s) = unknown , (⊢□ s) , refl
    ⊢⇐s-⊢⇒s (⊢∶ (w , ě)) 
      with τ' , ě' , eq ← ⊢⇐-⊢⇒ ě rewrite eq
         = τ' , (⊢∶ (w , ě')) , refl
    ⊢⇐s-⊢⇒s (⊢⋏ s ė*)
      with ė*' , eq* ← ⊢⇐s-⊢⇒s* ė*
      rewrite ⊢⇐s-⊢⇒s*-eq eq* = unknown , (⊢⋏ s ė*') , refl

    ⊢⇐s-⊢⇒s* : ∀ {Γ τ}
             → (ė* : List (EdgeId × Γ ⊢⇐ τ))
             → Σ[ ė*' ∈ List (EdgeId × ∃[ τ' ] Γ ⊢⇒ τ') ] Pointwise (λ { (w , ě) (w' , _ , ě') → w ≡ w' × ě ⇐□ ≡ ě' ⇒□ }) ė* ė*'
    ⊢⇐s-⊢⇒s* [] = [] , []
    ⊢⇐s-⊢⇒s* ((w , ě) ∷ ė*)
      with τ' , ě' , eq ← ⊢⇐-⊢⇒ ě
      with ė*' , eq* ← ⊢⇐s-⊢⇒s* ė*
         = (w , τ' , ě') ∷ ė*' , (refl , eq) ∷ eq*

    ⊢⇐s-⊢⇒s*-eq : ∀ {Γ τ} {ė* : List (EdgeId × Γ ⊢⇐ τ)}
      → {ė*' : List (EdgeId × ∃[ τ' ] Γ ⊢⇒ τ')}
      → (eq* : Pointwise (λ { (w , ě) (w' , _ , ě') → w ≡ w' × ě ⇐□ ≡ ě' ⇒□ }) ė* ė*')
      → ė* ⇐□s* ≡ ė*' ⇒□s*
    ⊢⇐s-⊢⇒s*-eq [] = refl
    ⊢⇐s-⊢⇒s*-eq ((weq , eq) ∷ eq*) rewrite weq | eq | ⊢⇐s-⊢⇒s*-eq eq* = refl

  private
    ⊢⇒-⊢⇐-subsume : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒ τ) → (su : MSubsumable ě) → Σ[ ě' ∈ Γ ⊢⇐ τ' ] ě ⇒□ ≡ ě' ⇐□
    ⊢⇒-⊢⇐-subsume {τ = τ} {τ' = τ'} ě su
      with τ' ~? τ 
    ...  | yes τ'~τ = ⊢∙ ě [ τ'~τ ∙ su ]  , refl
    ...  | no  τ'~̸τ = ⊢⸨ ě ⸩[ τ'~̸τ ∙ su ] , refl

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
    ⊢⇒-⊢⇐ ě@(⊢⋎^ w ^ v)              = (⊢⋎^ w ^ v) , refl
    ⊢⇒-⊢⇐ ě@(⊢↻^ w ^ v)              = (⊢↻^ w ^ v) , refl

    ⊢⇒s-⊢⇐s : ∀ {Γ τ τ'} → (ě : Γ ⊢⇒s τ) → Σ[ ě' ∈ Γ ⊢⇐s τ' ] ě ⇒□s ≡ ě' ⇐□s
    ⊢⇒s-⊢⇐s (⊢□ s) = ⊢□ s , refl
    ⊢⇒s-⊢⇐s (⊢∶ (w , ě))
      with ě' , eq ← ⊢⇒-⊢⇐ ě
      rewrite eq = (⊢∶ (w , ě')) , refl
    ⊢⇒s-⊢⇐s (⊢⋏ s ė*)
      with ė*' , eq* ← ⊢⇒s-⊢⇐s* ė*
      rewrite ⊢⇒s-⊢⇐s*-eq eq* = (⊢⋏ s ė*') , refl

    ⊢⇒s-⊢⇐s* : ∀ {Γ τ}
             → (ė* : List (EdgeId × ∃[ τ' ] Γ ⊢⇒ τ'))
             → Σ[ ė*' ∈ List (EdgeId × Γ ⊢⇐ τ) ] Pointwise (λ { (w , _ , ě) (w' , ě') → w ≡ w' × ě ⇒□ ≡ ě' ⇐□ }) ė* ė*'
    ⊢⇒s-⊢⇐s* [] = [] , []
    ⊢⇒s-⊢⇐s* ((w , τ , ě) ∷ ė*)
      with ě' , eq ← ⊢⇒-⊢⇐ ě
      with ė*' , eq* ← ⊢⇒s-⊢⇐s* ė*
         = (w , ě') ∷ ė*' , (refl , eq) ∷ eq*

    ⊢⇒s-⊢⇐s*-eq : ∀ {Γ τ} {ė* : List (EdgeId × ∃[ τ' ] Γ ⊢⇒ τ')}
      → {ė*' : List (EdgeId × Γ ⊢⇐ τ)}
      → (eq* : Pointwise (λ { (w , _ , ě) (w' , ě') → w ≡ w' × ě ⇒□ ≡ ě' ⇐□ }) ė* ė*')
      → ė* ⇒□s* ≡ ė*' ⇐□s*
    ⊢⇒s-⊢⇐s*-eq [] = refl
    ⊢⇒s-⊢⇐s*-eq ((weq , eq) ∷ eq*) rewrite weq | eq | ⊢⇒s-⊢⇐s*-eq eq* = refl
