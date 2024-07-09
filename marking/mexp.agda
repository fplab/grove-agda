open import marking.prelude

open import marking.id
open import marking.var
open import marking.typ
open import marking.gtyp
open import marking.ctx
open import marking.multiparents

-- instrinsically typed marked expressions
module marking.mexp where
  infix  4 _⊢⇒_∣_
  infix  4 _⊢⇐_∣_
  infix  4 _⊢⇒s_∣_
  infix  4 _⊢⇐s_∣_

  mutual
    -- synthesis
    data _⊢⇒_∣_ : (Γ : Ctx) (τ : Typ) (𝕞 : MultiParents) → Set where
      -- MSVar
      ⊢_^_ : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → (u : VertexId)
        → Γ ⊢⇒ τ ∣ []

      -- MSLam
      ⊢λ_∶_∙_^_ : ∀ {Γ τ' 𝕞}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇒s τ' ∣ 𝕞)
        → (u : VertexId)
        → Γ ⊢⇒ (τ △) -→ τ' ∣ 𝕞

      -- MSAp1
      ⊢_∙_[_]^_ : ∀ {Γ τ τ₁ τ₂ 𝕞₁ 𝕞₂}
        → (ě₁ : Γ ⊢⇒s τ ∣ 𝕞₁)
        → (ě₂ : Γ ⊢⇐s τ₁ ∣ 𝕞₂)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (u : VertexId)
        → Γ ⊢⇒ τ₂ ∣ 𝕞₁ ++ 𝕞₂

      -- MSAp2
      ⊢⸨_⸩∙_[_]^_ : ∀ {Γ τ 𝕞₁ 𝕞₂}
        → (ě₁ : Γ ⊢⇒s τ ∣ 𝕞₁)
        → (ě₂ : Γ ⊢⇐s unknown ∣ 𝕞₂)
        → (τ!▸ : τ !▸-→)
        → (u : VertexId)
        → Γ ⊢⇒ unknown ∣ 𝕞₁ ++ 𝕞₂

      -- MSNum
      ⊢ℕ_^_ : ∀ {Γ}
        → (n : ℕ)
        → (u : VertexId)
        → Γ ⊢⇒ num ∣ []

      -- MSPlus
      ⊢_+_^_ : ∀ {Γ 𝕞₁ 𝕞₂}
        → (ě₁ : Γ ⊢⇐s num ∣ 𝕞₁)
        → (ě₂ : Γ ⊢⇐s num ∣ 𝕞₂)
        → (u : VertexId)
        → Γ ⊢⇒ num ∣ 𝕞₁ ++ 𝕞₂

      -- MSFree
      ⊢⟦_⟧^_ : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → (u : VertexId)
        → Γ ⊢⇒ unknown ∣ []

      ⊢⋎^_ : ∀ {Γ}
        → (u : VertexId)
        → Γ ⊢⇒ unknown ∣ ∣[ ⟨ u , Γ , Syn ⟩ ]

      ⊢↻^_ : ∀ {Γ}
        → (u : VertexId)
        → Γ ⊢⇒ unknown ∣ ∣[ ⟨ u , Γ , Syn ⟩ ]

    data _⊢⇒s_∣_ : (Γ : Ctx) (τ : Typ) (𝕞 : MultiParents) → Set where
      -- MSubSHole: \vdash\sq^_^_
      ⊢□^_^_ : ∀ {Γ}
        → (w : EdgeId)
        → (p : Position)
        → Γ ⊢⇒s unknown ∣ []

      -- MSubSJust
      ⊢∶ : ∀ {Γ τ 𝕞}
        → (ė : EdgeId × Γ ⊢⇒ τ ∣ 𝕞)
        → Γ ⊢⇒s τ ∣ 𝕞

      -- MSubSConflict: \vdash\curlywedge_
      -- TODO synthesize meet?
      ⊢⋏_ : ∀ {Γ}
        → (ė* : List (EdgeId × ∃[ τ ] ∃[ 𝕞 ] Γ ⊢⇒ τ ∣ 𝕞))
        → Γ ⊢⇒s unknown ∣ (concat (map (λ { ⟨ _ , ⟨ _ , ⟨ 𝕞 , _ ⟩ ⟩ ⟩ → 𝕞 }) ė*))

    data MSubsumable : {Γ : Ctx} {τ : Typ} {𝕞 : MultiParents} → (ě : Γ ⊢⇒ τ ∣ 𝕞) → Set where
      MSuVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → MSubsumable {Γ} (⊢ ∋x ^ u)

      MSuAp1 : ∀ {Γ u τ τ₁ τ₂ 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇒s τ ∣ 𝕞₁}
        → {ě₂ : Γ ⊢⇐s τ₁ ∣ 𝕞₂}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MSubsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MSuAp2 : ∀ {Γ u τ 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇒s τ ∣ 𝕞₁}
        → {ě₂ : Γ ⊢⇐s unknown ∣ 𝕞₂}
        → {τ!▸ : τ !▸-→}
        → MSubsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u)

      MSuNum : ∀ {Γ u}
        → {n : ℕ}
        → MSubsumable {Γ} (⊢ℕ n ^ u)

      MSuPlus : ∀ {Γ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇐s num ∣ 𝕞₁}
        → {ě₂ : Γ ⊢⇐s num ∣ 𝕞₂}
        → MSubsumable {Γ} (⊢ ě₁ + ě₂ ^ u)

      MSuFree : ∀ {Γ y u}
        → {∌y : Γ ∌ y}
        → MSubsumable {Γ} (⊢⟦ ∌y ⟧^ u)

      MSuMultiParent : ∀ {Γ u}
        → MSubsumable {Γ} (⊢⋎^ u)

      MSuUnicycle : ∀ {Γ u}
        → MSubsumable {Γ} (⊢↻^ u)

    -- analysis
    data _⊢⇐_∣_ : (Γ : Ctx) (τ : Typ) (𝕞 : MultiParents) → Set where
      -- MALam1
      ⊢λ_∶_∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃ 𝕞}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇐s τ₂ ∣ 𝕞)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △) ~ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃ ∣ 𝕞

      -- MALam2
      ⊢⸨λ_∶_∙_⸩[_]^_ : ∀ {Γ τ' 𝕞}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇐s unknown ∣ 𝕞)
        → (τ'!▸ : τ' !▸-→)
        → (u : VertexId)
        → Γ ⊢⇐ τ' ∣ 𝕞

      -- MALam3
      ⊢λ_∶⸨_⸩∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃ 𝕞}
        → (x : Var)
        → (τ : GTyp)
        → (ě : Γ , x ∶ (τ △) ⊢⇐s τ₂ ∣ 𝕞)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ △) ~̸ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃ ∣ 𝕞

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ' 𝕞}
        → (ě : Γ ⊢⇒ τ' ∣ 𝕞)
        → (τ~̸τ' : τ ~̸ τ')
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ ∣ 𝕞

      -- MASubsume
      ⊢∙_[_∙_] : ∀ {Γ τ τ' 𝕞}
        → (ě : Γ ⊢⇒ τ' ∣ 𝕞)
        → (τ~τ' : τ ~ τ')
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ ∣ 𝕞

    data _⊢⇐s_∣_ : (Γ : Ctx) (τ : Typ) (𝕞 : MultiParents) → Set where
      -- MSubASubsume
      ⊢∙_[_] : ∀ {Γ τ τ' 𝕞}
        → (ě : Γ ⊢⇒s τ' ∣ 𝕞)
        → (τ~τ' : τ ~ τ')
        → Γ ⊢⇐s τ ∣ 𝕞

      -- MSubAInconsistentTypes
      ⊢⸨_⸩[_] : ∀ {Γ τ τ' 𝕞}
        → (ě : Γ ⊢⇒s τ' ∣ 𝕞)
        → (τ~̸τ' : τ ~̸ τ')
        → Γ ⊢⇐s τ ∣ 𝕞

  mutual
    data Markless⇒ : ∀ {Γ τ 𝕞} → (ě : Γ ⊢⇒ τ ∣ 𝕞) → Set where
      MLSVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → Markless⇒ {Γ} (⊢ ∋x ^ u)

      MLSLam : ∀ {Γ τ' x τ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇒s τ' ∣ 𝕞}
        → (less : Markless⇒s ě)
        → Markless⇒ {Γ} (⊢λ x ∶ τ ∙ ě ^ u)

      MLSAp : ∀ {Γ τ τ₁ τ₂ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇒s τ ∣ 𝕞₁}
        → {ě₂ : Γ ⊢⇐s τ₁ ∣ 𝕞₂}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (less₁ : Markless⇒s ě₁)
        → (less₂ : Markless⇐s ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MLSNum : ∀ {Γ n u}
        → Markless⇒ {Γ} (⊢ℕ n ^ u)

      MLSPlus : ∀ {Γ u 𝕞₁ 𝕞₂}
        → {ě₁ : Γ ⊢⇐s num ∣ 𝕞₁}
        → {ě₂ : Γ ⊢⇐s num ∣ 𝕞₂}
        → (less₁ : Markless⇐s ě₁)
        → (less₂ : Markless⇐s ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ + ě₂ ^ u)

      MLSMultiParent : ∀ {Γ u}
        → Markless⇒ {Γ} (⊢⋎^ u)

      MLSUnicycle : ∀ {Γ u}
        → Markless⇒ {Γ} (⊢↻^ u)

    data Markless⇒s : ∀ {Γ τ 𝕞} → (ě : Γ ⊢⇒s τ ∣ 𝕞) → Set where
      MLSubSHole : ∀ {Γ w p}
        → Markless⇒s {Γ} (⊢□^ w ^ p)

      MLSubSJust : ∀ {Γ w τ 𝕞}
        → {ě : Γ ⊢⇒ τ ∣ 𝕞}
        → (less : Markless⇒ ě)
        → Markless⇒s {Γ} (⊢∶ ⟨ w , ě ⟩)

      -- TODO maybe this is a mark?
      MLSubSConflict : ∀ {Γ}
        → {ė* : List (EdgeId × ∃[ τ ] ∃[ 𝕞 ] Γ ⊢⇒ τ ∣ 𝕞)}
        → (less* : All (λ { ⟨ _ , ⟨ _ , ⟨ _ , ě ⟩ ⟩ ⟩ → Markless⇒ ě }) ė*)
        → Markless⇒s {Γ} (⊢⋏ ė*)

    data Markless⇐ : ∀ {Γ τ 𝕞} → (ě : Γ ⊢⇐ τ ∣ 𝕞) → Set where
      MLALam : ∀ {Γ τ₁ τ₂ τ₃ x τ u 𝕞}
        → {ě : Γ , x ∶ (τ △) ⊢⇐s τ₂ ∣ 𝕞}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : (τ △) ~ τ₁}
        → (less : Markless⇐s ě)
        → Markless⇐ {Γ} (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)

      MLASubsume : ∀ {Γ τ τ' 𝕞}
        → {ě : Γ ⊢⇒ τ' ∣ 𝕞}
        → {τ~τ' : τ ~ τ'}
        → {su : MSubsumable ě}
        → (less : Markless⇒ ě)
        → Markless⇐ {Γ} (⊢∙ ě [ τ~τ' ∙ su ])

    data Markless⇐s : ∀ {Γ τ 𝕞} → (ě : Γ ⊢⇐s τ ∣ 𝕞) → Set where
      MLSubASubsume : ∀ {Γ τ τ' 𝕞}
        → {ě : Γ ⊢⇒s τ' ∣ 𝕞}
        → {τ~τ' : τ ~ τ'}
        → (less : Markless⇒s ě)
        → Markless⇐s {Γ} (⊢∙ ě [ τ~τ' ])
