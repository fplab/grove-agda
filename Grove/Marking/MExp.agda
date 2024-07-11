open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Grove.Ident
open import Grove.Marking.Var
open import Grove.Marking.Typ
open import Grove.Marking.GTyp
open import Grove.Marking.Ctx

open import Grove.Marking.Grove using (Vertex; Source)

-- instrinsically typed marked expressions
module Grove.Marking.MExp where
  infix  4 _⊢⇒_
  infix  4 _⊢⇐_
  infix  4 _⊢⇒s_
  infix  4 _⊢⇐s_

  mutual
    -- synthesis
    data _⊢⇒_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSVar
      ⊢_^_ : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → (u : VertexId)
        → Γ ⊢⇒ τ

      -- MSLam
      ⊢λ_∶_∙_^_ : ∀ {Γ τ'}
        → (x : Var)
        → (τ : GChildTyp)
        → (ě : Γ , x ∶ (τ △s) ⊢⇒s τ')
        → (u : VertexId)
        → Γ ⊢⇒ (τ △s) -→ τ'

      -- MSAp1
      ⊢_∙_[_]^_ : ∀ {Γ τ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒s τ)
        → (ě₂ : Γ ⊢⇐s τ₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (u : VertexId)
        → Γ ⊢⇒ τ₂

      -- MSAp2
      ⊢⸨_⸩∙_[_]^_ : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇒s τ)
        → (ě₂ : Γ ⊢⇐s unknown)
        → (τ!▸ : τ !▸-→)
        → (u : VertexId)
        → Γ ⊢⇒ unknown

      -- MSNum
      ⊢ℕ_^_ : ∀ {Γ}
        → (n : ℕ)
        → (u : VertexId)
        → Γ ⊢⇒ num

      -- MSPlus
      ⊢_+_^_ : ∀ {Γ}
        → (ě₁ : Γ ⊢⇐s num)
        → (ě₂ : Γ ⊢⇐s num)
        → (u : VertexId)
        → Γ ⊢⇒ num

      -- MSFree
      ⊢⟦_⟧^_ : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → (u : VertexId)
        → Γ ⊢⇒ unknown

      ⊢⋎^_^_ : ∀ {Γ}
        → (w : EdgeId)
        → (v : Vertex)
        → Γ ⊢⇒ unknown

      ⊢↻^_^_ : ∀ {Γ}
        → (w : EdgeId)
        → (v : Vertex)
        → Γ ⊢⇒ unknown

    data _⊢⇒s_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSHole: \vdash\sq
      ⊢□ : ∀ {Γ}
        → (s : Source)
        → Γ ⊢⇒s unknown

      -- MSOnly
      ⊢∶ : ∀ {Γ τ}
        → (ė : EdgeId × Γ ⊢⇒ τ)
        → Γ ⊢⇒s τ

      -- MSLocalConflict: \vdash\curlywedge
      ⊢⋏ : ∀ {Γ}
        → (s : Source)
        → (ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ))
        → Γ ⊢⇒s unknown

    data MSubsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      MSuVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → MSubsumable {Γ} (⊢ ∋x ^ u)

      MSuAp1 : ∀ {Γ u τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MSubsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MSuAp2 : ∀ {Γ u τ}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s unknown}
        → {τ!▸ : τ !▸-→}
        → MSubsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u)

      MSuNum : ∀ {Γ u}
        → {n : ℕ}
        → MSubsumable {Γ} (⊢ℕ n ^ u)

      MSuPlus : ∀ {Γ u}
        → {ě₁ : Γ ⊢⇐s num}
        → {ě₂ : Γ ⊢⇐s num}
        → MSubsumable {Γ} (⊢ ě₁ + ě₂ ^ u)

      MSuFree : ∀ {Γ y u}
        → {∌y : Γ ∌ y}
        → MSubsumable {Γ} (⊢⟦ ∌y ⟧^ u)

    -- analysis
    data _⊢⇐_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MALam1
      ⊢λ_∶_∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : GChildTyp)
        → (ě : Γ , x ∶ (τ △s) ⊢⇐s τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △s) ~ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃

      -- MALam2
      ⊢⸨λ_∶_∙_⸩[_]^_ : ∀ {Γ τ'}
        → (x : Var)
        → (τ : GChildTyp)
        → (ě : Γ , x ∶ (τ △s) ⊢⇐s unknown)
        → (τ'!▸ : τ' !▸-→)
        → (u : VertexId)
        → Γ ⊢⇐ τ'

      -- MALam3
      ⊢λ_∶⸨_⸩∙_[_∙_]^_ : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : GChildTyp)
        → (ě : Γ , x ∶ (τ △s) ⊢⇐s τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ △s) ~̸ τ₁)
        → (u : VertexId)
        → Γ ⊢⇐ τ₃

      ⊢⋎^_^_ : ∀ {Γ τ}
        → (w : EdgeId)
        → (v : Vertex)
        → Γ ⊢⇐ τ

      ⊢↻^_^_ : ∀ {Γ τ}
        → (w : EdgeId)
        → (v : Vertex)
        → Γ ⊢⇐ τ

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒ τ')
        → (τ~̸τ' : τ ~̸ τ')
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ

      -- MASubsume
      ⊢∙_[_∙_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒ τ')
        → (τ~τ' : τ ~ τ')
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ

    data _⊢⇐s_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MAHole: \vdash\sq
      ⊢□ : ∀ {Γ τ}
        → (s : Source)
        → Γ ⊢⇐s τ

      -- MAOnly
      ⊢∶ : ∀ {Γ τ}
        → (ė : EdgeId × Γ ⊢⇐ τ)
        → Γ ⊢⇐s τ

      -- MALocalConflict: \vdash\curlywedge
      ⊢⋏ : ∀ {Γ τ}
        → (s : Source)
        → (ė* : List (EdgeId × Γ ⊢⇐ τ))
        → Γ ⊢⇐s τ

  mutual
    data Markless⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → Set where
      MLSVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → Markless⇒ {Γ} (⊢ ∋x ^ u)

      MLSLam : ∀ {Γ τ' x τ u}
        → {ě : Γ , x ∶ (τ △s) ⊢⇒s τ'}
        → (less : Markless⇒s ě)
        → Markless⇒ {Γ} (⊢λ x ∶ τ ∙ ě ^ u)

      MLSAp : ∀ {Γ τ τ₁ τ₂ u}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (less₁ : Markless⇒s ě₁)
        → (less₂ : Markless⇐s ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MLSNum : ∀ {Γ n u}
        → Markless⇒ {Γ} (⊢ℕ n ^ u)

      MLSPlus : ∀ {Γ u}
        → {ě₁ : Γ ⊢⇐s num}
        → {ě₂ : Γ ⊢⇐s num}
        → (less₁ : Markless⇐s ě₁)
        → (less₂ : Markless⇐s ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ + ě₂ ^ u)

      MLSMultiLocationConflict : ∀ {Γ w v}
        → Markless⇒ {Γ} (⊢⋎^ w ^ v)

      MLSCycleLocationConflict : ∀ {Γ w v}
        → Markless⇒ {Γ} (⊢↻^ w ^ v)

    data Markless⇒s : ∀ {Γ τ} → (ě : Γ ⊢⇒s τ) → Set where
      MLSHole : ∀ {Γ s}
        → Markless⇒s {Γ} (⊢□ s)

      MLSOnly : ∀ {Γ w τ}
        → {ě : Γ ⊢⇒ τ}
        → (less : Markless⇒ ě)
        → Markless⇒s {Γ} (⊢∶ (w , ě))

      MLSLocalConflict : ∀ {Γ s}
        → {ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)}
        → (less* : All (λ { (_ , _ , ě) → Markless⇒ ě }) ė*)
        → Markless⇒s {Γ} (⊢⋏ s ė*)

    data Markless⇐ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → Set where
      MLALam : ∀ {Γ τ₁ τ₂ τ₃ x τ u}
        → {ě : Γ , x ∶ (τ △s) ⊢⇐s τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : (τ △s) ~ τ₁}
        → (less : Markless⇐s ě)
        → Markless⇐ {Γ} (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]^ u)

      MLAMultiLocationConflict : ∀ {Γ w v τ}
        → Markless⇐ {Γ} (⊢⋎^_^_ {τ = τ} w v)

      MLACycleLocationConflict : ∀ {Γ w v τ}
        → Markless⇐ {Γ} (⊢↻^_^_ {τ = τ} w v)

      MLASubsume : ∀ {Γ τ τ'}
        → {ě : Γ ⊢⇒ τ'}
        → {τ~τ' : τ ~ τ'}
        → {su : MSubsumable ě}
        → (less : Markless⇒ ě)
        → Markless⇐ {Γ} (⊢∙ ě [ τ~τ' ∙ su ])

    data Markless⇐s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → Set where
      MLAHole : ∀ {Γ s τ}
        → Markless⇐s {Γ} (⊢□ {τ = τ} s)

      MLAOnly : ∀ {Γ w τ}
        → {ě : Γ ⊢⇐ τ}
        → (less : Markless⇐ ě)
        → Markless⇐s {Γ} (⊢∶ (w , ě))

      MLALocalConflict : ∀ {Γ s τ}
        → {ė* : List (EdgeId × Γ ⊢⇐ τ)}
        → (less* : All (λ { (_ , ě) → Markless⇐ ě }) ė*)
        → Markless⇐s {Γ} (⊢⋏ s ė*)
