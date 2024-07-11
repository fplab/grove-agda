open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Grove.Ident
open import Grove.Marking.Var
open import Grove.Marking.Typ
open import Grove.Marking.GTyp
open import Grove.Marking.Ctx
open import Grove.Marking.MultiParents

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
      -- MChildSHole: \vdash\sq
      ⊢□ : ∀ {Γ}
        → (s : Source)
        → Γ ⊢⇒s unknown

      -- MChildSOnly
      ⊢∶ : ∀ {Γ τ}
        → (ė : EdgeId × Γ ⊢⇒ τ)
        → Γ ⊢⇒s τ

      -- MChildSLocalConflict: \vdash\curlywedge
      ⊢⋏ : ∀ {Γ}
        → (s : Source)
        → (ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ))
        → Γ ⊢⇒s unknown

    data MChildsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      MSuVar : ∀ {Γ x u τ}
        → {∋x : Γ ∋ x ∶ τ}
        → MChildsumable {Γ} (⊢ ∋x ^ u)

      MSuAp1 : ∀ {Γ u τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MChildsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ]^ u)

      MSuAp2 : ∀ {Γ u τ}
        → {ě₁ : Γ ⊢⇒s τ}
        → {ě₂ : Γ ⊢⇐s unknown}
        → {τ!▸ : τ !▸-→}
        → MChildsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]^ u)

      MSuNum : ∀ {Γ u}
        → {n : ℕ}
        → MChildsumable {Γ} (⊢ℕ n ^ u)

      MSuPlus : ∀ {Γ u}
        → {ě₁ : Γ ⊢⇐s num}
        → {ě₂ : Γ ⊢⇐s num}
        → MChildsumable {Γ} (⊢ ě₁ + ě₂ ^ u)

      MSuFree : ∀ {Γ y u}
        → {∌y : Γ ∌ y}
        → MChildsumable {Γ} (⊢⟦ ∌y ⟧^ u)

      MSuMultiParent : ∀ {Γ w v}
        → MChildsumable {Γ} (⊢⋎^ w ^ v)

      MSuCycleLocationConflict : ∀ {Γ w v}
        → MChildsumable {Γ} (⊢↻^ w ^ v)

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

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒ τ')
        → (τ~̸τ' : τ ~̸ τ')
        → (su : MChildsumable ě)
        → Γ ⊢⇐ τ

      -- MASubsume
      ⊢∙_[_∙_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒ τ')
        → (τ~τ' : τ ~ τ')
        → (su : MChildsumable ě)
        → Γ ⊢⇐ τ

    data _⊢⇐s_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MChildASubsume
      ⊢∙_[_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒s τ')
        → (τ~τ' : τ ~ τ')
        → Γ ⊢⇐s τ

      -- MChildAInconsistentTypes
      ⊢⸨_⸩[_] : ∀ {Γ τ τ'}
        → (ě : Γ ⊢⇒s τ')
        → (τ~̸τ' : τ ~̸ τ')
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
      MLSubSHole : ∀ {Γ s}
        → Markless⇒s {Γ} (⊢□ s)

      MLSubSOnly : ∀ {Γ w τ}
        → {ě : Γ ⊢⇒ τ}
        → (less : Markless⇒ ě)
        → Markless⇒s {Γ} (⊢∶ (w , ě))

      -- TODO maybe this is a mark?
      MLSubSLocalConflict : ∀ {Γ s}
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

      MLASubsume : ∀ {Γ τ τ'}
        → {ě : Γ ⊢⇒ τ'}
        → {τ~τ' : τ ~ τ'}
        → {su : MChildsumable ě}
        → (less : Markless⇒ ě)
        → Markless⇐ {Γ} (⊢∙ ě [ τ~τ' ∙ su ])

      -- TODO analysis cases for multiparent + unicycle conflicts

    data Markless⇐s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → Set where
      MLSubASubsume : ∀ {Γ τ τ'}
        → {ě : Γ ⊢⇒s τ'}
        → {τ~τ' : τ ~ τ'}
        → (less : Markless⇒s ě)
        → Markless⇐s {Γ} (⊢∙ ě [ τ~τ' ])

  mutual
    multiparents⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → MultiParents
    multiparents⇒ (⊢ _ ^ _)              = []
    multiparents⇒ (⊢λ _ ∶ _ ∙ ě ^ _)     = multiparents⇒s ě
    multiparents⇒ (⊢ ě₁ ∙ ě₂ [ _ ]^ _)   = (multiparents⇒s ě₁) ++ (multiparents⇐s ě₂)
    multiparents⇒ (⊢⸨ ě₁ ⸩∙ ě₂ [ _ ]^ _) = (multiparents⇒s ě₁) ++ (multiparents⇐s ě₂)
    multiparents⇒ (⊢ℕ _ ^ _)             = []
    multiparents⇒ (⊢ ě₁ + ě₂ ^ _)        = (multiparents⇐s ě₁) ++ (multiparents⇐s ě₂)
    multiparents⇒ (⊢⟦ _ ⟧^ _)            = []
    multiparents⇒ {Γ} (⊢⋎^ w ^ v)        = [ ⟨ v , w , Γ , Syn ⟩ ]
    multiparents⇒ {Γ} (⊢↻^ w ^ v)        = [ ⟨ v , w , Γ , Syn ⟩ ]

    multiparents⇒s : ∀ {Γ τ} → (ě : Γ ⊢⇒s τ) → MultiParents
    multiparents⇒s (⊢□ _)       = []
    multiparents⇒s (⊢∶ (_ , ě)) = multiparents⇒ ě
    multiparents⇒s (⊢⋏ _ ė*)    = multiparents⇒s* ė*

    multiparents⇒s* : ∀ {Γ} → (ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)) → MultiParents
    multiparents⇒s* []                 = []
    multiparents⇒s* ((_ , _ , ě) ∷ ė*) = (multiparents⇒ ě) ++ multiparents⇒s* ė*

    multiparents⇐ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → MultiParents
    multiparents⇐ (⊢λ _ ∶ _ ∙ ě [ _ ∙ _ ]^ _)   = multiparents⇐s ě
    multiparents⇐ (⊢⸨λ _ ∶ _ ∙ ě ⸩[ _ ]^ _)     = multiparents⇐s ě
    multiparents⇐ (⊢λ _ ∶⸨ _ ⸩∙ ě [ _ ∙ _ ]^ _) = multiparents⇐s ě
    multiparents⇐ ⊢⸨ ě ⸩[ _ ∙ _ ]               = multiparents⇒ ě
    multiparents⇐ ⊢∙ ě [ _ ∙ _ ]                = multiparents⇒ ě

    multiparents⇐s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → MultiParents
    multiparents⇐s ⊢∙ ě [ _ ]  = multiparents⇒s ě
    multiparents⇐s ⊢⸨ ě ⸩[ _ ] = multiparents⇒s ě
