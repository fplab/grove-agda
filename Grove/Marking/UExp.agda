open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Grove.Ident
open import Grove.Marking.Var
open import Grove.Marking.Typ
open import Grove.Marking.GTyp
open import Grove.Marking.Ctx

open import Grove.Marking.Grove using (Vertex; Source)

-- unmarked expressions
module Grove.Marking.UExp where
  infix  4 _⊢_⇒_
  infix  4 _⊢_⇐_
  infix  4 _⊢s_⇒_
  infix  4 _⊢s_⇐_

  mutual
    data UExp : Set where
      -_^_      : (x : Var) → (u : VertexId) → UExp
      -λ_∶_∙_^_ : (x : Var) → (τ : GChildTyp) → (e : UChildExp) → (u : VertexId) → UExp
      -_∙_^_    : (e₁ : UChildExp) → (e₂ : UChildExp) → (u : VertexId) → UExp
      -ℕ_^_     : (n : ℕ) → (u : VertexId) → UExp
      -_+_^_    : (e₁ : UChildExp) → (e₂ : UChildExp) → (u : VertexId) → UExp
      -⋎^_^_    : (w : EdgeId) → (v : Vertex) → UExp
      -↻^_^_    : (w : EdgeId) → (v : Vertex) → UExp

    -- TODO fix to match term representation
    data UChildExp : Set where
      -□ : (s : Source) → UChildExp
      -∶ : (ė : UChildExp') → UChildExp
      -⋏ : (s : Source) → (ė* : List UChildExp')  → UChildExp

    UChildExp' = EdgeId × UExp

  data USubsumable : UExp → Set where
    USuVar : ∀ {x u}
      → USubsumable (- x ^ u)

    USuAp : ∀ {e₁ e₂ u}
      → USubsumable (- e₁ ∙ e₂ ^ u)

    USuNum : ∀ {n u}
      → USubsumable (-ℕ n ^ u)

    USuPlus : ∀ {e₁ e₂ u}
      → USubsumable (- e₁ + e₂ ^ u)

  mutual
    -- synthesis
    data _⊢_⇒_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      USVar : ∀ {Γ x u τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ - x ^ u ⇒ τ

      USLam : ∀ {Γ x τ e u τ'}
        → (e⇒τ' : Γ , x ∶ (τ △s) ⊢s e ⇒ τ')
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ⇒ (τ △s) -→ τ'

      USAp : ∀ {Γ e₁ e₂ u τ τ₁ τ₂}
        → (e₁⇒τ : Γ ⊢s e₁ ⇒ τ)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₁⇐τ₁ : Γ ⊢s e₂ ⇐ τ₁)
        → Γ ⊢ - e₁ ∙ e₂ ^ u ⇒ τ₂

      USNum : ∀ {Γ n u}
        → Γ ⊢ -ℕ n ^ u ⇒ num

      USPlus : ∀ {Γ e₁ e₂ u}
        → (e₁⇐num : Γ ⊢s e₁ ⇐ num)
        → (e₂⇐num : Γ ⊢s e₂ ⇐ num)
        → Γ ⊢ - e₁ + e₂ ^ u ⇒ num

      USMultiLocationConflict : ∀ {Γ w v}
        → Γ ⊢ -⋎^ w ^ v ⇒ unknown

      USCycleLocationConflict : ∀ {Γ w v}
        → Γ ⊢ -↻^ w ^ v ⇒ unknown

    data _⊢s_⇒_ : (Γ : Ctx) (e : UChildExp) (τ : Typ) → Set where
      USHole : ∀ {Γ s}
        → Γ ⊢s -□ s ⇒ unknown

      USOnly : ∀ {Γ w e τ}
        → (e⇒τ : Γ ⊢ e ⇒ τ)
        → Γ ⊢s -∶ (w , e) ⇒ τ

      USLocalConflict : ∀ {Γ s ė*}
        → (ė⇒* : All (λ (_ , e) → ∃[ τ ] Γ ⊢ e ⇒ τ) ė*)
        → Γ ⊢s -⋏ s ė* ⇒ unknown

    -- analysis
    data _⊢_⇐_ : (Γ : Ctx) (e : UExp) (τ : Typ) → Set where
      UALam : ∀ {Γ x τ e u τ₁ τ₂ τ₃}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ △s) ~ τ₁)
        → (e⇐τ₂ : Γ , x ∶ (τ △s) ⊢s e ⇐ τ₂)
        → Γ ⊢ -λ x ∶ τ ∙ e ^ u ⇐ τ₃

      UAMultiLocationConflict : ∀ {Γ w v τ}
        → Γ ⊢ -⋎^ w ^ v ⇐ τ

      UACycleLocationConflict : ∀ {Γ w v τ}
        → Γ ⊢ -↻^ w ^ v ⇐ τ

      UASubsume : ∀ {Γ e τ τ'}
        → (e⇒τ' : Γ ⊢ e ⇒ τ')
        → (τ~τ' : τ ~ τ')
        → (su : USubsumable e)
        → Γ ⊢ e ⇐ τ

    data _⊢s_⇐_ : (Γ : Ctx) (e : UChildExp) (τ : Typ) → Set where
      UAHole : ∀ {Γ s τ}
        → Γ ⊢s -□ s ⇐ τ

      UAOnly : ∀ {Γ w e τ}
        → (e⇐τ : Γ ⊢ e ⇐ τ)
        → Γ ⊢s -∶ (w , e) ⇐ τ

      UALocalConflict : ∀ {Γ s ė* τ}
        → (ė⇐* : All (λ (_ , e) → Γ ⊢ e ⇐ τ) ė*)
        → Γ ⊢s -⋏ s ė* ⇐ τ

  -- synthesis unicity
  mutual
    ⇒-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ}
              → Γ ⊢ e ⇒ τ₁
              → Γ ⊢ e ⇒ τ₂
              → τ₁ ≡ τ₂
    ⇒-unicity (USVar ∋x)             (USVar ∋x')              = ∋→τ-≡ ∋x ∋x'
    ⇒-unicity (USLam e⇒τ₁)           (USLam e⇒τ₂)
      rewrite ⇒s-unicity e⇒τ₁ e⇒τ₂                            = refl
    ⇒-unicity (USAp e₁⇒τ₁ τ▸ e₂⇐τ₂)  (USAp e₁⇒τ₁' τ▸' e₂⇐τ₂')
      rewrite ⇒s-unicity e₁⇒τ₁ e₁⇒τ₁'
      with refl ← ▸-→-unicity τ▸ τ▸'                          = refl
    ⇒-unicity USNum                  USNum                    = refl
    ⇒-unicity (USPlus e₁⇐num e₂⇐num) (USPlus e₁⇐num' e₂⇐num') = refl
    ⇒-unicity USMultiLocationConflict          USMultiLocationConflict            = refl
    ⇒-unicity USCycleLocationConflict             USCycleLocationConflict               = refl

    ⇒s-unicity : ∀ {Γ : Ctx} {e : UChildExp} {τ₁ τ₂ : Typ}
               → Γ ⊢s e ⇒ τ₁
               → Γ ⊢s e ⇒ τ₂
               → τ₁ ≡ τ₂
    ⇒s-unicity USHole           USHole            = refl
    ⇒s-unicity (USOnly e⇒τ)     (USOnly e⇒τ')
      rewrite ⇒-unicity e⇒τ e⇒τ'                        = refl
    ⇒s-unicity (USLocalConflict ė⇒*) (USLocalConflict ė⇒*') = refl
