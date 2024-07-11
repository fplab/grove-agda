open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Grove.Ident
open import Grove.Marking.Typ
open import Grove.Marking.Ctx
open import Grove.Marking.MExp

open import Grove.Marking.Grove using (Vertex; Location)

module Grove.Marking.LocationConflictCtx where
  data Mode : Set where
    Syn : Mode
    Ana : (τ : Typ) → Mode

  record LocationConflict : Set where
    constructor ⟨_,_,_,_⟩
    field
      v : Vertex
      w : EdgeId
      Γ : Ctx
      m : Mode

  LocationConflictCtx = List LocationConflict

  mutual
    locationConflictCtx⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → LocationConflictCtx
    locationConflictCtx⇒ (⊢ _ ^ _)              = []
    locationConflictCtx⇒ (⊢λ _ ∶ _ ∙ ě ^ _)     = locationConflictCtx⇒s ě
    locationConflictCtx⇒ (⊢ ě₁ ∙ ě₂ [ _ ]^ _)   = (locationConflictCtx⇒s ě₁) ++ (locationConflictCtx⇐s ě₂)
    locationConflictCtx⇒ (⊢⸨ ě₁ ⸩∙ ě₂ [ _ ]^ _) = (locationConflictCtx⇒s ě₁) ++ (locationConflictCtx⇐s ě₂)
    locationConflictCtx⇒ (⊢ℕ _ ^ _)             = []
    locationConflictCtx⇒ (⊢ ě₁ + ě₂ ^ _)        = (locationConflictCtx⇐s ě₁) ++ (locationConflictCtx⇐s ě₂)
    locationConflictCtx⇒ (⊢⟦ _ ⟧^ _)            = []
    locationConflictCtx⇒ {Γ} (⊢⋎^ w ^ v)        = [ ⟨ v , w , Γ , Syn ⟩ ]
    locationConflictCtx⇒ {Γ} (⊢↻^ w ^ v)        = [ ⟨ v , w , Γ , Syn ⟩ ]

    locationConflictCtx⇒s : ∀ {Γ τ} → (ě : Γ ⊢⇒s τ) → LocationConflictCtx
    locationConflictCtx⇒s (⊢□ _)       = []
    locationConflictCtx⇒s (⊢∶ (_ , ě)) = locationConflictCtx⇒ ě
    locationConflictCtx⇒s (⊢⋏ _ ė*)    = locationConflictCtx⇒s* ė*

    locationConflictCtx⇒s* : ∀ {Γ} → (ė* : List (EdgeId × ∃[ τ ] Γ ⊢⇒ τ)) → LocationConflictCtx
    locationConflictCtx⇒s* []                 = []
    locationConflictCtx⇒s* ((_ , _ , ě) ∷ ė*) = (locationConflictCtx⇒ ě) ++ locationConflictCtx⇒s* ė*

    locationConflictCtx⇐ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → LocationConflictCtx
    locationConflictCtx⇐ (⊢λ _ ∶ _ ∙ ě [ _ ∙ _ ]^ _)   = locationConflictCtx⇐s ě
    locationConflictCtx⇐ (⊢⸨λ _ ∶ _ ∙ ě ⸩[ _ ]^ _)     = locationConflictCtx⇐s ě
    locationConflictCtx⇐ (⊢λ _ ∶⸨ _ ⸩∙ ě [ _ ∙ _ ]^ _) = locationConflictCtx⇐s ě
    locationConflictCtx⇐ {Γ} {τ} (⊢⋎^ w ^ v)           = [ ⟨ v , w , Γ , Ana τ ⟩ ]
    locationConflictCtx⇐ {Γ} {τ} (⊢↻^ w ^ v)           = [ ⟨ v , w , Γ , Ana τ ⟩ ]
    locationConflictCtx⇐ ⊢⸨ ě ⸩[ _ ∙ _ ]               = locationConflictCtx⇒ ě
    locationConflictCtx⇐ ⊢∙ ě [ _ ∙ _ ]                = locationConflictCtx⇒ ě

    locationConflictCtx⇐s : ∀ {Γ τ} → (ě : Γ ⊢⇐s τ) → LocationConflictCtx
    locationConflictCtx⇐s (⊢□ _)       = []
    locationConflictCtx⇐s (⊢∶ (_ , ě)) = locationConflictCtx⇐ ě
    locationConflictCtx⇐s (⊢⋏ _ ė*)    = locationConflictCtx⇐s* ė*

    locationConflictCtx⇐s* : ∀ {Γ τ} → (ė* : List (EdgeId × Γ ⊢⇐ τ)) → LocationConflictCtx
    locationConflictCtx⇐s* []             = []
    locationConflictCtx⇐s* ((_ , ě) ∷ ė*) = (locationConflictCtx⇐ ě) ++ locationConflictCtx⇐s* ė*
