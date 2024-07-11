open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map; zipWith)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; inspect; [_])

open import Grove.Ident using (EdgeId)
open import Grove.Marking.Grove using (Ctor; Term; TermList; T; ⋎; ↻; □; ∶; ⋏)
open import Grove.Marking.Typ
open import Grove.Marking.UExp

module Grove.Marking.Properties.Correspondence where
  -- generic and concrete representations are isomorphic
  mutual
    Term→UExp : Term → Maybe UExp
    Term→UExp (⋎ w v)                             = just (-⋎^ w ^ v)
    Term→UExp (↻ w v)                             = just (-↻^ w ^ v)
    Term→UExp (T u (Ctor.CEVar x) [])             = just (- x ^ u)
    Term→UExp (T u (Ctor.CELam x) (τ ∷ e ∷ []))   = zipWith (λ { τ e → -λ x ∶ τ ∙ e ^ u }) (TermList→ChildTyp τ) (TermList→UChildExp e)
    Term→UExp (T u Ctor.CEAp      (e₁ ∷ e₂ ∷ [])) = zipWith (λ { e₁ e₂ → - e₁ ∙ e₂ ^ u }) (TermList→UChildExp e₁) (TermList→UChildExp e₂)
    Term→UExp (T u (Ctor.CENum n) [])             = just (-ℕ n ^ u)
    Term→UExp (T u Ctor.CEPlus    (e₁ ∷ e₂ ∷ [])) = zipWith (λ { e₁ e₂ → - e₁ + e₂ ^ u }) (TermList→UChildExp e₁) (TermList→UChildExp e₂)
    Term→UExp (T u Ctor.CTNum     [])             = nothing
    Term→UExp (T u Ctor.CTArrow   (_ ∷ _ ∷ []))   = nothing

    TermList→UChildExp : TermList → Maybe UChildExp
    TermList→UChildExp (□ s) = just (-□ s)
    TermList→UChildExp (∶ (w , e)) = map (λ e → -∶ (w , e)) (Term→UExp e)
    TermList→UChildExp (⋏ s ė*) = map (λ ė* → -⋏ s ė*) (TermList→UChildExp* ė*)

    TermList→UChildExp* : List (EdgeId × Term) → Maybe (List UChildExp')
    TermList→UChildExp* []             = just []
    TermList→UChildExp* ((w , e) ∷ ė*) = zipWith (λ { e ė* → (w , e) ∷ ė* }) (Term→UExp e) (TermList→UChildExp* ė*)

    Term→Typ : Term → Maybe Typ
    Term→Typ (⋎ w v)                           = just (⋎^ w ^ v)
    Term→Typ (↻ w v)                           = just (↻^ w ^ v)
    Term→Typ (T u Ctor.CTNum [])               = just (num^ u)
    Term→Typ (T u Ctor.CTArrow (τ₁ ∷ τ₂ ∷ [])) = zipWith (λ { τ₁ τ₂ → τ₁ -→ τ₂ ^ u }) (TermList→ChildTyp τ₁) (TermList→ChildTyp τ₂)
    Term→Typ (T u (Ctor.CEVar x) [])           = nothing
    Term→Typ (T u (Ctor.CELam x) (_ ∷ _ ∷ [])) = nothing
    Term→Typ (T u Ctor.CEAp      (_ ∷ _ ∷ [])) = nothing
    Term→Typ (T u (Ctor.CENum n) [])           = nothing
    Term→Typ (T u Ctor.CEPlus    (_ ∷ _ ∷ [])) = nothing

    TermList→ChildTyp : TermList → Maybe ChildTyp
    TermList→ChildTyp (□ s) = just (□ s)
    TermList→ChildTyp (∶ (w , τ)) = map (λ τ → ∶ (w , τ)) (Term→Typ τ)
    TermList→ChildTyp (⋏ s τ*) = map (λ τ* → ⋏ s τ*) (TermList→ChildTyp* τ*)

    TermList→ChildTyp* : List (EdgeId × Term) → Maybe (List ChildTyp')
    TermList→ChildTyp* []             = just []
    TermList→ChildTyp* ((w , τ) ∷ τ*) = zipWith (λ { τ τ* → (w , τ) ∷ τ* }) (Term→Typ τ) (TermList→ChildTyp* τ*)

  mutual
    UExp→Term : UExp → Term
    UExp→Term (- x ^ u) = T u (Ctor.CEVar x) []
    UExp→Term (-λ x ∶ τ ∙ e ^ u) = T u (Ctor.CELam x) ((ChildTyp→TermList τ) ∷ (UChildExp→TermList e) ∷ [])
    UExp→Term (- e₁ ∙ e₂ ^ u) = T u (Ctor.CEPlus) ((UChildExp→TermList e₁) ∷ (UChildExp→TermList e₂) ∷ [])
    UExp→Term (-ℕ n ^ u) = T u (Ctor.CENum n) []
    UExp→Term (- e₁ + e₂ ^ u) = T u (Ctor.CEPlus) ((UChildExp→TermList e₁) ∷ (UChildExp→TermList e₂) ∷ [])
    UExp→Term (-⋎^ w ^ v) = ⋎ w v
    UExp→Term (-↻^ w ^ v) = ↻ w v

    UChildExp→TermList : UChildExp → TermList
    UChildExp→TermList (-□ s) = □ s
    UChildExp→TermList (-∶ (w , e)) = ∶ (w , UExp→Term e)
    UChildExp→TermList (-⋏ s ė*) = ⋏ s (UChildExp→TermList* ė*)

    UChildExp→TermList* : List UChildExp' → List (EdgeId × Term)
    UChildExp→TermList* [] = []
    UChildExp→TermList* ((w , e) ∷ ė*) = (w , UExp→Term e) ∷ (UChildExp→TermList* ė*)

    Typ→Term : Typ → Term
    Typ→Term (num^ u) = T u Ctor.CTNum []
    Typ→Term (τ₁ -→ τ₂ ^ u) = T u Ctor.CTArrow ((ChildTyp→TermList τ₁) ∷ (ChildTyp→TermList τ₂) ∷ [])
    Typ→Term (⋎^ w ^ v) = ⋎ w v
    Typ→Term (↻^ w ^ v) = ↻ w v

    ChildTyp→TermList : ChildTyp → TermList
    ChildTyp→TermList (□ s) = □ s
    ChildTyp→TermList (∶ (w , τ)) = ∶ (w , Typ→Term τ)
    ChildTyp→TermList (⋏ s τ*) = ⋏ s (ChildTyp→TermList* τ*)

    ChildTyp→TermList* : List ChildTyp' → List (EdgeId × Term)
    ChildTyp→TermList* [] = []
    ChildTyp→TermList* ((w , τ) ∷ τ*) = (w , Typ→Term τ) ∷ (ChildTyp→TermList* τ*)

  mutual
    Term→UExp→Term-sig : (t : Term) → Set
    Term→UExp→Term-sig t with Term→UExp t
    ... | just e  = UExp→Term e ≡ t
    ... | nothing = ⊤

    Term→UExp→Term : (e : Term) → Term→UExp→Term-sig e
    Term→UExp→Term (⋎ w v)                             = {! !}
    Term→UExp→Term (↻ w v)                             = {! !}
    Term→UExp→Term (T u (Ctor.CEVar x) [])             = {! !}
    Term→UExp→Term (T u (Ctor.CELam x) (t₁ ∷ t₂ ∷ []))
      with TermList→ChildTyp t₁ | TermList→UChildExp t₂ in h₂ | TermList→UChildExp→TermList t₂
    ...  | just τ | just e | ih₂ = goal eqv₁ (eqv₂ ih₂)
      where eqv₁ : ChildTyp→TermList τ ≡ t₁
            eqv₁ = {! !}
            eqv₂ : TermList→UChildExp→TermList-sig t₂ → UChildExp→TermList e ≡ t₂
            eqv₂ ih₂ rewrite h₂ = ?
            goal : ChildTyp→TermList τ ≡ t₁ → UChildExp→TermList e ≡ t₂
                 → UExp→Term (-λ x ∶ τ ∙ e ^ u) ≡ T u (Ctor.CELam x) (t₁ ∷ t₂ ∷ [])
            goal refl refl = refl
    Term→UExp→Term (T u Ctor.CEAp      (e₁ ∷ e₂ ∷ [])) = {! !}
    Term→UExp→Term (T u (Ctor.CENum n) [])             = {! !}
    Term→UExp→Term (T u Ctor.CEPlus    (e₁ ∷ e₂ ∷ [])) = {! !}
    Term→UExp→Term (T u Ctor.CTNum     [])             = tt
    Term→UExp→Term (T u Ctor.CTArrow   (_ ∷ _ ∷ []))   = tt

    TermList→UChildExp→TermList-sig : (t : TermList) → Set
    TermList→UChildExp→TermList-sig t with TermList→UChildExp t
    ... | just e  = UChildExp→TermList e ≡ t
    ... | nothing = ⊤

    TermList→UChildExp→TermList : (e : TermList) → TermList→UChildExp→TermList-sig e
