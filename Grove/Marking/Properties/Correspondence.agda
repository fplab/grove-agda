open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map; zipWith)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; inspect; [_])

open import Grove.Ident using (EdgeId)
open import Grove.Marking.Grove using (Ctor; Term; TermList; T; ⋎; ↻; □; ∶; ⋏)
open import Grove.Marking.GTyp
open import Grove.Marking.UExp

module Grove.Marking.Properties.Correspondence where
  -- generic and concrete representations are isomorphic
  mutual
    Term→UExp : Term → Maybe UExp
    Term→UExp (⋎ w v)                             = just (-⋎^ w ^ v)
    Term→UExp (↻ w v)                             = just (-↻^ w ^ v)
    Term→UExp (T u (Ctor.CEVar x) [])             = just (- x ^ u)
    Term→UExp (T u (Ctor.CELam x) (τ ∷ e ∷ []))   = zipWith (λ { τ e → -λ x ∶ τ ∙ e ^ u }) (TermList→GSubTyp τ) (TermList→USubExp e)
    Term→UExp (T u Ctor.CEAp      (e₁ ∷ e₂ ∷ [])) = zipWith (λ { e₁ e₂ → - e₁ ∙ e₂ ^ u }) (TermList→USubExp e₁) (TermList→USubExp e₂)
    Term→UExp (T u (Ctor.CENum n) [])             = just (-ℕ n ^ u)
    Term→UExp (T u Ctor.CEPlus    (e₁ ∷ e₂ ∷ [])) = zipWith (λ { e₁ e₂ → - e₁ + e₂ ^ u }) (TermList→USubExp e₁) (TermList→USubExp e₂)
    Term→UExp (T u Ctor.CTNum     [])             = nothing
    Term→UExp (T u Ctor.CTArrow   (_ ∷ _ ∷ []))   = nothing

    TermList→USubExp : TermList → Maybe USubExp
    TermList→USubExp (□ s) = just (-□ s)
    TermList→USubExp (∶ (w , e)) = map (λ e → -∶ (w , e)) (Term→UExp e)
    TermList→USubExp (⋏ s ė*) = map (λ ė* → -⋏ s ė*) (TermList→USubExp* ė*)

    TermList→USubExp* : List (EdgeId × Term) → Maybe (List USubExp')
    TermList→USubExp* []             = just []
    TermList→USubExp* ((w , e) ∷ ė*) = zipWith (λ { e ė* → (w , e) ∷ ė* }) (Term→UExp e) (TermList→USubExp* ė*)

    Term→GTyp : Term → Maybe GTyp
    Term→GTyp (⋎ w v)                           = just (⋎^ w ^ v)
    Term→GTyp (↻ w v)                           = just (↻^ w ^ v)
    Term→GTyp (T u Ctor.CTNum [])               = just (num^ u)
    Term→GTyp (T u Ctor.CTArrow (τ₁ ∷ τ₂ ∷ [])) = zipWith (λ { τ₁ τ₂ → τ₁ -→ τ₂ ^ u }) (TermList→GSubTyp τ₁) (TermList→GSubTyp τ₂)
    Term→GTyp (T u (Ctor.CEVar x) [])           = nothing
    Term→GTyp (T u (Ctor.CELam x) (_ ∷ _ ∷ [])) = nothing
    Term→GTyp (T u Ctor.CEAp      (_ ∷ _ ∷ [])) = nothing
    Term→GTyp (T u (Ctor.CENum n) [])           = nothing
    Term→GTyp (T u Ctor.CEPlus    (_ ∷ _ ∷ [])) = nothing

    TermList→GSubTyp : TermList → Maybe GSubTyp
    TermList→GSubTyp (□ s) = just (□ s)
    TermList→GSubTyp (∶ (w , τ)) = map (λ τ → ∶ (w , τ)) (Term→GTyp τ)
    TermList→GSubTyp (⋏ s τ*) = map (λ τ* → ⋏ s τ*) (TermList→GSubTyp* τ*)

    TermList→GSubTyp* : List (EdgeId × Term) → Maybe (List GSubTyp')
    TermList→GSubTyp* []             = just []
    TermList→GSubTyp* ((w , τ) ∷ τ*) = zipWith (λ { τ τ* → (w , τ) ∷ τ* }) (Term→GTyp τ) (TermList→GSubTyp* τ*)

  mutual
    UExp→Term : UExp → Term
    UExp→Term (- x ^ u) = T u (Ctor.CEVar x) []
    UExp→Term (-λ x ∶ τ ∙ e ^ u) = T u (Ctor.CELam x) ((GSubTyp→TermList τ) ∷ (USubExp→TermList e) ∷ [])
    UExp→Term (- e₁ ∙ e₂ ^ u) = T u (Ctor.CEPlus) ((USubExp→TermList e₁) ∷ (USubExp→TermList e₂) ∷ [])
    UExp→Term (-ℕ n ^ u) = T u (Ctor.CENum n) []
    UExp→Term (- e₁ + e₂ ^ u) = T u (Ctor.CEPlus) ((USubExp→TermList e₁) ∷ (USubExp→TermList e₂) ∷ [])
    UExp→Term (-⋎^ w ^ v) = ⋎ w v
    UExp→Term (-↻^ w ^ v) = ↻ w v

    USubExp→TermList : USubExp → TermList
    USubExp→TermList (-□ s) = □ s
    USubExp→TermList (-∶ (w , e)) = ∶ (w , UExp→Term e)
    USubExp→TermList (-⋏ s ė*) = ⋏ s (USubExp→TermList* ė*)

    USubExp→TermList* : List USubExp' → List (EdgeId × Term)
    USubExp→TermList* [] = []
    USubExp→TermList* ((w , e) ∷ ė*) = (w , UExp→Term e) ∷ (USubExp→TermList* ė*)

    GTyp→Term : GTyp → Term
    GTyp→Term (num^ u) = T u Ctor.CTNum []
    GTyp→Term (τ₁ -→ τ₂ ^ u) = T u Ctor.CTArrow ((GSubTyp→TermList τ₁) ∷ (GSubTyp→TermList τ₂) ∷ [])
    GTyp→Term (⋎^ w ^ v) = ⋎ w v
    GTyp→Term (↻^ w ^ v) = ↻ w v

    GSubTyp→TermList : GSubTyp → TermList
    GSubTyp→TermList (□ s) = □ s
    GSubTyp→TermList (∶ (w , τ)) = ∶ (w , GTyp→Term τ)
    GSubTyp→TermList (⋏ s τ*) = ⋏ s (GSubTyp→TermList* τ*)

    GSubTyp→TermList* : List GSubTyp' → List (EdgeId × Term)
    GSubTyp→TermList* [] = []
    GSubTyp→TermList* ((w , τ) ∷ τ*) = (w , GTyp→Term τ) ∷ (GSubTyp→TermList* τ*)

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
      with TermList→GSubTyp t₁ | TermList→USubExp t₂ in h₂ | TermList→USubExp→TermList t₂
    ...  | just τ | just e | ih₂ = goal eqv₁ (eqv₂ ih₂)
      where eqv₁ : GSubTyp→TermList τ ≡ t₁
            eqv₁ = {! !}
            eqv₂ : TermList→USubExp→TermList-sig t₂ → USubExp→TermList e ≡ t₂
            eqv₂ ih₂ rewrite h₂ = ?
            goal : GSubTyp→TermList τ ≡ t₁ → USubExp→TermList e ≡ t₂
                 → UExp→Term (-λ x ∶ τ ∙ e ^ u) ≡ T u (Ctor.CELam x) (t₁ ∷ t₂ ∷ [])
            goal refl refl = refl
    Term→UExp→Term (T u Ctor.CEAp      (e₁ ∷ e₂ ∷ [])) = {! !}
    Term→UExp→Term (T u (Ctor.CENum n) [])             = {! !}
    Term→UExp→Term (T u Ctor.CEPlus    (e₁ ∷ e₂ ∷ [])) = {! !}
    Term→UExp→Term (T u Ctor.CTNum     [])             = tt
    Term→UExp→Term (T u Ctor.CTArrow   (_ ∷ _ ∷ []))   = tt

    TermList→USubExp→TermList-sig : (t : TermList) → Set
    TermList→USubExp→TermList-sig t with TermList→USubExp t
    ... | just e  = USubExp→TermList e ≡ t
    ... | nothing = ⊤

    TermList→USubExp→TermList : (e : TermList) → TermList→USubExp→TermList-sig e
