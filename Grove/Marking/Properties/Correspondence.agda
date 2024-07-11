open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map; zipWith)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; inspect; [_])

open import Grove.Ident using (EdgeId)
open import Grove.Marking.Grove using (Ctor; Term; ChildTerm; T; ⋎; ↻; □; ∶; ⋏)
open import Grove.Marking.Typ
open import Grove.Marking.UExp

module Grove.Marking.Properties.Correspondence where
  -- generic and concrete representations are isomorphic
  mutual
    Term→UExp : Term → Maybe UExp
    Term→UExp (⋎ w v)                             = just (-⋎^ w ^ v)
    Term→UExp (↻ w v)                             = just (-↻^ w ^ v)
    Term→UExp (T u (Ctor.CEVar x) [])             = just (- x ^ u)
    Term→UExp (T u (Ctor.CELam x) (τ ∷ e ∷ []))   = zipWith (λ { τ e → -λ x ∶ τ ∙ e ^ u }) (ChildTerm→ChildTyp τ) (ChildTerm→UChildExp e)
    Term→UExp (T u Ctor.CEAp      (e₁ ∷ e₂ ∷ [])) = zipWith (λ { e₁ e₂ → - e₁ ∙ e₂ ^ u }) (ChildTerm→UChildExp e₁) (ChildTerm→UChildExp e₂)
    Term→UExp (T u (Ctor.CENum n) [])             = just (-ℕ n ^ u)
    Term→UExp (T u Ctor.CEPlus    (e₁ ∷ e₂ ∷ [])) = zipWith (λ { e₁ e₂ → - e₁ + e₂ ^ u }) (ChildTerm→UChildExp e₁) (ChildTerm→UChildExp e₂)
    Term→UExp (T u Ctor.CTNum     [])             = nothing
    Term→UExp (T u Ctor.CTArrow   (_ ∷ _ ∷ []))   = nothing

    ChildTerm→UChildExp : ChildTerm → Maybe UChildExp
    ChildTerm→UChildExp (□ s) = just (-□ s)
    ChildTerm→UChildExp (∶ (w , e)) = map (λ e → -∶ (w , e)) (Term→UExp e)
    ChildTerm→UChildExp (⋏ s ė*) = map (λ ė* → -⋏ s ė*) (ChildTerm→UChildExp* ė*)

    ChildTerm→UChildExp* : List (EdgeId × Term) → Maybe (List UChildExp')
    ChildTerm→UChildExp* []             = just []
    ChildTerm→UChildExp* ((w , e) ∷ ė*) = zipWith (λ { e ė* → (w , e) ∷ ė* }) (Term→UExp e) (ChildTerm→UChildExp* ė*)

    Term→Typ : Term → Maybe Typ
    Term→Typ (⋎ w v)                           = just (⋎^ w ^ v)
    Term→Typ (↻ w v)                           = just (↻^ w ^ v)
    Term→Typ (T u Ctor.CTNum [])               = just (num^ u)
    Term→Typ (T u Ctor.CTArrow (τ₁ ∷ τ₂ ∷ [])) = zipWith (λ { τ₁ τ₂ → τ₁ -→ τ₂ ^ u }) (ChildTerm→ChildTyp τ₁) (ChildTerm→ChildTyp τ₂)
    Term→Typ (T u (Ctor.CEVar x) [])           = nothing
    Term→Typ (T u (Ctor.CELam x) (_ ∷ _ ∷ [])) = nothing
    Term→Typ (T u Ctor.CEAp      (_ ∷ _ ∷ [])) = nothing
    Term→Typ (T u (Ctor.CENum n) [])           = nothing
    Term→Typ (T u Ctor.CEPlus    (_ ∷ _ ∷ [])) = nothing

    ChildTerm→ChildTyp : ChildTerm → Maybe ChildTyp
    ChildTerm→ChildTyp (□ s) = just (□ s)
    ChildTerm→ChildTyp (∶ (w , τ)) = map (λ τ → ∶ (w , τ)) (Term→Typ τ)
    ChildTerm→ChildTyp (⋏ s τ*) = map (λ τ* → ⋏ s τ*) (ChildTerm→ChildTyp* τ*)

    ChildTerm→ChildTyp* : List (EdgeId × Term) → Maybe (List ChildTyp')
    ChildTerm→ChildTyp* []             = just []
    ChildTerm→ChildTyp* ((w , τ) ∷ τ*) = zipWith (λ { τ τ* → (w , τ) ∷ τ* }) (Term→Typ τ) (ChildTerm→ChildTyp* τ*)

  mutual
    UExp→Term : UExp → Term
    UExp→Term (- x ^ u) = T u (Ctor.CEVar x) []
    UExp→Term (-λ x ∶ τ ∙ e ^ u) = T u (Ctor.CELam x) ((ChildTyp→ChildTerm τ) ∷ (UChildExp→ChildTerm e) ∷ [])
    UExp→Term (- e₁ ∙ e₂ ^ u) = T u (Ctor.CEPlus) ((UChildExp→ChildTerm e₁) ∷ (UChildExp→ChildTerm e₂) ∷ [])
    UExp→Term (-ℕ n ^ u) = T u (Ctor.CENum n) []
    UExp→Term (- e₁ + e₂ ^ u) = T u (Ctor.CEPlus) ((UChildExp→ChildTerm e₁) ∷ (UChildExp→ChildTerm e₂) ∷ [])
    UExp→Term (-⋎^ w ^ v) = ⋎ w v
    UExp→Term (-↻^ w ^ v) = ↻ w v

    UChildExp→ChildTerm : UChildExp → ChildTerm
    UChildExp→ChildTerm (-□ s) = □ s
    UChildExp→ChildTerm (-∶ (w , e)) = ∶ (w , UExp→Term e)
    UChildExp→ChildTerm (-⋏ s ė*) = ⋏ s (UChildExp→ChildTerm* ė*)

    UChildExp→ChildTerm* : List UChildExp' → List (EdgeId × Term)
    UChildExp→ChildTerm* [] = []
    UChildExp→ChildTerm* ((w , e) ∷ ė*) = (w , UExp→Term e) ∷ (UChildExp→ChildTerm* ė*)

    Typ→Term : Typ → Term
    Typ→Term (num^ u) = T u Ctor.CTNum []
    Typ→Term (τ₁ -→ τ₂ ^ u) = T u Ctor.CTArrow ((ChildTyp→ChildTerm τ₁) ∷ (ChildTyp→ChildTerm τ₂) ∷ [])
    Typ→Term (⋎^ w ^ v) = ⋎ w v
    Typ→Term (↻^ w ^ v) = ↻ w v

    ChildTyp→ChildTerm : ChildTyp → ChildTerm
    ChildTyp→ChildTerm (□ s) = □ s
    ChildTyp→ChildTerm (∶ (w , τ)) = ∶ (w , Typ→Term τ)
    ChildTyp→ChildTerm (⋏ s τ*) = ⋏ s (ChildTyp→ChildTerm* τ*)

    ChildTyp→ChildTerm* : List ChildTyp' → List (EdgeId × Term)
    ChildTyp→ChildTerm* [] = []
    ChildTyp→ChildTerm* ((w , τ) ∷ τ*) = (w , Typ→Term τ) ∷ (ChildTyp→ChildTerm* τ*)

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
      with ChildTerm→ChildTyp t₁ | ChildTerm→UChildExp t₂ in h₂ | ChildTerm→UChildExp→ChildTerm t₂
    ...  | just τ | just e | ih₂ = goal eqv₁ (eqv₂ ih₂)
      where eqv₁ : ChildTyp→ChildTerm τ ≡ t₁
            eqv₁ = {! !}
            eqv₂ : ChildTerm→UChildExp→ChildTerm-sig t₂ → UChildExp→ChildTerm e ≡ t₂
            eqv₂ ih₂ rewrite h₂ = ?
            goal : ChildTyp→ChildTerm τ ≡ t₁ → UChildExp→ChildTerm e ≡ t₂
                 → UExp→Term (-λ x ∶ τ ∙ e ^ u) ≡ T u (Ctor.CELam x) (t₁ ∷ t₂ ∷ [])
            goal refl refl = refl
    Term→UExp→Term (T u Ctor.CEAp      (e₁ ∷ e₂ ∷ [])) = {! !}
    Term→UExp→Term (T u (Ctor.CENum n) [])             = {! !}
    Term→UExp→Term (T u Ctor.CEPlus    (e₁ ∷ e₂ ∷ [])) = {! !}
    Term→UExp→Term (T u Ctor.CTNum     [])             = tt
    Term→UExp→Term (T u Ctor.CTArrow   (_ ∷ _ ∷ []))   = tt

    ChildTerm→UChildExp→ChildTerm-sig : (t : ChildTerm) → Set
    ChildTerm→UChildExp→ChildTerm-sig t with ChildTerm→UChildExp t
    ... | just e  = UChildExp→ChildTerm e ≡ t
    ... | nothing = ⊤

    ChildTerm→UChildExp→ChildTerm : (e : ChildTerm) → ChildTerm→UChildExp→ChildTerm-sig e
