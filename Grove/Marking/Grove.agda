open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grove.Marking.Var

module Grove.Marking.Grove where
  -- grove instantiation
  data Ctor : Set where
    -- expressions
    CEVar   : (x : Var) → Ctor
    CELam   : (x : Var) → Ctor
    CEAp    : Ctor
    CENum   : (n : ℕ) → Ctor
    CEPlus  : Ctor
    -- types
    CTNum   : Ctor
    CTArrow : Ctor

  _≟ℂ_ : Decidable (_≡_ {A = Ctor})
  CEVar x ≟ℂ CEVar x' with x ≟ x'
  ... | yes refl     = yes refl
  ... | no  x≢x'     = no λ { refl → x≢x' refl }
  CEVar x ≟ℂ CELam _ = no (λ ())
  CEVar _ ≟ℂ CEAp    = no (λ ())
  CEVar _ ≟ℂ CENum _ = no (λ ())
  CEVar _ ≟ℂ CEPlus  = no (λ ())
  CEVar _ ≟ℂ CTNum   = no (λ ())
  CEVar _ ≟ℂ CTArrow = no (λ ())
  CELam _ ≟ℂ CEVar _ = no (λ ())
  CELam x ≟ℂ CELam x' with x ≟ x'
  ... | yes refl     = yes refl
  ... | no  x≢x'     = no λ { refl → x≢x' refl }
  CELam _ ≟ℂ CEAp    = no (λ ())
  CELam _ ≟ℂ CENum _ = no (λ ())
  CELam _ ≟ℂ CEPlus  = no (λ ())
  CELam _ ≟ℂ CTNum   = no (λ ())
  CELam _ ≟ℂ CTArrow = no (λ ())
  CEAp    ≟ℂ CEVar _ = no (λ ())
  CEAp    ≟ℂ CELam _ = no (λ ())
  CEAp    ≟ℂ CEAp    = yes refl
  CEAp    ≟ℂ CENum _ = no (λ ())
  CEAp    ≟ℂ CEPlus  = no (λ ())
  CEAp    ≟ℂ CTNum   = no (λ ())
  CEAp    ≟ℂ CTArrow = no (λ ())
  CENum _ ≟ℂ CEVar _ = no (λ ())
  CENum _ ≟ℂ CELam _ = no (λ ())
  CENum _ ≟ℂ CEAp    = no (λ ())
  CENum n ≟ℂ CENum n' with n ≟ n'
  ... | yes refl     = yes refl
  ... | no  n≢n'     = no λ { refl → n≢n' refl }
  CENum _ ≟ℂ CEPlus  = no (λ ())
  CENum _ ≟ℂ CTNum   = no (λ ())
  CENum _ ≟ℂ CTArrow = no (λ ())
  CEPlus  ≟ℂ CEVar _ = no (λ ())
  CEPlus  ≟ℂ CELam _ = no (λ ())
  CEPlus  ≟ℂ CEAp    = no (λ ())
  CEPlus  ≟ℂ CENum _ = no (λ ())
  CEPlus  ≟ℂ CEPlus  = yes refl
  CEPlus  ≟ℂ CTNum   = no (λ ())
  CEPlus  ≟ℂ CTArrow = no (λ ())
  CTNum   ≟ℂ CEVar x = no (λ ())
  CTNum   ≟ℂ CELam x = no (λ ())
  CTNum   ≟ℂ CEAp    = no (λ ())
  CTNum   ≟ℂ CENum n = no (λ ())
  CTNum   ≟ℂ CEPlus  = no (λ ())
  CTNum   ≟ℂ CTNum   = yes refl
  CTNum   ≟ℂ CTArrow = no (λ ())
  CTArrow ≟ℂ CEVar x = no (λ ())
  CTArrow ≟ℂ CELam x = no (λ ())
  CTArrow ≟ℂ CEAp    = no (λ ())
  CTArrow ≟ℂ CENum n = no (λ ())
  CTArrow ≟ℂ CEPlus  = no (λ ())
  CTArrow ≟ℂ CTNum   = no (λ ())
  CTArrow ≟ℂ CTArrow = yes refl

  arity : Ctor → ℕ
  arity (CEVar _) = 0
  arity (CELam _) = 2
  arity (CEAp   ) = 2
  arity (CENum _) = 0
  arity (CEPlus ) = 2
  arity (CTNum  ) = 0
  arity (CTArrow) = 2

  import Grove.Core
  open Grove.Core Ctor _≟ℂ_ arity public
