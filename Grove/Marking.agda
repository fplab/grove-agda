open import Data.Nat using (ℕ)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Grove.Marking where
  -- reexport marking definitions
  open import Grove.Marking.Hole public
  open import Grove.Marking.Ident public
  open import Grove.Marking.Var public
  open import Grove.Marking.Typ public
  open import Grove.Marking.GTyp public
  open import Grove.Marking.Ctx public
  open import Grove.Marking.MultiParents public
  open import Grove.Marking.UExp public
  open import Grove.Marking.MExp public
  open import Grove.Marking.Erasure public
  open import Grove.Marking.Marking public

  open import Grove.Marking.Properties

  -- grove instantiation
  data Ctor : Set where
    CVar  : Ctor
    CLam  : Ctor
    CAp   : Ctor
    CNum  : Ctor
    CPlus : Ctor

  _≟ℂ_ : Decidable (_≡_ {A = Ctor})
  CVar  ≟ℂ CVar  = yes refl
  CVar  ≟ℂ CLam  = no (λ ())
  CVar  ≟ℂ CAp   = no (λ ())
  CVar  ≟ℂ CNum  = no (λ ())
  CVar  ≟ℂ CPlus = no (λ ())
  CLam  ≟ℂ CVar  = no (λ ())
  CLam  ≟ℂ CLam  = yes refl
  CLam  ≟ℂ CAp   = no (λ ())
  CLam  ≟ℂ CNum  = no (λ ())
  CLam  ≟ℂ CPlus = no (λ ())
  CAp   ≟ℂ CVar  = no (λ ())
  CAp   ≟ℂ CLam  = no (λ ())
  CAp   ≟ℂ CAp   = yes refl
  CAp   ≟ℂ CNum  = no (λ ())
  CAp   ≟ℂ CPlus = no (λ ())
  CNum  ≟ℂ CVar  = no (λ ())
  CNum  ≟ℂ CLam  = no (λ ())
  CNum  ≟ℂ CAp   = no (λ ())
  CNum  ≟ℂ CNum  = yes refl
  CNum  ≟ℂ CPlus = no (λ ())
  CPlus ≟ℂ CVar  = no (λ ())
  CPlus ≟ℂ CLam  = no (λ ())
  CPlus ≟ℂ CAp   = no (λ ())
  CPlus ≟ℂ CNum  = no (λ ())
  CPlus ≟ℂ CPlus = yes refl

  arity : Ctor → ℕ
  arity CVar  = 0
  arity CLam  = 2
  arity CAp   = 2
  arity CNum  = 0
  arity CPlus = 2

  import Grove.Core.Grove using (Term; T; ⋎; ⤾)
  open module Grove = Grove.Core.Grove Ctor _≟ℂ_ arity public

  -- y : Term → UExp
  -- y (T u CVar es) = {! !}
  -- y (T u CLam es) = {! !}
  -- y (T u CAp es) = {! !}
  -- y (T u CNum es) = {! !}
  -- y (T u CPlus es) = {! !}
  -- y (⋎ w v) = {! !}
  -- y (⤾ w v) = {! !}
