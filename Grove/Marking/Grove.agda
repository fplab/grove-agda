open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grove.Marking.Var

module Grove.Marking.Grove where
  -- grove instantiation
  data Ctor : Set where
    CVar  : (x : Var) → Ctor
    CLam  : (x : Var) → Ctor
    CAp   : Ctor
    CNum  : (n : ℕ) → Ctor
    CPlus : Ctor

  _≟ℂ_ : Decidable (_≡_ {A = Ctor})
  CVar x ≟ℂ CVar x' with x ≟ x'
  ... | yes refl   = yes refl
  ... | no  x≢x'   = no λ { refl → x≢x' refl }
  CVar x ≟ℂ CLam _ = no (λ ())
  CVar _ ≟ℂ CAp    = no (λ ())
  CVar _ ≟ℂ CNum _ = no (λ ())
  CVar _ ≟ℂ CPlus  = no (λ ())
  CLam _ ≟ℂ CVar _ = no (λ ())
  CLam x ≟ℂ CLam x' with x ≟ x'
  ... | yes refl   = yes refl
  ... | no  x≢x'   = no λ { refl → x≢x' refl }
  CLam _ ≟ℂ CAp    = no (λ ())
  CLam _ ≟ℂ CNum _ = no (λ ())
  CLam _ ≟ℂ CPlus  = no (λ ())
  CAp    ≟ℂ CVar _ = no (λ ())
  CAp    ≟ℂ CLam _ = no (λ ())
  CAp    ≟ℂ CAp    = yes refl
  CAp    ≟ℂ CNum _ = no (λ ())
  CAp    ≟ℂ CPlus  = no (λ ())
  CNum _ ≟ℂ CVar _ = no (λ ())
  CNum _ ≟ℂ CLam _ = no (λ ())
  CNum _ ≟ℂ CAp    = no (λ ())
  CNum n ≟ℂ CNum n' with n ≟ n'
  ... | yes refl   = yes refl
  ... | no  n≢n'   = no λ { refl → n≢n' refl }
  CNum _ ≟ℂ CPlus  = no (λ ())
  CPlus  ≟ℂ CVar _ = no (λ ())
  CPlus  ≟ℂ CLam _ = no (λ ())
  CPlus  ≟ℂ CAp    = no (λ ())
  CPlus  ≟ℂ CNum _ = no (λ ())
  CPlus  ≟ℂ CPlus  = yes refl

  arity : Ctor → ℕ
  arity (CVar _) = 0
  arity (CLam _) = 2
  arity (CAp   ) = 2
  arity (CNum _) = 0
  arity (CPlus ) = 2

  import Grove.Core
  open Grove.Core Ctor _≟ℂ_ arity public
