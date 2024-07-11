open import Data.Empty using (⊥-elim)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grove.Prelude using (assimilation; ¬-≡)
open import Grove.Marking.STyp
open import Grove.Marking.Var

module Grove.Marking.Ctx where
  infix  4 _∋_∶_
  infixl 5 _,_∶_

  -- contexts
  data Ctx : Set where
    ∅     : Ctx
    _,_∶_ : Ctx → Var → STyp → Ctx

  -- context membership
  data _∋_∶_ : (Γ : Ctx) (x : Var) (τ : STyp) → Set where
    Z : ∀ {Γ x τ}                            → Γ , x  ∶ τ  ∋ x ∶ τ
    S : ∀ {Γ x x' τ τ'} → x ≢ x' → Γ ∋ x ∶ τ → Γ , x' ∶ τ' ∋ x ∶ τ

  _∌_ : (Γ : Ctx) → (x : Var) → Set
  Γ ∌ x = ¬ (∃[ τ ] Γ ∋ x ∶ τ)

  -- decidable context membership
  _∋?_ : Decidable (λ Γ x → ∃[ τ ] Γ ∋ x ∶ τ)
  ∅            ∋? x          = no (λ ())
  (Γ , x' ∶ τ) ∋? x
    with x ≟ x'
  ...  | yes refl            = yes (_ , Z)
  ...  | no  x≢x' with Γ ∋? x
  ...                | yes (_ , ∋x) = yes (_ , S x≢x' ∋x)
  ...                | no ∌x        = no λ { (_ , Z) → x≢x' refl
                                           ; (τ' , S _ ∋x₁) → ∌x (τ' , ∋x₁) }

  -- membership type equality
  ∋→τ-≡ : ∀ {Γ x τ₁ τ₂}
        → (Γ ∋ x ∶ τ₁)
        → (Γ ∋ x ∶ τ₂)
        → τ₁ ≡ τ₂
  ∋→τ-≡ Z         Z         = refl
  ∋→τ-≡ Z         (S x≢x _) = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S x≢x _) Z         = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S _ ∋x)  (S _ ∋x') = ∋→τ-≡ ∋x ∋x'

  -- membership derivation equality
  ∋-≡ : ∀ {Γ x τ}
      → (∋x : Γ ∋ x ∶ τ)
      → (∋x' : Γ ∋ x ∶ τ)
      → ∋x ≡ ∋x'
  ∋-≡ Z           Z         = refl
  ∋-≡ Z           (S x≢x _) = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x _)   Z         = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x' ∋x) (S x≢x'' ∋x')
    rewrite ¬-≡ x≢x' x≢x''
          | ∋-≡ ∋x ∋x' = refl

  -- non-membership derivation equality
  ∌-≡ : ∀ {Γ y}
      → (∌y : Γ ∌ y)
      → (∌y' : Γ ∌ y)
      → ∌y ≡ ∌y'
  ∌-≡ ∌y ∌y' = assimilation ∌y ∌y'
