open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

module Grove.Prelude where
  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
  assimilation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))

  ¬-≡ : ∀ {A : Set} → (¬a : ¬ A) → (¬a' : ¬ A) → ¬a ≡ ¬a'
  ¬-≡ ¬a ¬a' = extensionality λ { a → ⊥-elim (¬a a) }
