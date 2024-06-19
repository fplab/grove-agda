module core.finite-set where 

open import Data.Bool
open import Data.List hiding (map)
open import Data.Nat hiding (_+_)
open import Level using (Level)
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import core.logic 

-- postulate
--   funext : {ℓ : level} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → (B x)} → ((x : A) → f x ≡ g x) → f ≡ g
postulate
  extensionality : {ℓ₁ ℓ₂ : Level} → Extensionality ℓ₁ ℓ₂

range : ℕ → Set 
range zero = ⊥
range (suc n) = ⊤ + (range n)

subset : (A : Set) → Set₁
subset A = A → Set 

-- equivalence of subsets
record _≃_ {A : Set} (S T : subset A) : Set where
  field
    to   : (a : A) → (S a) → (T a)
    from : (a : A) → (T a) → (S a)
open _≃_

record Finite (A : Set) (S : subset A) : Set₁ where
  constructor FIN
  field
    bound : ℕ
    enum : (range bound) → A 
    enum-cover : (a : A) → (S a) → Σ[ n ∈ (range bound) ] ((enum n) ≡ a)

intersect : {A : Set} → (S T : subset A) → (subset A) 
intersect S T a = (S a) × (T a)

intersect-finite : {A : Set} → (S T : subset A) → (Finite A S) → (Finite A (intersect S T))
Finite.bound (intersect-finite S T fin) = Finite.bound fin
Finite.enum (intersect-finite S T fin) = Finite.enum fin
Finite.enum-cover (intersect-finite S T fin) a (n , _) = Finite.enum-cover fin a n 

intersect-comm : {A : Set} → (S T : subset A) → (intersect S T) ≃ (intersect T S)
to (intersect-comm S T) a (sa , ta) = (ta , sa)
from (intersect-comm S T) a (ta , sa) = (sa , ta)

map : {A B : Set} → (subset A) → (A → B) → (subset B)
map {A} S f b = Σ[ a ∈ A ] ((f a ≡ b) × S a)

map-finite : {A B : Set} → (S : subset A) → (f : A → B) → (Finite A S) → (Finite B (map S f))
Finite.bound (map-finite S f fin) = Finite.bound fin
Finite.enum (map-finite S f fin) n = f (Finite.enum fin n)
Finite.enum-cover (map-finite S f fin) .(f a) (a , refl , elem) with Finite.enum-cover fin a elem 
... | (n , refl) = (n , refl)

empty : (A : Set) → (subset A)
empty A a = ⊥

singleton : {A : Set} → A → (subset A)
singleton a b = a ≡ b 

empty-finite : (A : Set) → (Finite A (empty A))
Finite.bound (empty-finite A) = zero
Finite.enum (empty-finite A) = λ ()
Finite.enum-cover (empty-finite A) a () 

singleton-finite : (A : Set) → (a : A) → (Finite A (singleton a))
Finite.bound (singleton-finite A a) = suc zero
Finite.enum (singleton-finite A a) = λ _ → a
Finite.enum-cover (singleton-finite A a) b refl = (Inl <>) , refl

Decidable : (A : Set) → (S : subset A) → Set 
Decidable A S = (a : A) → (S a) + ¬(S a)

DecidableEquality : (A : Set) → Set 
DecidableEquality A = (a b : A) → (a ≡ b) + ¬(a ≡ b)

-- removes the first enumerated element of S
trim : (A : Set) → (S : subset A) → (Finite A S) → (subset A)
trim A S fin a with Finite.bound fin | Finite.enum fin
trim A S fin a | zero | _ = ⊥
trim A S fin a | suc n | enum = (S a) × ¬(a ≡ (enum (Inl <>)))

trim-finite : (A : Set) → (S : subset A) → (fin : Finite A S) → (Finite A (trim A S fin))
Finite.bound (trim-finite A S fin) = Finite.bound fin
Finite.enum (trim-finite A S fin) n = Finite.enum fin n
Finite.enum-cover (trim-finite A S (FIN (suc bound) enum enum-cover)) a (elem , neq) = enum-cover a elem 

trim-decidable : (A : Set) → (S : subset A) → (fin : Finite A S) → (Decidable A S) → (DecidableEquality A) → (Decidable A (trim A S fin))
trim-decidable A S fin dec deceq a with Finite.bound fin | Finite.enum fin
... | zero | _ = Inr (λ x → x)
... | suc n | enum with dec a 
... | Inr no = Inr λ (elem , _) → no elem
... | Inl yes with deceq a (enum (Inl <>))
... | Inl eq = Inr λ (_ , neq) → neq eq
... | Inr neq = Inl (yes , neq) 

list-of-finite : (A : Set) → (S : subset A) → (Finite A S) → (Decidable A S) → (DecidableEquality A) → (List A)
list-of-finite A S fin dec deceq with Finite.bound fin | Finite.enum fin
list-of-finite A S fin dec deceq | zero | _ = []
list-of-finite A S fin dec deceq | suc n | enum with (enum (Inl <>))
list-of-finite A S fin dec deceq | suc n | enum | a with dec a 
list-of-finite A S fin dec deceq | suc n | enum | a | Inl yes = (enum (Inl <>)) ∷ list-of-finite A (trim A S fin) (trim-finite A S fin) (trim-decidable A S fin dec deceq) deceq 
list-of-finite A S fin dec deceq | suc n | enum | a | Inr no = {!   !}


-- Finsize : (A : Set) → (subset A) → Set 
-- Finsize A S = 
--   ((a : A) → ¬(S a)) + 
--   (Σ[ a ∈ A ] ())

-- data Finsize (A : Set) (S : subset A) : Set where 
--   Empty : ((a : A) → ¬(S a)) → Finsize
--   Singleton : Finsize 
--   Multiple : Finsize

-- size : {A : Set} → (Finset A) → Finsize
  