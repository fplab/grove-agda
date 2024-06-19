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
Finite.bound (trim-finite A S (FIN zero enum enum-cover)) = zero
Finite.bound (trim-finite A S (FIN (suc bound) enum enum-cover)) = bound
Finite.enum (trim-finite A S (FIN zero enum enum-cover)) ()
Finite.enum (trim-finite A S (FIN (suc bound) enum enum-cover)) n = enum (Inr n)
Finite.enum-cover (trim-finite A S (FIN (suc bound) enum enum-cover)) a (elem , neq) with enum-cover a elem 
... | Inl <> , refl = abort (neq refl)
... | Inr x , eq = x , eq

trim-decidable : (A : Set) → (S : subset A) → (fin : Finite A S) → (Decidable A S) → (DecidableEquality A) → (Decidable A (trim A S fin))
trim-decidable A S fin dec deceq a with Finite.bound fin | Finite.enum fin
... | zero | _ = Inr (λ x → x)
... | suc n | enum with dec a 
... | Inr no = Inr λ (elem , _) → no elem
... | Inl yes with deceq a (enum (Inl <>))
... | Inl eq = Inr λ (_ , neq) → neq eq
... | Inr neq = Inl (yes , neq) 

finite-of-size : (A : Set) → (subset A) → (n : ℕ) → Set₁
finite-of-size A S n = Σ[ fin ∈ (Finite A S) ] (Finite.bound fin ≡ n)

trim-trims : (A : Set) → (S : subset A) → (fin : Finite A S) → (n : ℕ) → (Finite.bound fin ≡ suc n) → (Finite.bound (trim-finite A S fin) ≡ n)
trim-trims A S (FIN (suc bound) enum enum-cover) .bound refl = refl

-- trim-of-size : (A : Set) → (S : subset A) → (n : ℕ) → ((fin , _) : finite-of-size A S (suc n)) → (finite-of-size A (trim A S fin) n)
-- trim-of-size A S n (fin , eq) = {!   !}
-- with trim A S fin | trim-finite A S fin 
-- ... | S' | fin' = fin' , trim-trims A S' {! fin'  !} {!   !} {!   !}


list-of-finite : (A : Set) → (S : subset A) → (fin : Finite A S) → (bound : ℕ) → (Finite.bound fin ≡ bound) → (Decidable A S) → (DecidableEquality A) → (List A)
list-of-finite A S fin bound eq dec deceq with Finite.bound fin | Finite.enum fin
list-of-finite A S fin bound eq dec deceq | zero | _ = []
list-of-finite A S fin bound eq dec deceq | suc n | enum with (enum (Inl <>))
list-of-finite A S fin bound eq dec deceq | suc n | enum | a with dec a 
list-of-finite A S fin bound eq dec deceq | suc n | enum | a | Inr no = {!   !}
list-of-finite A S fin (suc bound) eq dec deceq | suc n | enum | a | Inl yes = (enum (Inl <>)) ∷ list-of-finite A (trim A S fin) (trim-finite A S fin) bound (trim-trims A S fin bound {! eq  !}) (trim-decidable A S fin dec deceq) deceq 


-- Finsize : (A : Set) → (subset A) → Set 
-- Finsize A S = 
--   ((a : A) → ¬(S a)) + 
--   (Σ[ a ∈ A ] ())

-- data Finsize (A : Set) (S : subset A) : Set where 
--   Empty : ((a : A) → ¬(S a)) → Finsize
--   Singleton : Finsize 
--   Multiple : Finsize

-- size : {A : Set} → (Finset A) → Finsize
  