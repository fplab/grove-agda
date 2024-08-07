open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)
open import Data.Bool hiding (_<_; _≟_)
open import Data.Empty
open import Data.Fin
open import Data.List hiding (lookup)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Unit renaming (tt to <>)
open import Data.Vec hiding (map; _++_; concat; filter)
open import Function
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Nullary
open import Relation.Unary

-- rename to Utilities
module Grove.Prelude where
  private
    variable
      ℓ : Level

  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
  assimilation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))

  ¬-≡ : ∀ {A : Set} → (¬a : ¬ A) → (¬a' : ¬ A) → ¬a ≡ ¬a'
  ¬-≡ ¬a ¬a' = extensionality λ { a → ⊥-elim (¬a a) }

  _≟Fin_ : {n : ℕ} → (n1 n2 : Fin n) → Dec (n1 ≡ n2)
  zero ≟Fin zero = yes refl
  zero ≟Fin (suc _) = no (λ ())
  (suc _) ≟Fin zero = no (λ ())
  (suc n) ≟Fin (suc m) with n ≟Fin m
  ... | yes refl = yes refl
  ... | no neq = no (λ { refl → neq refl })

  cast-up : {n : ℕ} → (i : Fin n) → (Fin (suc n))
  cast-up zero = zero 
  cast-up (suc i) = suc (cast-up i)

  vec-of-map : {A : Set} → {n : ℕ} → ((Fin n) → A) → Vec A n
  vec-of-map {n = zero} f = []
  vec-of-map {n = suc n} f = f zero ∷ vec-of-map {n = n} (λ x → f (suc x))

  lookup-vec-of-map : {A : Set} → {n : ℕ} → (f : (Fin n) → A) → (i : Fin n) → (lookup (vec-of-map f) i ≡ (f i))
  lookup-vec-of-map {n = suc n} f zero = refl
  lookup-vec-of-map {n = suc n} f (suc i) = lookup-vec-of-map (λ z → f (suc z)) i

  comprehend : {A B : Set} → {n : ℕ} → (Vec A n) → ((Fin n) → A → B) → List B 
  comprehend {n = zero} [] f = []
  comprehend {n = suc n} (a ∷ v) f = (f zero a) ∷ comprehend v (λ x → f (suc x))

  comprehend-vec-of-map : {A B : Set} → {n : ℕ} → (f1 : (Fin n) → A) → (f2 : (Fin n) → A → B) → comprehend (vec-of-map f1) f2 ≡ toList (vec-of-map (λ x → f2 x (f1 (x)))) 
  comprehend-vec-of-map {n = zero} f1 f2 = refl
  comprehend-vec-of-map {n = suc n} f1 f2 rewrite comprehend-vec-of-map (λ z → f1 (suc z)) (λ z → f2 (suc z)) = refl

  map-compose : {A B C : Set} → {l : List A} → {f : B → C} → {g : A → B} → map f (map g l) ≡ map (f ∘ g) l 
  map-compose {l = []} {f = f} {g = g} = refl
  map-compose {l = x ∷ l} {f = f} {g = g} rewrite map-compose {l = l} {f = f} {g = g} = refl

  list-forall : ∀ {A : Set} → (A → Set) → (List A) → Set
  list-forall P [] = ⊤
  list-forall P (a ∷ l) = (P a) × (list-forall P l)

  list-forall-append : {A : Set} → {P : A → Set} → {l1 l2 : List A} → (list-forall P l1) → (list-forall P l2) → (list-forall P (l1 ++ l2))
  list-forall-append {l1 = []} <> f2 = f2
  list-forall-append {l1 = _ ∷ _} (p , f1) f2 = p , list-forall-append f1 f2

  list-forall-concat : {A : Set} → {P : A → Set} → {ls : List (List A)} → (list-forall (λ l → list-forall P l) ls) → list-forall P (concat ls)
  list-forall-concat {ls = []} f = <>
  list-forall-concat {ls = l ∷ ls} (p , f) = list-forall-append p (list-forall-concat f)

  list-forall-map : ∀ {A : Set} → {B : Set} → {P : B → Set} → {l : List A} → {f : A → B} → (list-forall (λ a → P (f a)) l) → list-forall P (map f l)
  list-forall-map {l = []} fa = <>
  list-forall-map {l = x ∷ l} (p , fa) = p , list-forall-map fa

  list-forall-filter : ∀ {A : Set} → {C : A → Set} → {P : A → Set} → {l : List A} → {dec : Decidable C} → (list-forall (λ a → C a → P a) l) → list-forall P (filter {P = C} dec l)
  list-forall-filter {l = []} <> = <>
  list-forall-filter {C = C} {l = x ∷ l} {dec = dec} (p , fa) with dec x 
  ... | yes p' = (p p') , (list-forall-filter fa)
  ... | no _ = list-forall-filter fa

  list-forall-toList : {A : Set} → {n : ℕ} → {f : Fin n → A} → {P : A → Set} → (p : (i : Fin n) → (P (f i))) → list-forall P (toList (vec-of-map f)) 
  list-forall-toList {n = zero} p = <>
  list-forall-toList {n = suc n} p = p zero , list-forall-toList (λ i → p (suc i))

  list-forall-implies : {A : Set} → {P1 P2 : A → Set} → {l : List A} → list-forall P1 l → ({a : A} → (P1 a) → (P2 a)) → list-forall P2 l
  list-forall-implies {l = []} f i = <>
  list-forall-implies {l = x ∷ l} (p , f) i = i p , list-forall-implies f i

  forall-map-implies : {A B : Set} → {P1 : A → Set} → {P2 : B → Set} → {l : List A} → {f : A → B} → list-forall P1 l → ({a : A} → (P1 a) → (P2 (f a))) → list-forall P2 (map f l)
  forall-map-implies {A} {B} {P1} {P2} {[]} {f} fa i = <>
  forall-map-implies {A} {B} {P1} {P2} {x ∷ l} {f} (p , fa) i = i p , forall-map-implies {A} {B} {P1} {P2} {l} {f} fa i

  list-forall-× : {A : Set} → {P1 P2 : A → Set} → {l : List A} → (list-forall P1 l) → (list-forall P2 l) → list-forall (λ a → (P1 a) × (P2 a)) l
  list-forall-× {l = []} <> <> = <>
  list-forall-× {l = x ∷ l} (p1 , f1) (p2 , f2) = (p1 , p2) , list-forall-× f1 f2

  data list-elem {A : Set} (a : A) : (List A) → Set where 
    ListElemHave : (l : List A) → list-elem a (a ∷ l) 
    ListElemSkip : {l : List A} → (b : A) → list-elem a l → list-elem a (b ∷ l)

  -- these two theorems are converses, and show that we could have instead defined forall in terms of elem
  list-forall-elem : {A : Set} → {P : A → Set} → {l : List A} → ((a : A) → (list-elem a l) → P a) → list-forall P l
  list-forall-elem {l = []} fa = <>
  list-forall-elem {l = x ∷ l} fa = (fa x (ListElemHave l)) , (list-forall-elem λ a elem → fa a (ListElemSkip x elem))

  list-elem-forall : {A : Set} → {P : A → Set} → {l : List A} → list-forall P l → ((a : A) → (list-elem a l) → P a)
  list-elem-forall {l = []} <> a ()
  list-elem-forall {l = x ∷ l} (p , fa) .x (ListElemHave .l) = p
  list-elem-forall {l = x ∷ l} (p , fa) a (ListElemSkip .x el) = list-elem-forall fa a el

  list-elem-append-left : {A : Set} → {a : A} → {l1 l2 : List A} → list-elem a l1 → list-elem a (l1 ++ l2)
  list-elem-append-left {l1 = []} ()
  list-elem-append-left {l1 = x ∷ l1} (ListElemHave .l1) = ListElemHave (l1 ++ _)
  list-elem-append-left {l1 = x ∷ l1} (ListElemSkip .x el) = ListElemSkip x (list-elem-append-left el)

  list-elem-append-right : {A : Set} → {a : A} → {l1 l2 : List A} → list-elem a l2 → list-elem a (l1 ++ l2)
  list-elem-append-right {l1 = []} el = el
  list-elem-append-right {l1 = x ∷ l1} el = ListElemSkip x (list-elem-append-right el)

  list-elem-concat : {A : Set} → {a : A} → {l : List A} → {ls : List (List A)} → list-elem a l → list-elem l ls → list-elem a (concat ls)
  list-elem-concat {l = l} {ls = []} el1 ()
  list-elem-concat {l = l} {ls = .l ∷ ls} el1 (ListElemHave .ls) = list-elem-append-left el1
  list-elem-concat {l = l1} {ls = l2 ∷ ls} el1 (ListElemSkip .l2 el2) = list-elem-append-right (list-elem-concat el1 el2)

  list-elem-map : {A B : Set} → {a : A} → {l : List A} → {f : A → B} → list-elem a l → list-elem (f a) (map f l)
  list-elem-map {l = []} ()
  list-elem-map {l = x ∷ l} {f = f} (ListElemHave .l) = ListElemHave (map f l)
  list-elem-map {l = x ∷ l} {f = f} (ListElemSkip .x el) = ListElemSkip (f x) (list-elem-map el)

  list-elem-filter : {A : Set} → {P : A → Set} → {a : A} → {l : List A} → {dec : Decidable P} → (P a) → list-elem a l → list-elem a (filter dec l)
  list-elem-filter {l = []} p ()
  list-elem-filter {l = a ∷ l} {dec = dec} p (ListElemHave .l) with dec a
  list-elem-filter {l = a ∷ l} {dec = dec} p (ListElemHave .l) | yes p' = ListElemHave (filter dec l)
  list-elem-filter {l = a ∷ l} p (ListElemHave .l) | no np = ⊥-elim (np p)
  list-elem-filter {l = x ∷ l} {dec = dec} p (ListElemSkip .x el) with dec x 
  list-elem-filter {l = x ∷ l} p (ListElemSkip .x el) | yes _ = ListElemSkip x (list-elem-filter p el)
  list-elem-filter {l = x ∷ l} p (ListElemSkip .x el) | no _ = list-elem-filter p el

  list-elem-toList : {A : Set} → {n : ℕ} → {f : Fin n → A} → (i : Fin n) → list-elem (f i) (toList (vec-of-map f)) 
  list-elem-toList {n = suc n} {f = f} zero = ListElemHave (toList (vec-of-map (λ z → f (suc z))))
  list-elem-toList {n = suc n} {f = f} (suc i) = ListElemSkip (f zero) (list-elem-toList i)

  elem-equiv : {A : Set} → (l1 l2 : List A) → Set
  elem-equiv {A} l1 l2 = (a : A) → ((list-elem a l1) → (list-elem a l2)) × ((list-elem a l2) → (list-elem a l1))
