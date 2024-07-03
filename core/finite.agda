{-# OPTIONS --allow-unsolved-metas #-}
module core.finite where
  
open import core.logic
open import Data.List hiding (lookup)
open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Nullary
open import Data.Bool hiding (_<_; _≟_)
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)

_≟Fin_ : {n : ℕ} → (n1 n2 : Fin n) → Dec (n1 ≡ n2)
zero ≟Fin zero = yes refl
zero ≟Fin (suc _) = no (λ ())
(suc _) ≟Fin zero = no (λ ())
(suc n) ≟Fin (suc m) with n ≟Fin m
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })

vec-of-map : {A : Set} → {n : ℕ} → ((Fin n) → A) → Vec A n
vec-of-map {n = zero} f = []
vec-of-map {n = suc n} f = f zero ∷ vec-of-map {n = n} (λ x → f (suc x))

lookup-vec-of-map : {A : Set} → {n : ℕ} → (f : (Fin n) → A) → (i : Fin n) → (lookup (vec-of-map f) i ≡ (f i))
lookup-vec-of-map {n = suc n} f zero = refl
lookup-vec-of-map {n = suc n} f (suc i) = lookup-vec-of-map (λ z → f (suc z)) i

comprehend : {A B : Set} → {n : ℕ} → (Vec A n) → ((Fin n) → A → B) → List B 
comprehend {n = zero} [] f = []
comprehend {n = suc n} (a ∷ v) f = (f zero a) ∷ comprehend v (λ x → f (suc x))

-- ++assoc : {A : Set} → (l1 l2 l3 : List A) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
-- ++assoc [] l2 l3 = refl
-- ++assoc (x ∷ l1) l2 l3 rewrite ++assoc l1 l2 l3 = refl

-- append-exist : {A : Set} → (P : A → Set) → (l1 l2 : List A) → (a : A) → list-exists P l2 → list-exists P (l1 ++ l2)
-- append-exist P [] l2 a ex = ex
-- append-exist P (x ∷ l1) l2 a ex = ListExistsSkip x (append-exist P l1 l2 a ex)