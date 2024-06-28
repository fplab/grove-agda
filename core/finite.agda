{-# OPTIONS --allow-unsolved-metas #-}
module core.finite where
  
open import core.logic
open import Data.List
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)

  
data Finite : Set → Set₁ where 
  FinEmpty : {A : Set} → (A → ⊥) → Finite A 
  FinCons : {A B : Set} → 
    (Finite A) → 
    (f : (⊤ + A) → B) → 
    (g : B → (⊤ + A)) → 
    ((a : (⊤ + A)) → g (f a) ≡ a) → 
    ((b : B) → f (g b) ≡ b) → 
    Finite B

data Finite-Fun : (A : Set) → (B : Set₁) → (Finite A) → Set₁ where 
  FinFunEmpty : {A : Set} → {B : Set₁} → (empty : A → ⊥) → Finite-Fun A B (FinEmpty empty)
  FinFunCons : {A B : Set} → {C : Set₁}→ 
    (fin : Finite A) → 
    (f : (⊤ + A) → B) → 
    (g : B → (⊤ + A)) → 
    (i1 : (a : (⊤ + A)) → g (f a) ≡ a) → 
    (i2 : (b : B) → f (g b) ≡ b) → 
    (finfun : Finite-Fun A C fin) → 
    (c : C) → 
    (Finite-Fun B C (FinCons fin f g i1 i2))

finite-map : {B : Set} → {C : Set₁} → (fin : Finite B) → (B → C) → (Finite-Fun B C fin)
finite-map (FinEmpty x) F = FinFunEmpty x
finite-map (FinCons fin f g i1 i2) F = FinFunCons fin f g i1 i2 (finite-map fin (λ a → F (f (Inr a)))) (F (f (Inl <>)))

apply-finite-map : {B : Set} → {C : Set₁} → (fin : Finite B) → (Finite-Fun B C fin) → B → C 
apply-finite-map (FinEmpty x) (FinFunEmpty .x) b = abort (x b)
apply-finite-map (FinCons fin f g i1 i2) (FinFunCons .fin .f .g .i1 .i2 finfun c) b with inspect (g b) 
... | Inl <> with≡ _ = c
... | Inr a with≡ _ = apply-finite-map fin finfun a

apply-finite-map-correct : {B : Set} → {C : Set₁} → (fin : Finite B) → (F : B → C) → (b : B) → (apply-finite-map fin (finite-map fin F) b ≡ F b)
apply-finite-map-correct (FinEmpty x) F b = abort (x b)
apply-finite-map-correct (FinCons fin f g i1 i2) F b with inspect (g b) 
... | Inl <> with≡ eq rewrite (sym eq) rewrite (i2 b) = refl 
... | Inr a with≡ eq with apply-finite-map-correct fin (λ a → F (f (Inr a)))
... | ih rewrite (ih a) rewrite (sym eq) rewrite (i2 b) = refl

finite-comprehension : {B C : Set} → (Finite B) → (B → C) → List(C)
finite-comprehension (FinEmpty x) F = []
finite-comprehension (FinCons fin f g _ _) F = F (f (Inl <>)) ∷ (finite-comprehension fin (λ a → F (f (Inr a))))

-- forall-concat-cons : list-forall P (concat (l ∷ ls))

forall-concat-comprehension : {B C : Set} → (fin : Finite B) → (F : B → List C) → (P : C → Set) → ((b : B) → list-forall P (F b)) → (list-forall P (concat (finite-comprehension fin F)))
forall-concat-comprehension (FinEmpty x) F P fas = <>
forall-concat-comprehension (FinCons fin f g x x₁) F P fas = list-forall-append (fas (f (Inl <>))) (forall-concat-comprehension fin (λ z → F (f (Inr z))) P (λ b → fas (f (Inr b))))

-- -- will need to produce proofs
-- finite-map : {B C : Set} → (Finite B) → (B → C) → List(B × C)
-- finite-map (FinEmpty x) F = []
-- finite-map (FinCons fin f g e1 e2) F with finite-map fin (λ a → F (f (Inr a)))
-- ... | t = ((f (Inl <>) , F (f (Inl <>)))) ∷ (map (λ (a , c) → f (Inr a) , c) t)

-- finite-comprehension : {B C : Set} → (Finite B) → (B → List(C)) → List(C)
-- finite-comprehension fin F = concat (map (λ (_ , cs) → cs) (finite-map fin F))

-- apply-finite-map : {B C : Set} → (Finite B) → List(B × C) → ⊤ + C 
-- apply-finite-map fin l = {!   !}

++assoc : {A : Set} → (l1 l2 l3 : List A) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++assoc [] l2 l3 = refl
++assoc (x ∷ l1) l2 l3 rewrite ++assoc l1 l2 l3 = refl

append-exist : {A : Set} → (P : A → Set) → (l1 l2 : List A) → (a : A) → list-exists P l2 → list-exists P (l1 ++ l2)
append-exist P [] l2 a ex = ex
append-exist P (x ∷ l1) l2 a ex = ListExistsSkip x (append-exist P l1 l2 a ex)

forall-map-implies : {A B : Set} → {P1 : A → Set} → {P2 : B → Set} → {l : List A} → {f : A → B} → list-forall P1 l → ({a : A} → (P1 a) → (P2 (f a))) → list-forall P2 (map f l)
forall-map-implies {A} {B} {P1} {P2} {[]} {f} fa i = <>
forall-map-implies {A} {B} {P1} {P2} {x ∷ l} {f} (p , fa) i = i p , forall-map-implies {A} {B} {P1} {P2} {l} {f} fa i
