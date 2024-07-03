module prelude where

open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- empty type
data ⊥ : Set where

-- from false, derive whatever
abort : ∀ {C : Set ℓ} → ⊥ → C
abort ()

-- negation 
open import Agda.Primitive using (Level)
¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

-- unit
data ⊤ {ℓ} : Set ℓ where
  <> : ⊤

-- pairs
infixr 1 _,_
record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (lmax ℓ₁ ℓ₂) where
  constructor _,_
  field
    π1 : A
    π2 : B π1
open Σ public

-- Sigma types, or dependent pairs, with nice notation.
syntax Σ A (\ x -> B) = Σ[ x ∈ A ] B

_×_ : (Set ℓ₁) → (Set ℓ₂) → Set (lmax ℓ₁ ℓ₂)
A × B = Σ A λ _ → B

-- sums
data _+_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (lmax ℓ₁ ℓ₂) where
  Inl : A → A + B
  Inr : B → A + B

infixr 1 _×_
infixr 1 _+_

data Singleton {A : Set ℓ} (x : A) : Set ℓ where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {A : Set ℓ} (x : A) → Singleton x
inspect x = x with≡ refl

list-forall : ∀ {A : Set ℓ₁} → (A → Set ℓ₂) → (List A) → (Set (lmax ℓ₁ ℓ₂))
list-forall P [] = ⊤
list-forall P (a ∷ l) = (P a) × (list-forall P l)

list-forall-append : {A : Set} → {P : A → Set} → {l1 l2 : List A} → (list-forall P l1) → (list-forall P l2) → (list-forall P (l1 ++ l2))
list-forall-append {l1 = []} <> f2 = f2
list-forall-append {l1 = _ ∷ _} (p , f1) f2 = p , list-forall-append f1 f2

list-forall-concat : {A : Set} → {P : A → Set} → {ls : List (List A)} → (list-forall (λ l → list-forall P l) ls) → list-forall P (concat ls)
list-forall-concat {ls = []} f = <>
list-forall-concat {ls = l ∷ ls} (p , f) = list-forall-append p (list-forall-concat f)

list-forall-map : ∀ {A : Set ℓ₁} → {B : Set ℓ₂} → {P : B → Set ℓ₃} → {l : List A} → {f : A → B} → (list-forall (λ a → P (f a)) l) → list-forall P (map f l)
list-forall-map {l = []} fa = <>
list-forall-map {l = x ∷ l} (p , fa) = p , list-forall-map fa

list-forall-implies : {A : Set} → {P1 P2 : A → Set} → {l : List A} → list-forall P1 l → ({a : A} → (P1 a) → (P2 a)) → list-forall P2 l
list-forall-implies {l = []} f i = <>
list-forall-implies {l = x ∷ l} (p , f) i = i p , list-forall-implies f i

forall-map-implies : {A B : Set} → {P1 : A → Set} → {P2 : B → Set} → {l : List A} → {f : A → B} → list-forall P1 l → ({a : A} → (P1 a) → (P2 (f a))) → list-forall P2 (map f l)
forall-map-implies {A} {B} {P1} {P2} {[]} {f} fa i = <>
forall-map-implies {A} {B} {P1} {P2} {x ∷ l} {f} (p , fa) i = i p , forall-map-implies {A} {B} {P1} {P2} {l} {f} fa i

list-forall-× : {A : Set} → {P1 P2 : A → Set} → {l : List A} → (list-forall P1 l) → (list-forall P2 l) → list-forall (λ a → (P1 a) × (P2 a)) l
list-forall-× {l = []} <> <> = <>
list-forall-× {l = x ∷ l} (p1 , f1) (p2 , f2) = (p1 , p2) , list-forall-× f1 f2

data list-exists {ℓ₁ ℓ₂} : {A : Set ℓ₁} → (A → Set ℓ₂) → (List A) → Set (lmax (lsuc ℓ₁) (lsuc ℓ₂)) where 
  ListExistsHave : {A : Set ℓ₁} → {P : A → Set ℓ₂} → (a : A) → (p : P a) → (l : List A) → list-exists P (a ∷ l) 
  ListExistsSkip : {A : Set ℓ₁} → {P : A → Set ℓ₂} → {l : List A} → (a : A) → list-exists P l → list-exists P (a ∷ l)

data list-equiv {ℓ} : {A : Set ℓ} → (l1 l2 : List A) → Set (lsuc ℓ) where 
  -- congruence
  ListEquivNil : {A : Set ℓ} → (list-equiv {ℓ} {A} [] [])
  ListEquivCons : {A : Set ℓ} → {l1 l2 : List A} → (a : A) → (list-equiv l1 l2) → (list-equiv (a ∷ l1) (a ∷ l2))
  -- symmetry
  ListEquivSym : {A : Set ℓ} → {l1 l2 : List A} → (list-equiv l1 l2) → (list-equiv l2 l1)
  -- transitvity
  ListEquivTrans : {A : Set ℓ} → {l1 l2 l3 : List A} → (list-equiv l1 l2) → (list-equiv l2 l3) → (list-equiv l1 l3)
  -- allow permutations
  ListEquivSwap : {A : Set ℓ} → {l1 l2 : List A} → (a b : A) → (list-equiv l1 l2) → (list-equiv (a ∷ b ∷ l1) (b ∷ a ∷ l2))
  -- todo? allow repeat entries

ListEquivRefl : {A : Set} → (l : List A) → (list-equiv l l)
ListEquivRefl [] = ListEquivNil
ListEquivRefl (x ∷ l) = ListEquivCons x (ListEquivRefl l)

ListEquivApp : {A : Set} → {l1 l2 l3 l4 : List A} → (list-equiv l1 l2) → (list-equiv l3 l4) → (list-equiv (l1 ++ l3) (l2 ++ l4))
ListEquivApp ListEquivNil eq = eq
ListEquivApp (ListEquivCons a e) eq = ListEquivCons a (ListEquivApp e eq)
ListEquivApp (ListEquivSym e) eq = ListEquivSym (ListEquivApp e (ListEquivSym eq))
ListEquivApp (ListEquivTrans e e₁) eq = ListEquivTrans (ListEquivApp e eq) (ListEquivApp e₁ (ListEquivTrans (ListEquivSym eq) eq))
ListEquivApp (ListEquivSwap a b e) eq = ListEquivSwap a b (ListEquivApp e eq)

ListEquivAppCons : {A : Set} → (l1 l2 : List A) → (a : A) → (list-equiv (l1 ++ (a ∷ l2)) (a ∷ (l1 ++ l2)))
ListEquivAppCons [] l2 a = ListEquivCons a (ListEquivRefl l2)
ListEquivAppCons (x ∷ l1) l2 a = ListEquivTrans (ListEquivCons x (ListEquivAppCons l1 l2 a)) (ListEquivSwap x a (ListEquivRefl _)) 

ListEquivAppAppCons : {A : Set} → (l1 l2 l3 : List A) → (a : A) → (list-equiv (l1 ++ l2 ++ (a ∷ l3)) (a ∷ (l1 ++ l2 ++ l3)))
ListEquivAppAppCons [] l2 l3 a = ListEquivAppCons l2 l3 a         
ListEquivAppAppCons (x ∷ l1) l2 l3 a = ListEquivTrans (ListEquivCons x (ListEquivAppAppCons l1 l2 l3 a)) ((ListEquivSwap x a (ListEquivRefl _)))
