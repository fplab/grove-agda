module core.logic where

open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

-- empty type
data ⊥ : Set where

-- from false, derive whatever
abort : ∀ {ℓ : Level} → {C : Set ℓ} → ⊥ → C
abort ()

-- negation 
open import Agda.Primitive using (Level)
¬_ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → ⊥

-- unit
data ⊤ : Set where
  <> : ⊤

-- pairs
infixr 1 _,_
record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (lmax l1 l2) where
  constructor _,_
  field
    π1 : A
    π2 : B π1
open Σ public

-- Sigma types, or dependent pairs, with nice notation.
syntax Σ A (\ x -> B) = Σ[ x ∈ A ] B

_×_ : {l1 : Level} {l2 : Level} → (Set l1) → (Set l2) → Set (lmax l1 l2)
A × B = Σ A λ _ → B

-- sums
data _+_ (A B : Set) : Set where
  Inl : A → A + B
  Inr : B → A + B

infixr 1 _×_
infixr 1 _+_

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

list-forall : {A : Set} → (A → Set) → (List A) → Set 
list-forall P [] = ⊤
list-forall P (a ∷ l) = (P a) × (list-forall P l)

data list-exists : {A : Set} → (A → Set) → (List A) → Set where 
  ListExistsHave : {A : Set} → {P : A → Set} → (a : A) → (p : P a) → (l : List A) → list-exists P (a ∷ l) 
  ListExistsSkip : {A : Set} → {P : A → Set} → {l : List A} → (a : A) → list-exists P l → list-exists P (a ∷ l)

data list-equiv : {A : Set} → (l1 l2 : List A) → Set where 
  -- congruence
  ListEquivNil : {A : Set} → (list-equiv {A} [] [])
  ListEquivCons : {A : Set} → {l1 l2 : List A} → (a : A) → (list-equiv l1 l2) → (list-equiv (a ∷ l1) (a ∷ l2))
  -- symmetry
  ListEquivSym : {A : Set} → {l1 l2 : List A} → (list-equiv l1 l2) → (list-equiv l2 l1)
  -- transitvity
  ListEquivTrans : {A : Set} → {l1 l2 l3 : List A} → (list-equiv l1 l2) → (list-equiv l2 l3) → (list-equiv l1 l3)
  -- allow permutations
  ListEquivSwap : {A : Set} → {l1 l2 : List A} → (a b : A) → (list-equiv l1 l2) → (list-equiv (a ∷ b ∷ l1) (b ∷ a ∷ l2))
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