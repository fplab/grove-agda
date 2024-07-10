open import Data.Unit renaming (tt to <>)
open import Data.Product hiding (map)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Vec hiding (concat;map;filter)
open import Function

open import Grove.Core.Ident
import Grove.Core.Graph
import Grove.Core.Grove

module Grove.Core.SimplEquiv where 
  
  postulate 
    Name : Set 
    _≟N_ : (x₁ x₂ : Name) → Dec (x₁ ≡ x₂) 

  data Ctor : Set where 
    Lam : Name → Ctor 
    Var : Name → Ctor 
    Ap : Ctor 

  _≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂) 
  Lam x ≟ℂ Lam x₁ with x ≟N x₁ 
  Lam x ≟ℂ Lam x₁ | yes refl = yes refl
  Lam x ≟ℂ Lam x₁ | no neq = no neq'
    where 
    neq' : ¬ Lam x ≡ Lam x₁
    neq' refl = neq refl
  Lam x ≟ℂ Var x₁ = no (λ ())
  Lam x ≟ℂ Ap = no (λ ())
  Var x ≟ℂ Lam x₁ = no (λ ())
  Var x ≟ℂ Var x₁ with x ≟N x₁ 
  Var x ≟ℂ Var x₁ | yes refl = yes refl
  Var x ≟ℂ Var x₁ | no neq = no neq'
    where 
    neq' : ¬ Var x ≡ Var x₁
    neq' refl = neq refl
  Var x ≟ℂ Ap = no (λ ())
  Ap ≟ℂ Lam x = no (λ ())
  Ap ≟ℂ Var x = no (λ ())
  Ap ≟ℂ Ap = yes refl

  arity : Ctor → ℕ
  arity (Lam x) = 1
  arity (Var x) = 0
  arity Ap = 2

  open module Graph = Grove.Core.Graph Ctor _≟ℂ_ arity

  mutual 
    data Term : Set where
      TAp : VertexId → TermList → TermList → Term 
      TVar : VertexId → Name → Term 
      TLam : VertexId → Name → TermList → Term 
      ⋎ : EdgeId → Vertex → Term 
      ⤾ : EdgeId → Vertex → Term
      
    data TermList : Set where 
      □ : Source → TermList 
      ∶ : (EdgeId × Term) → TermList
      ⋏ : Source → (List (EdgeId × Term)) → TermList

  open module grove = core.grove Ctor _≟ℂ_ arity renaming (Term to GTerm; TermList to GTermList)

  mutual 
    {-# TERMINATING #-}
    f1 : Term → GTerm 
    f1 (TAp x x₁ x₂) = T x Ap ((f1-list x₁) ∷ (f1-list x₂) ∷ [])
    f1 (TVar x x₁) = T x (Var x₁) []
    f1 (TLam x x₁ x₂) = T x (Lam x₁) (f1-list x₂ ∷ [])
    f1 (⋎ x x₁) = ⋎ x x₁ 
    f1 (⤾ x x₁) = ⤾ x x₁

    f1-list : TermList → GTermList
    f1-list (□ x) = □ x 
    f1-list (∶ (u , x)) = ∶ (u , f1 x)
    f1-list (⋏ x x₁) = ⋏ x (map (λ (u , x₂) → (u , f1 x₂)) x₁)

  mutual 
    {-# TERMINATING #-}
    f2 : GTerm → Term 
    f2 (T x (Lam x₁) (x₂ ∷ [])) = TLam x x₁ (f2-list x₂)
    f2 (T x (Var x₁) []) = TVar x x₁
    f2 (T x Ap (x₁ ∷ x₂ ∷ [])) = TAp x (f2-list x₁) (f2-list x₂)
    f2 (⋎ x x₁) = ⋎ x x₁ 
    f2 (⤾ x x₁) = ⤾ x x₁

    f2-list : GTermList → TermList
    f2-list (□ x) = □ x  
    f2-list (∶ (u , x)) = ∶ (u , f2 x)
    f2-list (⋏ x x₁) = ⋏ x (map (λ (u , x₂) → (u , f2 x₂)) x₁)

  mutual 
    {-# TERMINATING #-}
    f1-f2 : (t : Term) → (f2 (f1 t)) ≡ t 
    f1-f2 (TAp x x₁ x₂) rewrite f1-f2-list x₁ rewrite f1-f2-list x₂ = refl
    f1-f2 (TVar x x₁) = refl
    f1-f2 (TLam x x₁ x₂) rewrite f1-f2-list x₂ = refl
    f1-f2 (⋎ x x₁) = refl 
    f1-f2 (⤾ x x₁) = refl

    f1-f2-list : (t : TermList) → (f2-list (f1-list t)) ≡ t 
    f1-f2-list (□ x) = refl 
    f1-f2-list (∶ (u , x)) rewrite f1-f2 x = refl
    f1-f2-list (⋏ x x₁) rewrite f1-f2-map x₁ = refl
      
    f1-f2-map : (x : List (EdgeId × Term)) → (map (λ (u , x₂) → (u , f2 x₂)) (map (λ (u , x₂) → (u , f1 x₂)) x)) ≡ x
    f1-f2-map [] = refl 
    f1-f2-map ((u , x) ∷ x₁) rewrite f1-f2 x rewrite f1-f2-map x₁ = refl 

  mutual 
    {-# TERMINATING #-}
    f2-f1 : (t : GTerm) → (f1 (f2 t)) ≡ t 
    f2-f1 (T x (Lam x₂) (x₁ ∷ [])) rewrite (f2-f1-list x₁) = refl
    f2-f1 (T x (Var x₂) []) = refl
    f2-f1 (T x Ap (x₁ ∷ x₂ ∷ [])) rewrite (f2-f1-list x₁) rewrite (f2-f1-list x₂) = refl
    f2-f1 (⋎ x x₁) = refl 
    f2-f1 (⤾ x x₁) = refl

    f2-f1-list : (t : GTermList) → (f1-list (f2-list t)) ≡ t 
    f2-f1-list (□ x) = refl 
    f2-f1-list (∶ (u , x)) rewrite f2-f1 x = refl
    f2-f1-list (⋏ x x₁) rewrite f2-f1-map x₁ = refl
      
    f2-f1-map : (x : List (EdgeId × GTerm)) → (map (λ (u , x₂) → (u , f1 x₂)) (map (λ (u , x₂) → (u , f2 x₂)) x)) ≡ x
    f2-f1-map [] = refl 
    f2-f1-map ((u , x) ∷ x₁) rewrite f2-f1 x rewrite f2-f1-map x₁ = refl 
