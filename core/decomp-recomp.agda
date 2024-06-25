module core.decomp-recomp where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
open import Data.Bool
-- open import Data.Nat hiding (_+_)
-- open import core.var
-- open import core.hole
-- open import core.exp
-- open import core.pat
-- open import core.typ
-- open import core.term
open import core.logic
open import core.graph
open import core.graph-functions
open import core.grove

concat-grove : Grove → Θ 
concat-grove (γ NP MP U) = NP ++ MP ++ U

++assoc : {A : Set} → (l1 l2 l3 : List A) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++assoc [] l2 l3 = refl
++assoc (x ∷ l1) l2 l3 rewrite ++assoc l1 l2 l3 = refl

forall-implies : {A : Set} → (P1 P2 : A → Set) → (l : List A) → list-forall P1 l → ({a : A} → (P1 a) → (P2 a)) → list-forall P2 l
forall-implies P1 P2 [] f i = <>
forall-implies P1 P2 (x ∷ l) (p , f) i = i p , forall-implies P1 P2 l f i

append-exist : {A : Set} → (P : A → Set) → (l1 l2 : List A) → (a : A) → list-exists P l2 → list-exists P (l1 ++ l2)
append-exist P [] l2 a ex = ex
append-exist P (x ∷ l1) l2 a ex = ListExistsSkip x (append-exist P l1 l2 a ex)

interskip-exist : {A : Set} → (P : A → Set) → (l1 l2 : List A) → (a : A) → list-exists P (l1 ++ l2) → list-exists P (l1 ++ (a ∷ l2))
interskip-exist P [] l2 a ex = ListExistsSkip a ex
interskip-exist P (x ∷ l1) a l2 (ListExistsHave .x p .(l1 ++ a)) = ListExistsHave x p (l1 ++ l2 ∷ a)
interskip-exist P (x ∷ l1) a l2 (ListExistsSkip .x ex) = ListExistsSkip x (interskip-exist P l1 a l2 ex)

double-interskip : {A : Set} → (P : A → Set) → (l1 l2 l3 : List A) → (a : A) → list-exists P (l1 ++ l2 ++ l3) → list-exists P (l1 ++ l2 ++ (a ∷ l3))
double-interskip P l1 l2 l3 a ex rewrite sym (++assoc l1 l2 (a ∷ l3)) = interskip-exist P (l1 ++ l2) l3 a ex'
  where 
    ex' : list-exists P ((l1 ++ l2) ++ l3)
    ex' rewrite ++assoc l1 l2 l3 = ex

lemma-eleven-helper : (GG G : Graph) → (list-forall (λ ε → list-exists (λ t → (edge-decomp GG ε) ≡ t) (concat-grove (decomp-helper GG G))) (edges G))
lemma-eleven-helper GG [] = <>
lemma-eleven-helper GG ((E s v u ws , -) ∷ G) = forall-implies _ _ (edges G) (lemma-eleven-helper GG G) helper
  where
    helper : {ε : Edge} → 
      list-exists (λ t → (edge-decomp GG ε) ≡ t) (concat-grove (decomp-helper GG G)) → 
      list-exists (λ t → (edge-decomp GG ε) ≡ t) (concat-grove (decomp-helper GG ((E s v u ws , -) ∷ G)))
    helper {ε} ex with decomp-helper GG G | inedges v GG 
    helper {ε} ex | γ NP MP U | [] = ListExistsSkip _ ex
    helper {ε} ex | γ NP MP U | _ ∷ _ ∷ _  = interskip-exist _ NP (MP ++ U) _ ex
    helper {ε} ex | γ NP MP U | _ ∷ [] with (is-own-min-ancestor v GG)
    helper {ε} ex | γ NP MP U | _ ∷ [] | false = ex
    helper {ε} ex | γ NP MP U | _ ∷ [] | true = double-interskip  _ NP MP U _ ex

lemma-eleven-helper GG ((E s v u ws , +) ∷ G) = helper1 , forall-implies _ _ (edges G) (lemma-eleven-helper GG G) helper 
  where
    helper1 : list-exists (λ t → (edge-decomp GG (E s v u ws)) ≡ t) (concat-grove (decomp-helper GG ((E s v u _ , +) ∷ G)))
    helper1 with decomp-helper GG G | inedges v GG 
    helper1 | γ NP MP U | [] = ListExistsHave _ refl _
    helper1 | γ NP MP U | _ ∷ _ ∷ _  = append-exist _ NP _ (edge-decomp GG (E s v u ws)) (ListExistsHave _ refl _)
    helper1 | γ NP MP U | _ ∷ [] with (is-own-min-ancestor v GG)
    helper1 | γ NP MP U | _ ∷ [] | true = append-exist _ NP _ (edge-decomp GG (E s v u ws)) (append-exist _ MP _  (edge-decomp GG (E s v u ws)) (ListExistsHave _ refl _))
    helper1 | γ NP MP U | _ ∷ [] | false = {!   !} -- what about this case? I don't even understand how it's true on paper - Thomas
    -- Specifically, Lemma A.11 says every + edge in G decomposes to an entry in the grove. But what about ordinary edges that are 
    -- inside subterms? they have one parent, aren't their own least ancestor but they don't get their own grove entry. Right?

    helper : {ε : Edge} → 
      list-exists (λ t → (edge-decomp GG ε) ≡ t) (concat-grove (decomp-helper GG G)) → 
      list-exists (λ t → (edge-decomp GG ε) ≡ t) (concat-grove (decomp-helper GG ((E s v u ws , +) ∷ G)))
    helper {ε} ex with decomp-helper GG G | inedges v GG 
    helper {ε} ex | γ NP MP U | [] = ListExistsSkip _ ex
    helper {ε} ex | γ NP MP U | _ ∷ _ ∷ _  = interskip-exist _ NP (MP ++ U) _ ex
    helper {ε} ex | γ NP MP U | _ ∷ [] with (is-own-min-ancestor v GG)
    helper {ε} ex | γ NP MP U | _ ∷ [] | false = ex
    helper {ε} ex | γ NP MP U | _ ∷ [] | true = double-interskip _ NP MP U _ ex

lemma-eleven : (G : Graph) → (list-forall (λ ε → list-exists (λ t → (edge-decomp G ε) ≡ t) (concat-grove (decomp G))) (edges G))
lemma-eleven G = lemma-eleven-helper G G

-- I know we'll need custom equivalence to account for the list rep

decomp-recomp : (G : Graph) → (recomp(decomp(G)) ≡ G)
decomp-recomp G = {!   !} 