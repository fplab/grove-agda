open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_<_; _≟_)
open import Data.List hiding (lookup; _∷ʳ_)
open import Data.Vec
open import Data.Fin hiding(_+_; _-_)
open import Data.Maybe hiding(map) 
open import Data.Nat hiding (_+_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit renaming (tt to <>)
open import Data.Product hiding (map)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)

open import core.finite
open import core.list-logic

module core.classify-lemmas 
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

import core.graph
open module graph = core.graph Ctor _≟ℂ_ arity
import core.classify
open module classify = core.classify Ctor _≟ℂ_ arity

id-min-leq : (u1 u2 : VertexId) → id-min u1 u2 ≤V𝕀 u1
id-min-leq u1 u2 with (u1 ≤?V𝕀 u2)
... | yes leq = ≤V𝕀-reflexive u1
... | no nleq with ≤V𝕀-total u1 u2 
... | Inl x = ⊥-elim (nleq x)
... | Inr x = x

id-min-comm : (u1 u2 : VertexId) → (id-min u1 u2) ≡ (id-min u2 u1)
id-min-comm u1 u2 with u1 ≤?V𝕀 u2 | u2 ≤?V𝕀 u1
id-min-comm u1 u2 | yes leq1 | yes leq2 = ≤V𝕀-antisym u1 u2 leq1 leq2
id-min-comm u1 u2 | no nleq | yes leq = refl
id-min-comm u1 u2 | yes leq | no nleq = refl
id-min-comm u1 u2 | no nleq1 | no nleq2 with ≤V𝕀-total u1 u2 
... | Inl x = ⊥-elim (nleq1 x)
... | Inr x = ⊥-elim (nleq2 x)

-- id-min-assoc : (u1 u2 u3 : Ident) → (id-min u1 (id-min u2 u3)) ≡ (id-min (id-min u1 u2) u3)
-- id-min-assoc u1 u2 u3 = {!   !}

lookup-snoc : {A : Set} → {n : ℕ} → (a : A) → (l : Vec A n) → lookup (l ∷ʳ a) (fromℕ n) ≡ a
lookup-snoc a [] = refl
lookup-snoc a (x ∷ l) = lookup-snoc a l

cp-snoc : {n : ℕ} → (G : Graph) → (x : Vertex) → (ws : Vec Vertex (suc (suc n))) → 
  classify-parents G (lookup ws (fromℕ (suc n))) ≡ PC-UP x → 
  ((i : Fin (suc n)) → classify-parents G (lookup ws (cast-up i)) ≡ PC-UP (lookup ws (suc i))) →
  ((i : Fin (suc (suc n))) → classify-parents G (lookup (ws ∷ʳ x) (cast-up i)) ≡ PC-UP (lookup (ws ∷ʳ x) (suc i)))
cp-snoc G x (_ ∷ y ∷ ws) eq cp zero = cp zero
cp-snoc G x (_ ∷ y ∷ []) eq cp (suc zero) = eq
cp-snoc G x (_ ∷ y ∷ z ∷ ws) eq cp (suc i) = cp-snoc G x (y ∷ z ∷ ws) eq (λ j → cp (suc j)) i

min-snoc : {n : ℕ} → (G : Graph) → (u : VertexId) → (x : Vertex) → (ws : Vec Vertex (suc n)) → 
  ((i : Fin (suc n)) → u ≤V𝕀 id-of-vertex (lookup ws i)) → 
  ((i : Fin (suc (suc n))) → id-min u (id-of-vertex x) ≤V𝕀 id-of-vertex (lookup (ws ∷ʳ x) i))
min-snoc G u x (_ ∷ []) min (suc zero) rewrite id-min-comm u (id-of-vertex x) = id-min-leq _ _
min-snoc G u x (_ ∷ ws) min zero = ≤V𝕀-transitive _ _ _ (id-min-leq _ _) (min zero)
min-snoc G u x (_ ∷ x₁ ∷ ws) min (suc i) = min-snoc G u x (x₁ ∷ ws) (λ j → min (suc j)) i

parent-implies-oa : (G : Graph) → (v w : Vertex) →
  classify-parents G v ≡ PC-UP w →
  is-only-ancestor G v w
parent-implies-oa G v w eq = zero , v ∷ w ∷ [] , refl , refl , cp
  where 
  cp : (i : Fin 1) → classify-parents G (lookup (v ∷ w ∷ []) (cast-up i)) ≡ PC-UP (lookup (w ∷ []) i)
  cp zero = eq

oa-extend-left : (G : Graph) → (v x w : Vertex) → 
  (classify-parents G v ≡ PC-UP x) → 
  (is-only-ancestor G x w) → 
  (is-only-ancestor G v w)
oa-extend-left G v x w cp (n , ws , eq1 , eq2 , cps) = suc n , v ∷ ws , refl , eq2 , cps'
  where 
  cps' : (i : Fin (suc (suc n))) → classify-parents G (lookup (v ∷ ws) (cast-up i)) ≡ PC-UP (lookup ws i)
  cps' zero rewrite eq1 = cp
  cps' (suc i) = cps i

parent-implies-oami : (G : Graph) → (v w : Vertex) →
  classify-parents G v ≡ PC-UP w →
  is-only-ancestor-min-id G v w (id-of-vertex w)
parent-implies-oami G v w eq = zero , v ∷ w ∷ [] , (refl , refl , cp) , min
  where 
  cp : (i : Fin 1) → classify-parents G (lookup (v ∷ w ∷ []) (cast-up i)) ≡ PC-UP (lookup (w ∷ []) i)
  cp zero = eq

  min : (i : Fin 1) → id-of-vertex w ≤V𝕀 id-of-vertex (lookup (w ∷ []) i)
  min zero = ≤V𝕀-reflexive _

oami-implies-oa : (G : Graph) → (v w : Vertex) → (u : VertexId) → 
  is-only-ancestor-min-id G v w u → 
  is-only-ancestor G v w
oami-implies-oa G v w u (a , b , c , d) = (a , b , c)

edge-of-parent :  (G : Graph) → (w v : Vertex) →
    (classify-parents G w ≡ PC-UP v) → 
    Σ[ p ∈ _ ] Σ[ u ∈ EdgeId ] (list-elem (E (S v p) w u) G)
edge-of-parent [] w v ()
edge-of-parent ((E s w? _) ∷ G) w v eq with (w ≟Vertex w?) 
edge-of-parent ((E (S v? _) .w _) ∷ G) w v eq | yes refl with (v ≟Vertex v?) 
edge-of-parent ((E (S v? p) .w u) ∷ G) w v eq | yes refl | yes refl = p , u , ListElemHave G
edge-of-parent ((E (S v? _) .w _) ∷ G) w v eq | yes refl | no neq with parents G w | inspect (parents G) w
edge-of-parent ((E (S v? _) .w _) ∷ G) w v refl | yes refl | no neq | [] | _ = ⊥-elim (neq refl)
edge-of-parent ((E (S v? _) .w _) ∷ G) w v () | yes refl | no neq | _ ∷ [] | _ 
edge-of-parent ((E (S v? _) .w _) ∷ G) w v () | yes refl | no neq | _ ∷ _ ∷ _ | _
edge-of-parent ((E (S v? p) w? u) ∷ G) w v eq | no neq with parents G w | inspect (parents G) w
edge-of-parent ((E (S v? p) w? u) ∷ G) w v () | no neq | [] | _
edge-of-parent ((E (S v? p) w? u) ∷ G) w v refl | no neq | .v ∷ [] | [ eq ] rewrite eq with edge-of-parent G w v (helper eq) 
  where 
  helper : parents G w ≡ v ∷ [] → classify-parents G w ≡ PC-UP v
  helper eq rewrite eq = refl
edge-of-parent ((E (S v? _) w? _) ∷ G) w v refl | no neq | .v ∷ [] | _ | p , u , elem = p , u , ListElemSkip _ elem
edge-of-parent ((E (S v? p) w? u) ∷ G) w v () | no neq | _ ∷ _ ∷ _ | _

-- BEGIN: this arithmetic is to jelp manifest termination for lem2

natminus : ℕ → ℕ → ℕ 
natminus a zero = a
natminus zero (suc b) = zero
natminus (suc a) (suc b) = natminus a b

gt-refl : (n : ℕ) → (n ≥ n)
gt-refl zero = z≤n
gt-refl (suc n) = s≤s (gt-refl n)

gt-boost : (a b : ℕ) → a ≥ b → (suc a) ≥ b
gt-boost a zero z≤n = z≤n
gt-boost (suc a) (suc b) (s≤s gt) = s≤s (gt-boost a b gt)

gt-minus-helper : (n1 n2 : ℕ) → ((Data.Nat._+_ n1 (suc n2)) ≥ (Data.Nat._+_ n1 (natminus n2 n1)))
gt-minus-helper zero zero = z≤n
gt-minus-helper zero (suc n2) = s≤s (gt-minus-helper zero n2)
gt-minus-helper (suc n1) zero rewrite +-suc n1 zero = s≤s (gt-boost _ _ (≤-reflexive refl))
gt-minus-helper (suc n1) (suc n2) rewrite +-suc n1 (suc n2) = s≤s (gt-boost _ _ (gt-minus-helper n1 n2))

gt-minus : (b n1 n2 m : ℕ) → (suc m ≡ (natminus n2 n1)) → (b ≥ Data.Nat._+_ n1 (suc n2)) → (b ≥ suc (Data.Nat._+_ n1 m))
gt-minus b n1 n2 m eq gt rewrite sym (+-suc n1 m) rewrite eq = ≤-trans (gt-minus-helper n1 n2) gt

-- END

lem1-termin : (G : Graph) → (x v w : Vertex) → (n1 n2 : ℕ) →
  nat-only-ancestor G x v n1 → 
  nat-only-ancestor G x w n2 → 
  (v ≡ w + (Σ[ m ∈ ℕ ] ((suc m ≡ (natminus n2 n1)) × nat-only-ancestor G v w m)) + is-only-ancestor G w v)
lem1-termin G x v w zero zero (.x ∷ .v ∷ [] , refl , refl , cp1) (.x ∷ .w ∷ [] , refl , refl , cp2) with classify-parents G x | cp1 zero | cp2 zero 
lem1-termin G x v w zero zero (.x ∷ .v ∷ [] , refl , refl , cp1) (.x ∷ .w ∷ [] , refl , refl , cp2) | .(PC-UP v) | refl | refl = Inl refl
lem1-termin G x v w zero (suc n2) (.x ∷ .v ∷ [] , refl , refl , cp1) (.x ∷ v? ∷ ws , refl , eq , cp2) with classify-parents G x | cp1 zero | cp2 zero
lem1-termin G x v w zero (suc n2) (.x ∷ .v ∷ [] , refl , refl , cp1) (.x ∷ v? ∷ ws , refl , eq , cp2) | .(PC-UP v) | refl | refl = Inr (Inl (n2 , refl , v ∷ ws , refl , eq , λ i → cp2 (suc i)))
lem1-termin G x v w (suc n1) zero (.x ∷ w? ∷ ws , refl , eq , cp1) (.x ∷ .w ∷ [] , refl , refl , cp2) with classify-parents G x | cp1 zero | cp2 zero
lem1-termin G x v w (suc n1) zero (.x ∷ w? ∷ ws , refl , eq , cp1) (.x ∷ .w ∷ [] , refl , refl , cp2) | .(PC-UP w) | refl | refl = Inr (Inr (n1 , w ∷ ws , refl , eq , λ i → cp1 (suc i)))
lem1-termin G x v w (suc n1) (suc n2) (.x ∷ x' ∷ ws1 , refl , eq1 , cp1) (.x ∷ x'? ∷ ws2 , refl , eq2 , cp2) with classify-parents G x | cp1 zero | cp2 zero
lem1-termin G x v w (suc n1) (suc n2) (.x ∷ x' ∷ ws1 , refl , eq1 , cp1) (.x ∷ x'? ∷ ws2 , refl , eq2 , cp2) | .(PC-UP x') | refl | refl = lem1-termin G x' v w n1 n2 (x' ∷ ws1 , refl , eq1 , λ i → cp1 (suc i)) (x' ∷ ws2 , refl , eq2 , λ i → cp2 (suc i))

lem1 : (G : Graph) → (x v w : Vertex) →
  is-only-ancestor G x v → 
  is-only-ancestor G x w → 
  (v ≡ w + is-only-ancestor G v w + is-only-ancestor G w v)
lem1 G x v w (n1 , oa1) (n2 , oa2) with lem1-termin G x v w n1 n2 oa1 oa2 
... | Inl eq = Inl eq
... | Inr (Inl (m , _ , oa)) = Inr (Inl (m , oa))
... | Inr (Inr oa) = Inr (Inr oa)

lem2-termin : (G : Graph) → (v w : Vertex) → (n1 n2 : ℕ) →
  (bound : ℕ) → 
  (bound ≥ Data.Nat._+_ n1 n2) →
  nat-only-ancestor G v v n1 → 
  nat-only-ancestor G v w n2 → 
  is-only-ancestor G w v 
lem2-termin G v w n1 n2 bound gt oa1 oa2 with lem1-termin G v v w n1 n2 oa1 oa2 
lem2-termin G v w n1 n2 bound gt oa1 oa2 | Inl refl = (n1 , oa1)
lem2-termin G v w n1 n2 bound gt oa1 oa2 | Inr (Inr oa3) = oa3
lem2-termin G v w zero (suc n2) (suc bound) (s≤s gt) oa1 oa2 | Inr (Inl (.n2 , refl , oa3)) = lem2-termin G v w zero n2 bound gt oa1 oa3
lem2-termin G v w (suc n1) (suc n2) (suc bound) (s≤s gt) oa1 oa2 | Inr (Inl (m , eq , oa3)) = lem2-termin G v w (suc n1) m bound (gt-minus _ _ _ _ eq gt) oa1 oa3

lem2 : (G : Graph) → (v w : Vertex) →
  is-only-ancestor G v v → 
  is-only-ancestor G v w → 
  is-only-ancestor G w v 
lem2 G v w (n1 , oa1) (n2 , oa2) = lem2-termin G v w n1 n2 _ (≤-reflexive refl) oa1 oa2

lem3 : (G : Graph) → (u : VertexId) → (v v' : Vertex) → (n : ℕ) → (ws : Vec Vertex n) → 
  (only-ancestor G v v n (v ∷ v' ∷ ws)) →
  (min-id (v ∷ v' ∷ ws) u) → 
  is-only-ancestor-min-id G v' v' u
lem3 G u v v' n ws (refl , eq , cp) min = (n , (v' ∷ ws) ∷ʳ v' , (refl , lookup-snoc v' ws , cycle-cp ws eq cp) , cycle-min v v' ws min)
  where 

  cycle-min : {n : ℕ} → (v v' : Vertex) → (ws : Vec Vertex n) → min-id (v ∷ v' ∷ ws) u → min-id (v' ∷ (ws ∷ʳ v')) u
  cycle-min v v' ws min i = min-helper (v ∷ ws) (λ j → min (suc j)) (min zero) i
    where 
    min-helper : {n : ℕ} → (ws : Vec Vertex n) → min-id ws u → (u ≤V𝕀 id-of-vertex v') → min-id (ws ∷ʳ v') u 
    min-helper (_ ∷ []) min lt zero = lt
    min-helper (_ ∷ x ∷ ws) min lt zero = min zero
    min-helper (_ ∷ x ∷ ws) min lt (suc i) = min-helper (x ∷ ws) (λ j → min (suc j)) lt i

  cycle-cp : {n : ℕ} → (ws : Vec Vertex n) → 
    (lookup (v' ∷ ws) (fromℕ n) ≡ v) →
    ((i : Fin (suc n)) → classify-parents G (lookup (v ∷ v' ∷ ws) (cast-up i)) ≡ PC-UP (lookup (v' ∷ ws) i)) → 
    ((i : Fin (suc n)) → classify-parents G (lookup (v' ∷ (ws ∷ʳ v')) (cast-up i)) ≡ PC-UP (lookup (ws ∷ʳ v') i))  
  cycle-cp [] eq cp zero rewrite eq = cp zero
  cycle-cp (x ∷ ws) eq cp zero = cp (suc zero)
  cycle-cp {suc n} (x ∷ ws) eq cp (suc i) rewrite eq = cp-helper x ws (equation eq) ((λ j → cp (suc (suc j)))) i
    where 
    equation : (lookup (x ∷ ws) (fromℕ n) ≡ v) → classify-parents G (lookup (x ∷ ws) (fromℕ n)) ≡ PC-UP v'
    equation eq rewrite eq = cp zero

    cp-helper : {n : ℕ} → (x : Vertex) → (ws : Vec Vertex n) → 
      (classify-parents G (lookup (x ∷ ws) (fromℕ n)) ≡ PC-UP v') →
      ((i : Fin n) → classify-parents G (lookup (x ∷ ws) (cast-up i)) ≡ PC-UP (lookup (x ∷ ws) (suc i))) → 
      ((i : Fin (suc n)) → classify-parents G (lookup ((x ∷ ws) ∷ʳ v') (cast-up i)) ≡ PC-UP (lookup ((x ∷ ws) ∷ʳ v') (suc i)))
    cp-helper x [] eq cp zero = eq
    cp-helper x (x₁ ∷ ws) eq cp zero = cp zero
    cp-helper x (x₁ ∷ ws) eq cp (suc i) = cp-helper x₁ ws eq (λ j → cp (suc j)) i

lem4-termin : (G : Graph) → (u : VertexId) → (v w : Vertex) → (n : ℕ) →
  is-only-ancestor-min-id G v v u → 
  nat-only-ancestor G v w n → 
  (u ≤V𝕀 id-of-vertex w)
lem4-termin G u v w zero (n1 , .v ∷ _ ∷ _ , (refl , _ , cp1) , min) (.v ∷ .w ∷ ws , refl , refl , cp2) with classify-parents G v | cp1 zero | cp2 zero 
lem4-termin G u v w zero (n1 , .v ∷ _ ∷ _ , (refl , _ , cp1) , min) (.v ∷ .w ∷ ws , refl , refl , cp2) | .(PC-UP w) | refl | refl = min zero
lem4-termin G u v w (suc n2) (zero , .v ∷ .v ∷ [] , (refl , refl , cp1) , min) (.v ∷ v? ∷ ws2 , refl , eq2 , cp2) with classify-parents G v | cp1 zero | cp2 zero
lem4-termin G u v w (suc n2) (zero , .v ∷ .v ∷ [] , (refl , refl , cp1) , min) (.v ∷ v? ∷ ws2 , refl , eq2 , cp2) | .(PC-UP v) | refl | refl = lem4-termin G u v w n2 ((zero , v ∷ v ∷ [] , (refl , refl , cp1) , min)) (v ∷ ws2 , refl , eq2 , λ i → cp2 (suc i))
lem4-termin G u v w (suc n2) (suc n1 , .v ∷ v' ∷ ws1 , (refl , eq1 , cp1) , min) (.v ∷ v'? ∷ ws2 , refl , eq2 , cp2) with classify-parents G v | cp1 zero | cp2 zero
lem4-termin G u v w (suc n2) (suc n1 , .v ∷ v' ∷ ws1 , (refl , eq1 , cp1) , min) (.v ∷ v'? ∷ ws2 , refl , eq2 , cp2) | .(PC-UP v') | refl | refl = lem4-termin G u v' w n2 (lem3 G u v v' (suc n1) ws1 (refl , eq1 , cp1) min) ( v' ∷ ws2 , refl , eq2 , λ i → cp2 (suc i))

lem4 : (G : Graph) → (u : VertexId) →  (v w : Vertex) → 
  is-only-ancestor-min-id G v v u → 
  is-only-ancestor G v w → 
  (u ≤V𝕀 id-of-vertex w)
lem4 G u v w oami (n , oa) = lem4-termin G u v w n oami oa 

lem5 : (G : Graph) → (v w : Vertex) → (top U G v) → is-only-ancestor G v w → (id-of-vertex v ≤V𝕀 id-of-vertex w)
lem5 G v w top oa = lem4 G _ v w top oa

lem6 : (G : Graph) → (has-uniq-ids G) → (v w : Vertex) → (top U G v) → (top U G w) → is-only-ancestor G v w → (v ≡ w)
lem6 G uniq-ids v w top1 top2 oa1 = uniq-ids _ _ (v-is-in-G oa1) (w-is-in-G oa1) (≤V𝕀-antisym _ _ (lem4 _ _ _ _ top1 oa1) (lem4 _ _ _ _ top2 oa2))
  where 
  v-is-in-G : is-only-ancestor G v w → v-in-G v G
  v-is-in-G (n , ws , eq1 , eq2 , cp) with edge-of-parent G v _ (eq3 eq1)
    where 
    eq3 : (lookup ws zero ≡ v) → classify-parents G v ≡ PC-UP (lookup ws (suc zero))
    eq3 eq1' rewrite (sym eq1) = cp zero
  ... | p , u , elem rewrite eq1 = VChild _ elem

  w-is-in-G : is-only-ancestor G v w → v-in-G w G
  w-is-in-G (n , ws , eq1 , eq2 , cp) with edge-of-parent G _ w eq3
    where 
    eq3 : classify-parents G (lookup ws (cast-up (fromℕ n))) ≡ PC-UP w
    eq3 rewrite (sym eq2) = cp (fromℕ n)
  ... | p , u , elem rewrite eq1 = VSource _ elem
  
  oa2 : is-only-ancestor G w v 
  oa2 = lem2 G v w (oami-implies-oa _ _ _ _ top1) oa1

lem7 : (G : Graph) → (has-uniq-ids G) → (v w : Vertex) → (top U G w) → is-only-ancestor G v w → ((v ≡ w) + (inner U G v w))
lem7 G uniq-ids v w top oa with (v ≟Vertex w)
... | yes refl = Inl refl 
... | no neq = Inr ((λ top' → neq (lem6 G uniq-ids _ _ top' top oa)) , oa , top)

lem8 : (G : Graph) → (has-uniq-ids G) → (v w : Vertex) → (top U G w) → is-only-ancestor G w v → ((v ≡ w) + (inner U G v w))
lem8 G uniq-ids v w top oa = lem7 G uniq-ids v w top (lem2 _ _ _ (oami-implies-oa _ _ _ _ top) oa)

lem9 : (G : Graph) → (has-uniq-ids G) → (v w : Vertex) → (top U G w) → (classify-parents G w ≡ PC-UP v) → ((v ≡ w) + (inner U G v w))
lem9 G uniq-ids v w top cp = lem8 G uniq-ids v w top (parent-implies-oa _ _ _ cp)

lem10 : (G : Graph) → (X Y : X) → (w : Vertex) → 
  (top X G w) → 
  (top Y G w) → 
  (X ≡ Y)
lem10 G NP NP w top1 top2 = refl
lem10 G NP MP w top1 top2 with classify-parents G w | top1 | top2
lem10 G NP MP w top1 top2 | _ | refl | ()
lem10 G NP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) with classify-parents G w | top1 | cp zero
lem10 G NP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) | _ | refl | ()
lem10 G MP NP w top1 top2 with classify-parents G w | top1 | top2
lem10 G MP NP w top1 top2 | _ | refl | ()
lem10 G MP MP w top1 top2 = refl
lem10 G MP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) with classify-parents G w | top1 | cp zero
lem10 G MP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) | _ | refl | ()
lem10 G U NP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 with classify-parents G w | cp zero | top2
lem10 G U NP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 | _ | refl | ()
lem10 G U MP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 with classify-parents G w | cp zero | top2
lem10 G U MP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 | _ | refl | ()
lem10 G U U w top1 top2 = refl

lem11 : (G : Graph) → (has-uniq-ids G) → (X Y : X) → (x w1 w2 : Vertex) → 
  is-only-ancestor G x w1 → 
  is-only-ancestor G x w2 → 
  (top X G w1) → 
  (top Y G w2) → 
  (X ≡ Y) × (w1 ≡ w2)
lem11 G uniq-ids X Y x w1 w2 oa1 oa2 top1 top2 with lem1 G x w1 w2 oa1 oa2
lem11 G uniq-ids X Y x w1 w1 oa1 oa2 top1 top2 | Inl refl = lem10 G X Y w1 top1 top2 , refl
lem11 G uniq-ids NP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) with classify-parents G w1 | top1 | cp zero
lem11 G uniq-ids NP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem11 G uniq-ids MP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) with classify-parents G w1 | top1 | cp zero
lem11 G uniq-ids MP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem11 G uniq-ids U Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) with lem8 G uniq-ids w2 w1 top1 oa3
lem11 G uniq-ids U Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inl refl = lem10 G U Y w1 top1 top2 , refl 
lem11 G uniq-ids U NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w2 | cp zero | top2
lem11 G uniq-ids U NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem11 G uniq-ids U MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w2 | cp zero | top2
lem11 G uniq-ids U MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem11 G uniq-ids U U x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , _ , _) = ⊥-elim (not-top top2)
lem11 G uniq-ids X NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) with classify-parents G w2 | top2 | cp zero
lem11 G uniq-ids X NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem11 G uniq-ids X MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) with classify-parents G w2 | top2 | cp zero
lem11 G uniq-ids X MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem11 G uniq-ids X U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) with lem8 G uniq-ids w1 w2 top2 oa3
lem11 G uniq-ids X U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inl refl = lem10 G X U w2 top1 top2 , refl 
lem11 G uniq-ids NP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w1 | cp zero | top1
lem11 G uniq-ids NP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem11 G uniq-ids MP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w1 | cp zero | top1
lem11 G uniq-ids MP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem11 G uniq-ids U U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , _ , _) = ⊥-elim (not-top top1)

parents-correct : (G : Graph) → (v : Vertex) → list-forall (λ w → parent G w v) (parents G v) 
parents-correct [] v = <>
parents-correct ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?) | Dec.proof (v ≟Vertex v?)
parents-correct (E (S w _) v _ ∷ G) .v | true | ofʸ refl = ParentHave , list-forall-implies (parents-correct G v) (λ x → ParentSkip x)
parents-correct (_ ∷ G) v | false | _ = list-forall-implies (parents-correct G v) (λ x → ParentSkip x)

children-correct : (G : Graph) → (v : Vertex) → (p : Fin (arity-v v)) → list-forall (λ (_ , w) → parent G v w) (children G (S v p))
children-correct [] v p = <>
children-correct ((E s? _ _) ∷ G) v p with Dec.does ((S v p) ≟Source s?) | Dec.proof ((S v p) ≟Source s?)
children-correct ((E _ w u) ∷ G) v p | true | ofʸ refl = ParentHave , (list-forall-implies (children-correct G v p) (λ x → ParentSkip x))
children-correct (_ ∷ G) v p | false | _ = list-forall-implies (children-correct G v p) (λ x → ParentSkip x)

locate-U-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × VertexId)) → (only-descendants G v ws) → (locate-U G v ws ≡ true) → (top U G v)
locate-U-correct G v [] oas () 
locate-U-correct G v ((v? , u) ∷ ws) (oa , oas) eq with Dec.does (v ≟Vertex v?) | Dec.does (u ≟V𝕀 (id-of-vertex v)) | Dec.proof (v ≟Vertex v?) | Dec.proof (u ≟V𝕀 (id-of-vertex v))
... | true | true | ofʸ refl | ofʸ refl = oa
... | true | false | _ | _ = locate-U-correct G v ws oas eq
... | false | _ | _ | _ = locate-U-correct G v ws oas eq

update-ws-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × VertexId)) → (x : Vertex) → (only-descendants G v ws) → (classify-parents G v ≡ PC-UP x) → (only-descendants G x (update-ws v ws x))
update-ws-correct G v ws x oas eq = (parent-implies-oami G v x eq) , forall-map-implies oas step
  where   
  step : {(w , u) : Vertex × VertexId} →
    is-only-ancestor-min-id G w v u →
    is-only-ancestor-min-id G w x (id-min u (id-of-vertex x))
  step {(w , u)} (n , (.w ∷ ws1) , (refl , eq2 , cp) , min) = 
      (suc n , (w ∷ ws1) ∷ʳ x , (refl , lookup-snoc x ws1 , cp-snoc G x (w ∷ ws1) (equation eq2 eq) cp) , min-snoc G u x ws1 min)
    where 
    equation : lookup ws1 (fromℕ n) ≡ v → classify-parents G v ≡ PC-UP x → classify-parents G (lookup ws1 (fromℕ n)) ≡ PC-UP x
    equation eq1 eq2 rewrite eq1 rewrite eq2 = refl 