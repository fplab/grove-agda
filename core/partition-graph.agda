-- {-# OPTIONS --allow-unsolved-metas #-}

module core.partition-graph where

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

open import prelude
open import core.finite
open import core.graph

id-of-vertex : Vertex → Ident 
id-of-vertex (V ctor ident) = ident

id-min : Ident → Ident → Ident  
id-min u1 u2 with Dec.does (u1 ≤?𝕀 u2)
... | true = u1
... | false = u2

id-min-leq : (u1 u2 : Ident) → id-min u1 u2 ≤𝕀 u1
id-min-leq u1 u2 with (u1 ≤?𝕀 u2)
... | yes leq = ≤𝕀-reflexive u1
... | no nleq = {!   !} -- requires total order

id-min-comm : (u1 u2 : Ident) → (id-min u1 u2) ≡ (id-min u2 u1)
id-min-comm u1 u2 = {!   !}

-- id-min-assoc : (u1 u2 u3 : Ident) → (id-min u1 (id-min u2 u3)) ≡ (id-min (id-min u1 u2) u3)
-- id-min-assoc u1 u2 u3 = {!   !}

data parent : Graph → (v w : Vertex) → Set where 
  ParentHave : ∀{G v w a c} → parent ((E (S v a) w c) ∷ G) v w
  ParentSkip : ∀{G v w ε} → parent G v w → parent (ε ∷ G) v w

-- might need to emit proofs one day
parents : Graph → Vertex → List(Vertex) 
parents [] v = [] 
parents ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?)
parents ((E (S w _) _ _) ∷ G) v | true = w ∷ (parents G v) 
parents (_ ∷ G) v | false = parents G v

parents-correct : (G : Graph) → (v : Vertex) → list-forall (λ w → parent G w v) (parents G v) 
parents-correct [] v = <>
parents-correct ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?) | Dec.proof (v ≟Vertex v?)
parents-correct (E (S w _) v _ ∷ G) .v | true | ofʸ refl = ParentHave , list-forall-implies (parents-correct G v) (λ x → ParentSkip x)
parents-correct (_ ∷ G) v | false | _ = list-forall-implies (parents-correct G v) (λ x → ParentSkip x)

-- might need to emit proofs one day
children : Graph → Source → List(Ident × Vertex) 
children [] s = [] 
children ((E s? _ _) ∷ G) s with Dec.does (s ≟Source s?)
children ((E _ v u) ∷ G) s | true = (u , v) ∷ (children G s) 
children (_ ∷ G) s | false = children G s

children-correct : (G : Graph) → (v : Vertex) → (p : Fin (arity-v v)) → list-forall (λ (_ , w) → parent G v w) (children G (S v p))
children-correct [] v p = <>
children-correct ((E s? _ _) ∷ G) v p with Dec.does ((S v p) ≟Source s?) | Dec.proof ((S v p) ≟Source s?)
children-correct ((E _ w u) ∷ G) v p | true | ofʸ refl = ParentHave , (list-forall-implies (children-correct G v p) (λ x → ParentSkip x))
children-correct (_ ∷ G) v p | false | _ = list-forall-implies (children-correct G v p) (λ x → ParentSkip x)

data parent-class : Graph → Vertex → Set where 
  PC-NP : ∀{G v} → parent-class G v
  PC-UP : ∀{G v} → Vertex → parent-class G v
  PC-MP : ∀{G v} → parent-class G v

classify-parents : (G : Graph) → (v : Vertex) → parent-class G v 
classify-parents G v with parents G v 
classify-parents G v | [] = PC-NP
classify-parents G v | x ∷ [] = PC-UP x
classify-parents G v | _ ∷ _ ∷ _ = PC-MP

only-ancestor : Graph → (v w : Vertex) → (n : ℕ) → (Vec Vertex (suc (suc n))) → Set 
only-ancestor G v w n ws = 
    (lookup ws zero ≡ v) × 
    (lookup ws (fromℕ (suc n)) ≡ w) × 
    ((i : Fin (suc n)) → classify-parents G (lookup ws (cast-up i)) ≡ PC-UP (lookup ws (suc i)))

nat-only-ancestor : Graph → (v w : Vertex) → (n : ℕ) → Set 
nat-only-ancestor G v w n = 
  Σ[ ws ∈ (Vec Vertex (suc (suc n))) ] 
  (only-ancestor G v w n ws)

is-only-ancestor : Graph → (v w : Vertex) → Set 
is-only-ancestor G v w = 
  Σ[ n ∈ ℕ ] 
  (nat-only-ancestor G v w n)

min-id : {m : ℕ} → Vec Vertex m → Ident → Set
min-id {zero} ws u = ⊤
min-id {suc m} ws u = (i : Fin m) → u ≤𝕀 id-of-vertex (lookup ws (suc i))

is-only-ancestor-min-id : Graph → (v w : Vertex) → (u : Ident) → Set 
is-only-ancestor-min-id G v w u = 
  Σ[ n ∈ ℕ ] 
  Σ[ ws ∈ (Vec Vertex (suc (suc n))) ] 
  ((only-ancestor G v w n ws) × 
  min-id ws u)

data X : Set where 
  NP : X 
  MP : X 
  U : X 

top : X → Graph → Vertex → Set 
top NP G v = classify-parents G v ≡ PC-NP
top MP G v = classify-parents G v ≡ PC-MP 
top U G v = is-only-ancestor-min-id G v v (id-of-vertex v)

inner : X → Graph → Vertex → Vertex → Set 
inner X G v w = ¬(top U G v) × (is-only-ancestor G v w) × (top X G w)

-- zip-ancestors : (only-ancestor G v w1 n1 (v?1 ∷ v'1 ∷ ws1)) → (only-ancestor G v w2 n2 (v?2 ∷ v'2 ∷ ws2)) → (only-ancestor G v w)

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

min-snoc : {n : ℕ} → (G : Graph) → (u : Ident) → (x : Vertex) → (ws : Vec Vertex (suc n)) → 
  ((i : Fin (suc n)) → u ≤𝕀 id-of-vertex (lookup ws i)) → 
  ((i : Fin (suc (suc n))) → id-min u (id-of-vertex x) ≤𝕀 id-of-vertex (lookup (ws ∷ʳ x) i))
min-snoc G u x (_ ∷ []) min (suc zero) rewrite id-min-comm u (id-of-vertex x) = id-min-leq _ _
min-snoc G u x (_ ∷ ws) min zero = ≤𝕀-transitive _ _ _ (id-min-leq _ _) (min zero)
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

  min : (i : Fin 1) → id-of-vertex w ≤𝕀 id-of-vertex (lookup (w ∷ []) i)
  min zero = ≤𝕀-reflexive _

oami-implies-oa : (G : Graph) → (v w : Vertex) → (u : Ident) → 
  is-only-ancestor-min-id G v w u → 
  is-only-ancestor G v w
oami-implies-oa G v w u (a , b , c , d) = (a , b , c)

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

lem3 : (G : Graph) → (u : Ident) → (v v' : Vertex) → (n : ℕ) → (ws : Vec Vertex n) → 
  (only-ancestor G v v n (v ∷ v' ∷ ws)) →
  (min-id (v ∷ v' ∷ ws) u) → 
  is-only-ancestor-min-id G v' v' u
lem3 G u v v' n ws (refl , eq , cp) min = (n , (v' ∷ ws) ∷ʳ v' , (refl , lookup-snoc v' ws , cycle-cp ws eq cp) , cycle-min v v' ws min)
  where 

  cycle-min : {n : ℕ} → (v v' : Vertex) → (ws : Vec Vertex n) → min-id (v ∷ v' ∷ ws) u → min-id (v' ∷ (ws ∷ʳ v')) u
  cycle-min v v' ws min i = min-helper (v ∷ ws) (λ j → min (suc j)) (min zero) i
    where 
    min-helper : {n : ℕ} → (ws : Vec Vertex n) → min-id ws u → (u ≤𝕀 id-of-vertex v') → min-id (ws ∷ʳ v') u 
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

lem4-termin : (G : Graph) → (u : Ident) → (v w : Vertex) → (n : ℕ) →
  is-only-ancestor-min-id G v v u → 
  nat-only-ancestor G v w n → 
  (u ≤𝕀 id-of-vertex w)
lem4-termin G u v w zero (n1 , .v ∷ _ ∷ _ , (refl , _ , cp1) , min) (.v ∷ .w ∷ ws , refl , refl , cp2) with classify-parents G v | cp1 zero | cp2 zero 
lem4-termin G u v w zero (n1 , .v ∷ _ ∷ _ , (refl , _ , cp1) , min) (.v ∷ .w ∷ ws , refl , refl , cp2) | .(PC-UP w) | refl | refl = min zero
lem4-termin G u v w (suc n2) (zero , .v ∷ .v ∷ [] , (refl , refl , cp1) , min) (.v ∷ v? ∷ ws2 , refl , eq2 , cp2) with classify-parents G v | cp1 zero | cp2 zero
lem4-termin G u v w (suc n2) (zero , .v ∷ .v ∷ [] , (refl , refl , cp1) , min) (.v ∷ v? ∷ ws2 , refl , eq2 , cp2) | .(PC-UP v) | refl | refl = lem4-termin G u v w n2 ((zero , v ∷ v ∷ [] , (refl , refl , cp1) , min)) (v ∷ ws2 , refl , eq2 , λ i → cp2 (suc i))
lem4-termin G u v w (suc n2) (suc n1 , .v ∷ v' ∷ ws1 , (refl , eq1 , cp1) , min) (.v ∷ v'? ∷ ws2 , refl , eq2 , cp2) with classify-parents G v | cp1 zero | cp2 zero
lem4-termin G u v w (suc n2) (suc n1 , .v ∷ v' ∷ ws1 , (refl , eq1 , cp1) , min) (.v ∷ v'? ∷ ws2 , refl , eq2 , cp2) | .(PC-UP v') | refl | refl = lem4-termin G u v' w n2 (lem3 G u v v' (suc n1) ws1 (refl , eq1 , cp1) min) ( v' ∷ ws2 , refl , eq2 , λ i → cp2 (suc i))

lem4 : (G : Graph) → (u : Ident) →  (v w : Vertex) → 
  is-only-ancestor-min-id G v v u → 
  is-only-ancestor G v w → 
  (u ≤𝕀 id-of-vertex w)
lem4 G u v w oami (n , oa) = lem4-termin G u v w n oami oa 

lem5 : (G : Graph) → (v w : Vertex) → (top U G v) → is-only-ancestor G v w → (id-of-vertex v ≤𝕀 id-of-vertex w)
lem5 G v w top oa = lem4 G _ v w top oa

lem6 : (G : Graph) → (v w : Vertex) → (top U G v) → (top U G w) → is-only-ancestor G v w → (v ≡ w)
lem6 G v w top1 top2 oa1 = V-ident-uniq _ _ (≤𝕀-antisym _ _ (lem4 _ _ _ _ top1 oa1) (lem4 _ _ _ _ top2 oa2))
  where 
  oa2 : is-only-ancestor G w v 
  oa2 = lem2 G v w (oami-implies-oa _ _ _ _ top1) oa1

lem7 : (G : Graph) → (v w : Vertex) → (top U G w) → is-only-ancestor G v w → ((v ≡ w) + (inner U G v w))
lem7 G v w top oa with (v ≟Vertex w)
... | yes refl = Inl refl 
... | no neq = Inr ((λ top' → neq (lem6 _ _ _ top' top oa)) , oa , top)

lem8 : (G : Graph) → (v w : Vertex) → (top U G w) → is-only-ancestor G w v → ((v ≡ w) + (inner U G v w))
lem8 G v w top oa = lem7 G v w top (lem2 _ _ _ (oami-implies-oa _ _ _ _ top) oa)

lem9 : (G : Graph) → (v w : Vertex) → (top U G w) → (classify-parents G w ≡ PC-UP v) → ((v ≡ w) + (inner U G v w))
lem9 G v w top cp = lem8 G v w top (parent-implies-oa _ _ _ cp)

-- lem10 : (G : Graph) → (X : X) → (v w : Vertex) → (top U G v) → (top X G w) → is-only-ancestor G v w → (X ≡ U) × (v ≡ w)
-- lem10 G U v w top1 top2 oa =  (refl , lem6 G v w top1 top2 oa)
-- lem10 G NP v w top1 top2 oa = {!   !}
-- lem10 G MP v w top1 top2 oa = {!   !}

-- lem10 : (G : Graph) → (X : X) → (v x w : Vertex) → (inner X G v w) → (classify-parents G v ≡ PC-UP x) → ((top X G x) + (inner X G x w))
-- lem10 G X v x w (not-top , (n , ws , (eq1 , eq2 , cps)) , is-top) cp = {!   !} 

data class : Graph → Vertex → Set where 
  Top : ∀{G v} → (X : X) → class G v
  Inner : ∀{G v} → (X : X) → (w : Vertex) → class G v

data class-correct : (G : Graph) → (v : Vertex) → (class G v) → Set where 
  TopCorrect : ∀{X G v} → (top X G v) → class-correct G v (Top X) 
  InnerCorrect : ∀{X G v} → (w : Vertex) → (inner X G v w) → class-correct G v (Inner X w)
  
only-descendants : Graph → Vertex → List(Vertex × Ident) → Set 
only-descendants G v ws = list-forall (λ (w , u) → is-only-ancestor-min-id G w v u) ws

-- returns true if ( v , v.id ) appears in ws
locate-U : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → Bool
locate-U G v [] = false
locate-U G v ((v? , u) ∷ ws) with Dec.does (v ≟Vertex v?) | Dec.does (u ≟𝕀 (id-of-vertex v))
... | true | true = true
... | true | false = locate-U G v ws
... | false | _ = locate-U G v ws

locate-U-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → (locate-U G v ws ≡ true) → (top U G v)
locate-U-correct G v [] oas () 
locate-U-correct G v ((v? , u) ∷ ws) (oa , oas) eq with Dec.does (v ≟Vertex v?) | Dec.does (u ≟𝕀 (id-of-vertex v)) | Dec.proof (v ≟Vertex v?) | Dec.proof (u ≟𝕀 (id-of-vertex v))
... | true | true | ofʸ refl | ofʸ refl = oa
... | true | false | _ | _ = locate-U-correct G v ws oas eq
... | false | _ | _ | _ = locate-U-correct G v ws oas eq

update-ws : Vertex → List(Vertex × Ident) → Vertex → List(Vertex × Ident)
update-ws v ws x = (v , (id-of-vertex x)) ∷ (Data.List.map (λ (w , u) → (w , id-min u (id-of-vertex x))) ws)

update-ws-correct : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (x : Vertex) → (only-descendants G v ws) → (classify-parents G v ≡ PC-UP x) → (only-descendants G x (update-ws v ws x))
update-ws-correct G v ws x oas eq = (parent-implies-oami G v x eq) , forall-map-implies oas step
  where   
  step : {(w , u) : Vertex × Ident} →
    is-only-ancestor-min-id G w v u →
    is-only-ancestor-min-id G w x (id-min u (id-of-vertex x))
  step {(w , u)} (n , (.w ∷ ws1) , (refl , eq2 , cp) , min) = 
      (suc n , (w ∷ ws1) ∷ʳ x , (refl , lookup-snoc x ws1 , cp-snoc G x (w ∷ ws1) (equation eq2 eq) cp) , min-snoc G u x ws1 min)
    where 
    equation : lookup ws1 (fromℕ n) ≡ v → classify-parents G v ≡ PC-UP x → classify-parents G (lookup ws1 (fromℕ n)) ≡ PC-UP x
    equation eq1 eq2 rewrite eq1 rewrite eq2 = refl
  
-- {-# TERMINATING #-} 
classify : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (class G v)
classify zero G v ws = {!   !}
classify (suc fuel) G v ws with classify-parents G v
classify (suc fuel) G v ws | PC-NP = Top NP -- if it has no parents, it is Top NP
classify (suc fuel) G v ws | PC-MP = Top MP -- if it has multiple parents, it is Top MP
classify (suc fuel) G v ws | PC-UP x with locate-U G v ws
classify (suc fuel) G v ws | PC-UP x | true = Top U -- if it appears in the seen list with minimal id, it is Top U
classify (suc fuel) G v ws | PC-UP x | false with Dec.does (v ≟Vertex x)
classify (suc fuel) G v ws | PC-UP x | false | true = Top U -- if its parent is itself, it is Top U
classify (suc fuel) G v ws | PC-UP x | false | false with classify fuel G x (update-ws v ws x)
classify (suc fuel) G v ws | PC-UP x | false | false | Top X = Inner X x -- if its parent is Top, it is Inner
classify (suc fuel) G v ws | PC-UP x | false | false | Inner NP w = Inner NP w -- if its parent is Inner NP, it's the same
classify (suc fuel) G v ws | PC-UP x | false | false | Inner MP w = Inner MP w -- if its parent is Inner MP, it's the same
classify (suc fuel) G v ws | PC-UP x | false | false | Inner U w with Dec.does (v ≟Vertex w)
classify (suc fuel) G v ws | PC-UP x | false | false | Inner U w | true = Top U -- if its parent is Inner U rooted at itself, its Top U
classify (suc fuel) G v ws | PC-UP x | false | false | Inner U w | false = Inner U w -- if its parent is Inner U with a different root, its the same

only-top-X : (G : Graph) (x : X) → (v : Vertex) → Set
only-top-X G x v = ((Y : X) → (w : Vertex) → ¬(inner Y G v w)) × ((Y : X) → ¬(x ≡ Y) → ¬(top Y G v))

record class-complete (fuel : ℕ) (G : Graph) (v : Vertex) (ws : List(Vertex × Ident)) : Set where 
  constructor Complete
  field 
    TopComplete : ∀{X} → (top X G v) → (classify fuel G v ws ≡ Top X)
    InnerComplete : ∀{X} → (w : Vertex) → (inner X G v w) → ((classify fuel G v ws ≡ Inner X w) × (only-top-X G X w))

-- {-# TERMINATING #-} 
mutual 
  classify-correct : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → class-correct G v (classify fuel G v ws)
  classify-correct zero G v ws oas = {!   !}
  classify-correct (suc fuel) G v ws oas with classify-parents G v | inspect (classify-parents G) v
  classify-correct (suc fuel) G v ws oas | PC-NP | [ eq ] rewrite eq = TopCorrect eq
  classify-correct (suc fuel) G v ws oas | PC-MP | [ eq ] rewrite eq = TopCorrect eq
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] rewrite eq with locate-U G v ws | inspect (locate-U G v) ws
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | true | [ eq2 ] rewrite eq2 = TopCorrect (locate-U-correct G v ws oas eq2)
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] rewrite eq2 with Dec.does (v ≟Vertex x) | Dec.proof (v ≟Vertex x)
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | true | ofʸ refl = TopCorrect (parent-implies-oami G v v eq)
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq with if-top | classify fuel G x (update-ws v ws x) | inspect (classify fuel G x) (update-ws v ws x) | classify-correct fuel G x (update-ws v ws x) (update-ws-correct G v ws x oas eq)
    where 
    if-top : (top U G v) → (classify fuel G x (update-ws v ws x) ≡ Inner U v)
    if-top is-top with lem9 G x v is-top eq 
    if-top is-top | Inl eq2 = ⊥-elim (neq (sym eq2))
    if-top is-top | Inr eq4 with classify-complete fuel G x (update-ws v ws x) (update-ws-correct G v ws x oas eq)
    if-top is-top | Inr eq4 | (Complete _ inner-complete) = π1 (inner-complete _ eq4)
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Top X | [ eq3 ] | TopCorrect is-top = InnerCorrect x (not-top , parent-implies-oa G v x eq , is-top) 
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | ()
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner NP w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top)= InnerCorrect w ( not-top , oa-extend-left G _ _ _ eq oa , is-top)
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | ()
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner MP w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top)= InnerCorrect w ( not-top , oa-extend-left G _ _ _ eq oa , is-top)
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | ()
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner U w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top) with Dec.does (v ≟Vertex w) | Dec.proof (v ≟Vertex w) 
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner U w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top) | true | ofʸ refl = TopCorrect is-top 
  classify-correct (suc fuel) G v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner U w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top) | false | ofⁿ neq' = InnerCorrect w ( not-top , oa-extend-left G _ _ _ eq oa , is-top)
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | refl = neq' refl


  classify-complete : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → class-complete fuel G v ws
  classify-complete zero G v ws oas = {!   !}
  -- (classify-complete (suc fuel) G v ws oas) = Complete classify-complete-top {!   !} 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {NP} is-top with classify-parents G v
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {NP} refl | .PC-NP = refl
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {MP} is-top with classify-parents G v
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {MP} refl | .PC-MP = refl
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp), min) with lookup ws1 zero | eq1 | classify-parents G v | inspect (classify-parents G) v | (cp zero) 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-NP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-NP | [ eq3 ] | eq4 | ()
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-MP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-MP | [ eq3 ] | eq4 | ()
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP x | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl with locate-U G v ws
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | true = refl 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false with (v ≟Vertex (lookup ws1 (suc zero)))
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false | yes eq5 = refl 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false | no neq with classify-parent
    where 
    classify-parent : classify fuel G (lookup ws1 (suc zero)) (update-ws v ws (lookup ws1 (suc zero))) ≡ Inner U v
    classify-parent with lem9 G _ v (n , ws1 , (eq1 , eq2 , cp) , min) eq3 
    classify-parent | Inl eq = ⊥-elim (neq (sym eq))
    classify-parent | Inr is-inner with classify-complete fuel G (lookup ws1 (suc zero)) (update-ws v ws (lookup ws1 (suc zero))) (update-ws-correct G v ws (lookup ws1 (suc zero)) oas eq3)
    ... | Complete TopComplete InnerComplete = π1 (InnerComplete v is-inner)
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false | no neq | eq5 rewrite eq5 with (v ≟Vertex v) 
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false | no neq | eq5 | yes refl = refl
  class-complete.TopComplete (classify-complete (suc fuel) G v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false | no neq | eq5 | no neq2 = ⊥-elim (neq2 refl)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) with classify-correct (suc fuel) G v ws oas | lookup ws1 zero | eq1 | classify-parents G v | inspect (classify-parents G) v | (cp zero) 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | correct | _ | refl | PC-NP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | correct | _ | refl | PC-NP | [ eq3 ] | eq4 | ()
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | correct | _ | refl | PC-MP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | correct | _ | refl | PC-MP | [ eq3 ] | eq4 | ()
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP x | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl with locate-U G v ws
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | TopCorrect is-top2 | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | true = ⊥-elim (not-top is-top2)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false with (v ≟Vertex (lookup ws1 (suc zero)))
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) | TopCorrect is-top2 | _ | refl | PC-UP .(lookup ws1 (suc zero)) | [ eq3 ] | eq4 | refl | false | yes eq5 = ⊥-elim (not-top is-top2)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (zero , .v ∷ .w ∷ [] , (refl , refl , cp)) , is-top) | correct | _ | refl | PC-UP w | [ eq3 ] | eq4 | refl | false | no neq with classify-complete fuel G w (update-ws v ws w) (update-ws-correct G v ws w oas eq3)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (zero , .v ∷ .w ∷ [] , (refl , refl , cp)) , is-top) | correct | _ | refl | PC-UP w | [ eq3 ] | eq4 | refl | false | no neq | Complete top-complete inner-complete rewrite (top-complete is-top) = (refl , not-inner , not-top2)
    where 
    not-inner : (Y : _) → (w' : Vertex) → ¬(inner Y G w w')
    not-inner Y w' is-inner with classify fuel G w (update-ws v ws w) | π1 (inner-complete _ is-inner)
    ... | .(_) | () 

    not-top2 : (Y : _) → ¬(X ≡ Y) → ¬(top Y G w)
    not-top2 Y neq is-top3 with classify fuel G w (update-ws v ws w) | top-complete is-top | top-complete is-top3
    ... | Top .X | refl | refl = neq refl
    ... | Inner _ _ | () | _
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq with classify fuel G x (update-ws v ws x) | inspect (classify fuel G x) (update-ws v ws x) | classify-correct fuel G x (update-ws v ws x) (update-ws-correct G v ws x oas eq3) | classify-complete fuel G x (update-ws v ws x) (update-ws-correct G v ws x oas eq3)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top NP | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ with classify-parents G x | is-top2 | cp (suc zero)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top NP | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ | PC-NP | refl | () 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top MP | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ with classify-parents G x | is-top2 | cp (suc zero)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top MP | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ | PC-MP | refl | () 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ with lem8 G w x is-top2 (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i)))
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ | Inl eq6 rewrite eq6 with classify-parents G x | is-top | cp (suc zero) 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ | Inl eq6 | .PC-NP | refl | () 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete inner-complete | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) with classify-parents G w | is-top | cp2 zero 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete inner-complete | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) | .PC-NP | refl | ()
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ with lem8 G w x is-top2 (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i)))
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ | Inl eq6 rewrite eq6 with classify-parents G x | is-top | cp (suc zero) 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete _ | Inl eq6 | .PC-MP | refl | () 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete inner-complete | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) with classify-parents G w | is-top | cp2 zero 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete inner-complete | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) | .PC-MP | refl | ()
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Top U | [ eq5 ] | TopCorrect is-top2 | Complete top-complete inner-complete rewrite lem6 G x w is-top2 is-top (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i))) = (refl , not-inner , not-top2)
    where 
    not-inner : (Y : _) → (w' : Vertex) → ¬(inner Y G w w')
    not-inner Y w' is-inner with lem6 G x w is-top2 is-top (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i))) 
    ... | eq rewrite eq rewrite eq5 with classify fuel G w (update-ws v ws w) | π1 (inner-complete _ is-inner)
    ... | .(_) | ()

    not-top2 : (Y : _) → ¬(U ≡ Y) → ¬(top Y G w)
    not-top2 Y neq is-top3 with lem6 G x w is-top2 is-top (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i))) 
    ... | eq rewrite eq rewrite eq5 with top-complete is-top | top-complete is-top3
    ... | refl | refl = neq refl
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner X? w? | [ eq5 ] | InnerCorrect thing is-inner | complete = {!   !}
    
    
    -- where 
    --   v-x?-inner : inner X? G v x
    --   v-x?-inner = not-top , (zero , v ∷ x ∷ []  , (refl , refl , cp')) , is-top2
    --     where 
    --     cp' : (i : Fin 1) → classify-parents G (lookup (v ∷ x ∷ []) (cast-up i)) ≡ PC-UP (lookup (x ∷ []) i)
    --     cp' zero = cp zero

    -- classify-complete fuel G x (update-ws v ws x) (update-ws-correct G v ws x oas eq3)
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Complete _ inner-complete with inner-complete w ({!   !} , (n , x ∷ ws1  , (refl , eq2 , λ i → cp (suc i))) , is-top)
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Complete _ inner-complete | thing = {!   !}
    
    
    
    
    -- where 
    -- classify-complete-top : {X : X} → top X G v → (classify (suc fuel) G v ws ≡ Top X)
    -- classify-complete-top {NP} is-top with classify-parents G v
    -- classify-complete-top {NP} refl | .PC-NP = refl
    -- classify-complete-top {MP} is-top with classify-parents G v
    -- classify-complete-top {MP} refl | .PC-MP = refl
    -- classify-complete-top {U} is-top with classify-parents G v
    -- classify-complete-top {U} eq | (PC-UP x) = ?

-- -- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | NPTop | NPTopCorrect top = InnerCorrect NP x (HOA-base eq , top)
-- -- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | MPTop | MPTopCorrect top = InnerCorrect MP x (HOA-base eq , top)
-- -- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | UTop | UTopCorrect top = InnerCorrect U x (HOA-base eq , top)
-- -- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | NPInner w | NPInnerCorrect _ (oa , top) = InnerCorrect NP w (HOA-step eq oa , top)
-- -- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | MPInner w | MPInnerCorrect _ (oa , top) = InnerCorrect MP w (HOA-step eq oa , top)
-- -- classify-correct (suc fuel) G v ws oas | PC-UP x with≡ eq | false with≡ eq' | UInner w | UInnerCorrect _ (oa , top) = InnerCorrect U w (HOA-step eq oa , top)

-- -- -- this typechecks for me... I have no idea how
-- -- classify-correct-nptop : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → (classify G v ws ≡ NPTop) → (NP-top G v)
-- -- classify-correct-nptop G v ws oas ()

-- -- -- I broke it
-- -- silly : (G : Graph) → (v : Vertex) → (ws : List(Vertex × Ident)) → (only-descendants G v ws) → (classify G v ws ≡ NPTop) → ⊥
-- -- silly G v ws oas ()

-- -- postulate 
-- --   k : Ctor 
-- --   u : Ident 

-- -- absurd : ⊥ 
-- -- absurd = silly [] (V k u) [] <> refl

-- -- -- this is important 
-- -- -- classify-of-parent : (G : Graph) → 
-- -- --   (v w : Vertex) → 
-- -- --   (classify G w [] ≡ NPInner v) → 
-- -- --   (v' : Vertex) → 
-- -- --   (classify-parents G v' ≡ PC-UP w) → 
-- -- --   (classify G v' [] ≡ NPInner v)
-- -- -- classify-of-parent G v w eq1 v' eq2 with classify G w [] | classify-correct G w [] <> | eq1
-- -- -- ... | NPInner .v | NPInnerCorrect .v (oa , top) | refl = let npinner' = (HOA-step eq2 oa , top) in {!   !}
-- -- -- with inspect (classify-parents G v') | eq2
-- -- -- ... | PC-NP with≡ eq | () 
-- -- -- ... | PC-MP with≡ eq | ()
-- -- -- ... | PC-UP x with≡ eq | _ rewrite eq = {!   !}

-- -- data edge-class : Graph → Edge → Set where 
-- --   NPE : ∀{G ε} → Vertex → edge-class G ε
-- --   MPE : ∀{G ε} → Vertex → edge-class G ε
-- --   UE : ∀{G ε} → Vertex → edge-class G ε
  
-- -- edge-classify : (G : Graph) → (ε : Edge) → edge-class G ε 
-- -- edge-classify G (E (S v _) _ _) with classify G v []
-- -- ... | NPTop = NPE v 
-- -- ... | MPTop = MPE v
-- -- ... | UTop = UE v
-- -- ... | NPInner w = NPE w
-- -- ... | MPInner w = MPE w
-- -- ... | UInner w = UE w


-- -- -- classify-np-top : (G : Graph) → (v : Vertex) → (eq : NP-top G v) → (classify G [] v <> ≡ NPTop eq)
-- -- -- classify-np-top G v eq with inspect (classify-parents G v)
-- -- -- classify-np-top G v eq | (PC-NP with≡ eq') = {!   !}

-- -- list-assoc-update : List (Vertex × Graph) → Vertex → Edge → List (Vertex × Graph)
-- -- list-assoc-update [] v ε = (v , ε ∷ []) ∷ []
-- -- list-assoc-update ((v? , εs) ∷ l) v ε with Dec.does (v ≟Vertex v?)
-- -- ... | true = (v , ε ∷ εs) ∷ l
-- -- ... | false = (v? , εs) ∷ list-assoc-update l v ε

-- -- record  Partitioned-Graph : Set where
-- --   constructor PG
-- --   field
-- --     NP : List (Vertex × Graph)
-- --     MP : List (Vertex × Graph)
-- --     U : List (Vertex × Graph)

-- -- partition-graph-rec : Graph → (List Edge) → Partitioned-Graph 
-- -- partition-graph-rec G [] = PG [] [] []
-- -- partition-graph-rec G (ε ∷ εs) with edge-classify G ε | partition-graph-rec G εs 
-- -- ... | NPE x | PG NP MP U = PG (list-assoc-update NP x ε) MP U
-- -- ... | MPE x | PG NP MP U = PG NP (list-assoc-update MP x ε)U  
-- -- ... | UE x | PG NP MP U = PG NP MP (list-assoc-update U x ε)
    
-- -- partition-graph : Graph → Partitioned-Graph 
-- -- partition-graph G = partition-graph-rec G G
   
-- -- unpartition-graph : Partitioned-Graph → Graph          
-- -- unpartition-graph (PG NP MP U) = (concat (map (λ (v , εs) → εs) NP)) ++ (concat (map (λ (v , εs) → εs) MP)) ++ (concat (map (λ (v , εs) → εs) U)) 
            