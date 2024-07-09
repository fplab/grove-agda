module core.decomp-recomp where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Vec hiding (concat;map;filter)
open import Function

open import prelude
open import core.finite
open import core.list-logic
open import core.graph
open import core.grove
open import core.classify
open import core.classify-lemmas
open import core.classify-correct
open import core.decomp
open import core.recomp

lem12 : (G : Graph) → (v : Vertex) → (X : X) → (ε : Edge) →
  (edge X G ε v) → (top X G v)
lem12 G v X ε (TopEdge is-top) = is-top
lem12 G v X ε (InnerEdge (_ , _ , is-top)) = is-top

parents-in-G : (G : Graph) → (v : Vertex) → list-forall (λ w → list-elem w (vertices-of-G G)) (parents G v) 
parents-in-G [] v = <>
parents-in-G ((E s v? _) ∷ G) v with Dec.does (v ≟Vertex v?)
parents-in-G ((E (S w _) _ _) ∷ G) v | true = (ListElemHave _) , (list-forall-implies (parents-in-G G v) (ListElemSkip _))
parents-in-G (_ ∷ G) v | false = list-forall-implies (parents-in-G G v) (ListElemSkip _)

children-edges-in-G : (G : Graph) → (v : Vertex) → (p : _) → list-forall (λ (u' , v') → list-elem (E (S v p) v' u') G) (children G (S v p))
children-edges-in-G [] v p = <>
children-edges-in-G ((E s? _ _) ∷ G) v p with ((S v p) ≟Source s?)
children-edges-in-G ((E _ w u) ∷ G) v p | yes refl = ListElemHave G , list-forall-implies (children-edges-in-G G v p) (ListElemSkip _)
children-edges-in-G (_ ∷ G) v p | no neq = list-forall-implies (children-edges-in-G G v p) (ListElemSkip _)

edges-in-G-children : ∀{s w u'} → (G : Graph) → (list-elem (E s w u') G) → list-elem (u' , w) (children G s)
edges-in-G-children [] ()
edges-in-G-children {s} (.(E _ _ _) ∷ G) (ListElemHave .G) with s ≟Source s
edges-in-G-children {s} (.(E _ _ _) ∷ G) (ListElemHave .G) | yes refl = ListElemHave (children G s)
edges-in-G-children {s} (.(E _ _ _) ∷ G) (ListElemHave .G) | no neq = ⊥-elim (neq refl)
edges-in-G-children {s} (x ∷ G) (ListElemSkip .x elem) with Dec.does (s ≟Source Edge.source x)
edges-in-G-children {s} (x ∷ G) (ListElemSkip .x elem) | true = ListElemSkip _ (edges-in-G-children G elem)
edges-in-G-children {s} (x ∷ G) (ListElemSkip .x elem) | false = edges-in-G-children G elem

parents-cons-lemma : (G : Graph) → (v w : Vertex) → (x : Edge) → (list-elem v (parents G w)) → list-elem v (parents (x ∷ G) w)
parents-cons-lemma G v w x elem with does (w ≟Vertex Edge.child x)
parents-cons-lemma G v w x elem | true = ListElemSkip _ elem
parents-cons-lemma G v w x elem | false = elem

parents-of-children : (G : Graph) → ((V k u) : Vertex) → (p : Fin (arity k)) →
  list-forall (λ (_ , w) → list-elem (V k u) (parents G w)) (children G (S (V k u) p))
parents-of-children [] (V k u) p = <>
parents-of-children ((E s? w _) ∷ G) (V k u) p with (S (V k u) p) ≟Source s? 
parents-of-children ((E .(S (V k u) p) w u') ∷ G) (V k u) p | yes refl with (w ≟Vertex w)
parents-of-children ((E .(S (V k u) p) w u') ∷ G) (V k u) p | yes refl | yes refl = (ListElemHave (parents G w)) , list-forall-implies (parents-of-children G (V k u) p) (parents-cons-lemma G _ _ (E (S (V k u) p) (V (Vertex.ctor w) (Vertex.ident w)) u'))
parents-of-children ((E .(S (V k u) p) w u') ∷ G) (V k u) p | yes refl | no neq = ⊥-elim (neq refl)
parents-of-children ((E s? w u') ∷ G) (V k u) p | no neq = list-forall-implies (parents-of-children G (V k u) p) (parents-cons-lemma G _ _ (E s? (V (Vertex.ctor w) (Vertex.ident w)) u'))

unique-parent-in-G : (G : Graph) → (x w : Vertex) →
  (classify-parents G x ≡ PC-UP w) → list-elem w (vertices-of-G G)
unique-parent-in-G G x w eq with parents G x | parents-in-G G x | eq
... | .w ∷ [] | (elem , _) | refl = elem

-- classify-parent ((E (S v? p) .w u) ∷ G) w ≡ PC-UP

edge-of-parent :  (G : Graph) → (w v : Vertex) →
    (classify-parents G w ≡ PC-UP v) → 
    Σ[ p ∈ _ ] Σ[ u ∈ Ident ] (list-elem (E (S v p) w u) G)
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

inner-in-G : (fuel : ℕ) → (G : Graph) → (v w : Vertex) → (X : X) →
    inner X G v w → 
    list-elem w (vertices-of-G G)
inner-in-G fuel G v w X (_ , (n , ws , (_ , eq , cps)) , _) with cps (fromℕ n) 
... | cp rewrite eq = unique-parent-in-G G _ w cp

edge-classify-in-G : (fuel : ℕ) → (G : Graph) → (w : Vertex) → (X : X) → (ε : Edge) →
  (list-elem ε G) →
  (edge X G ε w) → 
  list-elem w (vertices-of-G G)
edge-classify-in-G fuel G w X .(E (S w _) _ _) elem (TopEdge _) = list-elem-map elem
edge-classify-in-G fuel G w X .(E (S _ _) _ _) elem (InnerEdge is-inner) = inner-in-G fuel G _ w X is-inner

vertex-of-decomp : (fuel : ℕ) → (G : Graph) → (v : Vertex) → vertex-of-term (decomp-v (suc fuel) G v) ≡ v 
vertex-of-decomp fuel G (V k u) = refl

vertex-of-decomp' : (fuel : ℕ) → (G : Graph) → (v : Vertex) → vertex-of-term (decomp-v' fuel G v) ≡ v 
vertex-of-decomp' zero G (V k u) = {!   !}
vertex-of-decomp' (suc fuel) G (V k u) with classify (suc fuel) G (V k u) [] 
... | Top NP = refl
... | Top MP = refl
... | Top U = refl
... | Inner X w = refl

-- 

-- 

-- -- can't use because no rewrite under binders
-- ideal-decomp-recomp-form : (fuel : ℕ) → (G : Graph) → ((V k u) : Vertex) →
--   recomp-t (decomp-v (suc fuel) G (V k u))
--   ≡ concat (toList (vec-of-map (λ p → 
--     concat (map (λ (u' , v') → ((E (S (V k u) p) v' u') ∷ (recomp-t (decomp-v' fuel G v')))) 
--            (children G (S (V k u) p))))))
-- ideal-decomp-recomp-form = {!   !} -- wait until you're unwrapping the result, then use the helpers below

decomp-recomp-form : (fuel : ℕ) → (G : Graph) → ((V k u) : Vertex) →
  recomp-t (decomp-v (suc fuel) G (V k u))
  ≡ concat (toList (vec-of-map (λ p → concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))))))
decomp-recomp-form fuel G (V k u) rewrite comprehend-vec-of-map (decomp-pos fuel G k u) (recomp-pos u k) = refl

-- decomp-recomp-inner-form : (fuel : ℕ) → (G : Graph) → ((V k u) : Vertex) → (p : Fin (arity k)) →
--   concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p))))
--   ≡ concat (map (λ (u' , v') → (E (S (V k u) p) (vertex-of-term (decomp-v' fuel G v')) u') ∷ (recomp-t (decomp-v' fuel G v'))) (children G (S (V k u) p)))
-- decomp-recomp-inner-form fuel G (V k u) p rewrite map-compose {l = (children G (S (V k u) p))} {f = (recomp-sub u k p)} {g = (decomp-sub fuel G)} = refl 

-- decomp-recomp-inner-inner-form : (fuel : ℕ) → (G : Graph) → ((V k u) : Vertex) → (p : Fin (arity k)) → (u' : Ident) → (v' : Vertex) →
--   _≡_ {A = List Edge} 
--     ((E (S (V k u) p) (vertex-of-term (decomp-v' fuel G v')) u') ∷ (recomp-t (decomp-v' fuel G v'))) 
--     ((E (S (V k u) p) v' u') ∷ (recomp-t (decomp-v' fuel G v')))
-- decomp-recomp-inner-inner-form fuel G (V k u) p u' v' rewrite vertex-of-decomp' fuel G v' = refl

--

--

lemma5 : (G : Graph) → (v v' : Vertex) → (X : X) → 
  (list-elem v (parents G v')) → (top X G v) → ¬(top MP G v') → ¬(top U G v') → inner X G v' v 
lemma5 G v v' X elem is-top not-top1 not-top2 with parents G v' | inspect (parents G) v'
lemma5 G v v' X () is-top not-top1 not-top2 | [] | _
lemma5 G v v' X elem is-top not-top1 not-top2 | _ ∷ _ ∷ _ | _ = ⊥-elim (not-top1 refl)
lemma5 G v v' X (ListElemHave .[]) is-top not-top1 not-top2 | .v ∷ [] | [ eq ] = not-top2 , (zero , v' ∷ v ∷ [] , refl , refl , cp) , is-top
  where 
  cp : (i : Fin 1) → (classify-parents G (Data.Vec.lookup (v' ∷ v ∷ []) (cast-up i))) ≡ PC-UP (Data.Vec.lookup (v ∷ []) i)
  cp zero rewrite eq = refl

lemma7 : (G : Graph) → (v w v' : Vertex) → (X : X) → 
  (list-elem w (parents G v')) → (inner X G w v) → ¬(top MP G v') → ¬(top U G v') → inner X G v' v 
lemma7 G v w v' X elem is-inner not-top1 not-top2 with parents G v' | inspect (parents G) v'
lemma7 G v w v' X () is-inner not-top1 not-top2 | [] | _
lemma7 G v w v' X elem is-inner not-top1 not-top2 | _ ∷ _ ∷ _ | _ = ⊥-elim (not-top1 refl)
lemma7 G v w v' X (ListElemHave .[]) (_ , (n , ws , eq1 , eq2 , cps) , is-top) not-top1 not-top2 | .w ∷ [] | [ eq ] = not-top2 , (suc n , v' ∷ ws , refl , eq2 , cps') , is-top
  where 
  cps' : (i : Fin (suc (suc n))) → (classify-parents G (Data.Vec.lookup (v' ∷ ws) (cast-up i))) ≡ PC-UP (Data.Vec.lookup ws i)
  cps' zero rewrite eq1 rewrite eq = refl
  cps' (suc i) = cps i

lemma9 : (fuel : ℕ) → (G : Graph) → (ε : Edge) → (list-elem ε G) → list-elem ε (recomp-t (decomp-v fuel G (Source.v (Edge.source ε))))
lemma9 zero G ε elem = {!   !} 
lemma9 (suc fuel) G (E (S (V k u) p) w u') elem rewrite decomp-recomp-form fuel G (V k u) = 
    list-elem-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))))))} 
    (list-elem-concat {ls = map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))} 
      elem1 (list-elem-map (list-elem-map (edges-in-G-children G elem)))) (list-elem-toList p)
    where 
    elem1 : list-elem (E (S (V k u) p) w u') (recomp-sub u k p (decomp-sub fuel G (u' , w))) 
    elem1 rewrite vertex-of-decomp' fuel G w = ListElemHave _

-- I can't get this to work because case2's type gets rewritten beyond recognition.
-- forall-decomp-recomp : (fuel : ℕ) → (G : Graph) → (X : X) → (v : Vertex) → (P : Edge → Set) →
--       (case1 : ∀{p u' v'} → (list-elem (E (S v p) v' u') G) → (list-elem v (parents G v')) → P (E (S v p) v' u')) →
--       (case2 : ∀{v'} → (list-elem v (parents G v')) → list-forall P (recomp-t (decomp-v fuel G v'))) →
--   list-forall P (recomp-t (decomp-v fuel G v))
-- forall-decomp-recomp zero G X (V k u) P case1 case2 = {!   !}
-- forall-decomp-recomp (suc fuel) G X (V k u) P case1 case2 rewrite decomp-recomp-form fuel G (V k u) = 
--     list-forall-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))))))} 
--     (list-forall-toList λ p → 
--     (list-forall-concat {ls = map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))} 
--     (list-forall-map {l = map (decomp-sub fuel G) (children G (S (V k u) p))} 
--     (list-forall-map {l = children G (S (V k u) p)}
--     (list-forall-implies (list-forall-× (children-edges-in-G G (V k u) p) (parents-of-children G (V k u) p)) (step2 p)))))) 
--     where
--     step2 : (p : Fin (arity k)) → {(u' , v') : Ident × Vertex} → ((edge-in-G , in-parents) : (list-elem (E (S (V k u) p) v' u') G) × (list-elem (V k u) (parents G v'))) → 
--               P (E (S (V k u) p) (vertex-of-term (decomp-v' fuel G v')) u') 
--               × list-forall P (recomp-t (decomp-v' fuel G v'))
--     step2 p {u' , v'} (edge-in-G , in-parents) rewrite vertex-of-decomp' fuel G v' = case1 edge-in-G in-parents , step3 in-parents {! case2 in-parents  !}
--       where 
--       step3 : (list-elem (V k u) (parents G v')) → (list-forall P (recomp-t (decomp-v fuel G v'))) →  list-forall P (recomp-t (decomp-v' fuel G v'))
--       step3 in-parents recurse with classify fuel G v' [] | inspect (classify fuel G v') [] | classify-correct fuel G v' [] <> | classify-complete fuel G v' [] <>
--       step3 in-parents recurse | Top NP | _ | TopCorrect is-top | _ with parents G v' | in-parents | is-top
--       step3 in-parents recurse | Top NP | _ | TopCorrect is-top | _ | [] | () | _
--       step3 in-parents recurse | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
--       step3 in-parents recurse | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
--       step3 in-parents recurse | Top MP | _ | _ | _ = <>
--       step3 in-parents recurse | Top U | _ | _ | _ = <> 
--       step3 in-parents recurse | Inner X? w? | [ eq ] | InnerCorrect .w? is-inner2 | Complete top-complete _ = recurse

-- unprime-rewrite : (fuel : ℕ) → (G : Graph) → (w v' : Vertex) → (P : Edge → Set) → (list-elem w (parents G v')) → list-forall P (recomp-t (decomp-v fuel G v')) → list-forall P (recomp-t (decomp-v' fuel G v'))
-- unprime-rewrite fuel G w v' P in-parents fa with classify fuel G v' [] | inspect (classify fuel G v') [] | classify-correct fuel G v' [] <> | classify-complete fuel G v' [] <>
-- unprime-rewrite fuel G w v' P in-parents fa | Top NP | _ | TopCorrect is-top | _ with parents G v' | in-parents | is-top
-- unprime-rewrite fuel G w v' P in-parents fa | Top NP | _ | TopCorrect is-top | _ | [] | () | _
-- unprime-rewrite fuel G w v' P in-parents fa | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
-- unprime-rewrite fuel G w v' P in-parents fa | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
-- unprime-rewrite fuel G w v' P in-parents fa | Top MP | _ | _ | _ = <>
-- unprime-rewrite fuel G w v' P in-parents fa | Top U | _ | _ | _ = <> 
-- unprime-rewrite fuel G w v' P in-parents fa | Inner X? w? | [ eq ] | InnerCorrect .w? is-inner2 | Complete top-complete _ = fa

lemma8 : (fuel : ℕ) → (G : Graph) → (X : X) → (w v : Vertex) →
  inner X G w v → 
  (ε : Edge) → 
  (list-elem ε (recomp-t (decomp-v fuel G w))) →
  list-elem ε (recomp-t (decomp-v fuel G v))
lemma8 zero G X w v is-inner = {!   !}
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (zero , .(V wk wu) ∷ .(V vk vu) ∷ [] , refl , refl , cp) , is-top) = base-case
  where 
  base-case : (ε : Edge) →
      list-elem ε (recomp-t (decomp-v (suc fuel) G (V wk wu))) →
      list-elem ε (recomp-t (decomp-v (suc fuel) G (V vk vu)))
  base-case ε elem rewrite decomp-recomp-form fuel G (V vk vu) with cp zero 
  ... | is-parent with edge-of-parent G _ _ is-parent 
  ... | p , u' , in-G = 
      list-elem-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub vu vk p) (map (decomp-sub fuel G) (children G (S (V vk vu) p)))))))}
      (list-elem-concat {ls = (map (recomp-sub vu vk p) (map (decomp-sub fuel G) (children G (S (V vk vu) p))))} 
      (ListElemSkip _ unprime)
      (list-elem-map (list-elem-map {a = (u' , (V wk wu))} (edges-in-G-children G in-G)))) 
      (list-elem-toList p) 
      where
      unprime : list-elem ε (recomp-t (decomp-v' fuel G (V wk wu)))
      unprime with classify fuel G (V wk wu) [] | inspect (classify fuel G (V wk wu)) [] | classify-correct fuel G (V wk wu) [] <> | classify-complete fuel G (V wk wu) [] <>
      unprime | Top NP | _ | TopCorrect is-top | _ with parents G (V wk wu) | cp zero | is-top
      unprime | Top NP | _ | TopCorrect is-top | _ | [] | () | _
      unprime | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
      unprime | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
      unprime | Top MP | _ | TopCorrect is-top | _ with parents G (V wk wu) | cp zero | is-top
      unprime | Top MP | _ | TopCorrect is-top | _ | [] | _ | ()
      unprime | Top MP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
      unprime | Top MP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | () | _      
      unprime | Top U | _ | TopCorrect is-top | _ = ⊥-elim (not-top is-top)
      unprime | Inner X? w? | [ eq ] | InnerCorrect .w? is-inner2 | Complete top-complete _ = fuel-change-elem
        where 
        fuel-change-elem : list-elem ε (recomp-t (decomp-v fuel G (V wk wu)))
        fuel-change-elem = {!   !} -- should be equivalent to elem
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) with classify fuel G w' [] | classify-correct fuel G w' [] <>
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) | Top NP | TopCorrect is-top2 with parents G w' | cp (suc zero) 
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) | Top NP | TopCorrect is-top2 | ps | eq rewrite is-top2 rewrite eq with eq 
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) | Top NP | TopCorrect is-top2 | ps | eq | ()
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) | Top MP | TopCorrect is-top2 with parents G w' | cp (suc zero) 
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) | Top MP | TopCorrect is-top2 | ps | eq rewrite is-top2 rewrite eq with eq 
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) | Top MP | TopCorrect is-top2 | ps | eq | ()
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ w' ∷ ws , refl , eq2 , cp) , is-top) | Top U | TopCorrect (n2 , ws2 , oa2 , min) = utop-case
  where 
  utop-case : (ε : Edge) → 
              (list-elem ε (recomp-t (decomp-v (suc fuel) G (V wk wu)))) →
              list-elem ε (recomp-t (decomp-v (suc fuel) G (V vk vu)))
  utop-case with lem11 G U X w' w' (V vk vu) (n2 , ws2 , oa2) (n , w' ∷ ws , refl , eq2 , λ i → cp (suc i)) (n2 , ws2 , oa2 , min) is-top  
  ... | refl , refl = lemma8 (suc fuel) G X (V wk wu) w' (not-top , (zero , (V wk wu) ∷ w' ∷ [] , refl , refl , cp') , is-top)
    where 
    cp' : (i : Fin 1) → classify-parents G (Data.Vec.lookup (V wk wu ∷ V vk vu ∷ []) (cast-up i)) ≡ PC-UP (Data.Vec.lookup (V vk vu ∷ []) i)
    cp' zero = cp zero
  
lemma8 (suc fuel) G X (V wk wu) (V vk vu) (not-top , (suc n , .(V wk wu) ∷ (V wk' wu') ∷ ws , refl , eq2 , cp) , is-top) | Inner Y v? | InnerCorrect .v? (no-top2 , (n2 , ws2 , eq3 , eq4 , cp2) , is-top2) = inner-case
  where 
  inner-case : (ε : Edge) → 
              (list-elem ε (recomp-t (decomp-v (suc fuel) G (V wk wu)))) →
              list-elem ε (recomp-t (decomp-v (suc fuel) G (V vk vu)))
  inner-case with lem11 G X Y (V wk' wu') (V vk vu) v? (n , (V wk' wu') ∷ ws , refl , eq2 , λ i → cp (suc i)) (n2 , ws2 , eq3 , eq4 , cp2) is-top is-top2
  ... | refl , refl = λ ε elem → fuel-change-ih _ (istep _ elem)
    where 
    istep : (ε : Edge) → 
         (list-elem ε (recomp-t (decomp-v (suc fuel) G (V wk wu)))) → 
          list-elem ε (recomp-t (decomp-v (suc fuel) G (V wk' wu')))
    istep ε elem rewrite decomp-recomp-form fuel G (V wk' wu') with cp zero 
    ... | is-parent with edge-of-parent G _ _ is-parent 
    ... | p , u' , in-G = 
        list-elem-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub wu' wk' p) (map (decomp-sub fuel G) (children G (S (V wk' wu') p)))))))}
        (list-elem-concat {ls = (map (recomp-sub wu' wk' p) (map (decomp-sub fuel G) (children G (S (V wk' wu') p))))} 
        (ListElemSkip _ unprime)
        (list-elem-map (list-elem-map {a = (u' , (V wk wu))} (edges-in-G-children G in-G)))) 
        (list-elem-toList p) 
        where
        unprime : list-elem ε (recomp-t (decomp-v' fuel G (V wk wu)))
        unprime with classify fuel G (V wk wu) [] | inspect (classify fuel G (V wk wu)) [] | classify-correct fuel G (V wk wu) [] <> | classify-complete fuel G (V wk wu) [] <>
        unprime | Top NP | _ | TopCorrect is-top | _ with parents G (V wk wu) | cp zero | is-top
        unprime | Top NP | _ | TopCorrect is-top | _ | [] | () | _
        unprime | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
        unprime | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
        unprime | Top MP | _ | TopCorrect is-top | _ with parents G (V wk wu) | cp zero | is-top
        unprime | Top MP | _ | TopCorrect is-top | _ | [] | _ | ()
        unprime | Top MP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
        unprime | Top MP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | () | _      
        unprime | Top U | _ | TopCorrect is-top | _ = ⊥-elim (not-top is-top)
        unprime | Inner X? w? | [ eq ] | InnerCorrect .w? is-inner2 | Complete top-complete _ = fuel-change-elem
          where 
          fuel-change-elem : list-elem ε (recomp-t (decomp-v fuel G (V wk wu)))
          fuel-change-elem = {!   !} -- should be equivalent to elem

    ih : (ε : Edge) → 
         (list-elem ε (recomp-t (decomp-v fuel G (V wk' wu')))) → 
          list-elem ε (recomp-t (decomp-v fuel G (V vk vu)))
    ih = lemma8 fuel G X (V wk' wu') (V vk vu) (no-top2 , (n2 , ws2 , eq3 , eq4 , cp2) , is-top2)

    fuel-change-ih : (ε : Edge) → 
         (list-elem ε (recomp-t (decomp-v (suc fuel) G (V wk' wu')))) → 
          list-elem ε (recomp-t (decomp-v (suc fuel) G (V vk vu)))
    fuel-change-ih = {!   !} -- should be equivalent to IH

-- lemma8 (suc fuel) G X (V wk wu) (V vk vu) is-inner rewrite decomp-recomp-form fuel G (V wk wu) =
--     list-forall-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub wu wk p) (map (decomp-sub fuel G) (children G (S (V wk wu) p)))))))} 
--     (list-forall-toList λ p → 
--     (list-forall-concat {ls = map (recomp-sub wu wk p) (map (decomp-sub fuel G) (children G (S (V wk wu) p)))} 
--     (list-forall-map {l = map (decomp-sub fuel G) (children G (S (V wk wu) p))} 
--     (list-forall-map {l = children G (S (V wk wu) p)} 
--     (list-forall-implies (list-forall-× (children-edges-in-G G (V wk wu) p) (parents-of-children G (V wk wu) p)) (step2 p)))))) 
--    where
--     step2 : (p : Fin (arity wk)) → {(u' , v') : Ident × Vertex} → ((edge-in-G , in-parents) : (list-elem (E (S (V wk wu) p) v' u') G) × (list-elem (V wk wu) (parents G v'))) → 
--               ( list-elem (E (S (V wk wu) p) (vertex-of-term (decomp-v' fuel G v')) u') (recomp-t (decomp-v (suc fuel) G (V vk vu))) 
--               × list-forall 
--                 (λ ε → list-elem ε (recomp-t (decomp-v (suc fuel) G (V vk vu))))              
--                 (recomp-t (decomp-v' fuel G v')) )
--     step2 p {u' , v'} (edge-in-G , in-parents) rewrite vertex-of-decomp' fuel G v' = {!   !} , step3 in-parents 
--       where 
--       base-case : list-elem (E (S (V wk wu) p) (vertex-of-term (decomp-v' fuel G v')) u') 
--                             (recomp-t (decomp-v (suc fuel) G (V vk vu)))  
--       base-case = {!   !}
--       step3 : (list-elem (V wk wu) (parents G v')) → list-forall (λ ε → list-elem ε (recomp-t (decomp-v (suc fuel) G (V vk vu)))) (recomp-t (decomp-v' fuel G v'))
--       step3 in-parents with classify fuel G v' [] | inspect (classify fuel G v') [] | classify-correct fuel G v' [] <> | classify-complete fuel G v' [] <>
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ with parents G v' | in-parents | is-top
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | [] | () | _
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
--       step3 in-parents | Top MP | _ | _ | _ = <>
--       step3 in-parents | Top U | _ | _ | _ = <> 
--       step3 in-parents | Inner X? w? | [ eq ] | InnerCorrect .w? is-inner2 | Complete top-complete _ = {!   !}

-- lemma8 (suc fuel) G X w v (not-top , (zero , .w ∷ .v ∷ [] , refl , refl , cp) , is-top) = {!   !}
-- lemma8 (suc fuel) G X w v (not-top , (suc n , ws , eq1 , eq2 , cp) , is-top) = {!   !}

-- lemma6 : (fuel : ℕ) → (G : Graph) → ((V k u) w : Vertex) → (X : X) → 
--   (inner X G (V k u) w) → list-forall (λ ε → edge X G ε w) (recomp-t (decomp-v fuel G (V k u)))
-- lemma6 zero G (V k u) w X is-inner = {!   !}
-- lemma6 (suc fuel) G (V k u) w X is-inner rewrite decomp-recomp-form fuel G (V k u) = 
--     list-forall-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))))))} 
--     (list-forall-toList λ p → 
--     (list-forall-concat {ls = map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))} 
--     (list-forall-map {l = map (decomp-sub fuel G) (children G (S (V k u) p))} 
--     (list-forall-map {l = children G (S (V k u) p)} 
--     (list-forall-implies (parents-of-children G (V k u) p) (step2 p)))))) 
--     where
--     step2 : (p : Fin (arity k)) → {(u' , v') : Ident × Vertex} → (in-parents : list-elem (V k u) (parents G v')) → 
--               edge X G (E (S (V k u) p) (vertex-of-term (decomp-v' fuel G v')) u') w 
--               × list-forall (λ ε → edge X G ε w) (recomp-t (decomp-v' fuel G v'))
--     step2 p {u' , v'} in-parents rewrite vertex-of-decomp' fuel G v' = InnerEdge is-inner , step3 in-parents
--       where 
--       step3 : (list-elem (V k u) (parents G v')) →  list-forall (λ ε → edge X G ε w) (recomp-t (decomp-v' fuel G v'))
--       step3 in-parents with classify fuel G v' [] | inspect (classify fuel G v') [] | classify-correct fuel G v' [] <> | classify-complete fuel G v' [] <>
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ with parents G v' | in-parents | is-top
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | [] | () | _
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
--       step3 in-parents | Top MP | _ | _ | _ = <>
--       step3 in-parents | Top U | _ | _ | _ = <> --(_ , (n , ws , eq1 , eq2 , cps) , is-top)
--       step3 in-parents | Inner X? w? | [ eq ] | InnerCorrect .w? is-inner2 | Complete top-complete _ = lemma6 fuel G _ _ X (lemma7 G _ _ _ X in-parents is-inner not-mp not-u) 
--           where 
--           not-mp : ¬ (top MP G v')
--           not-mp is-top with (top-complete {X = MP} is-top)
--           ... | eq2 rewrite eq with eq2 
--           ... | ()
--           not-u : ¬ (top U G v')
--           not-u is-top with (top-complete {X = U} is-top)
--           ... | eq2 rewrite eq with eq2 
--           ... | ()
          
-- decomp-recomp-v-sound : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (X : X) → 
--   (top X G v) → 
--   list-forall (λ ε → edge X G ε v) (recomp-t (decomp-v fuel G v))
-- decomp-recomp-v-sound zero G (V k u) X is-top = {!   !}
-- decomp-recomp-v-sound (suc fuel) G (V k u) X is-top rewrite decomp-recomp-form fuel G (V k u) =
--     list-forall-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))))))} 
--     (list-forall-toList λ p → 
--     (list-forall-concat {ls = map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))} 
--     (list-forall-map {l = map (decomp-sub fuel G) (children G (S (V k u) p))} 
--     (list-forall-map {l = children G (S (V k u) p)} 
--     (list-forall-implies (parents-of-children G (V k u) p) (step2 p))))))
--     where
--     step2 : (p : Fin (arity k)) → {(u' , v') : Ident × Vertex} → (in-parents : list-elem (V k u) (parents G v')) → 
--               edge X G (E (S (V k u) p) (vertex-of-term (decomp-v' fuel G v')) u') (V k u)
--               × list-forall (λ ε → edge X G ε (V k u)) (recomp-t (decomp-v' fuel G v'))
--     step2 p {u' , v'} in-parents rewrite vertex-of-decomp' fuel G v' = TopEdge is-top , (step3 in-parents)
--       where 
--       step3 : (list-elem (V k u) (parents G v')) →  list-forall (λ ε → edge X G ε (V k u)) (recomp-t (decomp-v' fuel G v'))
--       step3 in-parents with classify fuel G v' [] | inspect (classify fuel G v') [] | classify-correct fuel G v' [] <> | classify-complete fuel G v' [] <>
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ with parents G v' | in-parents | is-top
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | [] | () | _
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
--       step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
--       step3 in-parents | Top MP | _ | _ | _ = <>
--       step3 in-parents | Top U | _ | _ | _ = <>
--       step3 in-parents | Inner X' w | [ eq ] | InnerCorrect .w is-inner | Complete top-complete _ = lemma6 fuel G v' (V k u) X (lemma5 G (V k u) v' X in-parents is-top not-mp not-u)
--         where 
--         not-mp : ¬ (top MP G v')
--         not-mp is-top with (top-complete {X = MP} is-top)
--         ... | eq2 rewrite eq with eq2 
--         ... | ()
--         not-u : ¬ (top U G v')
--         not-u is-top with (top-complete {X = U} is-top)
--         ... | eq2 rewrite eq with eq2 
--         ... | ()

lemma6 : (fuel : ℕ) → (G : Graph) → ((V k u) w : Vertex) → (X : X) → 
  (inner X G (V k u) w) → list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v fuel G (V k u)))
lemma6 zero G (V k u) w X is-inner = {!   !} 
lemma6 (suc fuel) G (V k u) w X is-inner rewrite decomp-recomp-form fuel G (V k u) = 
    list-forall-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))))))} 
    (list-forall-toList λ p → 
    (list-forall-concat {ls = map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))} 
    (list-forall-map {l = map (decomp-sub fuel G) (children G (S (V k u) p))} 
    (list-forall-map {l = children G (S (V k u) p)} 
    (list-forall-implies (list-forall-× (children-edges-in-G G (V k u) p) (parents-of-children G (V k u) p)) (step2 p)))))) 
    where
    step2 : (p : Fin (arity k)) → {(u' , v') : Ident × Vertex} → ((edge-in-G , in-parents) : (list-elem (E (S (V k u) p) v' u') G) × (list-elem (V k u) (parents G v'))) → 
              list-elem (E (S (V k u) p) (vertex-of-term (decomp-v' fuel G v')) u') G 
              × list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v' fuel G v'))
    step2 p {u' , v'} (edge-in-G , in-parents) rewrite vertex-of-decomp' fuel G v' = edge-in-G , step3 in-parents
      where 
      step3 : (list-elem (V k u) (parents G v')) →  list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v' fuel G v'))
      step3 in-parents with classify fuel G v' [] | inspect (classify fuel G v') [] | classify-correct fuel G v' [] <> | classify-complete fuel G v' [] <>
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ with parents G v' | in-parents | is-top
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ | [] | () | _
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
      step3 in-parents | Top MP | _ | _ | _ = <>
      step3 in-parents | Top U | _ | _ | _ = <> --(_ , (n , ws , eq1 , eq2 , cps) , is-top)
      step3 in-parents | Inner X? w? | [ eq ] | InnerCorrect .w? is-inner2 | Complete top-complete _ = lemma6 fuel G _ _ X (lemma7 G _ _ _ X in-parents is-inner not-mp not-u) 
          where 
          not-mp : ¬ (top MP G v')
          not-mp is-top with (top-complete {X = MP} is-top)
          ... | eq2 rewrite eq with eq2 
          ... | ()
          not-u : ¬ (top U G v')
          not-u is-top with (top-complete {X = U} is-top)
          ... | eq2 rewrite eq with eq2 
          ... | ()

decomp-recomp-v-in-G : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (X : X) → 
  (top X G v) → 
  list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v fuel G v))
decomp-recomp-v-in-G zero G (V k u) X is-top = {!   !}
decomp-recomp-v-in-G (suc fuel) G (V k u) X is-top rewrite decomp-recomp-form fuel G (V k u) =
    list-forall-concat {ls = (toList (vec-of-map (λ p → concat (map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))))))} 
    (list-forall-toList λ p → 
    (list-forall-concat {ls = map (recomp-sub u k p) (map (decomp-sub fuel G) (children G (S (V k u) p)))} 
    (list-forall-map {l = map (decomp-sub fuel G) (children G (S (V k u) p))} 
    (list-forall-map {l = children G (S (V k u) p)}  --(children-edges-in-G G (V k u) p , ?) 
    (list-forall-implies (list-forall-× (children-edges-in-G G (V k u) p) (parents-of-children G (V k u) p)) (step2 p))))))
    where
    step2 : (p : Fin (arity k)) → {(u' , v') : Ident × Vertex} → ((edge-in-G , in-parents) : (list-elem (E (S (V k u) p) v' u') G) × (list-elem (V k u) (parents G v'))) → 
              list-elem (E (S (V k u) p) (vertex-of-term (decomp-v' fuel G v')) u') G
              × list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v' fuel G v'))
    step2 p {u' , v'} (edge-in-G , in-parents) rewrite vertex-of-decomp' fuel G v' = edge-in-G , (step3 in-parents)
      where 
      step3 : (list-elem (V k u) (parents G v')) →  list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v' fuel G v'))
      step3 in-parents  with classify fuel G v' [] | inspect (classify fuel G v') [] | classify-correct fuel G v' [] <> | classify-complete fuel G v' [] <>
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ with parents G v' | in-parents | is-top
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ | [] | () | _
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ [] | _ | ()
      step3 in-parents | Top NP | _ | TopCorrect is-top | _ | _ ∷ _ ∷ _ | _ | ()
      step3 in-parents | Top MP | _ | _ | _ = <>
      step3 in-parents | Top U | _ | _ | _ = <>
      step3 in-parents | Inner X' w | [ eq ] | InnerCorrect .w is-inner | Complete top-complete _ = lemma6 fuel G v' (V k u) X (lemma5 G (V k u) v' X in-parents is-top not-mp not-u)
        where 
        not-mp : ¬ (top MP G v')
        not-mp is-top with (top-complete {X = MP} is-top)
        ... | eq2 rewrite eq with eq2 
        ... | ()
        not-u : ¬ (top U G v')
        not-u is-top with (top-complete {X = U} is-top)
        ... | eq2 rewrite eq with eq2 
        ... | ()

decomp-recomp-v-complete : (fuel : ℕ) → (G : Graph) → (v : Vertex) → (X : X) → (ε : Edge) →
  (list-elem ε G) →
  (top X G v) → 
  (edge X G ε v) →
  list-elem ε (recomp-t (decomp-v fuel G v))
decomp-recomp-v-complete fuel G v X (E (S .v _) _ _) elem is-top (TopEdge x) = lemma9 fuel G _ elem
decomp-recomp-v-complete fuel G v X (E (S w p) w' u) elem is-top (InnerEdge x) = lemma8 fuel G _ _ _ x _ (lemma9 fuel G _ elem)

decomp-recomp-sound : (fuel : ℕ) → (G : Graph) → list-forall (λ ε → list-elem ε G) (recomp-grove (decomp-G' fuel G))
decomp-recomp-sound fuel G = list-forall-concat {ls = (map recomp-t (decomp-G' fuel G))} 
                            (list-forall-map {l = (decomp-G' fuel G)}
                            (list-forall-map {l = (filter (some-top-decidable fuel G) (vertices-of-G G))} 
                            (list-forall-filter {l = vertices-of-G G} 
                            (list-forall-map {l = G} 
                            (list-forall-elem reg-forall)))))
  where 
  reg-forall : ((E (S v _) _ _) : Edge) → 
                list-elem _ _ →
                some-top G v → 
                list-forall (λ ε → list-elem ε G) (recomp-t (decomp-v fuel G v))
  reg-forall (E (S v _) _ _ ) _ (X , is-top) = decomp-recomp-v-in-G fuel G v X is-top 
  
decomp-recomp-complete : (fuel : ℕ) → (G : Graph) → list-forall (λ ε → list-elem ε (recomp-grove (decomp-G' fuel G))) G
decomp-recomp-complete fuel G = list-forall-elem elem-forall
  where 
  elem-forall : (ε : Edge) → list-elem ε G → list-elem ε (recomp-grove (decomp-G' fuel G))
  elem-forall ε elem with edge-classify fuel G ε | edge-classify-correct fuel G ε
  ... | EC X w | EdgeCorrect is-edge with lem12 G w X ε is-edge 
  ... | is-top = list-elem-concat {ls = (map recomp-t (decomp-G' fuel G))} 
                (decomp-recomp-v-complete fuel G w X ε elem is-top is-edge) 
                (list-elem-map {a = decomp-v fuel G w} {l = decomp-G' fuel G} {f = recomp-t}  
                (list-elem-map {a = w} {l = filter (some-top-decidable fuel G) (vertices-of-G G)} {f = decomp-v fuel G} 
                (list-elem-filter {l = vertices-of-G G} {dec = some-top-decidable fuel G} (X , is-top) (edge-classify-in-G fuel G w X ε elem is-edge))))  

decomp-recomp : (fuel : ℕ) → (G : Graph) → elem-equiv (recomp-grove (decomp-G' fuel G)) G     
decomp-recomp fuel G ε = (λ elem → list-elem-forall (decomp-recomp-sound fuel G) ε elem) ,    
                         (λ elem → list-elem-forall (decomp-recomp-complete fuel G) ε elem)      