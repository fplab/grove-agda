{-# OPTIONS --allow-unsolved-metas #-}

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

open import core.ident
open import core.finite
open import core.list-logic

module core.classify-correct 
  (Ctor : Set) 
  (_≟ℂ_ : (c₁ c₂ : Ctor) → Dec (c₁ ≡ c₂))
  (arity : Ctor → ℕ)
  where

import core.graph
open module graph = core.graph Ctor _≟ℂ_ arity
import core.classify
open module classify = core.classify Ctor _≟ℂ_ arity
import core.classify-lemmas
open module classify-lemmas = core.classify-lemmas Ctor _≟ℂ_ arity

data class-correct : (G : Graph) → (v : Vertex) → (class G v) → Set where 
  TopCorrect : ∀{X G v} → (top X G v) → class-correct G v (Top X) 
  InnerCorrect : ∀{X G v} → (w : Vertex) → (inner X G v w) → class-correct G v (Inner X w)

record class-complete (fuel : ℕ) (G : Graph) (v : Vertex) (ws : List(Vertex × VertexId)) : Set where 
  constructor Complete
  field 
    TopComplete : ∀{X} → (top X G v) → (classify fuel G v ws ≡ Top X)
    InnerComplete : ∀{X} → (w : Vertex) → (inner X G v w) → (classify fuel G v ws ≡ Inner X w)

mutual 
  classify-correct : (fuel : ℕ) → (G : Graph) → (has-uniq-ids G) → (v : Vertex) → (ws : List(Vertex × VertexId)) → (only-descendants G v ws) → class-correct G v (classify fuel G v ws)
  classify-correct zero G uniq-ids v ws oas = {!   !}
  classify-correct (suc fuel) G uniq-ids v ws oas with classify-parents G v | inspect (classify-parents G) v
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-NP | [ eq ] rewrite eq = TopCorrect eq
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-MP | [ eq ] rewrite eq = TopCorrect eq
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] rewrite eq with locate-U G v ws | inspect (locate-U G v) ws
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | true | [ eq2 ] rewrite eq2 = TopCorrect (locate-U-correct G v ws oas eq2)
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] rewrite eq2 with Dec.does (v ≟Vertex x) | Dec.proof (v ≟Vertex x)
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | true | ofʸ refl = TopCorrect (parent-implies-oami G v v eq)
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq with if-top | classify fuel G x (update-ws v ws x) | inspect (classify fuel G x) (update-ws v ws x) | classify-correct fuel G uniq-ids x (update-ws v ws x) (update-ws-correct G v ws x oas eq)
    where 
    if-top : (top U G v) → (classify fuel G x (update-ws v ws x) ≡ Inner U v)
    if-top is-top with lem9 G uniq-ids x v is-top eq 
    if-top is-top | Inl eq2 = ⊥-elim (neq (sym eq2))
    if-top is-top | Inr eq4 with classify-complete fuel G uniq-ids x (update-ws v ws x) (update-ws-correct G v ws x oas eq)
    if-top is-top | Inr eq4 | (Complete _ inner-complete) = inner-complete _ eq4
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Top X | [ eq3 ] | TopCorrect is-top = InnerCorrect x (not-top , parent-implies-oa G v x eq , is-top) 
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | ()
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner NP w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top)= InnerCorrect w ( not-top , oa-extend-left G _ _ _ eq oa , is-top)
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | ()
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner MP w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top)= InnerCorrect w ( not-top , oa-extend-left G _ _ _ eq oa , is-top)
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | ()
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner U w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top) with Dec.does (v ≟Vertex w) | Dec.proof (v ≟Vertex w) 
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner U w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top) | true | ofʸ refl = TopCorrect is-top 
  classify-correct (suc fuel) G uniq-ids v ws oas | PC-UP x | [ eq ] | false | [ eq2 ] | false | ofⁿ neq | if-top | Inner U w | [ eq3 ] | InnerCorrect _ (not-utop , oa , is-top) | false | ofⁿ neq' = InnerCorrect w ( not-top , oa-extend-left G _ _ _ eq oa , is-top)
    where 
    not-top : ¬(top U G v)
    not-top is-top' rewrite eq3 with if-top is-top' 
    ... | refl = neq' refl

  classify-complete : (fuel : ℕ) → (G : Graph) → (has-uniq-ids G) → (v : Vertex) → (ws : List(Vertex × VertexId)) → (only-descendants G v ws) → class-complete fuel G v ws
  classify-complete zero G v ws oas = {!   !}
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {NP} is-top with classify-parents G v
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {NP} refl | .PC-NP = refl
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {MP} is-top with classify-parents G v
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {MP} refl | .PC-MP = refl
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp), min) with lookup ws1 zero | eq1 | classify-parents G v | inspect (classify-parents G) v | (cp zero) 
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-NP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-NP | [ eq3 ] | eq4 | ()
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-MP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-MP | [ eq3 ] | eq4 | ()
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-UP x | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-UP .(_) |  _ | eq4 | refl with locate-U G v ws
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-UP .(_) | [ eq3 ] | eq4 | refl | true = refl 
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} (n , ws1 , _ , min) | _ | refl | PC-UP .(_) | [ eq3 ] | eq4 | refl | false with (v ≟Vertex (lookup ws1 (suc zero)))
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} _ | _ | refl | PC-UP .(_) | [ eq3 ] | eq4 | refl | false | yes eq5 = refl 
  class-complete.TopComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {U} (n , ws1 , (eq1 , eq2 , cp) , min) | _ | refl | PC-UP .(_) | [ eq3 ] | eq4 | refl | false | no neq with classify-parent
    where 
    classify-parent : classify fuel G (lookup ws1 (suc zero)) (update-ws v ws (lookup ws1 (suc zero))) ≡ Inner U v
    classify-parent with lem9 G uniq-ids _ v (n , ws1 , (eq1 , eq2 , cp) , min) eq3 
    classify-parent | Inl eq = ⊥-elim (neq (sym eq))
    classify-parent | Inr is-inner with classify-complete fuel G uniq-ids (lookup ws1 (suc zero)) (update-ws v ws (lookup ws1 (suc zero))) (update-ws-correct G v ws (lookup ws1 (suc zero)) oas eq3)
    ... | Complete TopComplete InnerComplete = InnerComplete v is-inner
  class-complete.TopComplete (classify-complete _ G uniq-ids v ws oas) {U} (n , ws1 , _ , min) | _ | refl | PC-UP .(_) | [ eq3 ] | eq4 | refl | false | no neq | eq5 rewrite eq5 with (v ≟Vertex v) 
  class-complete.TopComplete (classify-complete _ G uniq-ids v ws oas) {U} (n , ws1 , _ , min) | _ | refl | PC-UP .(_) | [ eq3 ] | eq4 | refl | false | no neq | eq5 | yes refl = refl
  class-complete.TopComplete (classify-complete _ G uniq-ids v ws oas) {U} (n , ws1 , _ , min) | _ | refl | PC-UP .(_) | [ eq3 ] | eq4 | refl | false | no neq | eq5 | no neq2 = ⊥-elim (neq2 refl)
  class-complete.InnerComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {X} w (not-top , (n , ws1 , (eq1 , eq2 , cp)) , is-top) with classify-correct (suc fuel) G uniq-ids v ws oas | lookup ws1 zero | eq1 | classify-parents G v | inspect (classify-parents G) v | (cp zero) 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w _ | correct | _ | refl | PC-NP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w _ | correct | _ | refl | PC-NP | _ | eq4 | ()
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w _ | correct | _ | refl | PC-MP | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w _ | correct | _ | refl | PC-MP | _ | eq4 | ()
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w _ | correct | _ | refl | PC-UP x | [ eq3 ] | eq4 rewrite eq3 with eq4 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w _ | correct | _ | refl | PC-UP .(_) | _ | eq4 | refl with locate-U G v ws
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , _ , is-top) | TopCorrect is-top2 | _ | refl | PC-UP .(_) | _ | eq4 | refl | true = ⊥-elim (not-top is-top2)
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (n , ws1 , _) , is-top) | _ | _ | refl | PC-UP .(_) | _ | eq4 | refl | false with (v ≟Vertex (lookup ws1 (suc zero)))
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (n , ws1 , _) , is-top) | TopCorrect is-top2 | _ | refl | PC-UP .(_) | _ | eq4 | refl | false | yes eq5 = ⊥-elim (not-top is-top2)
  class-complete.InnerComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {X} w (not-top , (zero , .v ∷ .w ∷ [] , (refl , refl , cp)) , is-top) | _ | _ | refl | PC-UP w | [ eq3 ] | eq4 | refl | false | no neq with classify-complete fuel G uniq-ids w (update-ws v ws w) (update-ws-correct G v ws w oas eq3)
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (zero , .v ∷ .w ∷ [] , (refl , refl , cp)) , is-top) | _ | _ | refl | PC-UP w | _ | eq4 | refl | false | no neq | Complete top-complete inner-complete rewrite (top-complete is-top) = refl
  class-complete.InnerComplete (classify-complete (suc fuel) G uniq-ids v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq with classify fuel G x (update-ws v ws x) | classify-correct fuel G uniq-ids x (update-ws v ws x) (update-ws-correct G v ws x oas eq3) 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top NP | TopCorrect is-top2 with classify-parents G x | is-top2 | cp (suc zero)
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top NP | _ | PC-NP | refl | () 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top MP | TopCorrect is-top2 with classify-parents G x | is-top2 | cp (suc zero)
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top MP | _ | PC-MP | refl | () 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | TopCorrect is-top2 with lem8 G uniq-ids w x is-top2 (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i)))
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inl eq6 rewrite eq6 with classify-parents G x | is-top | cp (suc zero) 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inl eq6 | .PC-NP | refl | () 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) with classify-parents G w | is-top | cp2 zero 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) | .PC-NP | refl | ()
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | TopCorrect is-top2 with lem8 G uniq-ids w x is-top2 (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i)))
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inl eq6 rewrite eq6 with classify-parents G x | is-top | cp (suc zero) 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inl eq6 | .PC-MP | refl | () 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) with classify-parents G w | is-top | cp2 zero 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | _ | Inr (a , (c , .w ∷ ws2 , (refl , f , cp2)) , b) | .PC-MP | refl | ()
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Top U | TopCorrect is-top2 rewrite lem6 G uniq-ids x w is-top2 is-top (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i))) = refl 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Inner X? w? | InnerCorrect w? (_ , oa , is-top2) with lem11 G uniq-ids X X? x w w? (n , x ∷ ws1 , (refl , eq2 , λ i → cp (suc i))) oa is-top is-top2 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Inner .NP w? | _ | refl , refl = refl 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Inner .MP w? | _ | refl , refl = refl 
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Inner .U w? | InnerCorrect w? (_ , oa , is-top2) | refl , refl with Dec.does (v ≟Vertex w?)
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | TopCorrect is-top2 | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Inner .U w? | InnerCorrect w? (not-top2 , oa , is-top3) | refl , refl | true = ⊥-elim (not-top is-top2)
  class-complete.InnerComplete (classify-complete _ G uniq-ids v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1 , (refl , eq2 , cp)) , is-top) | _ | _ | refl | PC-UP .x | _ | eq4 | refl | false | no neq | Inner .U w? | InnerCorrect w? (_ , oa , is-top2) | refl , refl | false = refl

  data edge-correct (G : Graph) (ε : Edge) : (edge-class G ε) → Set where 
    EdgeCorrect : ∀{X w} → (edge X G ε w) → edge-correct G ε (EC X w) 

  edge-classify-correct : (fuel : ℕ) → (G : Graph) → (has-uniq-ids G) → (ε : Edge) → edge-correct G ε (edge-classify fuel G ε)
  edge-classify-correct fuel G uniq-ids (E (S v _) _ _) with classify fuel G v [] | classify-correct fuel G uniq-ids v [] <>
  ... | Top X | TopCorrect is-top = EdgeCorrect (TopEdge is-top)
  ... | Inner X w | InnerCorrect .w is-inner = EdgeCorrect (InnerEdge is-inner)