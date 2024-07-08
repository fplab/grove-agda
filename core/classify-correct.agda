-- {-# OPTIONS --allow-unsolved-metas #-}

module core.classify-correct where

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
open import core.partition-graph

lem11 : (G : Graph) → (X Y : X) → (w : Vertex) → 
  (top X G w) → 
  (top Y G w) → 
  (X ≡ Y)
lem11 G NP NP w top1 top2 = refl
lem11 G NP MP w top1 top2 with classify-parents G w | top1 | top2
lem11 G NP MP w top1 top2 | _ | refl | ()
lem11 G NP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) with classify-parents G w | top1 | cp zero
lem11 G NP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) | _ | refl | ()
lem11 G MP NP w top1 top2 with classify-parents G w | top1 | top2
lem11 G MP NP w top1 top2 | _ | refl | ()
lem11 G MP MP w top1 top2 = refl
lem11 G MP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) with classify-parents G w | top1 | cp zero
lem11 G MP U w top1 (_ , .w ∷ _ , (refl , _ , cp) , _) | _ | refl | ()
lem11 G U NP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 with classify-parents G w | cp zero | top2
lem11 G U NP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 | _ | refl | ()
lem11 G U MP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 with classify-parents G w | cp zero | top2
lem11 G U MP w (_ , .w ∷ _ , (refl , _ , cp) , _) top2 | _ | refl | ()
lem11 G U U w top1 top2 = refl

lem10 : (G : Graph) → (X Y : X) → (x w1 w2 : Vertex) → 
  is-only-ancestor G x w1 → 
  is-only-ancestor G x w2 → 
  (top X G w1) → 
  (top Y G w2) → 
  (X ≡ Y) × (w1 ≡ w2)
lem10 G X Y x w1 w2 oa1 oa2 top1 top2 with lem1 G x w1 w2 oa1 oa2
lem10 G X Y x w1 w1 oa1 oa2 top1 top2 | Inl refl = lem11 G X Y w1 top1 top2 , refl

lem10 G NP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) with classify-parents G w1 | top1 | cp zero
lem10 G NP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem10 G MP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) with classify-parents G w1 | top1 | cp zero
lem10 G MP Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl (_ , .w1 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem10 G U Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) with lem8 G w2 w1 top1 oa3
lem10 G U Y x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inl refl = lem11 G U Y w1 top1 top2 , refl 
lem10 G U NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w2 | cp zero | top2
lem10 G U NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem10 G U MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w2 | cp zero | top2
lem10 G U MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , (_ , .w2 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem10 G U U x w1 w2 oa1 oa2 top1 top2 | Inr (Inl oa3) | Inr (not-top , _ , _) = ⊥-elim (not-top top2)

lem10 G X NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) with classify-parents G w2 | top2 | cp zero
lem10 G X NP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem10 G X MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) with classify-parents G w2 | top2 | cp zero
lem10 G X MP x w1 w2 oa1 oa2 top1 top2 | Inr (Inr (_ , .w2 ∷ ws , (refl , _ , cp))) | _ | refl | ()
lem10 G X U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) with lem8 G w1 w2 top2 oa3
lem10 G X U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inl refl = lem11 G X U w2 top1 top2 , refl 
lem10 G NP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w1 | cp zero | top1
lem10 G NP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem10 G MP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) with classify-parents G w1 | cp zero | top1
lem10 G MP U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , (_ , .w1 ∷ _ , (refl , _ , cp)) , _) | _ | refl | ()
lem10 G U U x w1 w2 oa1 oa2 top1 top2 | Inr (Inr oa3) | Inr (not-top , _ , _) = ⊥-elim (not-top top1)

data class-correct : (G : Graph) → (v : Vertex) → (class G v) → Set where 
  TopCorrect : ∀{X G v} → (top X G v) → class-correct G v (Top X) 
  InnerCorrect : ∀{X G v} → (w : Vertex) → (inner X G v w) → class-correct G v (Inner X w)

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

  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {X} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner X? w? | [ eq5 ] | InnerCorrect w? (_ , oa , is-top2) | Complete top-complete inner-complete with lem10 G X X? x w w? (n , x ∷ ws1  , (refl , eq2 , λ i → cp (suc i))) oa is-top is-top2 
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner .NP w? | [ eq5 ] | InnerCorrect w? (_ , oa , is-top2) | Complete top-complete inner-complete | refl , refl = refl , {!   !}
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner .MP w? | [ eq5 ] | InnerCorrect w? (_ , oa , is-top2) | Complete top-complete inner-complete | refl , refl = refl , {!   !}
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner .U w? | [ eq5 ] | InnerCorrect w? (_ , oa , is-top2) | Complete top-complete inner-complete | refl , refl with Dec.does (v ≟Vertex w?)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | TopCorrect is-top2 | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner .U w? | [ eq5 ] | InnerCorrect w? (not-top2 , oa , is-top3) | Complete top-complete inner-complete | refl , refl | true = ⊥-elim (not-top is-top2)
  class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner .U w? | [ eq5 ] | InnerCorrect w? (_ , oa , is-top2) | Complete top-complete inner-complete | refl , refl | false = refl , {! X?  !}

  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner NP w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner MP w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {NP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner U w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner NP w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner MP w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {MP} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner U w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner NP w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner MP w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
  -- class-complete.InnerComplete (classify-complete (suc fuel) G v ws oas) {U} w (not-top , (suc n , .v ∷ x ∷ ws1  , (refl , eq2 , cp)) , is-top) | correct | _ | refl | PC-UP .x | [ eq3 ] | eq4 | refl | false | no neq | Inner U w? | [ eq5 ] | InnerCorrect w? is-inner | Complete top-complete inner-complete = {!   !} , {!   !}
     