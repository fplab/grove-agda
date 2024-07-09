open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grove.Prelude

-- types
module Grove.Marking.Typ where
  data Typ : Set where
    num     : Typ
    unknown : Typ
    _-→_    : Typ → Typ → Typ

  infixr 25  _-→_

  -- arrow type equality
  -→-≡ : ∀ {τ₁ τ₂ τ₁' τ₂'} → (τ₁ ≡ τ₁') → (τ₂ ≡ τ₂') → τ₁ -→ τ₂ ≡ τ₁' -→ τ₂'
  -→-≡ refl refl = refl

  -- inverted arrow type equality
  -→-inj : ∀ {τ₁ τ₂ τ₁' τ₂'} → (τ₁ -→ τ₂ ≡ τ₁' -→ τ₂') → (τ₁ ≡ τ₁') × (τ₂ ≡ τ₂')
  -→-inj refl = refl , refl

  -- arrow type inequalities
  -→-≢₁ : ∀ {τ₁ τ₂ τ₁' τ₂'} → (τ₁ ≢ τ₁') → τ₁ -→ τ₂ ≢ τ₁' -→ τ₂'
  -→-≢₁ τ₁≢τ₁' refl = τ₁≢τ₁' refl

  -→-≢₂ : ∀ {τ₁ τ₂ τ₁' τ₂'} → (τ₂ ≢ τ₂') → τ₁ -→ τ₂ ≢ τ₁' -→ τ₂'
  -→-≢₂ τ₂≢τ₂' refl = τ₂≢τ₂' refl

  -- decidable equality
  _≡τ?_ : (τ : Typ) → (τ' : Typ) → Dec (τ ≡ τ')
  num        ≡τ? num      = yes refl
  num        ≡τ? unknown  = no (λ ())
  num        ≡τ? (_ -→ _) = no (λ ())
  unknown    ≡τ? num      = no (λ ())
  unknown    ≡τ? unknown  = yes refl
  unknown    ≡τ? (_ -→ _) = no (λ ())
  (_ -→ _)   ≡τ? num      = no (λ ())
  (_ -→ _)   ≡τ? unknown  = no (λ ())
  (τ₁ -→ τ₂) ≡τ? (τ₁' -→ τ₂') with τ₁ ≡τ? τ₁' | τ₂ ≡τ? τ₂'
  ...                           | yes refl    | yes refl  = yes refl
  ...                           | _           | no τ₂≢τ₂' = no  (-→-≢₂ τ₂≢τ₂')
  ...                           | no τ₁≢τ₁'   | _         = no  (-→-≢₁ τ₁≢τ₁')

  module base where
    -- base types
    data _base : (τ : Typ) → Set where
      TBNum  : num base

    -- decidable base
    _base? : (τ : Typ) → Dec (τ base)
    num      base? = yes TBNum
    unknown  base? = no (λ ())
    (_ -→ _) base? = no (λ ())

    -- base judgment equality
    base-≡ : ∀ {τ} → (b₁ : τ base) → (b₂ : τ base) → b₁ ≡ b₂
    base-≡ TBNum TBNum = refl

  module consistency where
    open base

    -- consistency
    data _~_ : (τ₁ τ₂ : Typ) → Set where
      TCUnknown     : unknown ~ unknown
      TCBase        : {τ : Typ} → (b : τ base) → τ ~ τ
      TCUnknownBase : {τ : Typ} → (b : τ base) → unknown ~ τ
      TCBaseUnknown : {τ : Typ} → (b : τ base) → τ ~ unknown
      TCArr         : {τ₁ τ₂ τ₁' τ₂' : Typ}
                    → (τ₁~τ₁' : τ₁ ~ τ₁')
                    → (τ₂~τ₂' : τ₂ ~ τ₂')
                    → τ₁ -→ τ₂ ~ τ₁' -→ τ₂'
      TCUnknownArr  : {τ₁ τ₂ : Typ}
                    → unknown ~ τ₁ -→ τ₂
      TCArrUnknown  : {τ₁ τ₂ : Typ}
                    → τ₁ -→ τ₂ ~ unknown

    -- inconsistency
    _~̸_ : (τ₁ : Typ) → (τ₂ : Typ) → Set
    τ₁ ~̸ τ₂ = ¬ (τ₁ ~ τ₂)

    -- consistency reflexivity
    ~-refl : ∀ {τ} → τ ~ τ
    ~-refl {num}      = TCBase TBNum
    ~-refl {unknown}  = TCUnknown
    ~-refl {τ₁ -→ τ₂} = TCArr ~-refl ~-refl

    -- consistency symmetry
    ~-sym : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ~ τ₁
    ~-sym TCUnknown              = TCUnknown
    ~-sym (TCBase b)             = TCBase b
    ~-sym (TCUnknownBase b)      = TCBaseUnknown b
    ~-sym (TCBaseUnknown b)      = TCUnknownBase b
    ~-sym TCUnknownArr           = TCArrUnknown
    ~-sym TCArrUnknown           = TCUnknownArr
    ~-sym (TCArr τ₁~τ₁' τ₂~τ₂')  = TCArr (~-sym τ₁~τ₁') (~-sym τ₂~τ₂')

    -- consistency with unknown type
    ~-unknown₁ : ∀ {τ} → unknown ~ τ
    ~-unknown₁ {num}     = TCUnknownBase TBNum
    ~-unknown₁ {unknown} = TCUnknown
    ~-unknown₁ {_ -→ _}  = TCUnknownArr

    ~-unknown₂ : ∀ {τ} → τ ~ unknown
    ~-unknown₂ {num}     = TCBaseUnknown TBNum
    ~-unknown₂ {unknown} = TCUnknown
    ~-unknown₂ {_ -→ _}  = TCArrUnknown

    -- consistency derivation equality
    ~-≡ : ∀ {τ₁ τ₂} → (τ₁~τ₂ : τ₁ ~ τ₂) → (τ₁~τ₂' : τ₁ ~ τ₂) → τ₁~τ₂ ≡ τ₁~τ₂'
    ~-≡ TCUnknown             TCUnknown               = refl
    ~-≡ (TCBase b)            (TCBase b')
      rewrite base-≡ b b'                             = refl
    ~-≡ (TCUnknownBase b)     (TCUnknownBase b')
      rewrite base-≡ b b'                             = refl
    ~-≡ (TCBaseUnknown b)     (TCBaseUnknown b')
      rewrite base-≡ b b'                             = refl
    ~-≡ (TCArr τ₁~τ₁' τ₂~τ₂') (TCArr τ₁~τ₁'' τ₂~τ₂'')
      rewrite ~-≡ τ₁~τ₁' τ₁~τ₁'' | ~-≡ τ₂~τ₂' τ₂~τ₂'' = refl
    ~-≡ TCUnknownArr          TCUnknownArr            = refl
    ~-≡ TCArrUnknown          TCArrUnknown            = refl

    -- inconsistency derivation equality
    ~̸-≡ : ∀ {τ₁ τ₂} → (τ₁~̸τ₂ : τ₁ ~̸ τ₂) → (τ₁~̸τ₂' : τ₁ ~̸ τ₂) → τ₁~̸τ₂ ≡ τ₁~̸τ₂'
    ~̸-≡ τ₁~̸τ₂ τ₁~̸τ₂' rewrite ¬-≡ τ₁~̸τ₂ τ₁~̸τ₂' = refl

    -- arrow type inconsistencies
    -→-~̸₁ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ~̸ τ₁' → τ₁ -→ τ₂ ~̸ τ₁' -→ τ₂'
    -→-~̸₁ τ₁~̸τ₁' = λ { (TCBase ()) ; (TCArr τ₁~τ₁' _) → τ₁~̸τ₁' τ₁~τ₁' }

    -→-~̸₂ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₂ ~̸ τ₂' → τ₁ -→ τ₂ ~̸ τ₁' -→ τ₂'
    -→-~̸₂ τ₂~̸τ₂' = λ { (TCBase ()) ; (TCArr _ τ₂~τ₂') → τ₂~̸τ₂' τ₂~τ₂' }

    -- decidable consistency
    _~?_ : (τ : Typ) → (τ' : Typ) → Dec (τ ~ τ')
    unknown    ~? num      = yes (TCUnknownBase TBNum)
    unknown    ~? unknown  = yes TCUnknown
    unknown    ~? (_ -→ _) = yes TCUnknownArr
    num        ~? num      = yes (TCBase TBNum)
    num        ~? unknown  = yes (TCBaseUnknown TBNum)
    num        ~? (_ -→ _) = no  (λ ())
    (_ -→ _)   ~? num      = no  (λ ())
    (_ -→ _)   ~? unknown  = yes TCArrUnknown
    (τ₁ -→ τ₂) ~? (τ₁' -→ τ₂') with τ₁ ~? τ₁'  | τ₂ ~? τ₂'
    ...                           | yes τ₁~τ₁' | yes τ₂~τ₂' = yes (TCArr τ₁~τ₁' τ₂~τ₂')
    ...                           | _          | no ¬τ₂~τ₂' = no λ { (TCBase ()) ; (TCArr _ τ₂~τ₂') → ¬τ₂~τ₂' τ₂~τ₂' }
    ...                           | no ¬τ₁~τ₁' | _          = no λ { (TCBase ()) ; (TCArr τ₁~τ₁' _) → ¬τ₁~τ₁' τ₁~τ₁' }

  module matched where
    open consistency

    -- matched arrow
    data _▸_-→_ : (τ τ₁ τ₂ : Typ) → Set where
      TMAUnknown : unknown ▸ unknown -→ unknown
      TMAArr     : {τ₁ τ₂ : Typ} → τ₁ -→ τ₂ ▸ τ₁ -→ τ₂

    -- no matched
    _!▸-→ : Typ → Set
    τ !▸-→ = ¬ (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)

    -- decidable matched arrow
    _▸-→? : (τ : Typ) → Dec (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)
    num        ▸-→? = no (λ ())
    unknown    ▸-→? = yes (unknown , unknown , TMAUnknown)
    (τ₁ -→ τ₂) ▸-→? = yes (τ₁      , τ₂      , TMAArr)

    -- matched arrow derivation equality
    ▸-→-≡ : ∀ {τ τ₁ τ₂} → (τ▸ : τ ▸ τ₁ -→ τ₂) → (τ▸' : τ ▸ τ₁ -→ τ₂) → τ▸ ≡ τ▸'
    ▸-→-≡ TMAUnknown TMAUnknown = refl
    ▸-→-≡ TMAArr     TMAArr     = refl

    -- matched arrow unicity
    ▸-→-unicity : ∀ {τ τ₁ τ₂ τ₃ τ₄} → (τ ▸ τ₁ -→ τ₂) → (τ ▸ τ₃ -→ τ₄) → τ₁ -→ τ₂ ≡ τ₃ -→ τ₄
    ▸-→-unicity TMAUnknown TMAUnknown = refl
    ▸-→-unicity TMAArr     TMAArr     = refl

    -- no matched arrow derivation equality
    !▸-→-≡ : ∀ {τ} → (τ!▸ : τ !▸-→) → (τ!▸' : τ !▸-→) → τ!▸ ≡ τ!▸'
    !▸-→-≡ τ!▸ τ!▸' = ¬-≡ τ!▸ τ!▸'

    -- only consistent types arrow match
    ▸-→→~ : ∀ {τ τ₁ τ₂} → τ ▸ τ₁ -→ τ₂ → τ ~ τ₁ -→ τ₂
    ▸-→→~ TMAUnknown = TCUnknownArr
    ▸-→→~ TMAArr     = ~-refl

    ▸-→-~̸₁ : ∀ {τ τ₁ τ₂ τ₁'} → τ ▸ τ₁ -→ τ₂ → τ₁' ~̸ τ₁ → τ ~̸ τ₁' -→ τ₂
    ▸-→-~̸₁ TMAArr     τ₁'~̸τ₁ (TCArr τ₁~τ₁' _) = τ₁'~̸τ₁ (~-sym τ₁~τ₁')
    ▸-→-~̸₁ TMAUnknown τ₁'~̸τ₁ TCUnknownArr     = τ₁'~̸τ₁ ~-unknown₂

    ▸-→-~̸₂ : ∀ {τ τ₁ τ₂ τ₂'} → τ ▸ τ₁ -→ τ₂ → τ₂' ~̸ τ₂ → τ ~̸ τ₁ -→ τ₂'
    ▸-→-~̸₂ TMAUnknown τ₂'~̸τ₂ TCUnknownArr     = τ₂'~̸τ₂ ~-unknown₂
    ▸-→-~̸₂ TMAArr     τ₂'~̸τ₂ (TCArr _ τ₂~τ₂') = τ₂'~̸τ₂ (~-sym τ₂~τ₂')

    -- consistency with an arrow type implies existence of a matched arrow type
    ~→▸-→ : ∀ {τ τ₁ τ₂} → τ ~ τ₁ -→ τ₂ → ∃[ τ₁' ] ∃[ τ₂' ] τ ▸ τ₁' -→ τ₂'
    ~→▸-→ (TCArr {τ₁ = τ₁} {τ₂ = τ₂} τ₁~ τ₂~) = τ₁      , τ₂      , TMAArr
    ~→▸-→ TCUnknownArr                        = unknown , unknown , TMAUnknown

    ~-▸-→→~ : ∀ {τ τ₁ τ₂ τ₁' τ₂'} → τ ~ τ₁ -→ τ₂ → τ ▸ τ₁' -→ τ₂' → τ₁ -→ τ₂ ~ τ₁' -→ τ₂'
    ~-▸-→→~ (TCArr τ₁~ τ₂~) TMAArr     = TCArr (~-sym τ₁~) (~-sym τ₂~)
    ~-▸-→→~ TCUnknownArr    TMAUnknown = TCArr ~-unknown₂ ~-unknown₂

  module meet where
    open base
    open consistency

    -- greatest lower bound (where the unknown type is the top of the imprecision partial order)
    data _⊓_⇒_ : (τ₁ τ₂ τ : Typ) → Set where
      TJBase        : {τ : Typ} → (b : τ base) → τ ⊓ τ ⇒ τ
      TJUnknown     : unknown ⊓ unknown ⇒ unknown
      TJUnknownBase : {τ : Typ} → (b : τ base) → unknown ⊓ τ ⇒ τ
      TJBaseUnknown : {τ : Typ} → (b : τ base) → τ ⊓ unknown ⇒ τ
      TJArr         : {τ₁ τ₂ τ₁' τ₂' τ₁″ τ₂″ : Typ}
                     → (τ₁⊓τ₁' : τ₁ ⊓ τ₁' ⇒ τ₁″)
                     → (τ₂⊓τ₂' : τ₂ ⊓ τ₂' ⇒ τ₂″)
                     → τ₁ -→ τ₂ ⊓ τ₁' -→ τ₂' ⇒ τ₁″ -→ τ₂″
      TJUnknownArr  : {τ₁ τ₂ : Typ}
                     → unknown ⊓ τ₁ -→ τ₂ ⇒ τ₁ -→ τ₂
      TJArrUnknown  : {τ₁ τ₂ : Typ}
                     → τ₁ -→ τ₂ ⊓ unknown ⇒ τ₁ -→ τ₂

    -- decidable meet
    _⊓?_ : (τ₁ : Typ) → (τ₂ : Typ) → Dec (∃[ τ ] τ₁ ⊓ τ₂ ⇒ τ)
    num        ⊓? num          = yes (num , TJBase TBNum)
    num        ⊓? unknown      = yes (num , TJBaseUnknown TBNum)
    num        ⊓? (_ -→ _)     = no λ()
    unknown    ⊓? num          = yes (num      , TJUnknownBase TBNum)
    unknown    ⊓? unknown      = yes (unknown  , TJUnknown)
    unknown    ⊓? (τ₁ -→ τ₂)   = yes (τ₁ -→ τ₂ , TJUnknownArr)
    (τ₁ -→ τ₂) ⊓? num          = no λ()
    (τ₁ -→ τ₂) ⊓? unknown      = yes (τ₁ -→ τ₂ , TJArrUnknown)
    (τ₁ -→ τ₂) ⊓? (τ₁' -→ τ₂')
      with τ₁ ⊓? τ₁'          | τ₂ ⊓? τ₂'
    ...  | yes (τ , τ₁⊓τ₁') | yes (τ' , τ₂⊓τ₂'') = yes (τ -→ τ' , TJArr τ₁⊓τ₁' τ₂⊓τ₂'')
    ...  | _                | no ¬τ₂⊓τ₂'         = no λ { (.(_ -→ _) , TJArr {τ₂″ = τ₂″} τ₁⊓τ₁'″ τ₂⊓τ₂'″) → ¬τ₂⊓τ₂' (τ₂″ , τ₂⊓τ₂'″) }
    ...  | no (¬τ₁⊓τ₁')     | _                  = no λ { (.(_ -→ _) , TJArr {τ₁″ = τ₁″} τ₁⊓τ₁'″ τ₂⊓τ₂'″) → ¬τ₁⊓τ₁' (τ₁″ , τ₁⊓τ₁'″) }

    -- meet of same type
    ⊓-refl : ∀ {τ} → τ ⊓ τ ⇒ τ
    ⊓-refl {num}     = TJBase TBNum
    ⊓-refl {unknown} = TJUnknown
    ⊓-refl {τ₁ -→ τ₂}
      with τ₁⊓τ₁ ← ⊓-refl {τ₁}
         | τ₂⊓τ₂ ← ⊓-refl {τ₂}
         = TJArr τ₁⊓τ₁ τ₂⊓τ₂

    -- meet is symmetric
    ⊓-sym : ∀ {τ₁ τ₂ τ} → τ₁ ⊓ τ₂ ⇒ τ → τ₂ ⊓ τ₁ ⇒ τ
    ⊓-sym (TJBase b)           = TJBase b
    ⊓-sym TJUnknown            = TJUnknown
    ⊓-sym (TJUnknownBase b)    = TJBaseUnknown b
    ⊓-sym (TJBaseUnknown b)    = TJUnknownBase b
    ⊓-sym TJUnknownArr         = TJArrUnknown
    ⊓-sym TJArrUnknown         = TJUnknownArr
    ⊓-sym (TJArr ⊓⇒τ₁″ ⊓⇒τ₂″)  = TJArr (⊓-sym ⊓⇒τ₁″) (⊓-sym ⊓⇒τ₂″)

    -- meet with unknown
    ⊓-unknown₁ : ∀ {τ} → unknown ⊓ τ ⇒ τ
    ⊓-unknown₁ {num}     = TJUnknownBase TBNum
    ⊓-unknown₁ {unknown} = TJUnknown
    ⊓-unknown₁ {_ -→ _}  = TJUnknownArr

    ⊓-unknown₂ : ∀ {τ} → τ ⊓ unknown ⇒ τ
    ⊓-unknown₂ {num}     = TJBaseUnknown TBNum
    ⊓-unknown₂ {unknown} = TJUnknown
    ⊓-unknown₂ {_ -→ _}  = TJArrUnknown

    -- meet unicity
    ⊓-unicity : ∀ {τ₁ τ₂ τ τ'} → τ₁ ⊓ τ₂ ⇒ τ → τ₁ ⊓ τ₂ ⇒ τ' → τ ≡ τ' 
    ⊓-unicity (TJBase _)            (TJBase _)                = refl
    ⊓-unicity TJUnknown             TJUnknown                 = refl
    ⊓-unicity (TJUnknownBase _)     (TJUnknownBase _)         = refl
    ⊓-unicity (TJBaseUnknown _)     (TJBaseUnknown _)         = refl
    ⊓-unicity TJUnknownArr          TJUnknownArr              = refl
    ⊓-unicity TJArrUnknown          TJArrUnknown              = refl
    ⊓-unicity (TJArr _ _)           (TJBase ())
    ⊓-unicity (TJArr τ₁⊓τ₁' τ₂⊓τ₂') (TJArr τ₁⊓τ₁'' τ₂⊓τ₂'')   = -→-≡ (⊓-unicity τ₁⊓τ₁' τ₁⊓τ₁'') (⊓-unicity τ₂⊓τ₂' τ₂⊓τ₂'')

    -- meet derivation equality
    ⊓-≡ : ∀ {τ₁ τ₂ τ} → (τ₁⊓τ₂ : τ₁ ⊓ τ₂ ⇒ τ) → (τ₁⊓τ₂' : τ₁ ⊓ τ₂ ⇒ τ) → τ₁⊓τ₂ ≡ τ₁⊓τ₂'
    ⊓-≡ (TJBase b) (TJBase b') 
      rewrite base-≡ b b'           = refl
    ⊓-≡ TJUnknown TJUnknown         = refl
    ⊓-≡ (TJUnknownBase b) (TJUnknownBase b')
      rewrite base-≡ b b'           = refl
    ⊓-≡ (TJBaseUnknown b) (TJBaseUnknown b')
      rewrite base-≡ b b'           = refl
    ⊓-≡ (TJArr τ₁⊓τ₁' τ₂⊓τ₂') (TJArr τ₁⊓τ₁'' τ₂⊓τ₂'')
      rewrite ⊓-≡ τ₁⊓τ₁' τ₁⊓τ₁''
            | ⊓-≡ τ₂⊓τ₂' τ₂⊓τ₂''    = refl
    ⊓-≡ TJUnknownArr TJUnknownArr   = refl
    ⊓-≡ TJArrUnknown TJArrUnknown   = refl

    -- meet existence means that types are consistent
    ⊓→~ : ∀ {τ τ₁ τ₂} → τ₁ ⊓ τ₂ ⇒ τ → τ₁ ~ τ₂
    ⊓→~ (TJBase b)             = TCBase b
    ⊓→~ TJUnknown              = TCUnknown
    ⊓→~ (TJUnknownBase b)      = TCUnknownBase b
    ⊓→~ (TJBaseUnknown b)      = TCBaseUnknown b
    ⊓→~ TJUnknownArr           = TCUnknownArr
    ⊓→~ TJArrUnknown           = TCArrUnknown
    ⊓→~ (TJArr τ₁⊓τ₁' τ₂⊓τ₂')  = TCArr (⊓→~ τ₁⊓τ₁') (⊓→~ τ₂⊓τ₂')

    -- consistent types have a meet
    ~→⊓ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ∃[ τ ] τ₁ ⊓ τ₂ ⇒ τ
    ~→⊓           TCUnknown         = unknown , TJUnknown
    ~→⊓ {τ₁ = τ } (TCBase b)        = τ       , TJBase b
    ~→⊓ {τ₂ = τ₂} (TCUnknownBase b) = τ₂      , TJUnknownBase b
    ~→⊓ {τ₁ = τ₁} (TCBaseUnknown b) = τ₁      , TJBaseUnknown b
    ~→⊓ {τ₂ = τ₂} TCUnknownArr      = τ₂      , TJUnknownArr
    ~→⊓ {τ₁ = τ₁} TCArrUnknown      = τ₁      , TJArrUnknown
    ~→⊓     (TCArr τ₁~τ₁' τ₂~τ₂')
      with τ₁″ , ⊓⇒τ₁″ ← ~→⊓ τ₁~τ₁'
         | τ₂″ , ⊓⇒τ₂″ ← ~→⊓ τ₂~τ₂'
         = τ₁″ -→ τ₂″ , TJArr ⊓⇒τ₁″ ⊓⇒τ₂″

    -- meet nonexistence means types are inconsistent
    ¬⊓→~̸ : ∀ {τ₁ τ₂} → ¬ (∃[ τ ] τ₁ ⊓ τ₂ ⇒ τ) → τ₁ ~̸ τ₂
    ¬⊓→~̸ ¬τ₁⊓τ₂ = λ { τ₁~τ₂ → ¬τ₁⊓τ₂ (~→⊓ τ₁~τ₂) }

    -- inconsistent types have no meet
    ~̸→¬⊓ : ∀ {τ₁ τ₂} → τ₁ ~̸ τ₂ → ¬ (∃[ τ ] τ₁ ⊓ τ₂ ⇒ τ)
    ~̸→¬⊓ τ₁~̸τ₂ = λ { (τ , τ₁⊓τ₂) → τ₁~̸τ₂ (⊓→~ τ₁⊓τ₂) }

    -- types are consistent with their meet
    ⊓⇒→~ : ∀ {τ₁ τ₂ τ} → τ₁ ⊓ τ₂ ⇒ τ → τ₁ ~ τ × τ₂ ~ τ
    ⊓⇒→~ (TJBase b) = TCBase b , TCBase b
    ⊓⇒→~ TJUnknown = TCUnknown , TCUnknown
    ⊓⇒→~ (TJUnknownBase b) = TCUnknownBase b , TCBase b
    ⊓⇒→~ (TJBaseUnknown b) = TCBase b , TCUnknownBase b
    ⊓⇒→~ (TJArr τ₁⊓τ₁' τ₂⊓τ₂')
      with τ₁~ , τ₁'~ ← ⊓⇒→~ τ₁⊓τ₁'
         | τ₂~ , τ₂'~ ← ⊓⇒→~ τ₂⊓τ₂'
         = TCArr τ₁~ τ₂~ , TCArr τ₁'~ τ₂'~
    ⊓⇒→~ TJUnknownArr = TCUnknownArr , TCArr ~-refl ~-refl
    ⊓⇒→~ TJArrUnknown = TCArr ~-refl ~-refl , TCUnknownArr

    -- types are consistent with types consistent to their meet
    ⊓⇒-~→~ : ∀ {τ₁ τ₂ τ τ'} → τ₁ ⊓ τ₂ ⇒ τ → τ ~ τ' → τ₁ ~ τ' × τ₂ ~ τ'
    ⊓⇒-~→~ (TJBase b)        τ~τ' = τ~τ' , τ~τ'
    ⊓⇒-~→~ TJUnknown         τ~τ' = τ~τ' , τ~τ'
    ⊓⇒-~→~ (TJUnknownBase b) τ~τ' = ~-unknown₁ , τ~τ'
    ⊓⇒-~→~ (TJBaseUnknown b) τ~τ' = τ~τ' , ~-unknown₁
    ⊓⇒-~→~ {τ = .(_ -→ _)} {unknown} (TJArr τ₁⊓τ₁' τ₂⊓τ₂') τ~τ'
         = TCArrUnknown , TCArrUnknown
    ⊓⇒-~→~ {τ = .(_ -→ _)} {τ₁″ -→ τ₂″} (TJArr τ₁⊓τ₁' τ₂⊓τ₂') (TCArr τ₁″~τ₁‴ τ₂″~τ₂‴)
      with τ₁~τ₁″ , τ₁'~τ₁″ ← ⊓⇒-~→~ τ₁⊓τ₁' τ₁″~τ₁‴
      with τ₂~τ₂″ , τ₂'~τ₂″ ← ⊓⇒-~→~ τ₂⊓τ₂' τ₂″~τ₂‴
         = TCArr τ₁~τ₁″ τ₂~τ₂″ , TCArr τ₁'~τ₁″ τ₂'~τ₂″
    ⊓⇒-~→~ {τ = .(_ -→ _)} TJUnknownArr τ~τ'
         = ~-unknown₁ , τ~τ'
    ⊓⇒-~→~ {τ = .(_ -→ _)} TJArrUnknown τ~τ'
         = τ~τ' , ~-unknown₁

  open base public
  open consistency public
  open matched public
  open meet public
