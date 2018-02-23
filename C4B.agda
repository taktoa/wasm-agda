--------------------------------------------------------------------------------

module C4B where

--------------------------------------------------------------------------------

import Data.Bool     as 𝟚      renaming (Bool   to t)
import Data.Empty    as 𝟘      renaming (⊥      to t)
import Data.Unit     as 𝟙      renaming (⊤      to t)
import Data.Bool     as 𝟚      renaming (Bool   to t)
import Data.Maybe    as Maybe  renaming (Maybe  to t)
import Data.Product  as ×      renaming (proj₁ to fst; proj₂ to snd)
import Data.Sum      as +      renaming (inj₁ to injᴸ; inj₂ to injᴿ)
import Data.Nat      as ℕ      renaming (ℕ      to t)
import Data.Integer  as ℤ      renaming (ℤ      to t)
import Data.Rational as ℚ      renaming (ℚ      to t)
import Data.Float    as 𝔽      renaming (Float  to t)
import Data.Fin      as Fin    renaming (Fin    to t)
import Data.Vec      as Vec    renaming (Vec    to t; [] to []ⱽ; _∷_ to _∷ⱽ_)
import Data.String   as String renaming (String to t)
import Level         as 𝕃      renaming (Level  to t)
import Function

module List where
  open import Data.List
       renaming (List   to t;
                 [] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_)
       public

  lookup : ∀ {a} {A : Set a} (xs : t A) → Fin.t (length xs) → A
  lookup []ᴸ       ()
  lookup (x ∷ᴸ xs) Fin.zero    = x
  lookup (x ∷ᴸ xs) (Fin.suc i) = lookup xs i


module Rel₀ where
  open import Relation.Nullary public

module Rel₂ where
  open import Relation.Binary                       public
  open import Relation.Binary.PropositionalEquality public

open 𝟚        using (if_then_else_)
open ×        using (∃; _×_; _,_; fst; snd)
open +        using (_⊎_; injᴸ; injᴿ)
open List     using ([]ᴸ; _∷ᴸ_; _++ᴸ_)
open Vec      using ([]ⱽ; _∷ⱽ_)
open 𝕃        using (_⊔_)
open Function using (case_return_of_; case_of_)
open Rel₀     using (¬_)
open Rel₂     using (_≡_; _≢_; refl; Rel)

--------------------------------------------------------------------------------

{-# FOREIGN GHC import Prelude (undefined, error) #-}
postulate unsafeUndefined : {t : Set} → t
{-# COMPILE GHC unsafeUndefined = undefined #-}
postulate unsafeError : {t : Set} → String.t → t
{-# COMPILE GHC unsafeError = error #-}

--------------------------------------------------------------------------------

congFin : ∀ {X : Set} {a b : ℕ.t}
        → a ≡ b
        → (Fin.t a → X)
        → Fin.t b
        → X
congFin p f n rewrite Rel₂.cong Fin.t p = f n

--------------------------------------------------------------------------------

module OperationalSemantics
       (V : Set)
       (E : Set)
       (_is_ : V → V → 𝟚.t)
       (ret  : V)
       where

  data FunCall : Set where
    _⟪_⟫ : V → List.t V → FunCall

  data Syntax : Set where
    assertˢ             : E → Syntax
    skipˢ               : Syntax
    breakˢ              : Syntax
    returnˢ             : V → Syntax
    _←ˢ_                : V → E → Syntax
    _≔ˢ_                : V → FunCall → Syntax
    loopˢ               : Syntax → Syntax
    ifˢ_thenˢ_elseˢ_fiˢ : E → Syntax → Syntax → Syntax
    _∷ˢ_                : Syntax → Syntax → Syntax
    tickˢ               : ℚ.t → Syntax

  infix 15 _≔ˢ_
  infix 16 _⟪_⟫

  data Continuation : Set where
    stopᴷ : Continuation
    seqᴷ  : Syntax → Continuation → Continuation
    loopᴷ : Syntax → Continuation → Continuation
    callᴷ : (r : V)
          → (θ : V → Maybe.t ℤ.t)
          → Continuation
          → Continuation

  Value : Set
  Value = ℤ.t

  record ProgramState : Set where
    constructor ⟨_#_⟩
    field
      localsᶠ  : (V → Maybe.t Value)
      globalsᶠ : (V → Maybe.t Value)

    lookup : ProgramState → V → Maybe.t Value
    lookup ps n with localsᶠ n     | globalsᶠ n
    ...            | Maybe.just v  | _             = Maybe.just v
    ...            | Maybe.nothing | Maybe.just v  = Maybe.just v
    ...            | Maybe.nothing | Maybe.nothing = Maybe.nothing

  record Eval : Set where
    constructor eval⟨_!_!_!_⟩
    field
     σ : ProgramState
     S : Syntax
     K : Continuation
     c : ℚ.t

  update_with:_↦_ : ProgramState → V → Value → ProgramState
  update σ with: x ↦ v = _

  is-true : ℤ.t → Set
  is-true n = n ≢ (ℤ.+_ 0)

  is-false : ℤ.t → Set
  is-false n = n ≡ (ℤ.+_ 0)

  negateℤ : ℤ.t → ℤ.t
  negateℤ = ℤ.-_

  negateℚ : ℚ.t → ℚ.t
  negateℚ n = record { numerator     = negateℤ (ℚ.t.numerator n)
                     ; denominator-1 = ℚ.t.denominator-1 n
                     ; isCoprime     = unsafeUndefined
                     }

  addℚ : ℚ.t → ℚ.t → ℚ.t
  addℚ a b = let ℕ→ℤ = ℤ.+_
                 denominatorA = ℕ.suc (ℚ.t.denominator-1 a)
                 denominatorB = ℕ.suc (ℚ.t.denominator-1 b)
             in ℚ._÷_ (ℤ._+_ (ℤ._*_ (ℚ.t.numerator a) (ℕ→ℤ denominatorB))
                             (ℤ._*_ (ℚ.t.numerator b) (ℕ→ℤ denominatorA)))
                      (ℕ._*_ denominatorA denominatorB)
                      {unsafeUndefined}
                      {unsafeUndefined}

  minusℚ : ℚ.t → ℚ.t → ℚ.t
  minusℚ a b = addℚ a (negateℚ b)

  _∈ⱽ_ : V
       → (xs : List.t V)
       → Maybe.t (Fin.t (List.length xs))
  _∈ⱽ_ = λ n xs → helper n (List.zip (List.allFin (List.length xs)) xs)
    where
      helper : {n : ℕ.t}
             → V
             → List.t (Fin.t n × V)
             → Maybe.t (Fin.t n)
      helper _ []ᴸ             = Maybe.nothing
      helper n ((k , v) ∷ᴸ xs) = if (n is v)
                                 then Maybe.just k
                                 else helper n xs


  data _↝_ {Σ : V → Maybe.t (List.t V × Syntax)}
           {⟦_⟧ : E → ProgramState → Value}
       : Eval → Eval → Set where
    S:Assert   : ∀ {σ} {e} {K} {c}
               → {_ : is-true (⟦ e ⟧ σ)}
               → eval⟨ σ ! assertˢ e ! K ! c ⟩
               ↝ eval⟨ σ ! skipˢ ! K ! c ⟩
    S:BrkSeq   : ∀ {σ} {S} {K} {c}
               → eval⟨ σ ! breakˢ ! seqᴷ S K ! c ⟩
               ↝ eval⟨ σ ! breakˢ ! K        ! c ⟩
    S:BrkLoop  : ∀ {σ} {S} {K} {c}
               → eval⟨ σ ! breakˢ ! loopᴷ S K ! c ⟩
               ↝ eval⟨ σ ! skipˢ  ! K         ! c ⟩
    S:RetSeq   : ∀ {σ} {x} {S} {K} {c}
               → eval⟨ σ ! returnˢ x ! seqᴷ S K ! c ⟩
               ↝ eval⟨ σ ! returnˢ x ! K        ! c ⟩
    S:RetLoop  : ∀ {σ} {x} {S} {K} {c}
               → eval⟨ σ ! returnˢ x ! loopᴷ S K ! c ⟩
               ↝ eval⟨ σ ! returnˢ x ! K         ! c ⟩
    S:RetCall  : ∀ {θ₁} {θ₂} {γ} {x} {v} {r} {K} {c}
               → {_ : Maybe.just v ≡ θ₁ x}
               → let σ₁ = ⟨ θ₁ # γ ⟩
                     σ₂ = update ⟨ θ₂ # γ ⟩ with: r ↦ v
                 in ( eval⟨ σ₁ ! returnˢ x ! callᴷ r θ₂ K ! c ⟩
                    ↝ eval⟨ σ₂ ! skipˢ     ! K            ! c ⟩ )
    S:Update   : ∀ {σ} {x} {e} {v} {K} {c}
               → {_ : v ≡ ⟦ e ⟧ σ }
               → eval⟨ σ                      ! x ←ˢ e ! K ! c ⟩
               ↝ eval⟨ (update σ with: x ↦ v) ! skipˢ  ! K ! c ⟩
    S:Call     : ∀ {θ₁} {γ} {r} {as} {f} {ps} {body} {K} {c}
               → {_ : Maybe.just (ps , body) ≡ Σ f}
               → {p : (List.length as) ≡ (List.length ps)}
               → let θ₂ n = case (n ∈ⱽ ps) of
                              λ { (Maybe.just k) → θ₁ (congFin p
                                                       (List.lookup as) k)
                                ; Maybe.nothing  → θ₁ n
                                }
                 in ( eval⟨ ⟨ θ₁ # γ ⟩ ! (r ≔ˢ f ⟪ as ⟫) ! K            ! c ⟩
                    ↝ eval⟨ ⟨ θ₂ # γ ⟩ ! body            ! callᴷ r θ₁ K ! c ⟩ )
    S:Loop     : ∀ {σ} {S} {K} {c}
               → eval⟨ σ ! loopˢ S ! K         ! c ⟩
               ↝ eval⟨ σ ! S       ! loopᴷ S K ! c ⟩
    S:SkipLoop : ∀ {σ} {S} {K} {c}
               → eval⟨ σ ! skipˢ   ! loopᴷ S K ! c ⟩
               ↝ eval⟨ σ ! loopˢ S ! K         ! c ⟩
    S:IfTrue   : ∀ {σ} {e} {S₁} {S₂} {K} {c}
               → {_ : is-true (⟦ e ⟧ σ)}
               → eval⟨ σ ! ifˢ e thenˢ S₁ elseˢ S₂ fiˢ ! K ! c ⟩
               ↝ eval⟨ σ ! S₁                          ! K ! c ⟩
    S:IfFalse  : ∀ {σ} {e} {S₁} {S₂} {K} {c}
               → {_ : is-false (⟦ e ⟧ σ)}
               → eval⟨ σ ! ifˢ e thenˢ S₁ elseˢ S₂ fiˢ ! K ! c ⟩
               ↝ eval⟨ σ ! S₂                          ! K ! c ⟩
    S:Seq      : ∀ {σ} {S₁} {S₂} {K} {c}
               → eval⟨ σ ! S₁ ∷ˢ S₂ ! K         ! c ⟩
               ↝ eval⟨ σ ! S₁       ! seqᴷ S₂ K ! c ⟩
    S:SkipSeq  : ∀ {σ} {S} {K} {c}
               → eval⟨ σ ! skipˢ ! seqᴷ S K ! c ⟩
               ↝ eval⟨ σ ! S     ! K        ! c ⟩
    S:Tick     : ∀ {σ} {n} {K} {c}
               → eval⟨ σ ! tickˢ n ! K ! c          ⟩
               ↝ eval⟨ σ ! skipˢ   ! K ! minusℚ c n ⟩

  data PValue : Set where
    varᴾ  : V → PValue
    exprᴾ : E → PValue

  data Predicate : Set where
   trueᴾ    : Predicate
   falseᴾ   : Predicate
   ¬ᴾ_      : Predicate → Predicate
   _∧ᴾ_     : Predicate → Predicate → Predicate
   _∨ᴾ_     : Predicate → Predicate → Predicate
   _⇒ᴾ_     : Predicate → Predicate → Predicate
   _<ᴾ_     : PValue → PValue → Predicate
   _=ᴾ_     : PValue → PValue → Predicate
   is-trueᴾ : PValue → Predicate

  is-falseᴾ : PValue → Predicate
  is-falseᴾ v = ¬ᴾ (is-trueᴾ v)

  _>ᴾ_ : PValue → PValue → Predicate
  a >ᴾ b = b <ᴾ a

  _≤ᴾ_ : PValue → PValue → Predicate
  a ≤ᴾ b = (a <ᴾ b) ∨ᴾ (a =ᴾ b)

  _≥ᴾ_ : PValue → PValue → Predicate
  a ≥ᴾ b = (a >ᴾ b) ∨ᴾ (a =ᴾ b)

  substᴾ_↦_within_ : V → PValue → Predicate → Predicate
  substᴾ_↦_within_ = {!!}

  QType : Set
  QType = List.t ℚ.t

  QContext : Set
  QContext = Predicate × QType

  data QState : Set where
    ⟨_,_⟩ : (B : QContext)
          → (R : QContext)
          → QState

  quantAdd : QType → ℚ.t → QType
  quantAdd []ᴸ       _ = []ᴸ
  quantAdd (x ∷ᴸ xs) n = addℚ x n ∷ᴸ xs

  quantSub : QType → ℚ.t → QType
  quantSub xs n = quantAdd xs (negateℚ n)

  quantFirst : (ℚ.t → Set) → QType → Set
  quantFirst f []ᴸ       = 𝟙.t
  quantFirst f (x ∷ᴸ xs) = f x

  _≤ℚ_ : ℚ.t → ℚ.t → Set
  _≤ℚ_ = ℚ._≤_

  _<ℚ_ : ℚ.t → ℚ.t → Set
  a <ℚ b = (a ≢ b) × (a ≤ℚ b)

  0ℚ : ℚ.t
  0ℚ = record { numerator     = ℤ.+_ 0
              ; denominator-1 = 0
              ; isCoprime     = unsafeUndefined
              }

  data QHoare : Set where
    [⦃_⦄⟨_⟩⦃_⦄] : QContext → Syntax → QContext → QHoare

  data _⊢_ : QState → QHoare → Set where
    Q:Skip   : ∀ {B R} {Γ} {Q}
             → ⟨ B , R ⟩
             ⊢ [⦃ Γ , Q ⦄⟨ skipˢ ⟩⦃ Γ , Q ⦄]
    Q:Break  : ∀ {R} {Γᴮ} {Qᴮ} {Γ'} {Q'}
             → ⟨ (Γᴮ , Qᴮ) , R ⟩
             ⊢ [⦃ Γᴮ , Qᴮ ⦄⟨ breakˢ ⟩⦃ Γ' , Q' ⦄]
    Q:Tick   : ∀ {B R} {Γ} {Q} {n}
             → ((n <ℚ 0ℚ) → quantFirst (λ q₀ → 0ℚ ≤ℚ q₀) Q)
             → ⟨ B , R ⟩
             ⊢ [⦃ Γ , Q ⦄⟨ tickˢ n ⟩⦃ Γ , quantSub Q n ⦄]
    Q:Return : ∀ {B} {Γᴿ} {Qᴿ} {Γ Γ'} {Q Q'} {x}
             → Γ ≡ substᴾ ret ↦ (varᴾ x) within Γᴿ
             -- → Q ≡ subst ret for x within Qᴿ
             --   -- perhaps these should be collected constraints
             → ⟨ B , (Γᴿ , Qᴿ) ⟩
             ⊢ [⦃ Γ , Q ⦄⟨ returnˢ x ⟩⦃ Γ' , Q' ⦄]
    -- Q:Update : _
    -- Q:Loop   : _
    -- Q:Inc    : _
    -- Q:Dec    : _
    Q:If     : ∀ {B R} {e} {S₁ S₂} {Γ Γ'} {Q Q'}
             → ⟨ B , R ⟩
             ⊢ [⦃ (Γ ∧ᴾ (is-trueᴾ  (exprᴾ e))) , Q ⦄⟨ S₁ ⟩⦃ Γ' , Q' ⦄]
             → ⟨ B , R ⟩
             ⊢ [⦃ (Γ ∧ᴾ (is-falseᴾ (exprᴾ e))) , Q ⦄⟨ S₂ ⟩⦃ Γ' , Q' ⦄]
             → ⟨ B , R ⟩
             ⊢ [⦃ Γ , Q ⦄⟨ ifˢ e thenˢ S₁ elseˢ S₂ fiˢ ⟩⦃ Γ' , Q' ⦄]
    Q:Seq    : ∀ {B R} {X Y Z} {S₁ S₂}
             → ⟨ B , R ⟩ ⊢ [⦃ X ⦄⟨ S₁ ⟩⦃ Y ⦄]
             → ⟨ B , R ⟩ ⊢ [⦃ Y ⦄⟨ S₂ ⟩⦃ Z ⦄]
             → ⟨ B , R ⟩ ⊢ [⦃ X ⦄⟨ S₁ ∷ˢ S₂ ⟩⦃ Z ⦄]
    -- Q:Call   : _
    Q:Assert : ∀ {B R} {Γ} {Q} {e}
             → let Γ' = Γ ∧ᴾ (is-trueᴾ (exprᴾ e))
               in ⟨ B , R ⟩ ⊢ [⦃ Γ , Q ⦄⟨ assertˢ e ⟩⦃ Γ' , Q ⦄]
    -- Q:Extend : _
    -- Q:Weak   : _
    -- Q:Relax  : _
    -- foo : ⟨ (_ , _) , (_ , _) ⟩ ⊢ [⦃ _ , _ ⦄⟨ _ ⟩⦃ _ , _ ⦄]

--------------------------------------------------------------------------------
