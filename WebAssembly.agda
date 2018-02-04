--------------------------------------------------------------------------------

module WebAssembly where

--------------------------------------------------------------------------------

import Data.Empty   as 𝟘      renaming (⊥      to t)
import Data.Unit    as 𝟙      renaming (⊤      to t)
import Data.Bool    as 𝟚      renaming (Bool   to t)
import Data.Maybe   as Maybe  renaming (Maybe  to t)
import Data.Product as ×      renaming (proj₁ to fst; proj₂ to snd)
import Data.Sum     as +      renaming (inj₁ to injᴸ; inj₂ to injᴿ)
import Data.Nat     as ℕ      renaming (ℕ      to t)
import Data.Integer as ℤ      renaming (ℤ      to t)
import Data.Float   as 𝔽      renaming (Float  to t)
import Data.Fin     as Fin    renaming (Fin    to t)
import Data.Vec     as Vec    renaming (Vec    to t; [] to []ⱽ; _∷_ to _∷ⱽ_)
import Data.List    as List   renaming (List   to t; [] to []ᴸ; _∷_ to _∷ᴸ_)
import Data.String  as String renaming (String to t)
import Level        as 𝕃      renaming (Level  to t)

open ×    using (Σ; ∃; _×_; _,_; fst; snd)
open +    using (_⊎_; injᴸ; injᴿ)
open List using ([]ᴸ; _∷ᴸ_)
open Vec  using ([]ⱽ; _∷ⱽ_)
open 𝕃    using (_⊔_)

module Rel₀ where
  open import Relation.Nullary public

module Rel₂ where
  open import Relation.Binary                       public
  open import Relation.Binary.PropositionalEquality public

open Rel₀ using (¬_)
open Rel₂ using (_≡_; refl; Rel)

--------------------------------------------------------------------------------

{-# FOREIGN GHC import Prelude (undefined, error) #-}
postulate unsafeUndefined : {t : Set} → t
{-# COMPILE GHC unsafeUndefined = undefined #-}
postulate unsafeError : {t : Set} → String.t → t
{-# COMPILE GHC unsafeError = error #-}

--------------------------------------------------------------------------------

module QT where
  data QuantityType : Set where
    bitsTypeᶜ  : QuantityType
    bytesTypeᶜ : QuantityType
    pagesTypeᶜ : QuantityType

  t : Set
  t = QuantityType

  data _<_ : Rel QuantityType 𝕃.zero where
    bits<bytes  : bitsTypeᶜ  < bytesTypeᶜ
    bits<pages  : bitsTypeᶜ  < pagesTypeᶜ
    bytes<pages : bytesTypeᶜ < pagesTypeᶜ

  _≠_ _>_ _≤_ _≥_ : Rel QuantityType 𝕃.zero

  _≠_ lhs rhs = ¬ (lhs ≡ rhs)

  _>_ lhs rhs = rhs < lhs

  _≤_ lhs rhs = let open 𝟚 using (_∨_)
                in (lhs ≡ rhs) ⊎ (lhs < rhs)

  _≥_ lhs rhs = rhs ≤ lhs

  instance
    <-bits-bytes  : bitsTypeᶜ < bytesTypeᶜ
    <-bits-bytes  = bits<bytes
    <-bytes-pages : bytesTypeᶜ < pagesTypeᶜ
    <-bytes-pages = bytes<pages
    <-bits-pages  : bitsTypeᶜ < pagesTypeᶜ
    <-bits-pages  = bits<pages

    ≤-is-reflexive : {t : QuantityType} → t ≤ t
    ≤-is-reflexive {t} = injᴸ refl

    ≡-is-reflexive : {t : QuantityType} → t ≡ t
    ≡-is-reflexive = refl

    ≡-implies-≤ : ∀ {t₁ t₂} → {{_ : t₁ ≡ t₂}} → t₁ ≤ t₂
    ≡-implies-≤ {{p}} = injᴸ p

    <-implies-≤ : ∀ {t₁ t₂} → {{_ : t₁ < t₂}} → t₁ ≤ t₂
    <-implies-≤ {{p}} = injᴿ p

module Quantity where
  data Quantity : QT.t → Set where
    bitsᶜ  : ℕ.t → Quantity QT.bitsTypeᶜ
    bytesᶜ : ℕ.t → Quantity QT.bytesTypeᶜ
    pagesᶜ : ℕ.t → Quantity QT.pagesTypeᶜ

  t : QT.t → Set
  t = Quantity

  typeOf : {t : QT.t} → Quantity t → QT.t
  typeOf {t} quantity = t

  Bits Bytes Pages : Set
  Bits  = Quantity QT.bitsTypeᶜ
  Bytes = Quantity QT.bytesTypeᶜ
  Pages = Quantity QT.pagesTypeᶜ

  zero : {t : QT.t} → Quantity t
  zero {t = QT.bitsTypeᶜ}  = bitsᶜ  ℕ.zero
  zero {t = QT.bytesTypeᶜ} = bytesᶜ ℕ.zero
  zero {t = QT.pagesTypeᶜ} = pagesᶜ ℕ.zero

  suc : {t : QT.t} → Quantity t → Quantity t
  suc (bitsᶜ  n) = bitsᶜ  (ℕ.suc n)
  suc (bytesᶜ n) = bytesᶜ (ℕ.suc n)
  suc (pagesᶜ n) = pagesᶜ (ℕ.suc n)

  _+_ : {t : QT.t} → Quantity t → Quantity t → Quantity t
  _+_ (bitsᶜ  a) (bitsᶜ  b) = bitsᶜ  (ℕ._+_ a b)
  _+_ (bytesᶜ a) (bytesᶜ b) = bytesᶜ (ℕ._+_ a b)
  _+_ (pagesᶜ a) (pagesᶜ b) = pagesᶜ (ℕ._+_ a b)

  scale : {t : QT.t} → ℕ.t → Quantity t → Quantity t
  scale k (bitsᶜ  n) = bitsᶜ  (ℕ._*_ k n)
  scale k (bytesᶜ n) = bytesᶜ (ℕ._*_ k n)
  scale k (pagesᶜ n) = pagesᶜ (ℕ._*_ k n)

  bitsPerByte bytesPerPage bitsPerPage : ℕ.t
  bitsPerByte  = 8
  bytesPerPage = 8
  bitsPerPage  = ℕ._*_ bitsPerByte bytesPerPage

  private
    divMod : (a   : ℕ.t)
           → (b-1 : ℕ.t)
           → ℕ.t × ℕ.t
    divMod a b-1 = (div-helper 0 b-1 a b-1 , mod-helper 0 b-1 a b-1)
      where
        open import Agda.Builtin.Nat using (div-helper; mod-helper)

    -- FIXME: make this not a postulate if possible?
    postulate
      divMod-law : {a : ℕ.t}
                 → {b-1 : ℕ.t}
                 → a ≡ (ℕ._+_ (ℕ._*_ (fst (divMod a b-1)) (ℕ.suc b-1))
                              (snd (divMod a b-1)))
    -- divMod-law {a} {b-1}
    --  = a ≡⟨ unsafeUndefined ⟩
    --    (ℕ._+_ (ℕ._*_ div (ℕ.suc b-1)) mod) ∎
    --  where
    --    div mod : ℕ.t
    --    div = fst (divMod a b-1)
    --    mod = snd (divMod a b-1)
    --    open Rel₂.≡-Reasoning

  downcast_to_ : {t₁ : QT.t}
               → Quantity t₁
               → (t₂ : QT.t)
               → {{_ : QT._≥_ t₁ t₂}}
               → Quantity t₂
  downcast_to_ {t} (bitsᶜ  n) QT.bitsTypeᶜ  {{p}} = bitsᶜ  n
  downcast_to_ {t} (bytesᶜ n) QT.bytesTypeᶜ {{p}} = bytesᶜ n
  downcast_to_ {t} (pagesᶜ n) QT.pagesTypeᶜ {{p}} = pagesᶜ n
  downcast_to_ {t} (bytesᶜ n) QT.bitsTypeᶜ  {{p}} = bitsᶜ  (ℕ._*_ n bitsPerByte)
  downcast_to_ {t} (pagesᶜ n) QT.bytesTypeᶜ {{p}} = bytesᶜ (ℕ._*_ n bytesPerPage)
  downcast_to_ {t} (pagesᶜ n) QT.bitsTypeᶜ  {{p}} = bitsᶜ  (ℕ._*_ n bitsPerPage)
  downcast_to_ {t} (bitsᶜ  n) QT.bytesTypeᶜ {{injᴸ ()}}
  downcast_to_ {t} (bitsᶜ  n) QT.bytesTypeᶜ {{injᴿ ()}}
  downcast_to_ {t} (bitsᶜ  n) QT.pagesTypeᶜ {{injᴸ ()}}
  downcast_to_ {t} (bitsᶜ  n) QT.pagesTypeᶜ {{injᴿ ()}}
  downcast_to_ {t} (bytesᶜ n) QT.pagesTypeᶜ {{injᴸ ()}}
  downcast_to_ {t} (bytesᶜ n) QT.pagesTypeᶜ {{injᴿ ()}}

  cast_to_ : {t₁ : QT.t}
           → Quantity t₁
           → (t₂ : QT.t)
           → (Quantity t₂ × Quantity t₁)
  cast_to_ = go
    where
      open QT using (bitsTypeᶜ; bytesTypeᶜ; pagesTypeᶜ)
      go : {t₁ : QT.t} → Quantity t₁ → (t₂ : QT.t) → (Quantity t₂ × Quantity t₁)
      go (bitsᶜ  n) bitsTypeᶜ  = ((downcast (bitsᶜ  n) to  bitsTypeᶜ) , zero)
      go (bytesᶜ n) bytesTypeᶜ = ((downcast (bytesᶜ n) to bytesTypeᶜ) , zero)
      go (pagesᶜ n) pagesTypeᶜ = ((downcast (pagesᶜ n) to pagesTypeᶜ) , zero)
      go (bytesᶜ n) bitsTypeᶜ  = ((downcast (bytesᶜ n) to  bitsTypeᶜ) , zero)
      go (pagesᶜ n) bytesTypeᶜ = ((downcast (pagesᶜ n) to bytesTypeᶜ) , zero)
      go (pagesᶜ n) bitsTypeᶜ  = ((downcast (pagesᶜ n) to  bitsTypeᶜ) , zero)
      go (bitsᶜ  n) bytesTypeᶜ = let (d , m) = divMod n bitsPerByte
                                 in (bytesᶜ d , bitsᶜ m)
      go (bitsᶜ  n) pagesTypeᶜ = let (d , m) = divMod n bitsPerPage
                                 in (pagesᶜ d , bitsᶜ m)
      go (bytesᶜ n) pagesTypeᶜ = let (d , m) = divMod n bytesPerPage
                                 in (pagesᶜ d , bytesᶜ m)

  cast-law : {t₁ t₂ : QT.t}
           → {{_ : QT._≤_ t₁ t₂}}
           → {q₁ : Quantity t₁}
           → {casted : Quantity t₂ × Quantity t₁}
           → {_ : casted ≡ (cast q₁ to t₂)}
           → q₁ ≡ ((downcast (fst casted) to t₁) + snd casted)
  cast-law = unsafeUndefined -- FIXME

--------------------------------------------------------------------------------

data Size : Set where
  S32ᶜ : Size
  S64ᶜ : Size

data Kind : Set where
  integerᶜ  : Kind
  floatingᶜ : Kind

record ValType : Set where
  constructor ValTypeᶜ
  field
    kind : Kind
    size : Size

pattern I32 = ValTypeᶜ integerᶜ  S32ᶜ
pattern I64 = ValTypeᶜ integerᶜ  S64ᶜ
pattern F32 = ValTypeᶜ floatingᶜ S32ᶜ
pattern F64 = ValTypeᶜ floatingᶜ S64ᶜ

--------------------------------------------------------------------------------

data FuncType : Set where
  _:→_ : List.t ValType
       → List.t ValType
       → FuncType
  -- FIXME: define constructor(s)

--------------------------------------------------------------------------------

data TableType : Set where
  -- FIXME: define constructor(s)

--------------------------------------------------------------------------------

record Limits : Set where
  constructor Limitsᶜ
  field
    min : ℕ.t
    max : Maybe.t ℕ.t

data MemType : Set where
  MemTypeᶜ : Limits → MemType

--------------------------------------------------------------------------------

data Mut : Set where
  constᶜ : Mut
  varᶜ   : Mut

record GlobalType : Set where
  constructor GlobalTypeᶜ
  field
    mutability : Mut
    type       : ValType

--------------------------------------------------------------------------------

data ResultType : Set where
  ResultTypeᶜ : List.t ValType → ResultType

--------------------------------------------------------------------------------

data Val : ValType → Set where
  ValI32 : ℤ.t → Val I32
  ValI64 : ℤ.t → Val I64
  ValF32 : 𝔽.t → Val F32
  ValF64 : 𝔽.t → Val F64

module HVec where
  -- Given a type family `family` indexed on a type `kind` and a list `L` of
  -- elements of `kind`, this is a type of lists containing inhabitants of
  -- `kind` such that mapping `family` over the value level list will give `L`.
  data t {ℓ} {kind : Set ℓ} (family : kind → Set ℓ)
       : {n : ℕ.t} → (L : Vec.t kind n) → Set ℓ where
    []ᴴ  : t family []ⱽ
    _∷ᴴ_ : {n : ℕ.t}
         → {type : kind}
         → {types : Vec.t kind n}
         → (elem : family type)
         → (rest : t family types)
         → t family (type ∷ⱽ types)

open HVec using ([]ᴴ; _∷ᴴ_)

typeOf : ∃ (λ t → Val t) → ValType
typeOf (t , _) = t

data Result (t : ResultType) : Set where
  ResultOkᶜ   : HVec.t
                {∃ (λ t → Val t)}
                typeOf _
              → Result t
  -- ResultOkᶜ   : List.t (∃ (λ vt → Val vt)) → Result t
  ResultTrapᶜ : Result t

--------------------------------------------------------------------------------

record Context : Set where
  field
    types   : List.t  FuncType
    funcs   : List.t  FuncType
    tables  : List.t  TableType
    mems    : List.t  MemType
    globals : List.t  GlobalType
    locals  : List.t  ValType
    labels  : List.t  ResultType
    return  : Maybe.t ResultType

--------------------------------------------------------------------------------

data Instruction : Set where


--------------------------------------------------------------------------------
