module WebAssembly where

import Data.Bool   as 𝟚     renaming (Bool to t)
import Data.Vec    as Vec   renaming (Vec to t)
import Data.Maybe  as Maybe renaming (Maybe to t)

open import Data.Product

data FuncType : Set where
  -- FIXME: define constructor(s)

data TableType : Set where
  -- FIXME: define constructor(s)

data MemType : Set where
  -- FIXME: define constructor(s)

data GlobalType : Set where
  -- FIXME: define constructor(s)

data ValType : Set where
  -- FIXME: define constructor(s)

data ResultType : Set where
  -- FIXME: define constructor(s)

record Context : Set where
  field
    types   : ∃ (λ n → Vec.t FuncType   n)
    funcs   : ∃ (λ n → Vec.t FuncType   n)
    tables  : ∃ (λ n → Vec.t TableType  n)
    mems    : ∃ (λ n → Vec.t MemType    n)
    globals : ∃ (λ n → Vec.t GlobalType n)
    locals  : ∃ (λ n → Vec.t ValType    n)
    labels  : ∃ (λ n → Vec.t ResultType n)
    return  : Maybe.t ResultType
