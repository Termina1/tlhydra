module TLStoreTypes

import TLMagic
import Data.SortedMap
import Data.Vect

%access public export
data TLSNatExpr = TLNatExprConst Nat | TLNatExprVar String
data TLSFlags = TLFlagsNone | TLFlagsFunction
data TLSMultiplicity = TLSMultiplicityExpr TLSNatExpr | TLSMultiplicityInfer

mutual
  data TLSExpr = TLExpNat TLSNatExpr | TLExpType TLSType

  record TLSArg where
    constructor MkTLSArg
    id : Maybe String
    type : TLSType

  data TLSType : Type where
    TLSTypeArray : (multiplicity : TLSMultiplicity) ->
                  (args : List TLSArg) -> TLSType
    TLSTypeVar : (id : String) -> (flags : TLSFlags) -> TLSType
    TLSTypeExpr : (id : String) -> (flags : TLSFlags) ->
                 (children : List TLSExpr) -> TLSType

record TLSCombinator where
  constructor MkTLCombinator
  identifier : String
  magic : Integer
  optArgs : List TLSArg
  args : List TLSArg
  resultType : TLSType

data TLSFinal : Type where

record TLStore where
  constructor MkTLStore
  magicMapping : SortedMap Integer String
  types : SortedMap String TLSCombinator
  functions : SortedMap String TLSCombinator
  finals : SortedMap String TLSFinal
