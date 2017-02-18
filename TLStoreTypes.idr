module TLStoreTypes

import TLMagic
import Data.SortedMap
import Data.Vect

%access public export
data TLSNatExpr = TLNatExprConst Nat | TLNatExprVar String
data TLSFlags = TLFlagsNone | TLFlagsFunction
data TLSMultiplicity = TLSMultiplicityExpr TLSNatExpr | TLSMultiplicityInfer
data TLSection = TLSectionTypes | TLSectionFuncs
data TLCondition = TLConditionVar String | TLConditionVarBit String Nat

mutual
  data TLSExpr = TLExpNat TLSNatExpr | TLExpType TLSTypeExpr

  record TLSArg where
    constructor MkTLSArg
    id : Maybe String
    condition: Maybe TLCondition
    type : TLSTypeExpr

  data TLSTypeExpr : Type where
    TLSTypeExprArray : (multiplicity : TLSMultiplicity) ->
                  (args : List TLSArg) -> TLSTypeExpr
    TLSTypeExprVar : (id : String) -> TLSTypeExpr
    TLSTypeExprExpr : (id : String) -> (children : List TLSExpr) -> TLSTypeExpr
    TLSTypeExprBoxed : (type : TLSTypeExpr) -> TLSTypeExpr
    TLSTypeExprUnboxed : (type : TLSTypeExpr) -> TLSTypeExpr

record TLSCombinator where
  constructor MkTLCombinator
  identifier : String
  magic : Integer
  optArgs : List TLSArg
  args : List TLSArg

data TLSFinal : Type where

record TLSType where
  constructor MkTLSType
  id : String
  type : TLSTypeExpr
  constructors : SortedMap String TLSCombinator

record TLStore where
  constructor MkTLStore
  types : SortedMap String TLSType
  functionConstructors : SortedMap String TLSCombinator
  finals : SortedMap String TLSFinal

Eq TLSNatExpr where
    (==) (TLNatExprConst k) (TLNatExprConst j) = k == j
    (==) (TLNatExprVar x) (TLNatExprVar y) = x == y
    (==) _ _ = False

Eq TLSMultiplicity where
    (==) (TLSMultiplicityExpr x) (TLSMultiplicityExpr y) = x == y
    (==) TLSMultiplicityInfer TLSMultiplicityInfer = True
    (==) _ _ = False -- TODO: actually we can have infer == explicit but fix later

Eq TLCondition where
    (==) (TLConditionVar x) (TLConditionVar y) = x == y
    (==) (TLConditionVarBit x k) (TLConditionVarBit y j) = x == y && k == j
    (==) _ _ = False

mutual
  Eq TLSArg where
      (==) (MkTLSArg id condition type) (MkTLSArg x y z) = id == x && condition == y && (assert_total $ type == z)

  Eq TLSExpr where
      (==) (TLExpNat x) (TLExpNat y) = x == y
      (==) (TLExpType x) (TLExpType y) = assert_total $ x == y
      (==) _ _ = False

  Eq TLSTypeExpr where
      (==) (TLSTypeExprArray multiplicity args) (TLSTypeExprArray x xs) = multiplicity == x && args == xs
      (==) (TLSTypeExprVar id) (TLSTypeExprVar x) = id == x
      (==) (TLSTypeExprBoxed x) (TLSTypeExprBoxed y) = x == y
      (==) (TLSTypeExprUnboxed x) (TLSTypeExprUnboxed y) = x == y
      (==) (TLSTypeExprExpr id children) (TLSTypeExprExpr x xs) = id == x && children == xs
      (==) _ _ = False
