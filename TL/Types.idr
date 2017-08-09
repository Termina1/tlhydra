module TL.Types

%access public export

data TLBuiltIn = TLInt | TLNat | TLLong | TLString | TLDouble | TLTType

TypeRef : Type
TypeRef = Either TLBuiltIn Int

VarRef : Type
VarRef = Int

Conditional : Type
Conditional = (Int, Int)

data TLSection = Types | Functions

mutual
  data TLSArg : Type where
    MkTLSArg : (id : String) -> (var_num : VarRef) -> (type : TLSTypeExpr) -> TLSArg
    MkTLSArgCond : (id : String) -> (var_num : VarRef) ->
                   (cond : Conditional) -> (type : TLSTypeExpr) -> TLSArg

  data TLSNat : Type where
    MkTLSNat : (nat : Nat) -> TLSNat
    MkTLSNatVar : (ref : VarRef) -> TLSNat

  data TLSExpr : Type where
    MkTLSExprType : (type : TLSTypeExpr) -> TLSExpr
    MKTLSExprNat : (natExpr : TLSNat) -> TLSExpr

  data TLSTypeExpr : Type where
    MkTLSTypeExpr : (type : TypeRef) -> (children : List TLSExpr) -> TLSTypeExpr
    MkTLSTypeArray : (mult : TLSNat) -> (args : List TLSArg) -> TLSTypeExpr
    MkTLSTypeVar : (ref : VarRef) -> TLSTypeExpr
    MkTLSTypeBare : (expr : TLSTypeExpr) -> TLSTypeExpr
    MkTLSTypeBang : (expr : TLSTypeExpr) -> TLSTypeExpr

record TLSCombinator where
  constructor MkTLSCombinator
  identifier : String
  magic : Int
  args : List TLSArg
  resultType : TLSTypeExpr

TLNatType : TLSTypeExpr
TLNatType = MkTLSTypeExpr (Left TLNat) []

TLIntType : TLSTypeExpr
TLIntType = MkTLSTypeExpr (Left TLInt) []

TLIntTypeBare : TLSTypeExpr
TLIntTypeBare = MkTLSTypeBare TLIntType

TLLongType : TLSTypeExpr
TLLongType = MkTLSTypeExpr (Left TLLong) []

TLLongTypeBare : TLSTypeExpr
TLLongTypeBare = MkTLSTypeBare TLLongType

TLStringType : TLSTypeExpr
TLStringType = MkTLSTypeExpr (Left TLString) []

TLStringTypeBare : TLSTypeExpr
TLStringTypeBare = MkTLSTypeBare TLStringType

TLDoubleType : TLSTypeExpr
TLDoubleType = MkTLSTypeExpr (Left TLDouble) []

TLDoubleTypeBare : TLSTypeExpr
TLDoubleTypeBare = MkTLSTypeBare TLDoubleType

TLTypeType : TLSTypeExpr
TLTypeType = MkTLSTypeExpr (Left TLTType) []
