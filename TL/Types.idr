module TL.Types

%access public export

data TLNameType = TLNameTypeLC | TLNameTypeUC

Eq TLNameType where
  (==) TLNameTypeLC TLNameTypeLC = True
  (==) TLNameTypeUC TLNameTypeUC = True
  (==) _ _ = False

data TLName : Type where
  MkTLName : (name : String) -> (type : TLNameType) -> TLName
  MkTLNameNs : (ns : String) -> (name : String) -> (type : TLNameType) -> TLName

nameType : TLName -> TLNameType
nameType (MkTLName name type) = type
nameType (MkTLNameNs ns name type) = type

Show TLName where
  show (MkTLName name type) = name
  show (MkTLNameNs ns name type) = ns ++ "." ++ name

data TLBuiltIn = TLInt | TLNat | TLLong | TLString | TLDouble | TLTType

Show TLBuiltIn where
  show TLInt = "Int"
  show TLNat = "Nat"
  show TLLong = "Long"
  show TLString = "String"
  show TLDouble = "Double"
  show TLTType = "Type"

data TLTypeParam = TLParamNat | TLParamType

Show TLTypeParam where
  show TLParamNat = "#"
  show TLParamType = "Type"

Eq TLTypeParam where
  (==) TLParamNat TLParamNat = True
  (==) TLParamType TLParamType = True
  (==) _ _ = False

data TLType : Type where
  MkTLType : (name : String) -> List TLTypeParam -> TLType
  MkTLTypeBuiltin : TLBuiltIn -> TLType

Show TLType where
  show (MkTLType name xs) = name ++ " " ++ (show xs)
  show (MkTLTypeBuiltin x) = show x

getTypeParams : TLType -> List TLTypeParam
getTypeParams (MkTLType name xs) = xs
getTypeParams (MkTLTypeBuiltin builtin) = []

Eq TLBuiltIn where
  (==) TLInt TLInt = True
  (==) TLNat TLNat = True
  (==) TLLong TLLong = True
  (==) TLString TLString = True
  (==) TLDouble TLDouble = True
  (==) TLTType TLTType = True
  (==) _ _ = False

TypeRef : Type
TypeRef = Either TLBuiltIn Int

VarRef : Type
VarRef = Int

Conditional : Type
Conditional = (VarRef, Int)

data TLSection = Types | Functions

Show TLSection where
  show Types = "Types"
  show Functions = "Functions"

Eq TLSection where
  (==) Types Types = True
  (==) Functions Functions = True
  (==) _ _ = False

mutual
  data TLSArg : Type where
    MkTLSArg : (id : String) -> (var_num : VarRef) -> (type : TLSTypeExpr) -> TLSArg
    MkTLSArgOpt : (id : String) -> (var_num : VarRef) -> (type : TLSTypeExpr) -> TLSArg
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
    MkTLSTypeArray : (mult : TLSNat) -> (args : List (String, TLSTypeExpr)) -> TLSTypeExpr
    MkTLSTypeVar : (ref : VarRef) -> TLSTypeExpr
    MkTLSTypeBare : (expr : TLSTypeExpr) -> TLSTypeExpr
    MkTLSTypeBang : (expr : TLSTypeExpr) -> TLSTypeExpr

  Show TLSArg where
    show (MkTLSArg id var_num type) = id ++ ":" ++ (show type)
    show (MkTLSArgOpt id var_num type) = "{" ++ id ++ ":" ++ (show type) ++ "}"
    show (MkTLSArgCond id var_num cond type) = id ++ ":" ++ (show type) ++ " " ++ (show cond)

  Show TLSNat where
    show (MkTLSNat nat) = (show nat)
    show (MkTLSNatVar ref) = "Var #" ++ (show ref)

  Show TLSExpr where
    show (MkTLSExprType type) = show type
    show (MKTLSExprNat natExpr) = show natExpr

  Show TLSTypeExpr where
    show (MkTLSTypeExpr type children) = "Type Ref (" ++ (show type) ++ ") " ++ (show children)
    show (MkTLSTypeArray mult args) = (show mult) ++ "*" ++ (show args)
    show (MkTLSTypeVar ref) = "TypeVar #" ++ (show ref)
    show (MkTLSTypeBare expr) = "%" ++ (show expr)
    show (MkTLSTypeBang expr) = "!" ++ (show expr)

  Eq TLSNat where
    (==) (MkTLSNat nat) (MkTLSNat nat1) = nat == nat1
    (==) (MkTLSNatVar ref) (MkTLSNatVar ref1) = ref == ref1
    (==) _ _ = False

  Eq TLSExpr where
    (==) (MkTLSExprType type1) (MkTLSExprType type2) = compareTypes type1 type2
    (==) (MKTLSExprNat natExpr) (MKTLSExprNat natExpr1) = natExpr == natExpr1
    (==) _ _ = False

  compareChildren : List TLSExpr -> List TLSExpr -> Bool
  compareChildren xs ys = assert_total (xs == ys)

  compareTypes : TLSTypeExpr -> TLSTypeExpr -> Bool
  compareTypes xs ys = assert_total (xs == ys)

  compareArgs : List (String, TLSTypeExpr) -> List (String, TLSTypeExpr) -> Bool
  compareArgs xs ys = assert_total (xs == ys)

  Eq TLSTypeExpr where
    (==) (MkTLSTypeExpr type children) (MkTLSTypeExpr type2 children2) = type == type2 && compareChildren children children2
    (==) (MkTLSTypeArray mult args) (MkTLSTypeArray mult2 args2) = mult == mult2 && compareArgs args args2
    (==) (MkTLSTypeVar ref) (MkTLSTypeVar ref2) = ref == ref2
    (==) (MkTLSTypeBare expr) (MkTLSTypeBare expr2) = expr == expr2
    (==) (MkTLSTypeBang expr) (MkTLSTypeBang expr2) = expr == expr2
    (==) _ _ = False

TLSEArg : Type
TLSEArg = (String, TLSTypeExpr)

record TLSConstructor where
  constructor MkTLSConstructor
  identifier : String
  magic : Int
  args : List TLSArg
  resultType : TypeRef

record TLSFunction where
  constructor MkTLSFunction
  identifier : String
  magic : Int
  args : List TLSArg
  resultType : TLSTypeExpr


argId : TLSArg -> String
argId (MkTLSArg id var_num type) = id
argId (MkTLSArgCond id var_num cond type) = id
argId (MkTLSArgOpt id var_num type) = id

argType : TLSArg -> TLSTypeExpr
argType (MkTLSArg id var_num type) = type
argType (MkTLSArgCond id var_num cond type) = type
argType (MkTLSArgOpt id var_num type) = type

argRef : TLSArg -> VarRef
argRef (MkTLSArg id var_num type) = var_num
argRef (MkTLSArgCond id var_num cond type) = var_num
argRef (MkTLSArgOpt id var_num type) = var_num

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
