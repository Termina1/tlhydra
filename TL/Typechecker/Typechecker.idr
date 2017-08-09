module TL.Typechecker.Typechecker

import TL.Types
import TL.Parser.Support

import Effects
import Effect.State
import Effect.Exception

import TL.Store.Store

data Args : Type where
data Store : Type where
data Section : Type where

data TLCStore : Type where


TLStore TLCStore where
  test = id

TEff : Type -> Type
TEff ret = Effects.SimpleEff.Eff ret [
  Store ::: STATE TLCStore,
  Args ::: STATE (List TLSArg),
  Section ::: STATE TLSection,
  EXCEPTION String
]

assertSection : TLSection -> TEff ()
convertTypeIdentToRef : String -> TEff TypeRef
assertTypeParams : TypeRef -> List TLSExpr -> TEff ()

checkExpression : TLExpressionLang -> TEff TLSExpr
checkTypeIdent : TLExpressionLang -> TEff TypeRef
checkArgs : TLEArg -> TEff TLSArg
checkVarWithType : TLName -> TLSTypeExpr -> TEff VarRef

checkIdent : String -> TEff TLSTypeExpr
-- check if this var or type
-- if var then check its nat or type and convert to VarRef
-- if type check assertTypeParams and convert to TypeRef

checkNatExpression : TLExpressionLang -> TEff TLSNat
checkNatExpression (TLENat k) = pure $ MkTLSNat k
checkNatExpression (TLEIdent x) = do varRef <- checkVarWithType x TLNatType
                                     pure $ MkTLSNatVar varRef
checkNatExpression (TLEExpression (x :: [])) = checkNatExpression x
checkNatExpression _ = raise "Not a nat expression, where it should be!"


checkTypeExpression : TLExpressionLang -> TEff TLSTypeExpr
checkTypeExpression (TLENat k) = raise "Nat is not an expression!"
checkTypeExpression (TLEIdent (MkTLName name TLNameTypeLC)) = case name of
                                                               "int" => pure TLIntTypeBare
                                                               "long" => pure TLLongTypeBare
                                                               "string" => pure TLStringTypeBare
                                                               "double" => pure TLDoubleTypeBare
                                                               _ => do ident <- checkIdent name
                                                                       pure $ MkTLSTypeBare ident

checkTypeExpression (TLEIdent (MkTLName name TLNameTypeUC)) = case name of
                                                               "Int" => pure TLIntType
                                                               "Long" => pure TLLongType
                                                               "String" => pure TLStringType
                                                               "Double" => pure TLDoubleType
                                                               "Type" => pure TLTypeType
                                                               _ => checkIdent name

checkTypeExpression (TLEIdent (MkTLNameNs ns name type)) = checkIdent (ns ++ "." ++ name)

checkTypeExpression TLEHash = pure TLNatType
checkTypeExpression TLEEmpty = raise "No Empty Expressions allowed!"
checkTypeExpression (TLEOperator TLBareOperator y) = checkTypeExpression y >>= \expr => pure $ MkTLSTypeBare expr
checkTypeExpression (TLEOperator TLBangOperator y) = do assertSection Functions
                                                        expr <- checkTypeExpression y
                                                        pure $ MkTLSTypeBang expr
checkTypeExpression (TLEOperator TLPlus _) = raise "Arithmetic operations should be already reduced!"
checkTypeExpression (TLEExpression (x :: xs)) = do ref <- checkTypeIdent x
                                                   args <- mapE (\exp => checkExpression exp) xs
                                                   assertTypeParams ref args
                                                   pure $ MkTLSTypeExpr ref args
checkTypeExpression (TLEMultiArg x xs) = do nat <- checkNatExpression x
                                            args <- mapE (\x => checkArgs x) xs
                                            pure $ MkTLSTypeArray nat args
