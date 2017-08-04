module TL.Parser.Support

import Text.Parser
import Text.Lexer

%access public export

data TLNameType = TLNameTypeLC | TLNameTypeUC

Eq TLNameType where
  (==) TLNameTypeLC TLNameTypeLC = True
  (==) TLNameTypeUC TLNameTypeUC = True
  (==) _ _ = False

data TLName : Type where
  MkTLName : (name : String) -> (type : TLNameType) -> TLName
  MkTLNameNs : (ns : String) -> (name : String) -> (type : TLNameType) -> TLName

data TLToken =
  TLTokenComment String |
  TLTokenChar Char |
  TLTokenTripleMinus |
  TLTokenNat Nat |
  TLTokenIdentFull TLName String |
  TLTokenIdent TLName |
  TLTokenCond String Nat |
  TLTokenFinal |
  TLTokenNew |
  TLTokenEmpty |
  TLTokenSpace |
  TLTokenFail String


Rule : Type -> Type
Rule ty = Grammar (TokenData TLToken) True ty

data TLCName : Type where
  TLCNameFull : (name : TLName) -> (magic : String) -> TLCName
  TLCNameShort : (name : TLName) -> TLCName

data TLOperator = TLBareOperator | TLBangOperator | TLPlus

data TLExpressionLang =
  TLENat Nat |
  TLEIdent TLName |
  TLEHash |
  TLEEmpty |
  TLEOperator TLOperator TLExpressionLang |
  TLEExpression (List TLExpressionLang)

terminald : (TLToken -> Maybe a) -> Grammar (TokenData TLToken) True a
terminald f = terminal (\token => (case token of
                                        (MkToken line col tok) => f tok))

combinatorName : Rule TLCName
combinatorName = terminald (\token => (case token of
                                           (TLTokenIdentFull tname@(MkTLName name TLNameTypeLC) magic) => Just (TLCNameFull tname magic)
                                           (TLTokenIdentFull tname@(MkTLNameNs ns name TLNameTypeLC) magic) => Just (TLCNameFull tname magic)
                                           (TLTokenIdent tname@(MkTLName name TLNameTypeLC)) => Just (TLCNameShort tname)
                                           (TLTokenIdent tname@(MkTLNameNs ns name TLNameTypeLC)) => Just (TLCNameShort tname)
                                           _ => Nothing))
varName : Rule String
varName = terminald (\token => (case token of
                                    (TLTokenIdent (MkTLName name TLNameTypeLC)) => Just name
                                    _ => Nothing))

natConst : Rule Nat
natConst = terminald (\token => (case token of
                                     (TLTokenNat k) =>Just k
                                     _ => Nothing))

typeName : Rule TLName
typeName = terminald (\token => (case token of
                                     (TLTokenIdent name) => Just name
                                     _ => Nothing))

compare : TLToken -> TLToken -> Maybe String
compare (TLTokenChar x) (TLTokenChar y) = if x == y then Just (cast x) else Nothing
compare (TLTokenIdent (MkTLName name type)) (TLTokenIdent (MkTLName name2 type2)) = if name == name2 && type == type2
                                                                                       then Just name
                                                                                       else Nothing
compare TLTokenTripleMinus TLTokenTripleMinus = Just ""
compare TLTokenFinal TLTokenFinal = Just ""
compare TLTokenNew TLTokenNew = Just ""
compare TLTokenEmpty TLTokenEmpty = Just ""
compare _ _ = Nothing

expect : TLToken -> Rule String
expect token = terminald (\next => compare token next)
