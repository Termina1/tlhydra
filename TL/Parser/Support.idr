module TL.Parser.Support

import Text.Parser
import Text.Lexer
import TL.Types

%access public export

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

Show TLToken where
  show (TLTokenComment x) = "Comment: " ++ x
  show (TLTokenChar x) = "Char: " ++ singleton x
  show TLTokenTripleMinus = "---"
  show (TLTokenNat k) = show k
  show (TLTokenIdentFull x y) = (show x) ++ "#" ++ y
  show (TLTokenIdent x) = show x
  show (TLTokenCond x k) = x ++ "." ++ (show k)
  show TLTokenFinal = "Final"
  show TLTokenNew = "New"
  show TLTokenEmpty = ""
  show TLTokenSpace = " "
  show (TLTokenFail x) = "Fail: " ++ x

Show a => Show (TokenData a) where
  show (MkToken line col tok) = "line: " ++ (show line) ++ " col: " ++(show col) ++ " " ++ (show tok) ++ "\n"


Rule : Type -> Type
Rule ty = Grammar (TokenData TLToken) True ty

RuleWeek : Type -> Type
RuleWeek ty = Grammar (TokenData TLToken) False ty

data TLCName : Type where
  TLCNameFull : (name : TLName) -> (magic : String) -> TLCName
  TLCNameShort : (name : TLName) -> TLCName
  TLCNameEmpty : TLCName

Show TLCName where
  show (TLCNameFull name magic) = (show name) ++ "#" ++ magic
  show (TLCNameShort name) = (show name)
  show TLCNameEmpty = "_"

data TLVarName : Type where
  MkTLVarName : (name : TLName) -> TLVarName
  MkTLVarOpt : TLVarName

Show TLVarName where
  show (MkTLVarName name) = show name
  show MkTLVarOpt = "_"

data TLOperator = TLBareOperator | TLBangOperator | TLPlus

Show TLOperator where
  show TLBareOperator = "%"
  show TLBangOperator = "!"
  show TLPlus = "+"

data TLFinalId = TLEmpty | TLFinal | TLNew

glueList : Show a => List a -> String
glueList xs = foldl (\acc, t => acc ++ t) "" (intersperse " " (map show xs))

mutual
  TLECond : Type
  TLECond = (String, Nat)

  data TLEArg : Type where
    MkTLEArg : (name : TLVarName) -> (type : TLExpressionLang) -> TLEArg
    MkTLEOptArg : (name : TLVarName) -> (type : TLExpressionLang) -> TLEArg
    MkTLEArgCond : (name : TLVarName) -> (cond : TLECond) -> (type : TLExpressionLang) -> TLEArg

  data TLExpressionLang =
    TLENat Nat |
    TLEIdent TLName |
    TLEHash |
    TLEEmpty |
    TLEOperator TLOperator TLExpressionLang |
    TLEExpression (List TLExpressionLang) |
    TLEMultiArg TLExpressionLang (List TLEArg)

  Show TLEArg where
    show (MkTLEArg name type) = (show name) ++ ":" ++ (show type)
    show (MkTLEOptArg name type) = "{" ++ (show name) ++ ":" ++ (show type) ++ "}"
    show (MkTLEArgCond name (a, b) type) = (show name) ++ ":" ++ a ++ "." ++ (show b) ++ "?" ++ (show type)

  Show TLExpressionLang where
    show (TLENat k) = show k
    show (TLEIdent x) = show x
    show TLEHash = "#"
    show TLEEmpty = ""
    show (TLEOperator x y) = (show x) ++ " " ++ (show y)
    show (TLEExpression xs) = glueList xs
    show (TLEMultiArg TLEEmpty xs) = "[" ++ (glueList xs) ++ "]"
    show (TLEMultiArg x xs) = (show x) ++ "*[" ++ (glueList xs) ++ "]"

record TLCombinator where
  constructor MkTLCombinator
  identifier : TLCName
  args : List TLEArg
  resultType : TLExpressionLang

Show TLCombinator where
  show (MkTLCombinator identifier args resultType)
    = (show identifier) ++ " " ++ (glueList args) ++ " = " ++ (show resultType)

data TLDeclaration = Combinator TLCombinator |
                     BuiltInCombinator TLCombinator |
                     FinalDecl TLFinalId TLName

data TLDeclarationBlock = TypeDeclarationBlock (List TLDeclaration)
                          | FunctionDeclarationBlock (List TLDeclaration)

record TLProgram where
  constructor MkTLProgram
  blocks : List TLDeclarationBlock

terminald : (TLToken -> Maybe a) -> Grammar (TokenData TLToken) True a
terminald f = terminal (\token => (case token of
                                        (MkToken line col tok) => f tok))

finalId : Rule TLFinalId
finalId = terminald (\token => (case token of
                                     (TLTokenIdent (MkTLName "Final" TLNameTypeUC)) => Just TLFinal
                                     (TLTokenIdent (MkTLName "New" TLNameTypeUC)) => Just TLNew
                                     (TLTokenIdent (MkTLName "Empty" TLNameTypeUC)) => Just TLEmpty
                                     _ => Nothing))

finalName : Rule TLName
finalName = terminald (\token => (case token of
                                       (TLTokenIdent tname@(MkTLName name TLNameTypeUC)) => Just tname
                                       (TLTokenIdent tname@(MkTLNameNs ns name TLNameTypeUC)) => Just tname
                                       _ => Nothing))

combinatorName : Rule TLCName
combinatorName = terminald (\token => (case token of
                                           (TLTokenIdentFull tname@(MkTLName name TLNameTypeLC) magic) => Just (TLCNameFull tname magic)
                                           (TLTokenIdentFull tname@(MkTLNameNs ns name TLNameTypeLC) magic) => Just (TLCNameFull tname magic)
                                           (TLTokenIdent tname@(MkTLName name TLNameTypeLC)) => Just (TLCNameShort tname)
                                           (TLTokenIdent tname@(MkTLNameNs ns name TLNameTypeLC)) => Just (TLCNameShort tname)
                                           (TLTokenChar '_') => Just TLCNameEmpty
                                           _ => Nothing))

varNameStrict : Rule TLVarName
varNameStrict = terminald (\token => (case token of
                                           (TLTokenIdent (MkTLName name type)) => Just (MkTLVarName (MkTLName name type))
                                           _ => Nothing))

varName : Rule TLVarName
varName = terminald (\token => (case token of
                                    (TLTokenIdent (MkTLName name type)) => Just (MkTLVarName (MkTLName name type))
                                    (TLTokenChar '_') => Just MkTLVarOpt
                                    _ => Nothing))

natConst : Rule Nat
natConst = terminald (\token => (case token of
                                     (TLTokenNat k) =>Just k
                                     _ => Nothing))

optional : Grammar tok True ty -> Grammar tok False (Maybe ty)
optional p = (p >>= \t => pure $ Just t) <|> pure Nothing

conditional : Rule TLECond
conditional = terminald (\token => (case token of
                                         (TLTokenCond x k) => Just (x, k)
                                         _ => Nothing))

typeName : Rule TLName
typeName = terminald (\token => (case token of
                                     (TLTokenIdent name) => Just name
                                     _ => Nothing))

boxedTypeName : Rule TLName
boxedTypeName = terminald (\token => (case token of
                                           (TLTokenIdent tname@(MkTLName name TLNameTypeUC)) => Just tname
                                           (TLTokenIdent tname@(MkTLNameNs ns name TLNameTypeUC)) => Just tname
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

expectUnit : TLToken -> Rule ()
expectUnit token = terminald (\next => compare token next) >>= (\s => pure ())
