module TL.Parser.Rules

import Text.Parser

import TL.Parser.Tokenizer
import TL.Parser.Support

data TLOpt : Type -> Type where
   Opt : (param : a) -> TLOpt a
   Ignore : TLOpt a

Show a => Show (TLOpt a) where
    show (Opt param) = show param
    show Ignore = "_"

record TLIdentLcNs where
  constructor MkTLIdentLcNs
  ns : Maybe String
  ident : String

Show TLIdentLcNs where
    show (MkTLIdentLcNs Nothing ident) = ident
    show (MkTLIdentLcNs (Just x) ident) = x ++ "." ++ ident

data TLTypeIdent = TypeIdentBoxed TLIdentLcNs |
                   TypeIdentLc TLIdentLcNs |
                   TypeIdentHash

Show TLTypeIdent where
    show (TypeIdentBoxed x) = "Boxed type " ++ (show x)
    show (TypeIdentLc x) = "Type " ++ (show x)
    show TypeIdentHash = "#"

mutual
  TLExpr : Type
  TLExpr = List TLSubExpr

  data TLSubExpr = SubExprTerm TLTerm TLSubExpr |
                   SubExprEmpty |
                   SubExprSum Nat TLSubExpr |
                   SubExprSeq TLSubExpr TLSubExpr

  Show TLSubExpr where
    show (SubExprTerm term subexpr) = (show term) ++ " " ++ (show subexpr)
    show SubExprEmpty = ""
    show (SubExprSum nat subexpr) = (show nat) ++ " + " ++ (show subexpr)
    show (SubExprSeq subexpr1 subexpr2) = (show subexpr1) ++ " " ++ (show subexpr2)

  data TLTerm = TermExpr TLExpr |
                TermTypeIdent TLTypeIdent |
                TermVarIdent String |
                TermNatConst Nat |
                TermTerm TLTerm |
                TermTypeWithExpr TLTypeIdent (List TLExpr)

  Show TLTerm where
    show (TermExpr expr) = show expr
    show (TermTypeIdent type) = show type
    show (TermVarIdent ident) = ident
    show (TermNatConst nat) = show nat
    show (TermTerm term) = show term
    show (TermTypeWithExpr ident xs) = (show ident) ++ "<" ++ (show xs) ++ ">"

data TLResultType = ResultType TLIdentLcNs (List TLSubExpr) |
                    ResultTypeParam TLIdentLcNs (List TLSubExpr)

Show TLResultType where
    show (ResultType x xs) = (show x) ++ " " ++ (show xs)
    show (ResultTypeParam x xs) = (show x) ++ "<" ++ (show xs) ++ ">"

data TLIdentLcFull = IdentLcFull TLIdentLcNs |
                     IdentLcFullMagic TLIdentLcNs String

Show TLIdentLcFull where
    show (IdentLcFull x) = show x
    show (IdentLcFullMagic x y) = (show x) ++ "#" ++ y

record TLConditionalDef where
  constructor MkTLConditionalDef
  ident : String
  nat : Maybe Nat

Show TLConditionalDef where
    show (MkTLConditionalDef ident nat) = ident ++ "?." ++ (show nat)

data TLArg = ArgSimple (TLOpt String) (Maybe TLConditionalDef) Bool TLTerm |
             ArgVector (Maybe (TLOpt String)) (Maybe TLTerm) (List TLArg) |
             ArgBraces (List (TLOpt String)) Bool TLTerm |
             ArgShort Bool TLTerm

showMark : Bool -> String
showMark x = if x then "!" else ""

Show TLArg where
    show (ArgSimple ident Nothing excl type) = (show ident) ++ ":" ++ (showMark excl) ++ (show type)
    show (ArgSimple ident (Just x) excl type) = (show ident) ++ ":" ++ (show x) ++ (showMark excl) ++ (show type)
    show (ArgVector Nothing Nothing args) = show args
    show (ArgVector Nothing (Just mult) args) = (show mult) ++ "* " ++ (show args)
    show (ArgVector (Just ident) Nothing args) = (show ident) ++ ":" ++ (show args)
    show (ArgVector (Just ident) (Just mult) args) = (show ident) ++ ":" ++ (show mult) ++ "* " ++ (show args)
    show (ArgBraces idents excl type) = (show idents) ++ (showMark excl) ++ (show type)
    show (ArgShort excl type) = (showMark excl) ++ (show type)

record TLCombinator where
  constructor MkTLCombinator
  identifier : TLOpt TLIdentLcFull
  optArgs : List TLArg
  args : List TLArg
  resultType : TLResultType

Show TLCombinator where
  show (MkTLCombinator identifier optArgs args resultType) = (show identifier) ++ " {" ++ (show optArgs) ++ "} " ++ (show args) ++ " = " ++ (show resultType)

record TLBuiltIn where
  constructor MkTLBuiltIn
  identifier : TLOpt TLIdentLcFull
  type : TLIdentLcNs

Show TLBuiltIn where
  show (MkTLBuiltIn identifier type) = (show identifier) ++ " ? = " ++ (show type);

data TLDeclaration = Combinator TLCombinator |
                     BuiltInCombinator TLBuiltIn |
                     FinalDecl String TLIdentLcNs

Show TLDeclaration where
    show (Combinator x) = (show x) ++ "\n"
    show (BuiltInCombinator x) = (show x) ++ "\n"
    show (FinalDecl y x) = y ++ " " ++ (show x) ++ "\n"

data TLDeclarationBlock = TypeDeclarationBlock (List TLDeclaration)
                          | FunctionDeclarationBlock (List TLDeclaration)

Show TLDeclarationBlock where
    show (TypeDeclarationBlock xs) = "--- types ---\n" ++ (show xs)
    show (FunctionDeclarationBlock xs) = "--- functions ---\n" ++ (show xs)

record TLProgram where
  constructor MkTLProgram
  blocks : List TLDeclarationBlock

Show TLProgram where
    show (MkTLProgram blocks) = (show blocks)

mutual
  parseFullExpression : RuleWeek TLExpressionLang
  parseFullExpression = do exprs <- many parseExpression
                           pure $ TLEExpression exprs


  parseExpression' : Rule TLExpressionLang
  parseExpression' = do expect $ TLTokenChar '+'
                        nat <- natConst
                        expr <- (parseExpression' <|> (pure TLEEmpty))
                        pure $ TLEOperator TLPlus (TLEExpression [(TLENat nat), expr])

  parseExpression : Rule TLExpressionLang
  parseExpression = do term <- assert_total parseTerm
                       expr <- (parseExpression' <|> (pure TLEEmpty))
                       pure $ TLEExpression [term, expr]
                <|> do nat <- natConst
                       expect $ TLTokenChar '+'
                       expr <- parseExpression
                       sexpr <- (parseExpression' <|> (pure TLEEmpty))
                       pure $ TLEOperator TLPlus (TLEExpression [(TLENat nat), expr, sexpr])

  parseTerm : Rule TLExpressionLang
  parseTerm = do expect $ TLTokenChar '('
                 commit
                 expr <- parseFullExpression
                 expect $ TLTokenChar ')'
                 pure expr
          <|> do expect $ TLTokenChar '%'
                 commit
                 term <- parseTerm
                 pure $ TLEOperator TLBareOperator term
          <|> do expect $ TLTokenChar '#'
                 commit
                 pure TLEHash
          <|> do nat <- natConst
                 pure $ TLENat nat
          <|> do name <- typeName
                 expect $ TLTokenChar '<'
                 commit
                 exprs <- sepBy1 (expectUnit $ TLTokenChar ',') ((some parseExpression) >>= \expr => pure $ TLEExpression expr)
                 expect $ TLTokenChar '>'
                 pure $ TLEExpression exprs

          <|> do name <- typeName
                 pure $ TLEIdent name



parseCombinator : Rule TLCombinator
parseCombinator = do name <- combinatorName
                     ?hole1

parseTLDeclaration: Rule TLDeclaration
parseTLDeclaration = parseCombinator >>= \comb => pure $ Combinator comb

declBlockFromToken : String -> List TLDeclaration -> TLDeclarationBlock
declBlockFromToken type decls = if type == "types" then TypeDeclarationBlock decls
                                                   else FunctionDeclarationBlock decls

blockTypesToken : TLName
blockTypesToken = MkTLName "types" TLNameTypeLC

funcTypesToken : TLName
funcTypesToken = MkTLName "functions" TLNameTypeLC

parseBlock : Rule TLDeclarationBlock
parseBlock = do expect TLTokenTripleMinus
                token <- (expect $ TLTokenIdent blockTypesToken) <|> (expect $ TLTokenIdent funcTypesToken)
                decls <- many parseTLDeclaration
                pure $ declBlockFromToken token decls

parseProgram : Rule TLProgram
parseProgram = some parseBlock >>= \blocks => pure $ MkTLProgram blocks
