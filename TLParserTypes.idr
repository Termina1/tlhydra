module TLParserTypes

%access public export

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
                    ResultTypeParam TLIdentLcNs (List TLSubExpr) |
                    ResultTypeStub

Show TLResultType where
    show (ResultType x xs) = (show x) ++ " " ++ (show xs)
    show (ResultTypeParam x xs) = (show x) ++ "<" ++ (show xs) ++ ">"
    show (ResultTypeStub) = ""

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
