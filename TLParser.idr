module TLParser

import Lightyear
import Lightyear.Char
import Lightyear.Strings

%access public export

data TLOpt : Type -> Type where
   Opt : (param : a) -> TLOpt a
   Ignore : TLOpt a

record TLIdentLcNs where
  constructor MkTLIdentLcNs
  ns : Maybe String
  ident : String

data TLTypeIdent = TypeIdentBoxed TLIdentLcNs |
                   TypeIdentLc TLIdentLcNs |
                   TypeIdentHash

mutual
  data TLSubExpr = SubExprTerm TLTerm |
                   SubExrpSum Nat TLSubExpr

  data TLTerm = TermExpr TLExpr |
                TermTypeIdent TLTypeIdent |
                TermVarIdent String |
                TermNatConst Nat |
                TermTerm TLTerm |
                TermTypeWithExpr (List TLExpr)

  TLExpr : Type
  TLExpr = List TLSubExpr

data TLResultType = ResultType TLIdentLcNs (List TLSubExpr) |
                    ResultTypeParam TLIdentLcNs (List TLSubExpr)

record TLIdentLcFull where
  constructor MkTLIdentLcFull
  ident : TLIdentLcNs
  magic : String

record TLArg where
  constructor MkTLArg
  identifier : TLOpt String
  type : TLTerm

record TLCombinator where
  constructor MkTLCombinator
  identifier : TLOpt TLIdentLcFull
  args : List TLArg
  resultType : TLResultType

data TLDeclaration = Combinator TLCombinator
data TLDeclarationBlock = TypeDeclarationBlock (List TLDeclaration)
                          | FunctionDeclarationBlock (List TLDeclaration)
record TLProgram where
  constructor MkTLProgram
  blocks : List TLDeclarationBlock

isIdentChar : (c : Char) -> Bool
isIdentChar c = isAlpha c || isDigit c || c == '_'

parseOpt : (Parser a) -> Parser (TLOpt a)
parseOpt parser = do result <- opt (satisfy (\c => c == '_'))
                     Just c <- pure result
                      | Nothing => map Opt parser
                     pure Ignore

parseComments : Parser String
parseComments = do spaces *> string "//" <* spaces
                   result <- manyTill anyToken (spaces *> eof)
                   pure $ pack result

parseLcIdent : Parser String
parseLcIdent = do lc <- satisfy (\c => isLower c && isIdentChar c)
                  other <- many (satisfy isIdentChar)
                  pure (pack (lc :: other))

parseUcIdent : Parser String
parseUcIdent = do uc <- satisfy (\c => isUpper c && isIdentChar c)
                  other <- many (satisfy isIdentChar)
                  pure (pack (uc :: other))

parseIdentNs : Parser String -> Parser TLIdentLcNs
parseIdentNs parser = do ns <- parser
                         Just _ <- opt (token ".")
                          | Nothing => pure (MkTLIdentLcNs Nothing ns)
                         lcident <- parseLcIdent
                         pure (MkTLIdentLcNs (Just ns) lcident)


parseBoxedTypeIdent : Parser TLIdentLcNs
parseBoxedTypeIdent = parseIdentNs parseUcIdent

parseTypeIdent : Parser TLTypeIdent
parseTypeIdent = (map TypeIdentBoxed parseBoxedTypeIdent) <|>
                 (map TypeIdentLc (parseIdentNs parseLcIdent)) <|>
                 (string "#" >>= (\t => pure TypeIdentHash))

parseNatConst : Parser Nat
parseNatConst = map (\t => the Nat (cast (pack t))) (some (satisfy isDigit))

parseVarIdent : Parser String
parseVarIdent = parseLcIdent <|> parseUcIdent

mutual
  parseSubExpr : Parser TLSubExpr
  parseSubExpr = (map SubExprTerm parseTerm) <|>
                 (parseNatConst >>= parseRightSub)
                -- TODO: remove left recursion
                --  (parseNatConst >>= parseLeftSub)
    where
      parseRightSub : Nat -> Parser TLSubExpr
      parseRightSub nat = parseSubExpr >>= (\sub => pure (SubExrpSum nat sub))

      parseLeftSub : TLSubExpr -> Parser TLSubExpr
      parseLeftSub sub = parseNatConst >>= (\nat => pure (SubExrpSum nat sub))

  parseTerm : Parser TLTerm
  parseTerm = (string "(" >! (map TermExpr parseExpr) <* string ")") <|>
              (map TermTypeIdent parseTypeIdent) <|>
              (map TermVarIdent parseVarIdent) <|>
              (map TermNatConst parseNatConst) <|>
              (string "%" >! map TermTerm parseTerm) <|>
              (string "<" >! map TermTypeWithExpr (many parseExpr))

  parseExpr : Parser TLExpr
  parseExpr = sepBy parseSubExpr spaces

parseArg : Parser TLArg
parseArg = do identOpt <- (parseOpt parseVarIdent)
              spaces
              string ":"
              spaces
              typeTerm <- parseTerm
              pure (MkTLArg identOpt typeTerm)

parseIdentFullLc : Parser TLIdentLcFull
parseIdentFullLc = do ident <- parseIdentNs parseLcIdent
                      hex <- do string "#"
                                mgc <- ntimes 8 hexDigit
                                pure (pack mgc)
                      pure (MkTLIdentLcFull ident hex)

parseResultType : Parser TLResultType
parseResultType = (parseIdentNs parseUcIdent <* spaces) >>= parseResultParams
  where
    parseResultParams : TLIdentLcNs -> Parser TLResultType
    parseResultParams ident = (string "<" >! parseResultParam ident) <|> (parseResult ident)
      where
        parseResultParam : TLIdentLcNs -> Parser TLResultType
        parseResultParam x = map (\params => ResultTypeParam x params) (some parseSubExpr)

        parseResult : TLIdentLcNs -> Parser TLResultType
        parseResult x = map (\params => ResultType x params) parseExpr

parseTLCombinator : Parser TLCombinator
parseTLCombinator = do ident <- parseOpt parseIdentFullLc
                       spaces
                       args <- sepBy1 parseArg spaces
                       spaces
                       token "="
                       spaces
                       result <- parseResultType
                       string ";"
                       pure (MkTLCombinator ident args result)

parseTLDeclaration : Parser TLDeclaration
parseTLDeclaration = map Combinator parseTLCombinator

parseFunctionDeclBlock : Parser TLDeclarationBlock
parseFunctionDeclBlock = map FunctionDeclarationBlock (many parseTLDeclaration)

parsTypeDeclBlock : Parser TLDeclarationBlock
parsTypeDeclBlock = map TypeDeclarationBlock (sepBy parseTLDeclaration (opt $ string "\n"))

parseTypeDeclarationBlock : Parser TLDeclarationBlock
parseTypeDeclarationBlock =
  string "--- functions ---" >! parseFunctionDeclBlock <|>
  string "--- types ---" >! parsTypeDeclBlock

parseProgram : Parser TLProgram
parseProgram = do block <- parsTypeDeclBlock
                  pure (MkTLProgram [block])
