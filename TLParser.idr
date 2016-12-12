module TLParser

import Lightyear
import Lightyear.Char
import Lightyear.Strings
import Debug.Trace
import TLParserTypes

%access public export

strace : String -> a -> a
strace x y = trace x y

isIdentChar : (c : Char) -> Bool
isIdentChar c = isAlpha c || isDigit c || c == '_'

parseOpt : (Parser a) -> Parser (TLOpt a)
parseOpt parser = do result <- opt (satisfy (\c => c == '_'))
                     Just c <- pure result
                      | Nothing => map Opt parser
                     pure Ignore

parseComments : Parser String
parseComments = do spaces *> string "//" <* spaces
                   result <- commitTo (manyTill anyToken (token "\n"))
                   pure $ pack result

stripComments : Parser String
stripComments = do all <- map (foldl (++) []) (many stripCommentsHelper)
                   last <- many anyToken
                   pure (pack (all ++ last))
  where
    stripCommentsHelper : Parser (List Char)
    stripCommentsHelper = do justStr <- manyTill anyToken (string "//")
                             manyTill anyToken (string "\n")
                             pure (justStr ++ ['\n'])

parseLcIdent : Parser String
parseLcIdent = (do lc <- (satisfy (\c => isLower c && isIdentChar c)) <?> "lowercase letter"
                   other <- many (satisfy isIdentChar)
                   pure (pack (lc :: other))) <?> "lowercase identifier"

parseUcIdent : Parser String
parseUcIdent = (do uc <- (satisfy (\c => isUpper c && isIdentChar c)) <?> "uppercase letter"
                   other <- many (satisfy isIdentChar)
                   pure (pack (uc :: other))) <?> "uppercase identifier"

parseIdentNs : Parser String -> Parser TLIdentLcNs
parseIdentNs parser = do Just ns <- opt (parseLcIdent <* string ".")
                          | Nothing => map (MkTLIdentLcNs Nothing) parser
                         ident <- parser
                         pure (MkTLIdentLcNs (Just ns) ident)


parseBoxedTypeIdent : Parser TLIdentLcNs
parseBoxedTypeIdent = parseIdentNs parseUcIdent

parseTypeIdent : Parser TLTypeIdent
parseTypeIdent = (string "#" >>= (\t => pure TypeIdentHash)) <|>
                 (map TypeIdentLc (parseIdentNs parseLcIdent)) <|>
                 (map TypeIdentBoxed parseBoxedTypeIdent)

parseNatConst : Parser Nat
parseNatConst = map (\t => the Nat (cast (pack t))) (some (satisfy isDigit))

parseVarIdent : Parser String
parseVarIdent = parseLcIdent <|> parseUcIdent <?> "variable"

mutual
  parseSubExpr : Parser TLSubExpr
  parseSubExpr = (parseTerm >!=
                 (\t => parseSubExpr' (Just t) >!=
                 (\subex => (case subex of
                                  Nothing => pure (SubExprTerm t SubExprEmpty)
                                  (Just x) => pure (SubExprTerm t x)))))
                <|>
                (parseNatConst >!= (\nat => spaces *> token "+" *> parseSubExpr >>=
                (\sub1 => parseSubExpr' Nothing >>=
                (\sub2 => (case sub2 of
                                Nothing => pure (SubExprSum nat sub1)
                                (Just x) => pure (SubExprSeq (SubExprSum nat sub1) x))))))
    where
      parseSubExpr' : Maybe TLTerm -> Parser (Maybe TLSubExpr)
      parseSubExpr' term = opt $
                           spaces *> token "+" >>= (
                           \t => parseNatConst >>= (
                           \nat => parseSubExpr' Nothing >>= (
                           \sub => (case sub of
                                         Nothing => (case term of
                                                          Nothing => pure (SubExprSum nat SubExprEmpty)
                                                          (Just term') => pure (SubExprTerm term' (SubExprSum nat SubExprEmpty)))
                                         (Just sub') => (case term of
                                                           Nothing => pure (SubExprSum nat sub')
                                                           (Just term') => pure (SubExprTerm term' (SubExprSum nat sub')))))))


  parseTerm : Parser TLTerm
  parseTerm = ((token "(" >! parseExpr <* token ")") >>= (\t => pure (TermExpr t))) <|>
              (char '%' >!= (\t => map TermTerm parseTerm)) <|>
              parseParametrisedType <|>
              (map TermNatConst parseNatConst) <|>
              (map TermVarIdent parseVarIdent)
    where
      parseBoxedParams : Parser (List TLExpr)
      parseBoxedParams = do token "<"
                            args <- commitTo (some (sepBy1 parseSubExpr spaces))
                            token ">"
                            pure args

      parseParametrisedType : Parser TLTerm
      parseParametrisedType = do type <- parseTypeIdent
                                 spaces
                                 params <- opt parseBoxedParams
                                 (case params of
                                       Nothing => pure (TermTypeIdent type)
                                       (Just x) => pure (TermTypeWithExpr type x))

  parseExpr : Parser TLExpr
  parseExpr = sepBy parseSubExpr spaces

parseConditionalDef : Parser TLConditionalDef
parseConditionalDef = do ident <- parseVarIdent
                         nat <- opt ((string ".") *> parseNatConst)
                         token "?"
                         pure (MkTLConditionalDef ident nat)


parseMutlArgs : Parser TLArg
parseMutlArgs = (do identsOpt <- sepBy1 (parseOpt parseVarIdent) spaces
                    token ":"
                    excl <- opt (token "!")
                    typeTerm <- parseTerm
                    pure (ArgBraces identsOpt (isJust excl) typeTerm))

parseArg : Parser TLArg
parseArg = parseArgBraces <|>
           parseOtherArgs
  where
    parseArgBraces : Parser TLArg
    parseArgBraces = (do token "("
                         arg <- parseMutlArgs
                         token ")"
                         pure arg) <?> "arguments with parens"

    parseSimpleArg : (TLOpt String) -> Parser TLArg
    parseSimpleArg ident = (do cdef <- opt parseConditionalDef
                               excl <- opt (token "!")
                               typeTerm <- parseTerm
                               pure (ArgSimple ident cdef (isJust excl) typeTerm)) <?> "simple argument"

    parseArgShort : Bool -> Parser TLArg
    parseArgShort excl = (do typeTerm <- parseTerm
                             pure (ArgShort excl typeTerm)) <?> "short argument"

    parseArgVector : Maybe (TLOpt String) -> (Maybe TLTerm) -> Parser TLArg
    parseArgVector ident term = (do token "["
                                    spaces
                                    args <- sepBy parseArg spaces
                                    spaces
                                    token "]"
                                    pure (ArgVector ident term args)) <?> "vector argument"

    parseArgWithNoIdent : Parser TLArg
    parseArgWithNoIdent = do excl <- opt (token "!")
                             if isJust excl
                                then parseArgShort True
                                else (do term <- opt parseTerm
                                         asterisk <- opt (token "*")
                                         if isNothing term || isJust asterisk
                                            then parseArgVector Nothing term
                                            else (case term of
                                                       Nothing => fail "expected term"
                                                       (Just term) => pure (ArgShort False term)))

    parserWithIdent : (TLOpt String) -> Parser TLArg
    parserWithIdent ident = do cdef <- opt parseConditionalDef
                               excl <- opt (token "!")
                               if isJust cdef || isJust excl
                                  then parseTerm >!= (\typeTerm => pure (ArgSimple ident cdef (isJust excl) typeTerm))
                                  else (do term <- parseTerm
                                           asterisk <- opt (token "*")
                                           if isJust asterisk
                                              then parseArgVector (Just ident) (Just term)
                                              else pure (ArgSimple ident cdef False term))

    parseOtherArgs : Parser TLArg
    parseOtherArgs = do identOpt <- opt (parseOpt parseVarIdent <* token ":")
                        (case identOpt of
                              Nothing => parseArgWithNoIdent
                              (Just ident) => parserWithIdent ident)

parseIdentFullLc : Parser TLIdentLcFull
parseIdentFullLc = do ident <- parseIdentNs parseLcIdent
                      Just hex <- opt (do string "#"
                                          mgc <- ntimes 8 hexDigit
                                          pure (pack mgc))
                        | Nothing => pure (IdentLcFull ident)
                      pure (IdentLcFullMagic ident hex)

parseResultType : Parser TLResultType
parseResultType = (parseIdentNs parseUcIdent <* spaces) >>= parseResultParams
  where
    parseResultParams : TLIdentLcNs -> Parser TLResultType
    parseResultParams ident = (token "<" >! parseResultParam ident <* token ">") <|> (parseResult ident)
      where
        parseResultParam : TLIdentLcNs -> Parser TLResultType
        parseResultParam x = map (\params => ResultTypeParam x params) (some parseSubExpr)

        parseResult : TLIdentLcNs -> Parser TLResultType
        parseResult x = map (\params => ResultType x params) parseExpr

parseOptArg : Parser TLArg
parseOptArg = do token "{"
                 arg <- parseMutlArgs
                 token "}"
                 pure arg

parseTLCombinator : Parser TLCombinator
parseTLCombinator = (do ident <- parseOpt parseIdentFullLc
                        spaces
                        optArgs <- many parseOptArg
                        spaces
                        args <- sepBy parseArg spaces
                        spaces
                        token "="
                        result <- parseResultType
                        token ";"
                        pure (MkTLCombinator ident optArgs args result)) <?> "combinator"

parseTLBuiltIn : Parser TLBuiltIn
parseTLBuiltIn = do ident <- parseOpt parseIdentFullLc
                    spaces
                    token "?"
                    token "="
                    type <- parseBoxedTypeIdent
                    token ";"
                    pure (MkTLBuiltIn ident type)

parseFinalDecl : Parser TLDeclaration
parseFinalDecl = (string "New" <|> string "Final" <|> string "Empty")
                 >!= (\t => (spaces *> parseBoxedTypeIdent <* token ";") >>= (\l => pure $ FinalDecl t l))

parseTLDeclaration : Parser TLDeclaration
parseTLDeclaration = spaces *> (map Combinator parseTLCombinator <|>
                     parseFinalDecl <|>
                     map BuiltInCombinator parseTLBuiltIn) <* spaces

parseFunctionDeclBlock : Parser TLDeclarationBlock
parseFunctionDeclBlock = map FunctionDeclarationBlock (sepBy parseTLDeclaration (opt $ string "\n"))

parsTypeDeclBlock : Parser TLDeclarationBlock
parsTypeDeclBlock = map TypeDeclarationBlock (sepBy parseTLDeclaration (opt $ string "\n"))

parseTypeDeclarationBlock : Parser TLDeclarationBlock
parseTypeDeclarationBlock =
  (string "---functions---" >! (many (string "\n")) *> parseFunctionDeclBlock) <|>
  (string "---types---" >! (many (string "\n")) *> parsTypeDeclBlock)

parseProgram : Parser TLProgram
parseProgram = do block <- parsTypeDeclBlock
                  other <- many parseTypeDeclarationBlock
                  pure (MkTLProgram (block :: other))
