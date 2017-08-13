module TL.Parser.Rules

import Text.Parser
import Text.Lexer

import TL.Parser.Tokenizer
import TL.Parser.Support
import TL.Types

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
                 pure $ TLEExpression [TLEIdent name, TLEExpression exprs]
          -- order matters, may be it could be fixed with rethinking grammar
          <|> do name <- typeName
                 pure $ TLEIdent name


parseResultTypeHelper : Rule TLExpressionLang
parseResultTypeHelper = do expect $ TLTokenChar '<'
                           expr <- sepBy1 (expectUnit $ TLTokenChar ',') parseExpression
                           expect $ TLTokenChar '<'
                           pure $ TLEExpression expr

parseResultType : Rule TLExpressionLang
parseResultType = do name <- boxedTypeName
                     expr <- (many parseExpression) >>= (\expr => pure $ TLEExpression expr) <|> parseResultTypeHelper
                     pure $ TLEExpression [(TLEIdent name), expr]

parseTypTermWithBang : Rule TLExpressionLang
parseTypTermWithBang = do bang <- optional $ expect $ TLTokenChar '!'
                          type <- parseTerm
                          pure $ parseTypTermWithBang bang type
                       where
                         parseTypTermWithBang : Maybe String -> TLExpressionLang -> TLExpressionLang
                         parseTypTermWithBang Nothing type = type
                         parseTypTermWithBang (Just x) type = TLEOperator TLBangOperator type

mutual
  parseSimpleArg : Rule (List TLEArg)
  parseSimpleArg = do var <- varName
                      expect $ TLTokenChar ':'
                      cond <- optional (do cond <- conditional
                                           expect $ TLTokenChar '?'
                                           pure cond)
                      typeTerm <- parseTypTermWithBang
                      pure $ [createArg var cond typeTerm]
                   where
                     createArg : TLVarName -> Maybe TLECond -> TLExpressionLang -> TLEArg
                     createArg var Nothing type = MkTLEArg var type
                     createArg var (Just x) type = MkTLEArgCond var x type

  parseShortArg : Rule (List TLEArg)
  parseShortArg = do type <- parseTypTermWithBang
                     pure $ [MkTLEArg MkTLVarOpt type]

  parseMultyplicityArg : Rule (List TLEArg)
  parseMultyplicityArg = do name <- optional (do name <- varName
                                                 expect $ TLTokenChar ':'
                                                 pure name)
                            mult <- optional (do term <- parseTerm
                                                 expect $ TLTokenChar '*'
                                                 pure term)
                            expect $ TLTokenChar '['
                            commit
                            args <- assert_total (many parseArg)
                            expect $ TLTokenChar ']'
                            pure $ createMultiArg name mult (join args)
                         where
                           createMultiArg : Maybe TLVarName -> Maybe TLExpressionLang -> List TLEArg -> List TLEArg
                           createMultiArg Nothing Nothing args = [MkTLEArg MkTLVarOpt $ TLEMultiArg TLEEmpty args]
                           createMultiArg Nothing (Just mult) args = [MkTLEArg MkTLVarOpt $ TLEMultiArg mult args]
                           createMultiArg (Just name) Nothing args = [MkTLEArg name $ TLEMultiArg TLEEmpty args]
                           createMultiArg (Just name) (Just mult) args = [MkTLEArg name $ TLEMultiArg mult args]

  parseListArg : Rule (List TLEArg)
  parseListArg = do expect $ TLTokenChar '('
                    names <- some varName
                    expect $ TLTokenChar ':'
                    type <- parseTypTermWithBang
                    expect $ TLTokenChar ')'
                    pure $ map (\name => MkTLEArg name type) names

  parseArg : Rule (List TLEArg)
  parseArg = parseMultyplicityArg <|> -- order matters again
             parseSimpleArg <|>
             parseListArg <|>
             parseShortArg

parseOptionalArg : Rule (List TLEArg)
parseOptionalArg = do expect $ TLTokenChar '{'
                      commit
                      names <- some varNameStrict
                      expect $ TLTokenChar ':'
                      type <- parseTypTermWithBang
                      expect $ TLTokenChar '}'
                      pure $ map (\name => MkTLEOptArg name type) names

parseCombinator : Rule TLCombinator
parseCombinator = do name <- combinatorName
                     optArgs <- many parseOptionalArg
                     args <- many parseArg
                     expect $ TLTokenChar '='
                     type <- parseResultType
                     expect $ TLTokenChar ';'
                     pure $ MkTLCombinator name ((join optArgs) ++ (join args)) type

parseFinalDecl : Rule TLDeclaration
parseFinalDecl = do name <- finalId
                    type <- finalName
                    expect $ TLTokenChar ';'
                    pure $ FinalDecl name type

parseBuiltin : Rule TLDeclaration
parseBuiltin = do name <- combinatorName
                  expect $ TLTokenChar '?'
                  expect $ TLTokenChar '='
                  type <- parseResultType
                  expect $ TLTokenChar ';'
                  pure $ BuiltInCombinator $ MkTLCombinator name [] type

parseTLDeclaration: Rule TLDeclaration
parseTLDeclaration = (parseCombinator >>= \comb => pure $ Combinator comb) <|>
                     parseFinalDecl <|>
                     parseBuiltin

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
                expect TLTokenTripleMinus
                decls <- many parseTLDeclaration
                pure $ declBlockFromToken token decls

parseProgram : Rule TLProgram
parseProgram = do decls <- many parseTLDeclaration
                  blocks <- some parseBlock
                  pure $ MkTLProgram $ (TypeDeclarationBlock decls) :: blocks

export
parseTL : String -> Either (ParseError (TokenData TLToken)) TLProgram
parseTL x = case parse (tlLex x) parseProgram of
                 (Left error) => Left error
                 (Right (program, left)) => if (length left) == 0
                                               then Right program
                                               else Left (Error "Not all tokens parsed!" left)
