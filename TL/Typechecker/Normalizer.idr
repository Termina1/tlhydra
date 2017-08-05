module TL.Typechecker.Normalizer

import TL.Parser.Support
import Text.Lexer
import Text.Parser
import TL.Parser.Tokenizer
import TL.Parser.Rules

isNotEmptyExpression : TLExpressionLang -> Bool
isNotEmptyExpression TLEEmpty = False
isNotEmptyExpression (TLEExpression xs) = (length xs) /= 0
isNotEmptyExpression expr = True

mutual
  argReduce : TLEArg -> TLEArg
  argReduce (MkTLEArg name type) = MkTLEArg name (expressionReduce type)
  argReduce (MkTLEOptArg name type) = MkTLEOptArg name (expressionReduce type)
  argReduce (MkTLEArgCond name cond type) = MkTLEArgCond name cond (expressionReduce type)

  export
  expressionReduce : TLExpressionLang -> TLExpressionLang
  expressionReduce (TLEOperator x expr) = TLEOperator x (expressionReduce expr)
  expressionReduce (TLEExpression xs) = case filter isNotEmptyExpression (map expressionReduce xs) of
                                             (x :: []) => x
                                             rs => TLEExpression rs
  expressionReduce (TLEMultiArg x xs) = TLEMultiArg (expressionReduce x) (map argReduce xs)
  expressionReduce expr = expr
