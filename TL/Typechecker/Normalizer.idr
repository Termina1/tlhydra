module TL.Typechecker.Normalizer

import TL.Parser.Support

isNotEmptyExpression : TLExpressionLang -> Bool
isNotEmptyExpression TLEEmpty = False
isNotEmptyExpression (TLEExpression xs) = (length xs) /= 0
isNotEmptyExpression expr = True

mutual
  argReduce : TLEArg -> TLEArg
  argReduce (MkTLEArg name type) = MkTLEArg name (expressionReduce type)
  argReduce (MkTLEOptArg name type) = MkTLEOptArg name (expressionReduce type)
  argReduce (MkTLEArgCond name cond type) = MkTLEArgCond name cond (expressionReduce type)

  -- when using map idris thinks it's not total
  expressionReduce' : List TLExpressionLang -> List TLExpressionLang
  expressionReduce' [] = []
  expressionReduce' (x :: xs) = (expressionReduce x) :: (expressionReduce' xs)

  export total
  expressionReduce : TLExpressionLang -> TLExpressionLang
  -- this is actually not always correct, i.e. if we write (test + 1 + 3), it will do something strange,
  -- however we will catch this later during typechecking, wich may result in not very obvious error message,
  -- neverthless it's easy to fix in future
  expressionReduce (TLEOperator TLPlus expr) = expressionReduce expr
  expressionReduce (TLEOperator x expr) = TLEOperator x (expressionReduce expr)
  expressionReduce (TLEExpression xs) = case filter isNotEmptyExpression (expressionReduce' xs) of
                                             (x :: []) => x
                                             ((TLENat k) :: (TLENat j) :: []) => TLENat (k + j)
                                             rs => TLEExpression rs
  expressionReduce (TLEMultiArg x xs) = TLEMultiArg (expressionReduce x) (map argReduce xs)
  expressionReduce expr = expr
