module Main

import TL.Parser.Rules
import TL.Typechecker.Typechecker
import TL.Store.Store
import Text.Parser
import Text.Lexer
import TL.Parser.Support

evaluateProgram : String -> Either String TLStore
evaluateProgram str with (parseTL str)
  evaluateProgram str | (Left (Error x xs)) = Left $ x ++ (show xs)
  evaluateProgram str | (Right tlProgram) with (runTypechecker tlProgram)
    evaluateProgram str | (Right tlProgram) | (Left err) = Left err
    evaluateProgram str | (Right tlProgram) | (Right store) = pure store

testStr : String
testStr = """
tls.schema_v2 version:int date:int types_num:# types:types_num*[tls.Type]

    constructor_num:# constructors:constructor_num*[tls.Combinator]
    functions_num:# functions:functions_num*[tls.Combinator] = tls.Schema;
tls.type name:int id:string constructors_num:int flags:int arity:int params_type:long = tls.Type;

tls.combinator name:int id:string type_name:int left:tls.CombinatorLeft right:tls.CombinatorRight = tls.Combinator;
"""
