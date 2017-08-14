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

vector {t:Type} # [t] = Vector t;
tuple {t:Type} {n:#} [t] = Tuple t n;
vectorTotal {t:Type} total_count:int vector:%(Vector t) = VectorTotal t;


dictionaryField {t:Type} key:string value:t = DictionaryField t;
dictionary {t:Type} %(Vector %(DictionaryField t)) = Dictionary t;
"""

testIO : String -> IO ()
testIO str with (evaluateProgram str)
  testIO str | (Left l) = putStrLn ("Error: " ++ l)
  testIO str | (Right r) = putStrLn "Done!"
