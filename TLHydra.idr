module Main

import TL.Parser.Rules
import TL.Typechecker.Typechecker
import TL.Store.Store
import Text.Parser
import Text.Lexer
import TL.Parser.Support
import TL.Parser.Rules
import TL.Parser.Tokenizer
import crc32

evaluateProgram : String -> Either String TLStore
evaluateProgram str with (parseTL str)
  evaluateProgram str | (Left (Error x xs)) = Left $ x ++ (show xs)
  evaluateProgram str | (Right tlProgram) with (runTypechecker tlProgram)
    evaluateProgram str | (Right tlProgram) | (Left err) = Left err
    evaluateProgram str | (Right tlProgram) | (Right store) = pure store

testStr : String
testStr = """
"""

testIO : String -> IO ()
testIO str with (evaluateProgram str)
  testIO str | (Left l) = putStrLn ("Error: " ++ l)
  testIO str | (Right r) = putStrLn (show r)

export
main : IO ()
main with (evaluateProgram testStr)
  main | (Left l) = putStrLn ("Error: " ++ l)
  main | (Right r) = putStrLn (show r)
