module Main
import TLParser
import TLParserTypes
import TLStore
import TLStoreTypes
import Lightyear.Strings
import Effects
import Data.SortedMap
import Effect.State
import Effect.Exception

%access public export

data Schema = MkSchema

readFileUntilEnd : File -> String -> IO (Either FileError String)
readFileUntilEnd file acc = do end <- fEOF file
                               if end then pure (Right acc)
                                      else do Right line <- fGetLine file
                                              | Left error => pure (Left error)
                                              readFileUntilEnd file (acc ++ line)

readSchemeFile : String -> IO (Either FileError String)
readSchemeFile filename = do Right file <- openFile filename Read
                             | Left error => pure (Left error)
                             Right filestr <- readFileUntilEnd file ""
                             | Left error => do closeFile file
                                                pure (Left error)
                             closeFile file
                             pure (Right filestr)

testText : String
testText = "getUsers#2d84d5f5 (Vector int) = Vector;"

testIo : Show a => String -> Parser a -> IO ()
testIo x p = do Right z <- pure (parse p x)
                  | Left y => putStrLn y
                putStrLn (show z)

testSimple : String -> Either String TLProgram
testSimple x = parse parseProgram x

initArg : TLSArg
initArg = (MkTLSArg (Just "X") Nothing typeType)

testTerm : String -> Either String TLSTypeExpr
testTerm str = parse parseTerm str >>= \term => (runInit [Args := [initArg], Store := (MkTLStore empty empty empty), default] (parseSimpleTermToType term))

main : IO ()
main = do Right result <- readSchemeFile "./example.tl"
            | Left error => putStrLn (show error)
          Right parseResult <- pure $ parse stripComments result
            | Left error => putStrLn error
          Right schemeTokens <- pure $ parse parseProgram parseResult
            | Left error => putStrLn error
          putStrLn "Done!"
