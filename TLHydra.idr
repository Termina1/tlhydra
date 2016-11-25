module TLHydra
import TLParser
import Lightyear.Strings

export
data Schema = MkSchema

export
loadSchema : String -> Schema

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
testText = "getUser#b0f732d5 test:int = User;\ngetUsers#2d84d5f5 res:%(Vector int) = Vector User;"

testSimple : String -> Either String TLProgram
testSimple x = parse parseProgram x
-- test : IO ()
-- test = do Right result <- readSchemeFile "./example.tl"
--             | Left error => putStrLn (show error)
--           Right parseResult <- pure $ parse parseComments result
--             | Left error => putStrLn (show error)
--           putStrLn parseResult
