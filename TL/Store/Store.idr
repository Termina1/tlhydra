module TL.Store.Store

%access public export

data StoreTypeInsertError = StoreTypeInsertErrorExists
data StoreCombinatorInsertError = StoreCombinatorInsertErrorExists

interface TLStore store where
  test : Int -> Int
  -- insertType : TLSType -> Either StoreTypeInsertError store
  -- insertTypeConstructor : String -> TLSCombinator -> Either StoreCombinatorInsertError store
  -- insertFunctionConstructor : String -> TLSCombinator -> Either StoreCombinatorInsertError store
  --
  -- lookupType : store -> String -> Maybe TLSType
  -- lookupTypeConstructor : store -> String -> Maybe TLSCombinator
  -- lookupFunctionConstructor : store -> String -> Maybe TLSCombinator
