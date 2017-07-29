module TLStore

import TLTypes

public data StoreTypeInsertError = StoreTypeInsertErrorExists
public data StoreCombinatorInsertError = StoreCombinatorInsertErrorExists

public export
interface TLStore store where
  insertType : TLSType -> Either StoreTypeInsertError store
  insertTypeConstructor : String -> TLSCombinator -> Either StoreCombinatorInsertError store
  insertFunctionConstructor : String -> TLSCombinator -> Either StoreCombinatorInsertError store

  lookupType : store -> String -> Maybe TLSType
  lookupTypeConstructor : store -> String -> Maybe TLSCombinator
  lookupFunctionConstructor : store -> String -> Maybe TLSCombinator
