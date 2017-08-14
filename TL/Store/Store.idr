module TL.Store.Store

import TL.Types

%access public export

record TLStore where
  constructor MkTLStore
  types : List TLType
  functions : List TLSFunction
  constructors : List TLSConstructor

emptyStore : TLStore
emptyStore = MkTLStore [] [] []

storeNameToType : TLName -> TLStore -> Maybe TypeRef
storeNameToType name store = storeNameToTypeHelper (show name) (types store) 0
  where
    storeNameToTypeHelper : String -> List TLType -> Int -> Maybe TypeRef
    storeNameToTypeHelper sname [] i = Nothing
    storeNameToTypeHelper sname ((MkTLType tname xs) :: types) i = if tname == sname
                                                                      then Just $ Right i
                                                                      else storeNameToTypeHelper sname types (i + 1)
    storeNameToTypeHelper sname ((MkTLTypeBuiltin builtin) :: types) i = Just $ Left builtin

storeGetType : TypeRef -> TLStore -> TLType
storeGetType (Left builtin) store = MkTLTypeBuiltin builtin
storeGetType (Right r) store = case drop (cast r) (types store) of
                                    [] => MkTLType "bottom" []
                                    (x :: xs) => x

storeNameToConstructor : TLName -> TLStore -> Maybe TLSConstructor
storeNameToConstructor name store = storeNameToConstructorHelper (show name) (constructors store)
  where
    storeNameToConstructorHelper : String -> List TLSConstructor -> Maybe TLSConstructor
    storeNameToConstructorHelper sname [] = Nothing
    storeNameToConstructorHelper sname (cs :: css) = if (identifier cs) == sname
                                                        then Just cs
                                                        else storeNameToConstructorHelper sname css

storeNameToFunction : TLName -> TLStore -> Maybe TLSFunction
storeNameToFunction name store = storeNameToFunctionrHelper (show name) (functions store)
  where
    storeNameToFunctionrHelper : String -> List TLSFunction -> Maybe TLSFunction
    storeNameToFunctionrHelper sname [] = Nothing
    storeNameToFunctionrHelper sname (cs :: css) = if (identifier cs) == sname
                                                      then Just cs
                                                      else storeNameToFunctionrHelper sname css


storeInsertFunction : TLSFunction -> TLStore -> TLStore
storeInsertFunction func store = record { functions = func :: (functions store) } store

storeInsertConstructor : TLSConstructor -> TLStore -> TLStore
storeInsertConstructor constr store = record { constructors = constr :: (constructors store) } store

storeInsertType : TLType -> TLStore -> TLStore
storeInsertType type store = record { types = ((types store) ++ [type]) } store
