module TL.Store.Store

import Data.Vect
import TL.Types

%access public export


record TLStore where
  constructor MkTLStore
  types : Vect m TLType
  functions : Vect n TLSFunction
  constructors : Vect t TLSConstructor

emptyStore : TLStore
emptyStore = MkTLStore [] [] []

storeNameToType : TLName -> TLStore -> Maybe TypeRef
storeGetType : TypeRef -> TLStore -> TLType
