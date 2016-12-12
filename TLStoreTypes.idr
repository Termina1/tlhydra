module TLStoreTypes

import TLMagic
import Data.SortedMap

%access public export

data TLArg : Type where

data TLType : Type where

record TLCombinator where
  constructor MkTLCombinator
  identifier : String
  magic : Integer
  optArgs : List TLArg
  args : List TLArg
  resultType : TLType

data TLFinal : Type where

record TLStore where
  constructor MkTLStore
  magicMapping : SortedMap Integer String
  types : SortedMap String TLCombinator
  functions : SortedMap String TLCombinator
  finals : SortedMap String TLFinal
