module TL.Serialize.Serializable

import TL.Types

import Data.Vect

%access public export

total
primitive : TLBuiltIn -> Type
primitive TLInt = Int
primitive TLNat = Nat
primitive TLLong = Integer
primitive TLString = String
primitive TLDouble = Double
primitive TLTType = Nat
primitive TLInt128 = Integer
primitive TLInt256 = Integer

data Serializy : Type where
  SBuiltIn : (ty : TLBuiltIn) -> (primitive ty) -> Serializy
  SMulti : Vect n (List Serializy) -> Serializy
  SExpr : TLName -> List Serializy -> Serializy

Show Serializy where
  show (SBuiltIn TLInt val) = show val
  show (SBuiltIn TLNat val) = show val
  show (SBuiltIn TLLong val) = show val
  show (SBuiltIn TLString val) = show val
  show (SBuiltIn TLDouble val) = show val
  show (SBuiltIn TLTType val) = show val
  show (SBuiltIn TLInt128 val) = show val
  show (SBuiltIn TLInt256 val) = show val
  show (SMulti seq) = assert_total $ show seq
  show (SExpr name sers) = assert_total $ (show name) ++ " " ++ (show sers)

interface TLSerializable a where
  serializable : a -> Serializy

TLSerializable Int where
  serializable d = SBuiltIn TLInt d

TLSerializable Integer where
  serializable d = SBuiltIn TLLong d

TLSerializable String where
  serializable d = SBuiltIn TLString d

TLSerializable Double where
  serializable d = SBuiltIn TLDouble d
