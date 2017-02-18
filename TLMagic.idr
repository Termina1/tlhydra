module TLMagic
import TLParserTypes
import Data.Bits
import Data.Vect
import crc32
import Data.Fin
import Debug.Trace


||| View for traversing a String one character at a time
public export
data StrList : String -> Type where
     SNil  : StrList ""
     SCons : (x : Char) -> (rec : StrList xs) -> StrList (strCons x xs)

||| Covering function for `StrList`
public export
strList : (x : String) -> StrList x
strList x with (strM x)
  strList "" | StrNil = SNil
  strList (strCons y xs) | (StrCons y xs)
          = assert_total $ SCons y (strList xs)

length : StrList str -> Nat
length SNil = 0
length (SCons x rec) = S (length rec)

public export
data hexFixedStr : (length : Nat) -> (subject : StrList str) -> Type where
  hexStrEmpty : hexFixedStr 0 SNil
  hexNext : (symbol : Char) ->
            (prf : (isHexDigit symbol) = True) ->
            hexFixedStr ln str ->
            hexFixedStr (S ln) (SCons symbol str)

public export
MagicLength : Nat
MagicLength = 8

public export
TLMagic : Type
TLMagic = Subset String (\str => hexFixedStr MagicLength (strList str))

hexFixedStrTail : hexFixedStr (S n) (SCons x xs) -> hexFixedStr n xs
hexFixedStrTail (hexNext sym prf prev) = prev

proveHexFixedStr : (str : StrList subject) -> Dec (hexFixedStr (length str) str)
proveHexFixedStr SNil = Yes hexStrEmpty
proveHexFixedStr (SCons x rec) with (proveHexFixedStr rec)
  proveHexFixedStr (SCons x rec) | (Yes prevHex) = case decEq (isHexDigit x) True of
                                                    (Yes prf) => Yes (hexNext x prf prevHex)
                                                    (No contra) => No (\contraVal => (case contraVal of
                                                                                           (hexNext x' prf y) => contra prf))
  proveHexFixedStr (SCons x rec) | (No contra) = No (\ contraVal => contra (hexFixedStrTail contraVal))

proveHexFixedStrEqualLength : (hexFixedStr n str) -> (length str) = n
proveHexFixedStrEqualLength {n = Z} {str = SNil} hexStrEmpty = Refl
proveHexFixedStrEqualLength {n = (S ln)} {str = (SCons symbol y)} (hexNext symbol _ z) = cong  (proveHexFixedStrEqualLength z)

proveMagic : (str : String) -> Dec (hexFixedStr MagicLength (strList str))
proveMagic str with (proveHexFixedStr (strList str))
  proveMagic str | (Yes prf1) = case decEq (length (strList str)) MagicLength of
                                     (Yes prf2) => Yes (rewrite sym prf2 in prf1)
                                     (No contra) => No (\ contra' => contra (proveHexFixedStrEqualLength contra'))
  proveMagic str | (No contra) = No (\ contra' => contra (rewrite (proveHexFixedStrEqualLength contra') in contra'))

export
calculateMagic : Show a => a -> Integer
calculateMagic x = bitsToInt $ crc32 $ (show x)

parseHex : hexFixedStr MagicLength str -> Integer
parseHex x = parseHexFixedStr x
  where
    parseHexFixedStr : hexFixedStr n str -> Integer
    parseHexFixedStr hexStrEmpty = 0
    parseHexFixedStr (hexNext symbol prf y) = (cast (((ord symbol) - (ord '0')))) + (parseHexFixedStr y)

export
ensureMagic : TLCombinator -> Either String Integer
ensureMagic comb with (identifier comb)
  ensureMagic comb | (Opt param) with (param)
    ensureMagic comb | (Opt param) | (IdentLcFull _) = Right $ calculateMagic comb
    ensureMagic comb | (Opt param) | (IdentLcFullMagic lc magic) =
      case proveMagic magic of
           (Yes prf) => Right (parseHex prf)
           (No contra) => Left $ "The name of this combinator (" ++ (show lc) ++ ") is not correct"

  ensureMagic comb | Ignore = Right $ calculateMagic comb
