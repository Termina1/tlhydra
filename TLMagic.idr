module TLMagic
import TLParserTypes


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

calculateMagic : TLCombinator -> Dec TLMagic

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
ensureMagic : TLCombinator -> Dec TLMagic
ensureMagic comb with (identifier comb)
  ensureMagic comb | (Opt param) with (param)
    ensureMagic comb | (Opt param) | (IdentLcFull _) = calculateMagic comb
    ensureMagic comb | (Opt param) | (IdentLcFullMagic _ magic) =
      case proveMagic magic of
           (Yes prf) => Yes (Element magic prf)
           (No contra) => No (\ contraVal => (case contraVal of
                                                   (Element x pf) => contra (believe_me pf)))

  ensureMagic comb | Ignore = calculateMagic comb
