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

bitsToBytes : Bits 32 -> Vect 4 (Bits 8)
bitsToBytes x = bitsToBytes' 4 x
  where
    bitsToBytes' : (n : Nat) -> Bits 32 -> Vect n (Bits 8)
    bitsToBytes' Z x = []
    bitsToBytes' (S k) bits = let prevBits = bitsToBytes' k bits in
                              let shifted = shiftRightLogical bits (MkBits $ natToBits {n = nextBytes 32} k * 8) in
                              let nextByte = truncate {m = 24} {n = 8} shifted in
                                  nextByte :: prevBits

upperBits : Bits 8 -> Fin 16
upperBits bits = let result = shiftRightLogical (and bits (intToBits 240)) (intToBits 4) in
                     restrict 15 (bitsToInt result)

lowerBits : Bits 8 -> Fin 16
lowerBits bits = let result = and bits (intToBits 15) in
                     restrict 15 (bitsToInt result)

finToHex : Fin 16 -> Char
finToHex FZ = '0'
finToHex (FS FZ) = '1'
finToHex (FS (FS FZ)) = '2'
finToHex (FS (FS (FS FZ))) = '3'
finToHex (FS (FS (FS (FS FZ)))) = '4'
finToHex (FS (FS (FS (FS (FS FZ))))) = '5'
finToHex (FS (FS (FS (FS (FS (FS FZ)))))) = '6'
finToHex (FS (FS (FS (FS (FS (FS (FS FZ))))))) = '7'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))) = '8'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))) = '9'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))) = 'A'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))) = 'B'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))) = 'C'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))) = 'D'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))))) = 'E'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))))) = 'F'
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))))))) impossible
finToHex (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS _))))))))))))))))) impossible

byteToHexStr : Bits 8 -> String
byteToHexStr bits =  let upper = finToHex $ upperBits bits in
                     let lower = finToHex $ lowerBits bits in
                         strCons upper (strCons lower "")

convertBitsToStrHex : Bits 32 -> String
convertBitsToStrHex bits = let bytes = bitsToBytes bits in
                               foldl (\acc, byte => acc ++ (byteToHexStr byte)) "" bytes

calculateMagic : TLCombinator -> Dec TLMagic
calculateMagic x = let magic = convertBitsToStrHex $ crc32 (show x) in
                   (case proveMagic magic of
                         (Yes prf) => Yes (Element magic prf)
                         (No contra) => No (\ contraVal => (case contraVal of
                                                                 (Element x pf) => contra (believe_me pf))))
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
