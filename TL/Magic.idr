module TL.Magic

import Data.Bits
import crc32
import TL.Parser.Support
import TL.Types

export
calculateMagic : Show a => a -> Int
calculateMagic x = fromInteger $ bitsToInt $ crc32 $ (show x)

hexToInt : Char -> Int
hexToInt 'A' = 10
hexToInt 'a' = 10
hexToInt 'B' = 11
hexToInt 'b' = 11
hexToInt 'C' = 12
hexToInt 'c' = 12
hexToInt 'D' = 13
hexToInt 'd' = 13
hexToInt 'E' = 14
hexToInt 'e' = 14
hexToInt 'F' = 15
hexToInt 'f' = 15
hexToInt x = (ord x) - (ord '0')

total
parseHex : String -> Nat -> Int
parseHex x y = parseHexHelper (strM x) y
  where
    parseHexHelper : StrM x1 -> Nat -> Int
    parseHexHelper (StrCons symbol xs) Z = hexToInt symbol
    parseHexHelper StrNil x = 0
    parseHexHelper (StrCons symbol xs) (S x) = ((hexToInt symbol) * (cast (16 `power` (S x)))) + (parseHex xs x)

export
ensureMagic : TLCombinator -> Int
ensureMagic (MkTLCombinator (TLCNameFull name magic) args resultType) = parseHex magic 7
ensureMagic comb = calculateMagic (comb)
