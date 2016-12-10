module crc32

import Data.Bits

g0 : Bits 32
g0 = intToBits 0xEDB88320

g1 : Bits 32
g1 = shiftRightLogical g0 (intToBits 1)

g2 : Bits 32
g2 = shiftRightLogical g0 (intToBits 2)

g3 : Bits 32
g3 = shiftRightLogical g0 (intToBits 3)

g4 : Bits 32
g4 = (intToBits 0xF)

g5 : Bits 32
g5 = (intToBits 4)

g0xg1 : Bits 32
g0xg1 = xor g0 g1
g0xg3 : Bits 32
g0xg3 = xor g0 g3
g0xg2 : Bits 32
g0xg2 = xor g0 g2
g1xg3 : Bits 32
g1xg3 = xor g1 g3
g1xg2 : Bits 32
g1xg2 = xor g1 g2
g2xg3 : Bits 32
g2xg3 = xor g2 g3
g0xg1xg3 : Bits 32
g0xg1xg3 = xor (xor g0 g1) g3
g0xg1xg2 : Bits 32
g0xg1xg2 = xor (xor g0 g1) g2
g0xg2xg3 : Bits 32
g0xg2xg3 = xor (xor g0 g2) g3
g1xg2xg3 : Bits 32
g1xg2xg3 = xor (xor g1 g2) g3
g0xg1xg2xg3 : Bits 32
g0xg1xg2xg3 = xor (xor g0 (xor g1 g2)) g3

zero : Bits 32
zero = intToBits 0

getNextXor : Bits 32 -> Char -> Bits 32
getNextXor crc y = case bitsToInt (and crc g4) of
                        0 => zero
                        1 => g3
                        2 => g2
                        3 => g2xg3
                        4 => g1
                        5 => g1xg3
                        6 => g1xg2
                        7 => g1xg2xg3
                        8 => g0
                        9 => g0xg3
                        10 => g0xg2
                        11 => g0xg2xg3
                        12 => g0xg1
                        13 => g0xg1xg3
                        14 => g0xg1xg2
                        15 => g0xg1xg2xg3

export
crc32 : String -> Bits 32
crc32 x = let crc = intToBits 0xFFFFFFFF in
              crc32' (unpack x) crc
  where
    getNextCrc : Bits 32 -> Char -> Bits 32
    getNextCrc crc y = let nextXor = getNextXor crc y in
                       let midCrc = (xor (shiftRightLogical crc g5) nextXor) in
                       let lastXor = getNextXor midCrc y in
                       (xor (shiftRightLogical midCrc g5) lastXor)

    crc32' : (List Char) -> Bits 32 -> Bits 32
    crc32' [] crc = complement crc
    crc32' (y :: xs) crc = let nextCrc = getNextCrc (xor crc (intToBits $ cast (ord y))) y in
                               crc32' xs nextCrc
