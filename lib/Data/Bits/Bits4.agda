module Data.Bits.Bits4 where 

open import Data.Bits
open import Data.Nat
open import Data.Fin
open import Data.Vec

bits⁴ : Vec (Bits 4) 16
bits⁴ = allBits 4

0000b = bits⁴ ! # 0
0001b = bits⁴ ! # 1
0010b = bits⁴ ! # 2
0011b = bits⁴ ! # 3
0100b = bits⁴ ! # 4
0101b = bits⁴ ! # 5
0110b = bits⁴ ! # 6
0111b = bits⁴ ! # 7
1000b = bits⁴ ! # 8
1001b = bits⁴ ! # 9
1010b = bits⁴ ! # 10
1011b = bits⁴ ! # 11
1100b = bits⁴ ! # 12
1101b = bits⁴ ! # 13
1110b = bits⁴ ! # 14
1111b = bits⁴ ! # 15

-- 1000b ≡ parse "1000"
