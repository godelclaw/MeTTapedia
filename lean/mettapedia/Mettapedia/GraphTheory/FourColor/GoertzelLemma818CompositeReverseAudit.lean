import Mettapedia.GraphTheory.FourColor.GoertzelLemma818CompositeCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Reverse-direction chunks for the generated `tau,tau` certificate

The generated parent rows point from each source state toward the chosen
fiber root.  Real closure arguments grow outward from the root, so this
module checks the reverse Kempe-step direction in small generated chunks.
The chunk size is intentionally two rows: larger chunks exceed the default
recursion-depth budget on some rows of this table.
-/

namespace GoertzelLemma818CompositeReverseAudit

open GoertzelLemma818CompositeCertificate

def ttReverseFiber3Chunk0 : Bool :=
  directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 0) &&
    directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 1)

theorem ttReverseFiber3Chunk0_ok : ttReverseFiber3Chunk0 = true := by
  decide

def ttReverseFiber3Chunk1 : Bool :=
  directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 2) &&
    directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 3)

theorem ttReverseFiber3Chunk1_ok : ttReverseFiber3Chunk1 = true := by
  decide

def ttReverseFiber3Chunk2 : Bool :=
  directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 4) &&
    directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 5)

theorem ttReverseFiber3Chunk2_ok : ttReverseFiber3Chunk2 = true := by
  decide

def ttReverseFiber3Chunk3 : Bool :=
  directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 6) &&
    directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt 7)

theorem ttReverseFiber3Chunk3_ok : ttReverseFiber3Chunk3 = true := by
  decide

def ttReverseFiber4Chunk0 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 0) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 1)

theorem ttReverseFiber4Chunk0_ok : ttReverseFiber4Chunk0 = true := by
  decide

def ttReverseFiber4Chunk1 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 2) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 3)

theorem ttReverseFiber4Chunk1_ok : ttReverseFiber4Chunk1 = true := by
  decide

def ttReverseFiber4Chunk2 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 4) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 5)

theorem ttReverseFiber4Chunk2_ok : ttReverseFiber4Chunk2 = true := by
  decide

def ttReverseFiber4Chunk3 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 6) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 7)

theorem ttReverseFiber4Chunk3_ok : ttReverseFiber4Chunk3 = true := by
  decide

def ttReverseFiber4Chunk4 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 8) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 9)

theorem ttReverseFiber4Chunk4_ok : ttReverseFiber4Chunk4 = true := by
  decide

def ttReverseFiber4Chunk5 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 10) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 11)

theorem ttReverseFiber4Chunk5_ok : ttReverseFiber4Chunk5 = true := by
  decide

def ttReverseFiber4Chunk6 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 12) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 13)

theorem ttReverseFiber4Chunk6_ok : ttReverseFiber4Chunk6 = true := by
  decide

def ttReverseFiber4Chunk7 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 14) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 15)

theorem ttReverseFiber4Chunk7_ok : ttReverseFiber4Chunk7 = true := by
  decide

def ttReverseFiber4Chunk8 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 16) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 17)

theorem ttReverseFiber4Chunk8_ok : ttReverseFiber4Chunk8 = true := by
  decide

def ttReverseFiber4Chunk9 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 18) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 19)

theorem ttReverseFiber4Chunk9_ok : ttReverseFiber4Chunk9 = true := by
  decide

def ttReverseFiber4Chunk10 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 20) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 21)

theorem ttReverseFiber4Chunk10_ok : ttReverseFiber4Chunk10 = true := by
  decide

def ttReverseFiber4Chunk11 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 22) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 23)

theorem ttReverseFiber4Chunk11_ok : ttReverseFiber4Chunk11 = true := by
  decide

def ttReverseFiber4Chunk12 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 24) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 25)

theorem ttReverseFiber4Chunk12_ok : ttReverseFiber4Chunk12 = true := by
  decide

def ttReverseFiber4Chunk13 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 26) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 27)

theorem ttReverseFiber4Chunk13_ok : ttReverseFiber4Chunk13 = true := by
  decide

def ttReverseFiber4Chunk14 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 28) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 29)

theorem ttReverseFiber4Chunk14_ok : ttReverseFiber4Chunk14 = true := by
  decide

def ttReverseFiber4Chunk15 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 30) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 31)

theorem ttReverseFiber4Chunk15_ok : ttReverseFiber4Chunk15 = true := by
  decide

def ttReverseFiber4Chunk16 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 32) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 33)

theorem ttReverseFiber4Chunk16_ok : ttReverseFiber4Chunk16 = true := by
  decide

def ttReverseFiber4Chunk17 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 34) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 35)

theorem ttReverseFiber4Chunk17_ok : ttReverseFiber4Chunk17 = true := by
  decide

def ttReverseFiber4Chunk18 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 36) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 37)

theorem ttReverseFiber4Chunk18_ok : ttReverseFiber4Chunk18 = true := by
  decide

def ttReverseFiber4Chunk19 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 38) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 39)

theorem ttReverseFiber4Chunk19_ok : ttReverseFiber4Chunk19 = true := by
  decide

def ttReverseFiber4Chunk20 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 40) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 41)

theorem ttReverseFiber4Chunk20_ok : ttReverseFiber4Chunk20 = true := by
  decide

def ttReverseFiber4Chunk21 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 42) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 43)

theorem ttReverseFiber4Chunk21_ok : ttReverseFiber4Chunk21 = true := by
  decide

def ttReverseFiber4Chunk22 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 44) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 45)

theorem ttReverseFiber4Chunk22_ok : ttReverseFiber4Chunk22 = true := by
  decide

def ttReverseFiber4Chunk23 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 46) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 47)

theorem ttReverseFiber4Chunk23_ok : ttReverseFiber4Chunk23 = true := by
  decide

def ttReverseFiber4Chunk24 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 48) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 49)

theorem ttReverseFiber4Chunk24_ok : ttReverseFiber4Chunk24 = true := by
  decide

def ttReverseFiber4Chunk25 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 50) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 51)

theorem ttReverseFiber4Chunk25_ok : ttReverseFiber4Chunk25 = true := by
  decide

def ttReverseFiber4Chunk26 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 52) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 53)

theorem ttReverseFiber4Chunk26_ok : ttReverseFiber4Chunk26 = true := by
  decide

def ttReverseFiber4Chunk27 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 54) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 55)

theorem ttReverseFiber4Chunk27_ok : ttReverseFiber4Chunk27 = true := by
  decide

def ttReverseFiber4Chunk28 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 56) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 57)

theorem ttReverseFiber4Chunk28_ok : ttReverseFiber4Chunk28 = true := by
  decide

def ttReverseFiber4Chunk29 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 58) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 59)

theorem ttReverseFiber4Chunk29_ok : ttReverseFiber4Chunk29 = true := by
  decide

def ttReverseFiber4Chunk30 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 60) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 61)

theorem ttReverseFiber4Chunk30_ok : ttReverseFiber4Chunk30 = true := by
  decide

def ttReverseFiber4Chunk31 : Bool :=
  directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 62) &&
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 63)

theorem ttReverseFiber4Chunk31_ok : ttReverseFiber4Chunk31 = true := by
  decide

def ttReverseFiber5Chunk0 : Bool :=
  directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 0) &&
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 1)

theorem ttReverseFiber5Chunk0_ok : ttReverseFiber5Chunk0 = true := by
  decide

def ttReverseFiber5Chunk1 : Bool :=
  directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 2) &&
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 3)

theorem ttReverseFiber5Chunk1_ok : ttReverseFiber5Chunk1 = true := by
  decide

def ttReverseFiber5Chunk2 : Bool :=
  directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 4) &&
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 5)

theorem ttReverseFiber5Chunk2_ok : ttReverseFiber5Chunk2 = true := by
  decide

def ttReverseFiber5Chunk3 : Bool :=
  directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 6) &&
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 7)

theorem ttReverseFiber5Chunk3_ok : ttReverseFiber5Chunk3 = true := by
  decide

def ttReverseFiber6Chunk0 : Bool :=
  directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 0) &&
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 1)

theorem ttReverseFiber6Chunk0_ok : ttReverseFiber6Chunk0 = true := by
  decide

def ttReverseFiber6Chunk1 : Bool :=
  directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 2) &&
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 3)

theorem ttReverseFiber6Chunk1_ok : ttReverseFiber6Chunk1 = true := by
  decide

def ttReverseFiber6Chunk2 : Bool :=
  directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 4) &&
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 5)

theorem ttReverseFiber6Chunk2_ok : ttReverseFiber6Chunk2 = true := by
  decide

def ttReverseFiber6Chunk3 : Bool :=
  directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 6) &&
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 7)

theorem ttReverseFiber6Chunk3_ok : ttReverseFiber6Chunk3 = true := by
  decide

def ttReverseFiber7Chunk0 : Bool :=
  directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 0) &&
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 1)

theorem ttReverseFiber7Chunk0_ok : ttReverseFiber7Chunk0 = true := by
  decide

def ttReverseFiber7Chunk1 : Bool :=
  directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 2) &&
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 3)

theorem ttReverseFiber7Chunk1_ok : ttReverseFiber7Chunk1 = true := by
  decide

def ttReverseFiber7Chunk2 : Bool :=
  directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 4) &&
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 5)

theorem ttReverseFiber7Chunk2_ok : ttReverseFiber7Chunk2 = true := by
  decide

def ttReverseFiber7Chunk3 : Bool :=
  directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 6) &&
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 7)

theorem ttReverseFiber7Chunk3_ok : ttReverseFiber7Chunk3 = true := by
  decide

def ttReverseFiber8Chunk0 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 0) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 1)

theorem ttReverseFiber8Chunk0_ok : ttReverseFiber8Chunk0 = true := by
  decide

def ttReverseFiber8Chunk1 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 2) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 3)

theorem ttReverseFiber8Chunk1_ok : ttReverseFiber8Chunk1 = true := by
  decide

def ttReverseFiber8Chunk2 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 4) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 5)

theorem ttReverseFiber8Chunk2_ok : ttReverseFiber8Chunk2 = true := by
  decide

def ttReverseFiber8Chunk3 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 6) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 7)

theorem ttReverseFiber8Chunk3_ok : ttReverseFiber8Chunk3 = true := by
  decide

def ttReverseFiber8Chunk4 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 8) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 9)

theorem ttReverseFiber8Chunk4_ok : ttReverseFiber8Chunk4 = true := by
  decide

def ttReverseFiber8Chunk5 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 10) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 11)

theorem ttReverseFiber8Chunk5_ok : ttReverseFiber8Chunk5 = true := by
  decide

def ttReverseFiber8Chunk6 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 12) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 13)

theorem ttReverseFiber8Chunk6_ok : ttReverseFiber8Chunk6 = true := by
  decide

def ttReverseFiber8Chunk7 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 14) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 15)

theorem ttReverseFiber8Chunk7_ok : ttReverseFiber8Chunk7 = true := by
  decide

def ttReverseFiber8Chunk8 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 16) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 17)

theorem ttReverseFiber8Chunk8_ok : ttReverseFiber8Chunk8 = true := by
  decide

def ttReverseFiber8Chunk9 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 18) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 19)

theorem ttReverseFiber8Chunk9_ok : ttReverseFiber8Chunk9 = true := by
  decide

def ttReverseFiber8Chunk10 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 20) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 21)

theorem ttReverseFiber8Chunk10_ok : ttReverseFiber8Chunk10 = true := by
  decide

def ttReverseFiber8Chunk11 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 22) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 23)

theorem ttReverseFiber8Chunk11_ok : ttReverseFiber8Chunk11 = true := by
  decide

def ttReverseFiber8Chunk12 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 24) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 25)

theorem ttReverseFiber8Chunk12_ok : ttReverseFiber8Chunk12 = true := by
  decide

def ttReverseFiber8Chunk13 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 26) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 27)

theorem ttReverseFiber8Chunk13_ok : ttReverseFiber8Chunk13 = true := by
  decide

def ttReverseFiber8Chunk14 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 28) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 29)

theorem ttReverseFiber8Chunk14_ok : ttReverseFiber8Chunk14 = true := by
  decide

def ttReverseFiber8Chunk15 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 30) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 31)

theorem ttReverseFiber8Chunk15_ok : ttReverseFiber8Chunk15 = true := by
  decide

def ttReverseFiber8Chunk16 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 32) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 33)

theorem ttReverseFiber8Chunk16_ok : ttReverseFiber8Chunk16 = true := by
  decide

def ttReverseFiber8Chunk17 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 34) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 35)

theorem ttReverseFiber8Chunk17_ok : ttReverseFiber8Chunk17 = true := by
  decide

def ttReverseFiber8Chunk18 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 36) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 37)

theorem ttReverseFiber8Chunk18_ok : ttReverseFiber8Chunk18 = true := by
  decide

def ttReverseFiber8Chunk19 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 38) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 39)

theorem ttReverseFiber8Chunk19_ok : ttReverseFiber8Chunk19 = true := by
  decide

def ttReverseFiber8Chunk20 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 40) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 41)

theorem ttReverseFiber8Chunk20_ok : ttReverseFiber8Chunk20 = true := by
  decide

def ttReverseFiber8Chunk21 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 42) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 43)

theorem ttReverseFiber8Chunk21_ok : ttReverseFiber8Chunk21 = true := by
  decide

def ttReverseFiber8Chunk22 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 44) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 45)

theorem ttReverseFiber8Chunk22_ok : ttReverseFiber8Chunk22 = true := by
  decide

def ttReverseFiber8Chunk23 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 46) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 47)

theorem ttReverseFiber8Chunk23_ok : ttReverseFiber8Chunk23 = true := by
  decide

def ttReverseFiber8Chunk24 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 48) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 49)

theorem ttReverseFiber8Chunk24_ok : ttReverseFiber8Chunk24 = true := by
  decide

def ttReverseFiber8Chunk25 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 50) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 51)

theorem ttReverseFiber8Chunk25_ok : ttReverseFiber8Chunk25 = true := by
  decide

def ttReverseFiber8Chunk26 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 52) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 53)

theorem ttReverseFiber8Chunk26_ok : ttReverseFiber8Chunk26 = true := by
  decide

def ttReverseFiber8Chunk27 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 54) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 55)

theorem ttReverseFiber8Chunk27_ok : ttReverseFiber8Chunk27 = true := by
  decide

def ttReverseFiber8Chunk28 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 56) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 57)

theorem ttReverseFiber8Chunk28_ok : ttReverseFiber8Chunk28 = true := by
  decide

def ttReverseFiber8Chunk29 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 58) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 59)

theorem ttReverseFiber8Chunk29_ok : ttReverseFiber8Chunk29 = true := by
  decide

def ttReverseFiber8Chunk30 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 60) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 61)

theorem ttReverseFiber8Chunk30_ok : ttReverseFiber8Chunk30 = true := by
  decide

def ttReverseFiber8Chunk31 : Bool :=
  directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 62) &&
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 63)

theorem ttReverseFiber8Chunk31_ok : ttReverseFiber8Chunk31 = true := by
  decide

def ttReverseFiber9Chunk0 : Bool :=
  directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 0) &&
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 1)

theorem ttReverseFiber9Chunk0_ok : ttReverseFiber9Chunk0 = true := by
  decide

def ttReverseFiber9Chunk1 : Bool :=
  directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 2) &&
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 3)

theorem ttReverseFiber9Chunk1_ok : ttReverseFiber9Chunk1 = true := by
  decide

def ttReverseFiber9Chunk2 : Bool :=
  directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 4) &&
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 5)

theorem ttReverseFiber9Chunk2_ok : ttReverseFiber9Chunk2 = true := by
  decide

def ttReverseFiber9Chunk3 : Bool :=
  directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 6) &&
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 7)

theorem ttReverseFiber9Chunk3_ok : ttReverseFiber9Chunk3 = true := by
  decide

def ttReverseFiber10Chunk0 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 0) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 1)

theorem ttReverseFiber10Chunk0_ok : ttReverseFiber10Chunk0 = true := by
  decide

def ttReverseFiber10Chunk1 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 2) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 3)

theorem ttReverseFiber10Chunk1_ok : ttReverseFiber10Chunk1 = true := by
  decide

def ttReverseFiber10Chunk2 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 4) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 5)

theorem ttReverseFiber10Chunk2_ok : ttReverseFiber10Chunk2 = true := by
  decide

def ttReverseFiber10Chunk3 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 6) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 7)

theorem ttReverseFiber10Chunk3_ok : ttReverseFiber10Chunk3 = true := by
  decide

def ttReverseFiber10Chunk4 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 8) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 9)

theorem ttReverseFiber10Chunk4_ok : ttReverseFiber10Chunk4 = true := by
  decide

def ttReverseFiber10Chunk5 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 10) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 11)

theorem ttReverseFiber10Chunk5_ok : ttReverseFiber10Chunk5 = true := by
  decide

def ttReverseFiber10Chunk6 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 12) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 13)

theorem ttReverseFiber10Chunk6_ok : ttReverseFiber10Chunk6 = true := by
  decide

def ttReverseFiber10Chunk7 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 14) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 15)

theorem ttReverseFiber10Chunk7_ok : ttReverseFiber10Chunk7 = true := by
  decide

def ttReverseFiber10Chunk8 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 16) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 17)

theorem ttReverseFiber10Chunk8_ok : ttReverseFiber10Chunk8 = true := by
  decide

def ttReverseFiber10Chunk9 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 18) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 19)

theorem ttReverseFiber10Chunk9_ok : ttReverseFiber10Chunk9 = true := by
  decide

def ttReverseFiber10Chunk10 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 20) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 21)

theorem ttReverseFiber10Chunk10_ok : ttReverseFiber10Chunk10 = true := by
  decide

def ttReverseFiber10Chunk11 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 22) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 23)

theorem ttReverseFiber10Chunk11_ok : ttReverseFiber10Chunk11 = true := by
  decide

def ttReverseFiber10Chunk12 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 24) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 25)

theorem ttReverseFiber10Chunk12_ok : ttReverseFiber10Chunk12 = true := by
  decide

def ttReverseFiber10Chunk13 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 26) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 27)

theorem ttReverseFiber10Chunk13_ok : ttReverseFiber10Chunk13 = true := by
  decide

def ttReverseFiber10Chunk14 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 28) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 29)

theorem ttReverseFiber10Chunk14_ok : ttReverseFiber10Chunk14 = true := by
  decide

def ttReverseFiber10Chunk15 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 30) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 31)

theorem ttReverseFiber10Chunk15_ok : ttReverseFiber10Chunk15 = true := by
  decide

def ttReverseFiber10Chunk16 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 32) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 33)

theorem ttReverseFiber10Chunk16_ok : ttReverseFiber10Chunk16 = true := by
  decide

def ttReverseFiber10Chunk17 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 34) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 35)

theorem ttReverseFiber10Chunk17_ok : ttReverseFiber10Chunk17 = true := by
  decide

def ttReverseFiber10Chunk18 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 36) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 37)

theorem ttReverseFiber10Chunk18_ok : ttReverseFiber10Chunk18 = true := by
  decide

def ttReverseFiber10Chunk19 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 38) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 39)

theorem ttReverseFiber10Chunk19_ok : ttReverseFiber10Chunk19 = true := by
  decide

def ttReverseFiber10Chunk20 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 40) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 41)

theorem ttReverseFiber10Chunk20_ok : ttReverseFiber10Chunk20 = true := by
  decide

def ttReverseFiber10Chunk21 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 42) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 43)

theorem ttReverseFiber10Chunk21_ok : ttReverseFiber10Chunk21 = true := by
  decide

def ttReverseFiber10Chunk22 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 44) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 45)

theorem ttReverseFiber10Chunk22_ok : ttReverseFiber10Chunk22 = true := by
  decide

def ttReverseFiber10Chunk23 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 46) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 47)

theorem ttReverseFiber10Chunk23_ok : ttReverseFiber10Chunk23 = true := by
  decide

def ttReverseFiber10Chunk24 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 48) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 49)

theorem ttReverseFiber10Chunk24_ok : ttReverseFiber10Chunk24 = true := by
  decide

def ttReverseFiber10Chunk25 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 50) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 51)

theorem ttReverseFiber10Chunk25_ok : ttReverseFiber10Chunk25 = true := by
  decide

def ttReverseFiber10Chunk26 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 52) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 53)

theorem ttReverseFiber10Chunk26_ok : ttReverseFiber10Chunk26 = true := by
  decide

def ttReverseFiber10Chunk27 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 54) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 55)

theorem ttReverseFiber10Chunk27_ok : ttReverseFiber10Chunk27 = true := by
  decide

def ttReverseFiber10Chunk28 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 56) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 57)

theorem ttReverseFiber10Chunk28_ok : ttReverseFiber10Chunk28 = true := by
  decide

def ttReverseFiber10Chunk29 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 58) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 59)

theorem ttReverseFiber10Chunk29_ok : ttReverseFiber10Chunk29 = true := by
  decide

def ttReverseFiber10Chunk30 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 60) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 61)

theorem ttReverseFiber10Chunk30_ok : ttReverseFiber10Chunk30 = true := by
  decide

def ttReverseFiber10Chunk31 : Bool :=
  directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 62) &&
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 63)

theorem ttReverseFiber10Chunk31_ok : ttReverseFiber10Chunk31 = true := by
  decide

def ttReverseFiber11Chunk0 : Bool :=
  directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 0) &&
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 1)

theorem ttReverseFiber11Chunk0_ok : ttReverseFiber11Chunk0 = true := by
  decide

def ttReverseFiber11Chunk1 : Bool :=
  directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 2) &&
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 3)

theorem ttReverseFiber11Chunk1_ok : ttReverseFiber11Chunk1 = true := by
  decide

def ttReverseFiber11Chunk2 : Bool :=
  directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 4) &&
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 5)

theorem ttReverseFiber11Chunk2_ok : ttReverseFiber11Chunk2 = true := by
  decide

def ttReverseFiber11Chunk3 : Bool :=
  directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 6) &&
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 7)

theorem ttReverseFiber11Chunk3_ok : ttReverseFiber11Chunk3 = true := by
  decide

def ttReverseFiber18Chunk0 : Bool :=
  directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 0) &&
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 1)

theorem ttReverseFiber18Chunk0_ok : ttReverseFiber18Chunk0 = true := by
  decide

def ttReverseFiber18Chunk1 : Bool :=
  directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 2) &&
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 3)

theorem ttReverseFiber18Chunk1_ok : ttReverseFiber18Chunk1 = true := by
  decide

def ttReverseFiber18Chunk2 : Bool :=
  directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 4) &&
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 5)

theorem ttReverseFiber18Chunk2_ok : ttReverseFiber18Chunk2 = true := by
  decide

def ttReverseFiber18Chunk3 : Bool :=
  directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 6) &&
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 7)

theorem ttReverseFiber18Chunk3_ok : ttReverseFiber18Chunk3 = true := by
  decide

def ttReverseFiber19Chunk0 : Bool :=
  directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 0) &&
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 1)

theorem ttReverseFiber19Chunk0_ok : ttReverseFiber19Chunk0 = true := by
  decide

def ttReverseFiber19Chunk1 : Bool :=
  directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 2) &&
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 3)

theorem ttReverseFiber19Chunk1_ok : ttReverseFiber19Chunk1 = true := by
  decide

def ttReverseFiber19Chunk2 : Bool :=
  directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 4) &&
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 5)

theorem ttReverseFiber19Chunk2_ok : ttReverseFiber19Chunk2 = true := by
  decide

def ttReverseFiber19Chunk3 : Bool :=
  directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 6) &&
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 7)

theorem ttReverseFiber19Chunk3_ok : ttReverseFiber19Chunk3 = true := by
  decide

def ttReverseFiber20Chunk0 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 0) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 1)

theorem ttReverseFiber20Chunk0_ok : ttReverseFiber20Chunk0 = true := by
  decide

def ttReverseFiber20Chunk1 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 2) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 3)

theorem ttReverseFiber20Chunk1_ok : ttReverseFiber20Chunk1 = true := by
  decide

def ttReverseFiber20Chunk2 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 4) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 5)

theorem ttReverseFiber20Chunk2_ok : ttReverseFiber20Chunk2 = true := by
  decide

def ttReverseFiber20Chunk3 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 6) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 7)

theorem ttReverseFiber20Chunk3_ok : ttReverseFiber20Chunk3 = true := by
  decide

def ttReverseFiber20Chunk4 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 8) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 9)

theorem ttReverseFiber20Chunk4_ok : ttReverseFiber20Chunk4 = true := by
  decide

def ttReverseFiber20Chunk5 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 10) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 11)

theorem ttReverseFiber20Chunk5_ok : ttReverseFiber20Chunk5 = true := by
  decide

def ttReverseFiber20Chunk6 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 12) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 13)

theorem ttReverseFiber20Chunk6_ok : ttReverseFiber20Chunk6 = true := by
  decide

def ttReverseFiber20Chunk7 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 14) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 15)

theorem ttReverseFiber20Chunk7_ok : ttReverseFiber20Chunk7 = true := by
  decide

def ttReverseFiber20Chunk8 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 16) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 17)

theorem ttReverseFiber20Chunk8_ok : ttReverseFiber20Chunk8 = true := by
  decide

def ttReverseFiber20Chunk9 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 18) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 19)

theorem ttReverseFiber20Chunk9_ok : ttReverseFiber20Chunk9 = true := by
  decide

def ttReverseFiber20Chunk10 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 20) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 21)

theorem ttReverseFiber20Chunk10_ok : ttReverseFiber20Chunk10 = true := by
  decide

def ttReverseFiber20Chunk11 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 22) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 23)

theorem ttReverseFiber20Chunk11_ok : ttReverseFiber20Chunk11 = true := by
  decide

def ttReverseFiber20Chunk12 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 24) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 25)

theorem ttReverseFiber20Chunk12_ok : ttReverseFiber20Chunk12 = true := by
  decide

def ttReverseFiber20Chunk13 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 26) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 27)

theorem ttReverseFiber20Chunk13_ok : ttReverseFiber20Chunk13 = true := by
  decide

def ttReverseFiber20Chunk14 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 28) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 29)

theorem ttReverseFiber20Chunk14_ok : ttReverseFiber20Chunk14 = true := by
  decide

def ttReverseFiber20Chunk15 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 30) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 31)

theorem ttReverseFiber20Chunk15_ok : ttReverseFiber20Chunk15 = true := by
  decide

def ttReverseFiber20Chunk16 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 32) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 33)

theorem ttReverseFiber20Chunk16_ok : ttReverseFiber20Chunk16 = true := by
  decide

def ttReverseFiber20Chunk17 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 34) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 35)

theorem ttReverseFiber20Chunk17_ok : ttReverseFiber20Chunk17 = true := by
  decide

def ttReverseFiber20Chunk18 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 36) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 37)

theorem ttReverseFiber20Chunk18_ok : ttReverseFiber20Chunk18 = true := by
  decide

def ttReverseFiber20Chunk19 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 38) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 39)

theorem ttReverseFiber20Chunk19_ok : ttReverseFiber20Chunk19 = true := by
  decide

def ttReverseFiber20Chunk20 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 40) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 41)

theorem ttReverseFiber20Chunk20_ok : ttReverseFiber20Chunk20 = true := by
  decide

def ttReverseFiber20Chunk21 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 42) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 43)

theorem ttReverseFiber20Chunk21_ok : ttReverseFiber20Chunk21 = true := by
  decide

def ttReverseFiber20Chunk22 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 44) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 45)

theorem ttReverseFiber20Chunk22_ok : ttReverseFiber20Chunk22 = true := by
  decide

def ttReverseFiber20Chunk23 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 46) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 47)

theorem ttReverseFiber20Chunk23_ok : ttReverseFiber20Chunk23 = true := by
  decide

def ttReverseFiber20Chunk24 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 48) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 49)

theorem ttReverseFiber20Chunk24_ok : ttReverseFiber20Chunk24 = true := by
  decide

def ttReverseFiber20Chunk25 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 50) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 51)

theorem ttReverseFiber20Chunk25_ok : ttReverseFiber20Chunk25 = true := by
  decide

def ttReverseFiber20Chunk26 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 52) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 53)

theorem ttReverseFiber20Chunk26_ok : ttReverseFiber20Chunk26 = true := by
  decide

def ttReverseFiber20Chunk27 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 54) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 55)

theorem ttReverseFiber20Chunk27_ok : ttReverseFiber20Chunk27 = true := by
  decide

def ttReverseFiber20Chunk28 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 56) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 57)

theorem ttReverseFiber20Chunk28_ok : ttReverseFiber20Chunk28 = true := by
  decide

def ttReverseFiber20Chunk29 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 58) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 59)

theorem ttReverseFiber20Chunk29_ok : ttReverseFiber20Chunk29 = true := by
  decide

def ttReverseFiber20Chunk30 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 60) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 61)

theorem ttReverseFiber20Chunk30_ok : ttReverseFiber20Chunk30 = true := by
  decide

def ttReverseFiber20Chunk31 : Bool :=
  directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 62) &&
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 63)

theorem ttReverseFiber20Chunk31_ok : ttReverseFiber20Chunk31 = true := by
  decide

def ttReverseFiber30Chunk0 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 0) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 1)

theorem ttReverseFiber30Chunk0_ok : ttReverseFiber30Chunk0 = true := by
  decide

def ttReverseFiber30Chunk1 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 2) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 3)

theorem ttReverseFiber30Chunk1_ok : ttReverseFiber30Chunk1 = true := by
  decide

def ttReverseFiber30Chunk2 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 4) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 5)

theorem ttReverseFiber30Chunk2_ok : ttReverseFiber30Chunk2 = true := by
  decide

def ttReverseFiber30Chunk3 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 6) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 7)

theorem ttReverseFiber30Chunk3_ok : ttReverseFiber30Chunk3 = true := by
  decide

def ttReverseFiber30Chunk4 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 8) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 9)

theorem ttReverseFiber30Chunk4_ok : ttReverseFiber30Chunk4 = true := by
  decide

def ttReverseFiber30Chunk5 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 10) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 11)

theorem ttReverseFiber30Chunk5_ok : ttReverseFiber30Chunk5 = true := by
  decide

def ttReverseFiber30Chunk6 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 12) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 13)

theorem ttReverseFiber30Chunk6_ok : ttReverseFiber30Chunk6 = true := by
  decide

def ttReverseFiber30Chunk7 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 14) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 15)

theorem ttReverseFiber30Chunk7_ok : ttReverseFiber30Chunk7 = true := by
  decide

def ttReverseFiber30Chunk8 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 16) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 17)

theorem ttReverseFiber30Chunk8_ok : ttReverseFiber30Chunk8 = true := by
  decide

def ttReverseFiber30Chunk9 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 18) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 19)

theorem ttReverseFiber30Chunk9_ok : ttReverseFiber30Chunk9 = true := by
  decide

def ttReverseFiber30Chunk10 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 20) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 21)

theorem ttReverseFiber30Chunk10_ok : ttReverseFiber30Chunk10 = true := by
  decide

def ttReverseFiber30Chunk11 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 22) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 23)

theorem ttReverseFiber30Chunk11_ok : ttReverseFiber30Chunk11 = true := by
  decide

def ttReverseFiber30Chunk12 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 24) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 25)

theorem ttReverseFiber30Chunk12_ok : ttReverseFiber30Chunk12 = true := by
  decide

def ttReverseFiber30Chunk13 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 26) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 27)

theorem ttReverseFiber30Chunk13_ok : ttReverseFiber30Chunk13 = true := by
  decide

def ttReverseFiber30Chunk14 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 28) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 29)

theorem ttReverseFiber30Chunk14_ok : ttReverseFiber30Chunk14 = true := by
  decide

def ttReverseFiber30Chunk15 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 30) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 31)

theorem ttReverseFiber30Chunk15_ok : ttReverseFiber30Chunk15 = true := by
  decide

def ttReverseFiber30Chunk16 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 32) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 33)

theorem ttReverseFiber30Chunk16_ok : ttReverseFiber30Chunk16 = true := by
  decide

def ttReverseFiber30Chunk17 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 34) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 35)

theorem ttReverseFiber30Chunk17_ok : ttReverseFiber30Chunk17 = true := by
  decide

def ttReverseFiber30Chunk18 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 36) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 37)

theorem ttReverseFiber30Chunk18_ok : ttReverseFiber30Chunk18 = true := by
  decide

def ttReverseFiber30Chunk19 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 38) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 39)

theorem ttReverseFiber30Chunk19_ok : ttReverseFiber30Chunk19 = true := by
  decide

def ttReverseFiber30Chunk20 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 40) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 41)

theorem ttReverseFiber30Chunk20_ok : ttReverseFiber30Chunk20 = true := by
  decide

def ttReverseFiber30Chunk21 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 42) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 43)

theorem ttReverseFiber30Chunk21_ok : ttReverseFiber30Chunk21 = true := by
  decide

def ttReverseFiber30Chunk22 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 44) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 45)

theorem ttReverseFiber30Chunk22_ok : ttReverseFiber30Chunk22 = true := by
  decide

def ttReverseFiber30Chunk23 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 46) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 47)

theorem ttReverseFiber30Chunk23_ok : ttReverseFiber30Chunk23 = true := by
  decide

def ttReverseFiber30Chunk24 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 48) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 49)

theorem ttReverseFiber30Chunk24_ok : ttReverseFiber30Chunk24 = true := by
  decide

def ttReverseFiber30Chunk25 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 50) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 51)

theorem ttReverseFiber30Chunk25_ok : ttReverseFiber30Chunk25 = true := by
  decide

def ttReverseFiber30Chunk26 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 52) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 53)

theorem ttReverseFiber30Chunk26_ok : ttReverseFiber30Chunk26 = true := by
  decide

def ttReverseFiber30Chunk27 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 54) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 55)

theorem ttReverseFiber30Chunk27_ok : ttReverseFiber30Chunk27 = true := by
  decide

def ttReverseFiber30Chunk28 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 56) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 57)

theorem ttReverseFiber30Chunk28_ok : ttReverseFiber30Chunk28 = true := by
  decide

def ttReverseFiber30Chunk29 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 58) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 59)

theorem ttReverseFiber30Chunk29_ok : ttReverseFiber30Chunk29 = true := by
  decide

def ttReverseFiber30Chunk30 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 60) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 61)

theorem ttReverseFiber30Chunk30_ok : ttReverseFiber30Chunk30 = true := by
  decide

def ttReverseFiber30Chunk31 : Bool :=
  directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 62) &&
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 63)

theorem ttReverseFiber30Chunk31_ok : ttReverseFiber30Chunk31 = true := by
  decide

def ttReverseFiber31Chunk0 : Bool :=
  directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 0) &&
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 1)

theorem ttReverseFiber31Chunk0_ok : ttReverseFiber31Chunk0 = true := by
  decide

def ttReverseFiber31Chunk1 : Bool :=
  directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 2) &&
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 3)

theorem ttReverseFiber31Chunk1_ok : ttReverseFiber31Chunk1 = true := by
  decide

def ttReverseFiber31Chunk2 : Bool :=
  directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 4) &&
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 5)

theorem ttReverseFiber31Chunk2_ok : ttReverseFiber31Chunk2 = true := by
  decide

def ttReverseFiber31Chunk3 : Bool :=
  directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 6) &&
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 7)

theorem ttReverseFiber31Chunk3_ok : ttReverseFiber31Chunk3 = true := by
  decide

def ttReverseFiber32Chunk0 : Bool :=
  directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 0) &&
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 1)

theorem ttReverseFiber32Chunk0_ok : ttReverseFiber32Chunk0 = true := by
  decide

def ttReverseFiber32Chunk1 : Bool :=
  directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 2) &&
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 3)

theorem ttReverseFiber32Chunk1_ok : ttReverseFiber32Chunk1 = true := by
  decide

def ttReverseFiber32Chunk2 : Bool :=
  directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 4) &&
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 5)

theorem ttReverseFiber32Chunk2_ok : ttReverseFiber32Chunk2 = true := by
  decide

def ttReverseFiber32Chunk3 : Bool :=
  directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 6) &&
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 7)

theorem ttReverseFiber32Chunk3_ok : ttReverseFiber32Chunk3 = true := by
  decide

def ttReverseFiber36Chunk0 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 0) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 1)

theorem ttReverseFiber36Chunk0_ok : ttReverseFiber36Chunk0 = true := by
  decide

def ttReverseFiber36Chunk1 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 2) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 3)

theorem ttReverseFiber36Chunk1_ok : ttReverseFiber36Chunk1 = true := by
  decide

def ttReverseFiber36Chunk2 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 4) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 5)

theorem ttReverseFiber36Chunk2_ok : ttReverseFiber36Chunk2 = true := by
  decide

def ttReverseFiber36Chunk3 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 6) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 7)

theorem ttReverseFiber36Chunk3_ok : ttReverseFiber36Chunk3 = true := by
  decide

def ttReverseFiber36Chunk4 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 8) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 9)

theorem ttReverseFiber36Chunk4_ok : ttReverseFiber36Chunk4 = true := by
  decide

def ttReverseFiber36Chunk5 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 10) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 11)

theorem ttReverseFiber36Chunk5_ok : ttReverseFiber36Chunk5 = true := by
  decide

def ttReverseFiber36Chunk6 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 12) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 13)

theorem ttReverseFiber36Chunk6_ok : ttReverseFiber36Chunk6 = true := by
  decide

def ttReverseFiber36Chunk7 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 14) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 15)

theorem ttReverseFiber36Chunk7_ok : ttReverseFiber36Chunk7 = true := by
  decide

def ttReverseFiber36Chunk8 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 16) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 17)

theorem ttReverseFiber36Chunk8_ok : ttReverseFiber36Chunk8 = true := by
  decide

def ttReverseFiber36Chunk9 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 18) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 19)

theorem ttReverseFiber36Chunk9_ok : ttReverseFiber36Chunk9 = true := by
  decide

def ttReverseFiber36Chunk10 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 20) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 21)

theorem ttReverseFiber36Chunk10_ok : ttReverseFiber36Chunk10 = true := by
  decide

def ttReverseFiber36Chunk11 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 22) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 23)

theorem ttReverseFiber36Chunk11_ok : ttReverseFiber36Chunk11 = true := by
  decide

def ttReverseFiber36Chunk12 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 24) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 25)

theorem ttReverseFiber36Chunk12_ok : ttReverseFiber36Chunk12 = true := by
  decide

def ttReverseFiber36Chunk13 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 26) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 27)

theorem ttReverseFiber36Chunk13_ok : ttReverseFiber36Chunk13 = true := by
  decide

def ttReverseFiber36Chunk14 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 28) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 29)

theorem ttReverseFiber36Chunk14_ok : ttReverseFiber36Chunk14 = true := by
  decide

def ttReverseFiber36Chunk15 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 30) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 31)

theorem ttReverseFiber36Chunk15_ok : ttReverseFiber36Chunk15 = true := by
  decide

def ttReverseFiber36Chunk16 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 32) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 33)

theorem ttReverseFiber36Chunk16_ok : ttReverseFiber36Chunk16 = true := by
  decide

def ttReverseFiber36Chunk17 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 34) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 35)

theorem ttReverseFiber36Chunk17_ok : ttReverseFiber36Chunk17 = true := by
  decide

def ttReverseFiber36Chunk18 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 36) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 37)

theorem ttReverseFiber36Chunk18_ok : ttReverseFiber36Chunk18 = true := by
  decide

def ttReverseFiber36Chunk19 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 38) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 39)

theorem ttReverseFiber36Chunk19_ok : ttReverseFiber36Chunk19 = true := by
  decide

def ttReverseFiber36Chunk20 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 40) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 41)

theorem ttReverseFiber36Chunk20_ok : ttReverseFiber36Chunk20 = true := by
  decide

def ttReverseFiber36Chunk21 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 42) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 43)

theorem ttReverseFiber36Chunk21_ok : ttReverseFiber36Chunk21 = true := by
  decide

def ttReverseFiber36Chunk22 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 44) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 45)

theorem ttReverseFiber36Chunk22_ok : ttReverseFiber36Chunk22 = true := by
  decide

def ttReverseFiber36Chunk23 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 46) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 47)

theorem ttReverseFiber36Chunk23_ok : ttReverseFiber36Chunk23 = true := by
  decide

def ttReverseFiber36Chunk24 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 48) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 49)

theorem ttReverseFiber36Chunk24_ok : ttReverseFiber36Chunk24 = true := by
  decide

def ttReverseFiber36Chunk25 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 50) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 51)

theorem ttReverseFiber36Chunk25_ok : ttReverseFiber36Chunk25 = true := by
  decide

def ttReverseFiber36Chunk26 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 52) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 53)

theorem ttReverseFiber36Chunk26_ok : ttReverseFiber36Chunk26 = true := by
  decide

def ttReverseFiber36Chunk27 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 54) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 55)

theorem ttReverseFiber36Chunk27_ok : ttReverseFiber36Chunk27 = true := by
  decide

def ttReverseFiber36Chunk28 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 56) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 57)

theorem ttReverseFiber36Chunk28_ok : ttReverseFiber36Chunk28 = true := by
  decide

def ttReverseFiber36Chunk29 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 58) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 59)

theorem ttReverseFiber36Chunk29_ok : ttReverseFiber36Chunk29 = true := by
  decide

def ttReverseFiber36Chunk30 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 60) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 61)

theorem ttReverseFiber36Chunk30_ok : ttReverseFiber36Chunk30 = true := by
  decide

def ttReverseFiber36Chunk31 : Bool :=
  directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 62) &&
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 63)

theorem ttReverseFiber36Chunk31_ok : ttReverseFiber36Chunk31 = true := by
  decide

def ttReverseFiber37Chunk0 : Bool :=
  directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 0) &&
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 1)

theorem ttReverseFiber37Chunk0_ok : ttReverseFiber37Chunk0 = true := by
  decide

def ttReverseFiber37Chunk1 : Bool :=
  directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 2) &&
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 3)

theorem ttReverseFiber37Chunk1_ok : ttReverseFiber37Chunk1 = true := by
  decide

def ttReverseFiber37Chunk2 : Bool :=
  directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 4) &&
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 5)

theorem ttReverseFiber37Chunk2_ok : ttReverseFiber37Chunk2 = true := by
  decide

def ttReverseFiber37Chunk3 : Bool :=
  directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 6) &&
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 7)

theorem ttReverseFiber37Chunk3_ok : ttReverseFiber37Chunk3 = true := by
  decide

def ttReverseFiber38Chunk0 : Bool :=
  directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 0) &&
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 1)

theorem ttReverseFiber38Chunk0_ok : ttReverseFiber38Chunk0 = true := by
  decide

def ttReverseFiber38Chunk1 : Bool :=
  directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 2) &&
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 3)

theorem ttReverseFiber38Chunk1_ok : ttReverseFiber38Chunk1 = true := by
  decide

def ttReverseFiber38Chunk2 : Bool :=
  directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 4) &&
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 5)

theorem ttReverseFiber38Chunk2_ok : ttReverseFiber38Chunk2 = true := by
  decide

def ttReverseFiber38Chunk3 : Bool :=
  directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 6) &&
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 7)

theorem ttReverseFiber38Chunk3_ok : ttReverseFiber38Chunk3 = true := by
  decide

def ttReverseFiber42Chunk0 : Bool :=
  directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 0) &&
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 1)

theorem ttReverseFiber42Chunk0_ok : ttReverseFiber42Chunk0 = true := by
  decide

def ttReverseFiber42Chunk1 : Bool :=
  directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 2) &&
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 3)

theorem ttReverseFiber42Chunk1_ok : ttReverseFiber42Chunk1 = true := by
  decide

def ttReverseFiber42Chunk2 : Bool :=
  directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 4) &&
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 5)

theorem ttReverseFiber42Chunk2_ok : ttReverseFiber42Chunk2 = true := by
  decide

def ttReverseFiber42Chunk3 : Bool :=
  directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 6) &&
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 7)

theorem ttReverseFiber42Chunk3_ok : ttReverseFiber42Chunk3 = true := by
  decide

def ttReverseFiber43Chunk0 : Bool :=
  directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 0) &&
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 1)

theorem ttReverseFiber43Chunk0_ok : ttReverseFiber43Chunk0 = true := by
  decide

def ttReverseFiber43Chunk1 : Bool :=
  directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 2) &&
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 3)

theorem ttReverseFiber43Chunk1_ok : ttReverseFiber43Chunk1 = true := by
  decide

def ttReverseFiber43Chunk2 : Bool :=
  directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 4) &&
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 5)

theorem ttReverseFiber43Chunk2_ok : ttReverseFiber43Chunk2 = true := by
  decide

def ttReverseFiber43Chunk3 : Bool :=
  directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 6) &&
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 7)

theorem ttReverseFiber43Chunk3_ok : ttReverseFiber43Chunk3 = true := by
  decide

def ttReverseFiber44Chunk0 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 0) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 1)

theorem ttReverseFiber44Chunk0_ok : ttReverseFiber44Chunk0 = true := by
  decide

def ttReverseFiber44Chunk1 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 2) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 3)

theorem ttReverseFiber44Chunk1_ok : ttReverseFiber44Chunk1 = true := by
  decide

def ttReverseFiber44Chunk2 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 4) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 5)

theorem ttReverseFiber44Chunk2_ok : ttReverseFiber44Chunk2 = true := by
  decide

def ttReverseFiber44Chunk3 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 6) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 7)

theorem ttReverseFiber44Chunk3_ok : ttReverseFiber44Chunk3 = true := by
  decide

def ttReverseFiber44Chunk4 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 8) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 9)

theorem ttReverseFiber44Chunk4_ok : ttReverseFiber44Chunk4 = true := by
  decide

def ttReverseFiber44Chunk5 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 10) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 11)

theorem ttReverseFiber44Chunk5_ok : ttReverseFiber44Chunk5 = true := by
  decide

def ttReverseFiber44Chunk6 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 12) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 13)

theorem ttReverseFiber44Chunk6_ok : ttReverseFiber44Chunk6 = true := by
  decide

def ttReverseFiber44Chunk7 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 14) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 15)

theorem ttReverseFiber44Chunk7_ok : ttReverseFiber44Chunk7 = true := by
  decide

def ttReverseFiber44Chunk8 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 16) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 17)

theorem ttReverseFiber44Chunk8_ok : ttReverseFiber44Chunk8 = true := by
  decide

def ttReverseFiber44Chunk9 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 18) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 19)

theorem ttReverseFiber44Chunk9_ok : ttReverseFiber44Chunk9 = true := by
  decide

def ttReverseFiber44Chunk10 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 20) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 21)

theorem ttReverseFiber44Chunk10_ok : ttReverseFiber44Chunk10 = true := by
  decide

def ttReverseFiber44Chunk11 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 22) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 23)

theorem ttReverseFiber44Chunk11_ok : ttReverseFiber44Chunk11 = true := by
  decide

def ttReverseFiber44Chunk12 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 24) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 25)

theorem ttReverseFiber44Chunk12_ok : ttReverseFiber44Chunk12 = true := by
  decide

def ttReverseFiber44Chunk13 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 26) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 27)

theorem ttReverseFiber44Chunk13_ok : ttReverseFiber44Chunk13 = true := by
  decide

def ttReverseFiber44Chunk14 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 28) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 29)

theorem ttReverseFiber44Chunk14_ok : ttReverseFiber44Chunk14 = true := by
  decide

def ttReverseFiber44Chunk15 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 30) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 31)

theorem ttReverseFiber44Chunk15_ok : ttReverseFiber44Chunk15 = true := by
  decide

def ttReverseFiber44Chunk16 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 32) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 33)

theorem ttReverseFiber44Chunk16_ok : ttReverseFiber44Chunk16 = true := by
  decide

def ttReverseFiber44Chunk17 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 34) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 35)

theorem ttReverseFiber44Chunk17_ok : ttReverseFiber44Chunk17 = true := by
  decide

def ttReverseFiber44Chunk18 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 36) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 37)

theorem ttReverseFiber44Chunk18_ok : ttReverseFiber44Chunk18 = true := by
  decide

def ttReverseFiber44Chunk19 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 38) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 39)

theorem ttReverseFiber44Chunk19_ok : ttReverseFiber44Chunk19 = true := by
  decide

def ttReverseFiber44Chunk20 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 40) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 41)

theorem ttReverseFiber44Chunk20_ok : ttReverseFiber44Chunk20 = true := by
  decide

def ttReverseFiber44Chunk21 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 42) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 43)

theorem ttReverseFiber44Chunk21_ok : ttReverseFiber44Chunk21 = true := by
  decide

def ttReverseFiber44Chunk22 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 44) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 45)

theorem ttReverseFiber44Chunk22_ok : ttReverseFiber44Chunk22 = true := by
  decide

def ttReverseFiber44Chunk23 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 46) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 47)

theorem ttReverseFiber44Chunk23_ok : ttReverseFiber44Chunk23 = true := by
  decide

def ttReverseFiber44Chunk24 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 48) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 49)

theorem ttReverseFiber44Chunk24_ok : ttReverseFiber44Chunk24 = true := by
  decide

def ttReverseFiber44Chunk25 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 50) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 51)

theorem ttReverseFiber44Chunk25_ok : ttReverseFiber44Chunk25 = true := by
  decide

def ttReverseFiber44Chunk26 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 52) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 53)

theorem ttReverseFiber44Chunk26_ok : ttReverseFiber44Chunk26 = true := by
  decide

def ttReverseFiber44Chunk27 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 54) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 55)

theorem ttReverseFiber44Chunk27_ok : ttReverseFiber44Chunk27 = true := by
  decide

def ttReverseFiber44Chunk28 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 56) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 57)

theorem ttReverseFiber44Chunk28_ok : ttReverseFiber44Chunk28 = true := by
  decide

def ttReverseFiber44Chunk29 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 58) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 59)

theorem ttReverseFiber44Chunk29_ok : ttReverseFiber44Chunk29 = true := by
  decide

def ttReverseFiber44Chunk30 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 60) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 61)

theorem ttReverseFiber44Chunk30_ok : ttReverseFiber44Chunk30 = true := by
  decide

def ttReverseFiber44Chunk31 : Bool :=
  directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 62) &&
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 63)

theorem ttReverseFiber44Chunk31_ok : ttReverseFiber44Chunk31 = true := by
  decide

def ttReverseFiber48Chunk0 : Bool :=
  directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 0) &&
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 1)

theorem ttReverseFiber48Chunk0_ok : ttReverseFiber48Chunk0 = true := by
  decide

def ttReverseFiber48Chunk1 : Bool :=
  directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 2) &&
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 3)

theorem ttReverseFiber48Chunk1_ok : ttReverseFiber48Chunk1 = true := by
  decide

def ttReverseFiber48Chunk2 : Bool :=
  directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 4) &&
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 5)

theorem ttReverseFiber48Chunk2_ok : ttReverseFiber48Chunk2 = true := by
  decide

def ttReverseFiber48Chunk3 : Bool :=
  directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 6) &&
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 7)

theorem ttReverseFiber48Chunk3_ok : ttReverseFiber48Chunk3 = true := by
  decide

def ttReverseFiber49Chunk0 : Bool :=
  directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 0) &&
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 1)

theorem ttReverseFiber49Chunk0_ok : ttReverseFiber49Chunk0 = true := by
  decide

def ttReverseFiber49Chunk1 : Bool :=
  directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 2) &&
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 3)

theorem ttReverseFiber49Chunk1_ok : ttReverseFiber49Chunk1 = true := by
  decide

def ttReverseFiber49Chunk2 : Bool :=
  directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 4) &&
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 5)

theorem ttReverseFiber49Chunk2_ok : ttReverseFiber49Chunk2 = true := by
  decide

def ttReverseFiber49Chunk3 : Bool :=
  directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 6) &&
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 7)

theorem ttReverseFiber49Chunk3_ok : ttReverseFiber49Chunk3 = true := by
  decide

def ttReverseFiber50Chunk0 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 0) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 1)

theorem ttReverseFiber50Chunk0_ok : ttReverseFiber50Chunk0 = true := by
  decide

def ttReverseFiber50Chunk1 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 2) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 3)

theorem ttReverseFiber50Chunk1_ok : ttReverseFiber50Chunk1 = true := by
  decide

def ttReverseFiber50Chunk2 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 4) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 5)

theorem ttReverseFiber50Chunk2_ok : ttReverseFiber50Chunk2 = true := by
  decide

def ttReverseFiber50Chunk3 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 6) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 7)

theorem ttReverseFiber50Chunk3_ok : ttReverseFiber50Chunk3 = true := by
  decide

def ttReverseFiber50Chunk4 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 8) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 9)

theorem ttReverseFiber50Chunk4_ok : ttReverseFiber50Chunk4 = true := by
  decide

def ttReverseFiber50Chunk5 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 10) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 11)

theorem ttReverseFiber50Chunk5_ok : ttReverseFiber50Chunk5 = true := by
  decide

def ttReverseFiber50Chunk6 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 12) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 13)

theorem ttReverseFiber50Chunk6_ok : ttReverseFiber50Chunk6 = true := by
  decide

def ttReverseFiber50Chunk7 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 14) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 15)

theorem ttReverseFiber50Chunk7_ok : ttReverseFiber50Chunk7 = true := by
  decide

def ttReverseFiber50Chunk8 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 16) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 17)

theorem ttReverseFiber50Chunk8_ok : ttReverseFiber50Chunk8 = true := by
  decide

def ttReverseFiber50Chunk9 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 18) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 19)

theorem ttReverseFiber50Chunk9_ok : ttReverseFiber50Chunk9 = true := by
  decide

def ttReverseFiber50Chunk10 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 20) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 21)

theorem ttReverseFiber50Chunk10_ok : ttReverseFiber50Chunk10 = true := by
  decide

def ttReverseFiber50Chunk11 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 22) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 23)

theorem ttReverseFiber50Chunk11_ok : ttReverseFiber50Chunk11 = true := by
  decide

def ttReverseFiber50Chunk12 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 24) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 25)

theorem ttReverseFiber50Chunk12_ok : ttReverseFiber50Chunk12 = true := by
  decide

def ttReverseFiber50Chunk13 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 26) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 27)

theorem ttReverseFiber50Chunk13_ok : ttReverseFiber50Chunk13 = true := by
  decide

def ttReverseFiber50Chunk14 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 28) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 29)

theorem ttReverseFiber50Chunk14_ok : ttReverseFiber50Chunk14 = true := by
  decide

def ttReverseFiber50Chunk15 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 30) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 31)

theorem ttReverseFiber50Chunk15_ok : ttReverseFiber50Chunk15 = true := by
  decide

def ttReverseFiber50Chunk16 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 32) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 33)

theorem ttReverseFiber50Chunk16_ok : ttReverseFiber50Chunk16 = true := by
  decide

def ttReverseFiber50Chunk17 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 34) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 35)

theorem ttReverseFiber50Chunk17_ok : ttReverseFiber50Chunk17 = true := by
  decide

def ttReverseFiber50Chunk18 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 36) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 37)

theorem ttReverseFiber50Chunk18_ok : ttReverseFiber50Chunk18 = true := by
  decide

def ttReverseFiber50Chunk19 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 38) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 39)

theorem ttReverseFiber50Chunk19_ok : ttReverseFiber50Chunk19 = true := by
  decide

def ttReverseFiber50Chunk20 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 40) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 41)

theorem ttReverseFiber50Chunk20_ok : ttReverseFiber50Chunk20 = true := by
  decide

def ttReverseFiber50Chunk21 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 42) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 43)

theorem ttReverseFiber50Chunk21_ok : ttReverseFiber50Chunk21 = true := by
  decide

def ttReverseFiber50Chunk22 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 44) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 45)

theorem ttReverseFiber50Chunk22_ok : ttReverseFiber50Chunk22 = true := by
  decide

def ttReverseFiber50Chunk23 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 46) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 47)

theorem ttReverseFiber50Chunk23_ok : ttReverseFiber50Chunk23 = true := by
  decide

def ttReverseFiber50Chunk24 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 48) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 49)

theorem ttReverseFiber50Chunk24_ok : ttReverseFiber50Chunk24 = true := by
  decide

def ttReverseFiber50Chunk25 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 50) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 51)

theorem ttReverseFiber50Chunk25_ok : ttReverseFiber50Chunk25 = true := by
  decide

def ttReverseFiber50Chunk26 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 52) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 53)

theorem ttReverseFiber50Chunk26_ok : ttReverseFiber50Chunk26 = true := by
  decide

def ttReverseFiber50Chunk27 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 54) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 55)

theorem ttReverseFiber50Chunk27_ok : ttReverseFiber50Chunk27 = true := by
  decide

def ttReverseFiber50Chunk28 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 56) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 57)

theorem ttReverseFiber50Chunk28_ok : ttReverseFiber50Chunk28 = true := by
  decide

def ttReverseFiber50Chunk29 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 58) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 59)

theorem ttReverseFiber50Chunk29_ok : ttReverseFiber50Chunk29 = true := by
  decide

def ttReverseFiber50Chunk30 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 60) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 61)

theorem ttReverseFiber50Chunk30_ok : ttReverseFiber50Chunk30 = true := by
  decide

def ttReverseFiber50Chunk31 : Bool :=
  directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 62) &&
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 63)

theorem ttReverseFiber50Chunk31_ok : ttReverseFiber50Chunk31 = true := by
  decide

def ttReverseFiber60Chunk0 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 0) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 1)

theorem ttReverseFiber60Chunk0_ok : ttReverseFiber60Chunk0 = true := by
  decide

def ttReverseFiber60Chunk1 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 2) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 3)

theorem ttReverseFiber60Chunk1_ok : ttReverseFiber60Chunk1 = true := by
  decide

def ttReverseFiber60Chunk2 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 4) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 5)

theorem ttReverseFiber60Chunk2_ok : ttReverseFiber60Chunk2 = true := by
  decide

def ttReverseFiber60Chunk3 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 6) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 7)

theorem ttReverseFiber60Chunk3_ok : ttReverseFiber60Chunk3 = true := by
  decide

def ttReverseFiber60Chunk4 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 8) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 9)

theorem ttReverseFiber60Chunk4_ok : ttReverseFiber60Chunk4 = true := by
  decide

def ttReverseFiber60Chunk5 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 10) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 11)

theorem ttReverseFiber60Chunk5_ok : ttReverseFiber60Chunk5 = true := by
  decide

def ttReverseFiber60Chunk6 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 12) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 13)

theorem ttReverseFiber60Chunk6_ok : ttReverseFiber60Chunk6 = true := by
  decide

def ttReverseFiber60Chunk7 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 14) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 15)

theorem ttReverseFiber60Chunk7_ok : ttReverseFiber60Chunk7 = true := by
  decide

def ttReverseFiber60Chunk8 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 16) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 17)

theorem ttReverseFiber60Chunk8_ok : ttReverseFiber60Chunk8 = true := by
  decide

def ttReverseFiber60Chunk9 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 18) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 19)

theorem ttReverseFiber60Chunk9_ok : ttReverseFiber60Chunk9 = true := by
  decide

def ttReverseFiber60Chunk10 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 20) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 21)

theorem ttReverseFiber60Chunk10_ok : ttReverseFiber60Chunk10 = true := by
  decide

def ttReverseFiber60Chunk11 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 22) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 23)

theorem ttReverseFiber60Chunk11_ok : ttReverseFiber60Chunk11 = true := by
  decide

def ttReverseFiber60Chunk12 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 24) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 25)

theorem ttReverseFiber60Chunk12_ok : ttReverseFiber60Chunk12 = true := by
  decide

def ttReverseFiber60Chunk13 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 26) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 27)

theorem ttReverseFiber60Chunk13_ok : ttReverseFiber60Chunk13 = true := by
  decide

def ttReverseFiber60Chunk14 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 28) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 29)

theorem ttReverseFiber60Chunk14_ok : ttReverseFiber60Chunk14 = true := by
  decide

def ttReverseFiber60Chunk15 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 30) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 31)

theorem ttReverseFiber60Chunk15_ok : ttReverseFiber60Chunk15 = true := by
  decide

def ttReverseFiber60Chunk16 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 32) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 33)

theorem ttReverseFiber60Chunk16_ok : ttReverseFiber60Chunk16 = true := by
  decide

def ttReverseFiber60Chunk17 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 34) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 35)

theorem ttReverseFiber60Chunk17_ok : ttReverseFiber60Chunk17 = true := by
  decide

def ttReverseFiber60Chunk18 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 36) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 37)

theorem ttReverseFiber60Chunk18_ok : ttReverseFiber60Chunk18 = true := by
  decide

def ttReverseFiber60Chunk19 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 38) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 39)

theorem ttReverseFiber60Chunk19_ok : ttReverseFiber60Chunk19 = true := by
  decide

def ttReverseFiber60Chunk20 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 40) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 41)

theorem ttReverseFiber60Chunk20_ok : ttReverseFiber60Chunk20 = true := by
  decide

def ttReverseFiber60Chunk21 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 42) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 43)

theorem ttReverseFiber60Chunk21_ok : ttReverseFiber60Chunk21 = true := by
  decide

def ttReverseFiber60Chunk22 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 44) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 45)

theorem ttReverseFiber60Chunk22_ok : ttReverseFiber60Chunk22 = true := by
  decide

def ttReverseFiber60Chunk23 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 46) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 47)

theorem ttReverseFiber60Chunk23_ok : ttReverseFiber60Chunk23 = true := by
  decide

def ttReverseFiber60Chunk24 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 48) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 49)

theorem ttReverseFiber60Chunk24_ok : ttReverseFiber60Chunk24 = true := by
  decide

def ttReverseFiber60Chunk25 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 50) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 51)

theorem ttReverseFiber60Chunk25_ok : ttReverseFiber60Chunk25 = true := by
  decide

def ttReverseFiber60Chunk26 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 52) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 53)

theorem ttReverseFiber60Chunk26_ok : ttReverseFiber60Chunk26 = true := by
  decide

def ttReverseFiber60Chunk27 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 54) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 55)

theorem ttReverseFiber60Chunk27_ok : ttReverseFiber60Chunk27 = true := by
  decide

def ttReverseFiber60Chunk28 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 56) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 57)

theorem ttReverseFiber60Chunk28_ok : ttReverseFiber60Chunk28 = true := by
  decide

def ttReverseFiber60Chunk29 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 58) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 59)

theorem ttReverseFiber60Chunk29_ok : ttReverseFiber60Chunk29 = true := by
  decide

def ttReverseFiber60Chunk30 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 60) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 61)

theorem ttReverseFiber60Chunk30_ok : ttReverseFiber60Chunk30 = true := by
  decide

def ttReverseFiber60Chunk31 : Bool :=
  directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 62) &&
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 63)

theorem ttReverseFiber60Chunk31_ok : ttReverseFiber60Chunk31 = true := by
  decide

def ttReverseFiber61Chunk0 : Bool :=
  directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 0) &&
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 1)

theorem ttReverseFiber61Chunk0_ok : ttReverseFiber61Chunk0 = true := by
  decide

def ttReverseFiber61Chunk1 : Bool :=
  directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 2) &&
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 3)

theorem ttReverseFiber61Chunk1_ok : ttReverseFiber61Chunk1 = true := by
  decide

def ttReverseFiber61Chunk2 : Bool :=
  directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 4) &&
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 5)

theorem ttReverseFiber61Chunk2_ok : ttReverseFiber61Chunk2 = true := by
  decide

def ttReverseFiber61Chunk3 : Bool :=
  directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 6) &&
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 7)

theorem ttReverseFiber61Chunk3_ok : ttReverseFiber61Chunk3 = true := by
  decide

def ttReverseFiber62Chunk0 : Bool :=
  directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 0) &&
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 1)

theorem ttReverseFiber62Chunk0_ok : ttReverseFiber62Chunk0 = true := by
  decide

def ttReverseFiber62Chunk1 : Bool :=
  directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 2) &&
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 3)

theorem ttReverseFiber62Chunk1_ok : ttReverseFiber62Chunk1 = true := by
  decide

def ttReverseFiber62Chunk2 : Bool :=
  directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 4) &&
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 5)

theorem ttReverseFiber62Chunk2_ok : ttReverseFiber62Chunk2 = true := by
  decide

def ttReverseFiber62Chunk3 : Bool :=
  directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 6) &&
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 7)

theorem ttReverseFiber62Chunk3_ok : ttReverseFiber62Chunk3 = true := by
  decide

def ttReverseFiber69Chunk0 : Bool :=
  directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 0) &&
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 1)

theorem ttReverseFiber69Chunk0_ok : ttReverseFiber69Chunk0 = true := by
  decide

def ttReverseFiber69Chunk1 : Bool :=
  directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 2) &&
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 3)

theorem ttReverseFiber69Chunk1_ok : ttReverseFiber69Chunk1 = true := by
  decide

def ttReverseFiber69Chunk2 : Bool :=
  directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 4) &&
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 5)

theorem ttReverseFiber69Chunk2_ok : ttReverseFiber69Chunk2 = true := by
  decide

def ttReverseFiber69Chunk3 : Bool :=
  directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 6) &&
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 7)

theorem ttReverseFiber69Chunk3_ok : ttReverseFiber69Chunk3 = true := by
  decide

def ttReverseFiber70Chunk0 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 0) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 1)

theorem ttReverseFiber70Chunk0_ok : ttReverseFiber70Chunk0 = true := by
  decide

def ttReverseFiber70Chunk1 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 2) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 3)

theorem ttReverseFiber70Chunk1_ok : ttReverseFiber70Chunk1 = true := by
  decide

def ttReverseFiber70Chunk2 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 4) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 5)

theorem ttReverseFiber70Chunk2_ok : ttReverseFiber70Chunk2 = true := by
  decide

def ttReverseFiber70Chunk3 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 6) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 7)

theorem ttReverseFiber70Chunk3_ok : ttReverseFiber70Chunk3 = true := by
  decide

def ttReverseFiber70Chunk4 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 8) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 9)

theorem ttReverseFiber70Chunk4_ok : ttReverseFiber70Chunk4 = true := by
  decide

def ttReverseFiber70Chunk5 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 10) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 11)

theorem ttReverseFiber70Chunk5_ok : ttReverseFiber70Chunk5 = true := by
  decide

def ttReverseFiber70Chunk6 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 12) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 13)

theorem ttReverseFiber70Chunk6_ok : ttReverseFiber70Chunk6 = true := by
  decide

def ttReverseFiber70Chunk7 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 14) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 15)

theorem ttReverseFiber70Chunk7_ok : ttReverseFiber70Chunk7 = true := by
  decide

def ttReverseFiber70Chunk8 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 16) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 17)

theorem ttReverseFiber70Chunk8_ok : ttReverseFiber70Chunk8 = true := by
  decide

def ttReverseFiber70Chunk9 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 18) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 19)

theorem ttReverseFiber70Chunk9_ok : ttReverseFiber70Chunk9 = true := by
  decide

def ttReverseFiber70Chunk10 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 20) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 21)

theorem ttReverseFiber70Chunk10_ok : ttReverseFiber70Chunk10 = true := by
  decide

def ttReverseFiber70Chunk11 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 22) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 23)

theorem ttReverseFiber70Chunk11_ok : ttReverseFiber70Chunk11 = true := by
  decide

def ttReverseFiber70Chunk12 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 24) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 25)

theorem ttReverseFiber70Chunk12_ok : ttReverseFiber70Chunk12 = true := by
  decide

def ttReverseFiber70Chunk13 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 26) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 27)

theorem ttReverseFiber70Chunk13_ok : ttReverseFiber70Chunk13 = true := by
  decide

def ttReverseFiber70Chunk14 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 28) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 29)

theorem ttReverseFiber70Chunk14_ok : ttReverseFiber70Chunk14 = true := by
  decide

def ttReverseFiber70Chunk15 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 30) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 31)

theorem ttReverseFiber70Chunk15_ok : ttReverseFiber70Chunk15 = true := by
  decide

def ttReverseFiber70Chunk16 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 32) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 33)

theorem ttReverseFiber70Chunk16_ok : ttReverseFiber70Chunk16 = true := by
  decide

def ttReverseFiber70Chunk17 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 34) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 35)

theorem ttReverseFiber70Chunk17_ok : ttReverseFiber70Chunk17 = true := by
  decide

def ttReverseFiber70Chunk18 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 36) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 37)

theorem ttReverseFiber70Chunk18_ok : ttReverseFiber70Chunk18 = true := by
  decide

def ttReverseFiber70Chunk19 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 38) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 39)

theorem ttReverseFiber70Chunk19_ok : ttReverseFiber70Chunk19 = true := by
  decide

def ttReverseFiber70Chunk20 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 40) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 41)

theorem ttReverseFiber70Chunk20_ok : ttReverseFiber70Chunk20 = true := by
  decide

def ttReverseFiber70Chunk21 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 42) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 43)

theorem ttReverseFiber70Chunk21_ok : ttReverseFiber70Chunk21 = true := by
  decide

def ttReverseFiber70Chunk22 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 44) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 45)

theorem ttReverseFiber70Chunk22_ok : ttReverseFiber70Chunk22 = true := by
  decide

def ttReverseFiber70Chunk23 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 46) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 47)

theorem ttReverseFiber70Chunk23_ok : ttReverseFiber70Chunk23 = true := by
  decide

def ttReverseFiber70Chunk24 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 48) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 49)

theorem ttReverseFiber70Chunk24_ok : ttReverseFiber70Chunk24 = true := by
  decide

def ttReverseFiber70Chunk25 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 50) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 51)

theorem ttReverseFiber70Chunk25_ok : ttReverseFiber70Chunk25 = true := by
  decide

def ttReverseFiber70Chunk26 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 52) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 53)

theorem ttReverseFiber70Chunk26_ok : ttReverseFiber70Chunk26 = true := by
  decide

def ttReverseFiber70Chunk27 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 54) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 55)

theorem ttReverseFiber70Chunk27_ok : ttReverseFiber70Chunk27 = true := by
  decide

def ttReverseFiber70Chunk28 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 56) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 57)

theorem ttReverseFiber70Chunk28_ok : ttReverseFiber70Chunk28 = true := by
  decide

def ttReverseFiber70Chunk29 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 58) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 59)

theorem ttReverseFiber70Chunk29_ok : ttReverseFiber70Chunk29 = true := by
  decide

def ttReverseFiber70Chunk30 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 60) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 61)

theorem ttReverseFiber70Chunk30_ok : ttReverseFiber70Chunk30 = true := by
  decide

def ttReverseFiber70Chunk31 : Bool :=
  directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 62) &&
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 63)

theorem ttReverseFiber70Chunk31_ok : ttReverseFiber70Chunk31 = true := by
  decide

def ttReverseFiber71Chunk0 : Bool :=
  directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 0) &&
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 1)

theorem ttReverseFiber71Chunk0_ok : ttReverseFiber71Chunk0 = true := by
  decide

def ttReverseFiber71Chunk1 : Bool :=
  directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 2) &&
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 3)

theorem ttReverseFiber71Chunk1_ok : ttReverseFiber71Chunk1 = true := by
  decide

def ttReverseFiber71Chunk2 : Bool :=
  directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 4) &&
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 5)

theorem ttReverseFiber71Chunk2_ok : ttReverseFiber71Chunk2 = true := by
  decide

def ttReverseFiber71Chunk3 : Bool :=
  directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 6) &&
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 7)

theorem ttReverseFiber71Chunk3_ok : ttReverseFiber71Chunk3 = true := by
  decide

def ttReverseFiber72Chunk0 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 0) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 1)

theorem ttReverseFiber72Chunk0_ok : ttReverseFiber72Chunk0 = true := by
  decide

def ttReverseFiber72Chunk1 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 2) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 3)

theorem ttReverseFiber72Chunk1_ok : ttReverseFiber72Chunk1 = true := by
  decide

def ttReverseFiber72Chunk2 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 4) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 5)

theorem ttReverseFiber72Chunk2_ok : ttReverseFiber72Chunk2 = true := by
  decide

def ttReverseFiber72Chunk3 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 6) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 7)

theorem ttReverseFiber72Chunk3_ok : ttReverseFiber72Chunk3 = true := by
  decide

def ttReverseFiber72Chunk4 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 8) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 9)

theorem ttReverseFiber72Chunk4_ok : ttReverseFiber72Chunk4 = true := by
  decide

def ttReverseFiber72Chunk5 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 10) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 11)

theorem ttReverseFiber72Chunk5_ok : ttReverseFiber72Chunk5 = true := by
  decide

def ttReverseFiber72Chunk6 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 12) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 13)

theorem ttReverseFiber72Chunk6_ok : ttReverseFiber72Chunk6 = true := by
  decide

def ttReverseFiber72Chunk7 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 14) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 15)

theorem ttReverseFiber72Chunk7_ok : ttReverseFiber72Chunk7 = true := by
  decide

def ttReverseFiber72Chunk8 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 16) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 17)

theorem ttReverseFiber72Chunk8_ok : ttReverseFiber72Chunk8 = true := by
  decide

def ttReverseFiber72Chunk9 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 18) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 19)

theorem ttReverseFiber72Chunk9_ok : ttReverseFiber72Chunk9 = true := by
  decide

def ttReverseFiber72Chunk10 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 20) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 21)

theorem ttReverseFiber72Chunk10_ok : ttReverseFiber72Chunk10 = true := by
  decide

def ttReverseFiber72Chunk11 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 22) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 23)

theorem ttReverseFiber72Chunk11_ok : ttReverseFiber72Chunk11 = true := by
  decide

def ttReverseFiber72Chunk12 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 24) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 25)

theorem ttReverseFiber72Chunk12_ok : ttReverseFiber72Chunk12 = true := by
  decide

def ttReverseFiber72Chunk13 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 26) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 27)

theorem ttReverseFiber72Chunk13_ok : ttReverseFiber72Chunk13 = true := by
  decide

def ttReverseFiber72Chunk14 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 28) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 29)

theorem ttReverseFiber72Chunk14_ok : ttReverseFiber72Chunk14 = true := by
  decide

def ttReverseFiber72Chunk15 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 30) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 31)

theorem ttReverseFiber72Chunk15_ok : ttReverseFiber72Chunk15 = true := by
  decide

def ttReverseFiber72Chunk16 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 32) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 33)

theorem ttReverseFiber72Chunk16_ok : ttReverseFiber72Chunk16 = true := by
  decide

def ttReverseFiber72Chunk17 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 34) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 35)

theorem ttReverseFiber72Chunk17_ok : ttReverseFiber72Chunk17 = true := by
  decide

def ttReverseFiber72Chunk18 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 36) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 37)

theorem ttReverseFiber72Chunk18_ok : ttReverseFiber72Chunk18 = true := by
  decide

def ttReverseFiber72Chunk19 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 38) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 39)

theorem ttReverseFiber72Chunk19_ok : ttReverseFiber72Chunk19 = true := by
  decide

def ttReverseFiber72Chunk20 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 40) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 41)

theorem ttReverseFiber72Chunk20_ok : ttReverseFiber72Chunk20 = true := by
  decide

def ttReverseFiber72Chunk21 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 42) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 43)

theorem ttReverseFiber72Chunk21_ok : ttReverseFiber72Chunk21 = true := by
  decide

def ttReverseFiber72Chunk22 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 44) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 45)

theorem ttReverseFiber72Chunk22_ok : ttReverseFiber72Chunk22 = true := by
  decide

def ttReverseFiber72Chunk23 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 46) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 47)

theorem ttReverseFiber72Chunk23_ok : ttReverseFiber72Chunk23 = true := by
  decide

def ttReverseFiber72Chunk24 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 48) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 49)

theorem ttReverseFiber72Chunk24_ok : ttReverseFiber72Chunk24 = true := by
  decide

def ttReverseFiber72Chunk25 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 50) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 51)

theorem ttReverseFiber72Chunk25_ok : ttReverseFiber72Chunk25 = true := by
  decide

def ttReverseFiber72Chunk26 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 52) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 53)

theorem ttReverseFiber72Chunk26_ok : ttReverseFiber72Chunk26 = true := by
  decide

def ttReverseFiber72Chunk27 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 54) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 55)

theorem ttReverseFiber72Chunk27_ok : ttReverseFiber72Chunk27 = true := by
  decide

def ttReverseFiber72Chunk28 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 56) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 57)

theorem ttReverseFiber72Chunk28_ok : ttReverseFiber72Chunk28 = true := by
  decide

def ttReverseFiber72Chunk29 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 58) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 59)

theorem ttReverseFiber72Chunk29_ok : ttReverseFiber72Chunk29 = true := by
  decide

def ttReverseFiber72Chunk30 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 60) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 61)

theorem ttReverseFiber72Chunk30_ok : ttReverseFiber72Chunk30 = true := by
  decide

def ttReverseFiber72Chunk31 : Bool :=
  directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 62) &&
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 63)

theorem ttReverseFiber72Chunk31_ok : ttReverseFiber72Chunk31 = true := by
  decide

def ttReverseFiber73Chunk0 : Bool :=
  directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 0) &&
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 1)

theorem ttReverseFiber73Chunk0_ok : ttReverseFiber73Chunk0 = true := by
  decide

def ttReverseFiber73Chunk1 : Bool :=
  directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 2) &&
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 3)

theorem ttReverseFiber73Chunk1_ok : ttReverseFiber73Chunk1 = true := by
  decide

def ttReverseFiber73Chunk2 : Bool :=
  directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 4) &&
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 5)

theorem ttReverseFiber73Chunk2_ok : ttReverseFiber73Chunk2 = true := by
  decide

def ttReverseFiber73Chunk3 : Bool :=
  directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 6) &&
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 7)

theorem ttReverseFiber73Chunk3_ok : ttReverseFiber73Chunk3 = true := by
  decide

def ttReverseFiber74Chunk0 : Bool :=
  directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 0) &&
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 1)

theorem ttReverseFiber74Chunk0_ok : ttReverseFiber74Chunk0 = true := by
  decide

def ttReverseFiber74Chunk1 : Bool :=
  directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 2) &&
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 3)

theorem ttReverseFiber74Chunk1_ok : ttReverseFiber74Chunk1 = true := by
  decide

def ttReverseFiber74Chunk2 : Bool :=
  directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 4) &&
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 5)

theorem ttReverseFiber74Chunk2_ok : ttReverseFiber74Chunk2 = true := by
  decide

def ttReverseFiber74Chunk3 : Bool :=
  directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 6) &&
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 7)

theorem ttReverseFiber74Chunk3_ok : ttReverseFiber74Chunk3 = true := by
  decide

def ttReverseFiber75Chunk0 : Bool :=
  directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 0) &&
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 1)

theorem ttReverseFiber75Chunk0_ok : ttReverseFiber75Chunk0 = true := by
  decide

def ttReverseFiber75Chunk1 : Bool :=
  directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 2) &&
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 3)

theorem ttReverseFiber75Chunk1_ok : ttReverseFiber75Chunk1 = true := by
  decide

def ttReverseFiber75Chunk2 : Bool :=
  directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 4) &&
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 5)

theorem ttReverseFiber75Chunk2_ok : ttReverseFiber75Chunk2 = true := by
  decide

def ttReverseFiber75Chunk3 : Bool :=
  directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 6) &&
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 7)

theorem ttReverseFiber75Chunk3_ok : ttReverseFiber75Chunk3 = true := by
  decide

def ttReverseFiber76Chunk0 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 0) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 1)

theorem ttReverseFiber76Chunk0_ok : ttReverseFiber76Chunk0 = true := by
  decide

def ttReverseFiber76Chunk1 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 2) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 3)

theorem ttReverseFiber76Chunk1_ok : ttReverseFiber76Chunk1 = true := by
  decide

def ttReverseFiber76Chunk2 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 4) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 5)

theorem ttReverseFiber76Chunk2_ok : ttReverseFiber76Chunk2 = true := by
  decide

def ttReverseFiber76Chunk3 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 6) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 7)

theorem ttReverseFiber76Chunk3_ok : ttReverseFiber76Chunk3 = true := by
  decide

def ttReverseFiber76Chunk4 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 8) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 9)

theorem ttReverseFiber76Chunk4_ok : ttReverseFiber76Chunk4 = true := by
  decide

def ttReverseFiber76Chunk5 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 10) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 11)

theorem ttReverseFiber76Chunk5_ok : ttReverseFiber76Chunk5 = true := by
  decide

def ttReverseFiber76Chunk6 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 12) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 13)

theorem ttReverseFiber76Chunk6_ok : ttReverseFiber76Chunk6 = true := by
  decide

def ttReverseFiber76Chunk7 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 14) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 15)

theorem ttReverseFiber76Chunk7_ok : ttReverseFiber76Chunk7 = true := by
  decide

def ttReverseFiber76Chunk8 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 16) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 17)

theorem ttReverseFiber76Chunk8_ok : ttReverseFiber76Chunk8 = true := by
  decide

def ttReverseFiber76Chunk9 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 18) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 19)

theorem ttReverseFiber76Chunk9_ok : ttReverseFiber76Chunk9 = true := by
  decide

def ttReverseFiber76Chunk10 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 20) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 21)

theorem ttReverseFiber76Chunk10_ok : ttReverseFiber76Chunk10 = true := by
  decide

def ttReverseFiber76Chunk11 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 22) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 23)

theorem ttReverseFiber76Chunk11_ok : ttReverseFiber76Chunk11 = true := by
  decide

def ttReverseFiber76Chunk12 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 24) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 25)

theorem ttReverseFiber76Chunk12_ok : ttReverseFiber76Chunk12 = true := by
  decide

def ttReverseFiber76Chunk13 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 26) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 27)

theorem ttReverseFiber76Chunk13_ok : ttReverseFiber76Chunk13 = true := by
  decide

def ttReverseFiber76Chunk14 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 28) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 29)

theorem ttReverseFiber76Chunk14_ok : ttReverseFiber76Chunk14 = true := by
  decide

def ttReverseFiber76Chunk15 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 30) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 31)

theorem ttReverseFiber76Chunk15_ok : ttReverseFiber76Chunk15 = true := by
  decide

def ttReverseFiber76Chunk16 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 32) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 33)

theorem ttReverseFiber76Chunk16_ok : ttReverseFiber76Chunk16 = true := by
  decide

def ttReverseFiber76Chunk17 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 34) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 35)

theorem ttReverseFiber76Chunk17_ok : ttReverseFiber76Chunk17 = true := by
  decide

def ttReverseFiber76Chunk18 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 36) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 37)

theorem ttReverseFiber76Chunk18_ok : ttReverseFiber76Chunk18 = true := by
  decide

def ttReverseFiber76Chunk19 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 38) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 39)

theorem ttReverseFiber76Chunk19_ok : ttReverseFiber76Chunk19 = true := by
  decide

def ttReverseFiber76Chunk20 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 40) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 41)

theorem ttReverseFiber76Chunk20_ok : ttReverseFiber76Chunk20 = true := by
  decide

def ttReverseFiber76Chunk21 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 42) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 43)

theorem ttReverseFiber76Chunk21_ok : ttReverseFiber76Chunk21 = true := by
  decide

def ttReverseFiber76Chunk22 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 44) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 45)

theorem ttReverseFiber76Chunk22_ok : ttReverseFiber76Chunk22 = true := by
  decide

def ttReverseFiber76Chunk23 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 46) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 47)

theorem ttReverseFiber76Chunk23_ok : ttReverseFiber76Chunk23 = true := by
  decide

def ttReverseFiber76Chunk24 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 48) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 49)

theorem ttReverseFiber76Chunk24_ok : ttReverseFiber76Chunk24 = true := by
  decide

def ttReverseFiber76Chunk25 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 50) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 51)

theorem ttReverseFiber76Chunk25_ok : ttReverseFiber76Chunk25 = true := by
  decide

def ttReverseFiber76Chunk26 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 52) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 53)

theorem ttReverseFiber76Chunk26_ok : ttReverseFiber76Chunk26 = true := by
  decide

def ttReverseFiber76Chunk27 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 54) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 55)

theorem ttReverseFiber76Chunk27_ok : ttReverseFiber76Chunk27 = true := by
  decide

def ttReverseFiber76Chunk28 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 56) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 57)

theorem ttReverseFiber76Chunk28_ok : ttReverseFiber76Chunk28 = true := by
  decide

def ttReverseFiber76Chunk29 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 58) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 59)

theorem ttReverseFiber76Chunk29_ok : ttReverseFiber76Chunk29 = true := by
  decide

def ttReverseFiber76Chunk30 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 60) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 61)

theorem ttReverseFiber76Chunk30_ok : ttReverseFiber76Chunk30 = true := by
  decide

def ttReverseFiber76Chunk31 : Bool :=
  directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 62) &&
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 63)

theorem ttReverseFiber76Chunk31_ok : ttReverseFiber76Chunk31 = true := by
  decide

def ttReverseFiber77Chunk0 : Bool :=
  directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 0) &&
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 1)

theorem ttReverseFiber77Chunk0_ok : ttReverseFiber77Chunk0 = true := by
  decide

def ttReverseFiber77Chunk1 : Bool :=
  directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 2) &&
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 3)

theorem ttReverseFiber77Chunk1_ok : ttReverseFiber77Chunk1 = true := by
  decide

def ttReverseFiber77Chunk2 : Bool :=
  directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 4) &&
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 5)

theorem ttReverseFiber77Chunk2_ok : ttReverseFiber77Chunk2 = true := by
  decide

def ttReverseFiber77Chunk3 : Bool :=
  directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 6) &&
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 7)

theorem ttReverseFiber77Chunk3_ok : ttReverseFiber77Chunk3 = true := by
  decide

def ttReverseChunkGroup0 : Bool :=
  ttReverseFiber3Chunk0 &&
    ttReverseFiber3Chunk1 &&
    ttReverseFiber3Chunk2 &&
    ttReverseFiber3Chunk3 &&
    ttReverseFiber4Chunk0 &&
    ttReverseFiber4Chunk1 &&
    ttReverseFiber4Chunk2 &&
    ttReverseFiber4Chunk3 &&
    ttReverseFiber4Chunk4 &&
    ttReverseFiber4Chunk5 &&
    ttReverseFiber4Chunk6 &&
    ttReverseFiber4Chunk7 &&
    ttReverseFiber4Chunk8 &&
    ttReverseFiber4Chunk9 &&
    ttReverseFiber4Chunk10 &&
    ttReverseFiber4Chunk11 &&
    ttReverseFiber4Chunk12 &&
    ttReverseFiber4Chunk13 &&
    ttReverseFiber4Chunk14 &&
    ttReverseFiber4Chunk15

theorem ttReverseChunkGroup0_ok : ttReverseChunkGroup0 = true := by
  simp [ttReverseChunkGroup0,
    ttReverseFiber3Chunk0_ok,
    ttReverseFiber3Chunk1_ok,
    ttReverseFiber3Chunk2_ok,
    ttReverseFiber3Chunk3_ok,
    ttReverseFiber4Chunk0_ok,
    ttReverseFiber4Chunk1_ok,
    ttReverseFiber4Chunk2_ok,
    ttReverseFiber4Chunk3_ok,
    ttReverseFiber4Chunk4_ok,
    ttReverseFiber4Chunk5_ok,
    ttReverseFiber4Chunk6_ok,
    ttReverseFiber4Chunk7_ok,
    ttReverseFiber4Chunk8_ok,
    ttReverseFiber4Chunk9_ok,
    ttReverseFiber4Chunk10_ok,
    ttReverseFiber4Chunk11_ok,
    ttReverseFiber4Chunk12_ok,
    ttReverseFiber4Chunk13_ok,
    ttReverseFiber4Chunk14_ok,
    ttReverseFiber4Chunk15_ok]

def ttReverseChunkGroup1 : Bool :=
  ttReverseFiber4Chunk16 &&
    ttReverseFiber4Chunk17 &&
    ttReverseFiber4Chunk18 &&
    ttReverseFiber4Chunk19 &&
    ttReverseFiber4Chunk20 &&
    ttReverseFiber4Chunk21 &&
    ttReverseFiber4Chunk22 &&
    ttReverseFiber4Chunk23 &&
    ttReverseFiber4Chunk24 &&
    ttReverseFiber4Chunk25 &&
    ttReverseFiber4Chunk26 &&
    ttReverseFiber4Chunk27 &&
    ttReverseFiber4Chunk28 &&
    ttReverseFiber4Chunk29 &&
    ttReverseFiber4Chunk30 &&
    ttReverseFiber4Chunk31 &&
    ttReverseFiber5Chunk0 &&
    ttReverseFiber5Chunk1 &&
    ttReverseFiber5Chunk2 &&
    ttReverseFiber5Chunk3

theorem ttReverseChunkGroup1_ok : ttReverseChunkGroup1 = true := by
  simp [ttReverseChunkGroup1,
    ttReverseFiber4Chunk16_ok,
    ttReverseFiber4Chunk17_ok,
    ttReverseFiber4Chunk18_ok,
    ttReverseFiber4Chunk19_ok,
    ttReverseFiber4Chunk20_ok,
    ttReverseFiber4Chunk21_ok,
    ttReverseFiber4Chunk22_ok,
    ttReverseFiber4Chunk23_ok,
    ttReverseFiber4Chunk24_ok,
    ttReverseFiber4Chunk25_ok,
    ttReverseFiber4Chunk26_ok,
    ttReverseFiber4Chunk27_ok,
    ttReverseFiber4Chunk28_ok,
    ttReverseFiber4Chunk29_ok,
    ttReverseFiber4Chunk30_ok,
    ttReverseFiber4Chunk31_ok,
    ttReverseFiber5Chunk0_ok,
    ttReverseFiber5Chunk1_ok,
    ttReverseFiber5Chunk2_ok,
    ttReverseFiber5Chunk3_ok]

def ttReverseChunkGroup2 : Bool :=
  ttReverseFiber6Chunk0 &&
    ttReverseFiber6Chunk1 &&
    ttReverseFiber6Chunk2 &&
    ttReverseFiber6Chunk3 &&
    ttReverseFiber7Chunk0 &&
    ttReverseFiber7Chunk1 &&
    ttReverseFiber7Chunk2 &&
    ttReverseFiber7Chunk3 &&
    ttReverseFiber8Chunk0 &&
    ttReverseFiber8Chunk1 &&
    ttReverseFiber8Chunk2 &&
    ttReverseFiber8Chunk3 &&
    ttReverseFiber8Chunk4 &&
    ttReverseFiber8Chunk5 &&
    ttReverseFiber8Chunk6 &&
    ttReverseFiber8Chunk7 &&
    ttReverseFiber8Chunk8 &&
    ttReverseFiber8Chunk9 &&
    ttReverseFiber8Chunk10 &&
    ttReverseFiber8Chunk11

theorem ttReverseChunkGroup2_ok : ttReverseChunkGroup2 = true := by
  simp [ttReverseChunkGroup2,
    ttReverseFiber6Chunk0_ok,
    ttReverseFiber6Chunk1_ok,
    ttReverseFiber6Chunk2_ok,
    ttReverseFiber6Chunk3_ok,
    ttReverseFiber7Chunk0_ok,
    ttReverseFiber7Chunk1_ok,
    ttReverseFiber7Chunk2_ok,
    ttReverseFiber7Chunk3_ok,
    ttReverseFiber8Chunk0_ok,
    ttReverseFiber8Chunk1_ok,
    ttReverseFiber8Chunk2_ok,
    ttReverseFiber8Chunk3_ok,
    ttReverseFiber8Chunk4_ok,
    ttReverseFiber8Chunk5_ok,
    ttReverseFiber8Chunk6_ok,
    ttReverseFiber8Chunk7_ok,
    ttReverseFiber8Chunk8_ok,
    ttReverseFiber8Chunk9_ok,
    ttReverseFiber8Chunk10_ok,
    ttReverseFiber8Chunk11_ok]

def ttReverseChunkGroup3 : Bool :=
  ttReverseFiber8Chunk12 &&
    ttReverseFiber8Chunk13 &&
    ttReverseFiber8Chunk14 &&
    ttReverseFiber8Chunk15 &&
    ttReverseFiber8Chunk16 &&
    ttReverseFiber8Chunk17 &&
    ttReverseFiber8Chunk18 &&
    ttReverseFiber8Chunk19 &&
    ttReverseFiber8Chunk20 &&
    ttReverseFiber8Chunk21 &&
    ttReverseFiber8Chunk22 &&
    ttReverseFiber8Chunk23 &&
    ttReverseFiber8Chunk24 &&
    ttReverseFiber8Chunk25 &&
    ttReverseFiber8Chunk26 &&
    ttReverseFiber8Chunk27 &&
    ttReverseFiber8Chunk28 &&
    ttReverseFiber8Chunk29 &&
    ttReverseFiber8Chunk30 &&
    ttReverseFiber8Chunk31

theorem ttReverseChunkGroup3_ok : ttReverseChunkGroup3 = true := by
  simp [ttReverseChunkGroup3,
    ttReverseFiber8Chunk12_ok,
    ttReverseFiber8Chunk13_ok,
    ttReverseFiber8Chunk14_ok,
    ttReverseFiber8Chunk15_ok,
    ttReverseFiber8Chunk16_ok,
    ttReverseFiber8Chunk17_ok,
    ttReverseFiber8Chunk18_ok,
    ttReverseFiber8Chunk19_ok,
    ttReverseFiber8Chunk20_ok,
    ttReverseFiber8Chunk21_ok,
    ttReverseFiber8Chunk22_ok,
    ttReverseFiber8Chunk23_ok,
    ttReverseFiber8Chunk24_ok,
    ttReverseFiber8Chunk25_ok,
    ttReverseFiber8Chunk26_ok,
    ttReverseFiber8Chunk27_ok,
    ttReverseFiber8Chunk28_ok,
    ttReverseFiber8Chunk29_ok,
    ttReverseFiber8Chunk30_ok,
    ttReverseFiber8Chunk31_ok]

def ttReverseChunkGroup4 : Bool :=
  ttReverseFiber9Chunk0 &&
    ttReverseFiber9Chunk1 &&
    ttReverseFiber9Chunk2 &&
    ttReverseFiber9Chunk3 &&
    ttReverseFiber10Chunk0 &&
    ttReverseFiber10Chunk1 &&
    ttReverseFiber10Chunk2 &&
    ttReverseFiber10Chunk3 &&
    ttReverseFiber10Chunk4 &&
    ttReverseFiber10Chunk5 &&
    ttReverseFiber10Chunk6 &&
    ttReverseFiber10Chunk7 &&
    ttReverseFiber10Chunk8 &&
    ttReverseFiber10Chunk9 &&
    ttReverseFiber10Chunk10 &&
    ttReverseFiber10Chunk11 &&
    ttReverseFiber10Chunk12 &&
    ttReverseFiber10Chunk13 &&
    ttReverseFiber10Chunk14 &&
    ttReverseFiber10Chunk15

theorem ttReverseChunkGroup4_ok : ttReverseChunkGroup4 = true := by
  simp [ttReverseChunkGroup4,
    ttReverseFiber9Chunk0_ok,
    ttReverseFiber9Chunk1_ok,
    ttReverseFiber9Chunk2_ok,
    ttReverseFiber9Chunk3_ok,
    ttReverseFiber10Chunk0_ok,
    ttReverseFiber10Chunk1_ok,
    ttReverseFiber10Chunk2_ok,
    ttReverseFiber10Chunk3_ok,
    ttReverseFiber10Chunk4_ok,
    ttReverseFiber10Chunk5_ok,
    ttReverseFiber10Chunk6_ok,
    ttReverseFiber10Chunk7_ok,
    ttReverseFiber10Chunk8_ok,
    ttReverseFiber10Chunk9_ok,
    ttReverseFiber10Chunk10_ok,
    ttReverseFiber10Chunk11_ok,
    ttReverseFiber10Chunk12_ok,
    ttReverseFiber10Chunk13_ok,
    ttReverseFiber10Chunk14_ok,
    ttReverseFiber10Chunk15_ok]

def ttReverseChunkGroup5 : Bool :=
  ttReverseFiber10Chunk16 &&
    ttReverseFiber10Chunk17 &&
    ttReverseFiber10Chunk18 &&
    ttReverseFiber10Chunk19 &&
    ttReverseFiber10Chunk20 &&
    ttReverseFiber10Chunk21 &&
    ttReverseFiber10Chunk22 &&
    ttReverseFiber10Chunk23 &&
    ttReverseFiber10Chunk24 &&
    ttReverseFiber10Chunk25 &&
    ttReverseFiber10Chunk26 &&
    ttReverseFiber10Chunk27 &&
    ttReverseFiber10Chunk28 &&
    ttReverseFiber10Chunk29 &&
    ttReverseFiber10Chunk30 &&
    ttReverseFiber10Chunk31 &&
    ttReverseFiber11Chunk0 &&
    ttReverseFiber11Chunk1 &&
    ttReverseFiber11Chunk2 &&
    ttReverseFiber11Chunk3

theorem ttReverseChunkGroup5_ok : ttReverseChunkGroup5 = true := by
  simp [ttReverseChunkGroup5,
    ttReverseFiber10Chunk16_ok,
    ttReverseFiber10Chunk17_ok,
    ttReverseFiber10Chunk18_ok,
    ttReverseFiber10Chunk19_ok,
    ttReverseFiber10Chunk20_ok,
    ttReverseFiber10Chunk21_ok,
    ttReverseFiber10Chunk22_ok,
    ttReverseFiber10Chunk23_ok,
    ttReverseFiber10Chunk24_ok,
    ttReverseFiber10Chunk25_ok,
    ttReverseFiber10Chunk26_ok,
    ttReverseFiber10Chunk27_ok,
    ttReverseFiber10Chunk28_ok,
    ttReverseFiber10Chunk29_ok,
    ttReverseFiber10Chunk30_ok,
    ttReverseFiber10Chunk31_ok,
    ttReverseFiber11Chunk0_ok,
    ttReverseFiber11Chunk1_ok,
    ttReverseFiber11Chunk2_ok,
    ttReverseFiber11Chunk3_ok]

def ttReverseChunkGroup6 : Bool :=
  ttReverseFiber18Chunk0 &&
    ttReverseFiber18Chunk1 &&
    ttReverseFiber18Chunk2 &&
    ttReverseFiber18Chunk3 &&
    ttReverseFiber19Chunk0 &&
    ttReverseFiber19Chunk1 &&
    ttReverseFiber19Chunk2 &&
    ttReverseFiber19Chunk3 &&
    ttReverseFiber20Chunk0 &&
    ttReverseFiber20Chunk1 &&
    ttReverseFiber20Chunk2 &&
    ttReverseFiber20Chunk3 &&
    ttReverseFiber20Chunk4 &&
    ttReverseFiber20Chunk5 &&
    ttReverseFiber20Chunk6 &&
    ttReverseFiber20Chunk7 &&
    ttReverseFiber20Chunk8 &&
    ttReverseFiber20Chunk9 &&
    ttReverseFiber20Chunk10 &&
    ttReverseFiber20Chunk11

theorem ttReverseChunkGroup6_ok : ttReverseChunkGroup6 = true := by
  simp [ttReverseChunkGroup6,
    ttReverseFiber18Chunk0_ok,
    ttReverseFiber18Chunk1_ok,
    ttReverseFiber18Chunk2_ok,
    ttReverseFiber18Chunk3_ok,
    ttReverseFiber19Chunk0_ok,
    ttReverseFiber19Chunk1_ok,
    ttReverseFiber19Chunk2_ok,
    ttReverseFiber19Chunk3_ok,
    ttReverseFiber20Chunk0_ok,
    ttReverseFiber20Chunk1_ok,
    ttReverseFiber20Chunk2_ok,
    ttReverseFiber20Chunk3_ok,
    ttReverseFiber20Chunk4_ok,
    ttReverseFiber20Chunk5_ok,
    ttReverseFiber20Chunk6_ok,
    ttReverseFiber20Chunk7_ok,
    ttReverseFiber20Chunk8_ok,
    ttReverseFiber20Chunk9_ok,
    ttReverseFiber20Chunk10_ok,
    ttReverseFiber20Chunk11_ok]

def ttReverseChunkGroup7 : Bool :=
  ttReverseFiber20Chunk12 &&
    ttReverseFiber20Chunk13 &&
    ttReverseFiber20Chunk14 &&
    ttReverseFiber20Chunk15 &&
    ttReverseFiber20Chunk16 &&
    ttReverseFiber20Chunk17 &&
    ttReverseFiber20Chunk18 &&
    ttReverseFiber20Chunk19 &&
    ttReverseFiber20Chunk20 &&
    ttReverseFiber20Chunk21 &&
    ttReverseFiber20Chunk22 &&
    ttReverseFiber20Chunk23 &&
    ttReverseFiber20Chunk24 &&
    ttReverseFiber20Chunk25 &&
    ttReverseFiber20Chunk26 &&
    ttReverseFiber20Chunk27 &&
    ttReverseFiber20Chunk28 &&
    ttReverseFiber20Chunk29 &&
    ttReverseFiber20Chunk30 &&
    ttReverseFiber20Chunk31

theorem ttReverseChunkGroup7_ok : ttReverseChunkGroup7 = true := by
  simp [ttReverseChunkGroup7,
    ttReverseFiber20Chunk12_ok,
    ttReverseFiber20Chunk13_ok,
    ttReverseFiber20Chunk14_ok,
    ttReverseFiber20Chunk15_ok,
    ttReverseFiber20Chunk16_ok,
    ttReverseFiber20Chunk17_ok,
    ttReverseFiber20Chunk18_ok,
    ttReverseFiber20Chunk19_ok,
    ttReverseFiber20Chunk20_ok,
    ttReverseFiber20Chunk21_ok,
    ttReverseFiber20Chunk22_ok,
    ttReverseFiber20Chunk23_ok,
    ttReverseFiber20Chunk24_ok,
    ttReverseFiber20Chunk25_ok,
    ttReverseFiber20Chunk26_ok,
    ttReverseFiber20Chunk27_ok,
    ttReverseFiber20Chunk28_ok,
    ttReverseFiber20Chunk29_ok,
    ttReverseFiber20Chunk30_ok,
    ttReverseFiber20Chunk31_ok]

def ttReverseChunkGroup8 : Bool :=
  ttReverseFiber30Chunk0 &&
    ttReverseFiber30Chunk1 &&
    ttReverseFiber30Chunk2 &&
    ttReverseFiber30Chunk3 &&
    ttReverseFiber30Chunk4 &&
    ttReverseFiber30Chunk5 &&
    ttReverseFiber30Chunk6 &&
    ttReverseFiber30Chunk7 &&
    ttReverseFiber30Chunk8 &&
    ttReverseFiber30Chunk9 &&
    ttReverseFiber30Chunk10 &&
    ttReverseFiber30Chunk11 &&
    ttReverseFiber30Chunk12 &&
    ttReverseFiber30Chunk13 &&
    ttReverseFiber30Chunk14 &&
    ttReverseFiber30Chunk15 &&
    ttReverseFiber30Chunk16 &&
    ttReverseFiber30Chunk17 &&
    ttReverseFiber30Chunk18 &&
    ttReverseFiber30Chunk19

theorem ttReverseChunkGroup8_ok : ttReverseChunkGroup8 = true := by
  simp [ttReverseChunkGroup8,
    ttReverseFiber30Chunk0_ok,
    ttReverseFiber30Chunk1_ok,
    ttReverseFiber30Chunk2_ok,
    ttReverseFiber30Chunk3_ok,
    ttReverseFiber30Chunk4_ok,
    ttReverseFiber30Chunk5_ok,
    ttReverseFiber30Chunk6_ok,
    ttReverseFiber30Chunk7_ok,
    ttReverseFiber30Chunk8_ok,
    ttReverseFiber30Chunk9_ok,
    ttReverseFiber30Chunk10_ok,
    ttReverseFiber30Chunk11_ok,
    ttReverseFiber30Chunk12_ok,
    ttReverseFiber30Chunk13_ok,
    ttReverseFiber30Chunk14_ok,
    ttReverseFiber30Chunk15_ok,
    ttReverseFiber30Chunk16_ok,
    ttReverseFiber30Chunk17_ok,
    ttReverseFiber30Chunk18_ok,
    ttReverseFiber30Chunk19_ok]

def ttReverseChunkGroup9 : Bool :=
  ttReverseFiber30Chunk20 &&
    ttReverseFiber30Chunk21 &&
    ttReverseFiber30Chunk22 &&
    ttReverseFiber30Chunk23 &&
    ttReverseFiber30Chunk24 &&
    ttReverseFiber30Chunk25 &&
    ttReverseFiber30Chunk26 &&
    ttReverseFiber30Chunk27 &&
    ttReverseFiber30Chunk28 &&
    ttReverseFiber30Chunk29 &&
    ttReverseFiber30Chunk30 &&
    ttReverseFiber30Chunk31 &&
    ttReverseFiber31Chunk0 &&
    ttReverseFiber31Chunk1 &&
    ttReverseFiber31Chunk2 &&
    ttReverseFiber31Chunk3 &&
    ttReverseFiber32Chunk0 &&
    ttReverseFiber32Chunk1 &&
    ttReverseFiber32Chunk2 &&
    ttReverseFiber32Chunk3

theorem ttReverseChunkGroup9_ok : ttReverseChunkGroup9 = true := by
  simp [ttReverseChunkGroup9,
    ttReverseFiber30Chunk20_ok,
    ttReverseFiber30Chunk21_ok,
    ttReverseFiber30Chunk22_ok,
    ttReverseFiber30Chunk23_ok,
    ttReverseFiber30Chunk24_ok,
    ttReverseFiber30Chunk25_ok,
    ttReverseFiber30Chunk26_ok,
    ttReverseFiber30Chunk27_ok,
    ttReverseFiber30Chunk28_ok,
    ttReverseFiber30Chunk29_ok,
    ttReverseFiber30Chunk30_ok,
    ttReverseFiber30Chunk31_ok,
    ttReverseFiber31Chunk0_ok,
    ttReverseFiber31Chunk1_ok,
    ttReverseFiber31Chunk2_ok,
    ttReverseFiber31Chunk3_ok,
    ttReverseFiber32Chunk0_ok,
    ttReverseFiber32Chunk1_ok,
    ttReverseFiber32Chunk2_ok,
    ttReverseFiber32Chunk3_ok]

def ttReverseChunkGroup10 : Bool :=
  ttReverseFiber36Chunk0 &&
    ttReverseFiber36Chunk1 &&
    ttReverseFiber36Chunk2 &&
    ttReverseFiber36Chunk3 &&
    ttReverseFiber36Chunk4 &&
    ttReverseFiber36Chunk5 &&
    ttReverseFiber36Chunk6 &&
    ttReverseFiber36Chunk7 &&
    ttReverseFiber36Chunk8 &&
    ttReverseFiber36Chunk9 &&
    ttReverseFiber36Chunk10 &&
    ttReverseFiber36Chunk11 &&
    ttReverseFiber36Chunk12 &&
    ttReverseFiber36Chunk13 &&
    ttReverseFiber36Chunk14 &&
    ttReverseFiber36Chunk15 &&
    ttReverseFiber36Chunk16 &&
    ttReverseFiber36Chunk17 &&
    ttReverseFiber36Chunk18 &&
    ttReverseFiber36Chunk19

theorem ttReverseChunkGroup10_ok : ttReverseChunkGroup10 = true := by
  simp [ttReverseChunkGroup10,
    ttReverseFiber36Chunk0_ok,
    ttReverseFiber36Chunk1_ok,
    ttReverseFiber36Chunk2_ok,
    ttReverseFiber36Chunk3_ok,
    ttReverseFiber36Chunk4_ok,
    ttReverseFiber36Chunk5_ok,
    ttReverseFiber36Chunk6_ok,
    ttReverseFiber36Chunk7_ok,
    ttReverseFiber36Chunk8_ok,
    ttReverseFiber36Chunk9_ok,
    ttReverseFiber36Chunk10_ok,
    ttReverseFiber36Chunk11_ok,
    ttReverseFiber36Chunk12_ok,
    ttReverseFiber36Chunk13_ok,
    ttReverseFiber36Chunk14_ok,
    ttReverseFiber36Chunk15_ok,
    ttReverseFiber36Chunk16_ok,
    ttReverseFiber36Chunk17_ok,
    ttReverseFiber36Chunk18_ok,
    ttReverseFiber36Chunk19_ok]

def ttReverseChunkGroup11 : Bool :=
  ttReverseFiber36Chunk20 &&
    ttReverseFiber36Chunk21 &&
    ttReverseFiber36Chunk22 &&
    ttReverseFiber36Chunk23 &&
    ttReverseFiber36Chunk24 &&
    ttReverseFiber36Chunk25 &&
    ttReverseFiber36Chunk26 &&
    ttReverseFiber36Chunk27 &&
    ttReverseFiber36Chunk28 &&
    ttReverseFiber36Chunk29 &&
    ttReverseFiber36Chunk30 &&
    ttReverseFiber36Chunk31 &&
    ttReverseFiber37Chunk0 &&
    ttReverseFiber37Chunk1 &&
    ttReverseFiber37Chunk2 &&
    ttReverseFiber37Chunk3 &&
    ttReverseFiber38Chunk0 &&
    ttReverseFiber38Chunk1 &&
    ttReverseFiber38Chunk2 &&
    ttReverseFiber38Chunk3

theorem ttReverseChunkGroup11_ok : ttReverseChunkGroup11 = true := by
  simp [ttReverseChunkGroup11,
    ttReverseFiber36Chunk20_ok,
    ttReverseFiber36Chunk21_ok,
    ttReverseFiber36Chunk22_ok,
    ttReverseFiber36Chunk23_ok,
    ttReverseFiber36Chunk24_ok,
    ttReverseFiber36Chunk25_ok,
    ttReverseFiber36Chunk26_ok,
    ttReverseFiber36Chunk27_ok,
    ttReverseFiber36Chunk28_ok,
    ttReverseFiber36Chunk29_ok,
    ttReverseFiber36Chunk30_ok,
    ttReverseFiber36Chunk31_ok,
    ttReverseFiber37Chunk0_ok,
    ttReverseFiber37Chunk1_ok,
    ttReverseFiber37Chunk2_ok,
    ttReverseFiber37Chunk3_ok,
    ttReverseFiber38Chunk0_ok,
    ttReverseFiber38Chunk1_ok,
    ttReverseFiber38Chunk2_ok,
    ttReverseFiber38Chunk3_ok]

def ttReverseChunkGroup12 : Bool :=
  ttReverseFiber42Chunk0 &&
    ttReverseFiber42Chunk1 &&
    ttReverseFiber42Chunk2 &&
    ttReverseFiber42Chunk3 &&
    ttReverseFiber43Chunk0 &&
    ttReverseFiber43Chunk1 &&
    ttReverseFiber43Chunk2 &&
    ttReverseFiber43Chunk3 &&
    ttReverseFiber44Chunk0 &&
    ttReverseFiber44Chunk1 &&
    ttReverseFiber44Chunk2 &&
    ttReverseFiber44Chunk3 &&
    ttReverseFiber44Chunk4 &&
    ttReverseFiber44Chunk5 &&
    ttReverseFiber44Chunk6 &&
    ttReverseFiber44Chunk7 &&
    ttReverseFiber44Chunk8 &&
    ttReverseFiber44Chunk9 &&
    ttReverseFiber44Chunk10 &&
    ttReverseFiber44Chunk11

theorem ttReverseChunkGroup12_ok : ttReverseChunkGroup12 = true := by
  simp [ttReverseChunkGroup12,
    ttReverseFiber42Chunk0_ok,
    ttReverseFiber42Chunk1_ok,
    ttReverseFiber42Chunk2_ok,
    ttReverseFiber42Chunk3_ok,
    ttReverseFiber43Chunk0_ok,
    ttReverseFiber43Chunk1_ok,
    ttReverseFiber43Chunk2_ok,
    ttReverseFiber43Chunk3_ok,
    ttReverseFiber44Chunk0_ok,
    ttReverseFiber44Chunk1_ok,
    ttReverseFiber44Chunk2_ok,
    ttReverseFiber44Chunk3_ok,
    ttReverseFiber44Chunk4_ok,
    ttReverseFiber44Chunk5_ok,
    ttReverseFiber44Chunk6_ok,
    ttReverseFiber44Chunk7_ok,
    ttReverseFiber44Chunk8_ok,
    ttReverseFiber44Chunk9_ok,
    ttReverseFiber44Chunk10_ok,
    ttReverseFiber44Chunk11_ok]

def ttReverseChunkGroup13 : Bool :=
  ttReverseFiber44Chunk12 &&
    ttReverseFiber44Chunk13 &&
    ttReverseFiber44Chunk14 &&
    ttReverseFiber44Chunk15 &&
    ttReverseFiber44Chunk16 &&
    ttReverseFiber44Chunk17 &&
    ttReverseFiber44Chunk18 &&
    ttReverseFiber44Chunk19 &&
    ttReverseFiber44Chunk20 &&
    ttReverseFiber44Chunk21 &&
    ttReverseFiber44Chunk22 &&
    ttReverseFiber44Chunk23 &&
    ttReverseFiber44Chunk24 &&
    ttReverseFiber44Chunk25 &&
    ttReverseFiber44Chunk26 &&
    ttReverseFiber44Chunk27 &&
    ttReverseFiber44Chunk28 &&
    ttReverseFiber44Chunk29 &&
    ttReverseFiber44Chunk30 &&
    ttReverseFiber44Chunk31

theorem ttReverseChunkGroup13_ok : ttReverseChunkGroup13 = true := by
  simp [ttReverseChunkGroup13,
    ttReverseFiber44Chunk12_ok,
    ttReverseFiber44Chunk13_ok,
    ttReverseFiber44Chunk14_ok,
    ttReverseFiber44Chunk15_ok,
    ttReverseFiber44Chunk16_ok,
    ttReverseFiber44Chunk17_ok,
    ttReverseFiber44Chunk18_ok,
    ttReverseFiber44Chunk19_ok,
    ttReverseFiber44Chunk20_ok,
    ttReverseFiber44Chunk21_ok,
    ttReverseFiber44Chunk22_ok,
    ttReverseFiber44Chunk23_ok,
    ttReverseFiber44Chunk24_ok,
    ttReverseFiber44Chunk25_ok,
    ttReverseFiber44Chunk26_ok,
    ttReverseFiber44Chunk27_ok,
    ttReverseFiber44Chunk28_ok,
    ttReverseFiber44Chunk29_ok,
    ttReverseFiber44Chunk30_ok,
    ttReverseFiber44Chunk31_ok]

def ttReverseChunkGroup14 : Bool :=
  ttReverseFiber48Chunk0 &&
    ttReverseFiber48Chunk1 &&
    ttReverseFiber48Chunk2 &&
    ttReverseFiber48Chunk3 &&
    ttReverseFiber49Chunk0 &&
    ttReverseFiber49Chunk1 &&
    ttReverseFiber49Chunk2 &&
    ttReverseFiber49Chunk3 &&
    ttReverseFiber50Chunk0 &&
    ttReverseFiber50Chunk1 &&
    ttReverseFiber50Chunk2 &&
    ttReverseFiber50Chunk3 &&
    ttReverseFiber50Chunk4 &&
    ttReverseFiber50Chunk5 &&
    ttReverseFiber50Chunk6 &&
    ttReverseFiber50Chunk7 &&
    ttReverseFiber50Chunk8 &&
    ttReverseFiber50Chunk9 &&
    ttReverseFiber50Chunk10 &&
    ttReverseFiber50Chunk11

theorem ttReverseChunkGroup14_ok : ttReverseChunkGroup14 = true := by
  simp [ttReverseChunkGroup14,
    ttReverseFiber48Chunk0_ok,
    ttReverseFiber48Chunk1_ok,
    ttReverseFiber48Chunk2_ok,
    ttReverseFiber48Chunk3_ok,
    ttReverseFiber49Chunk0_ok,
    ttReverseFiber49Chunk1_ok,
    ttReverseFiber49Chunk2_ok,
    ttReverseFiber49Chunk3_ok,
    ttReverseFiber50Chunk0_ok,
    ttReverseFiber50Chunk1_ok,
    ttReverseFiber50Chunk2_ok,
    ttReverseFiber50Chunk3_ok,
    ttReverseFiber50Chunk4_ok,
    ttReverseFiber50Chunk5_ok,
    ttReverseFiber50Chunk6_ok,
    ttReverseFiber50Chunk7_ok,
    ttReverseFiber50Chunk8_ok,
    ttReverseFiber50Chunk9_ok,
    ttReverseFiber50Chunk10_ok,
    ttReverseFiber50Chunk11_ok]

def ttReverseChunkGroup15 : Bool :=
  ttReverseFiber50Chunk12 &&
    ttReverseFiber50Chunk13 &&
    ttReverseFiber50Chunk14 &&
    ttReverseFiber50Chunk15 &&
    ttReverseFiber50Chunk16 &&
    ttReverseFiber50Chunk17 &&
    ttReverseFiber50Chunk18 &&
    ttReverseFiber50Chunk19 &&
    ttReverseFiber50Chunk20 &&
    ttReverseFiber50Chunk21 &&
    ttReverseFiber50Chunk22 &&
    ttReverseFiber50Chunk23 &&
    ttReverseFiber50Chunk24 &&
    ttReverseFiber50Chunk25 &&
    ttReverseFiber50Chunk26 &&
    ttReverseFiber50Chunk27 &&
    ttReverseFiber50Chunk28 &&
    ttReverseFiber50Chunk29 &&
    ttReverseFiber50Chunk30 &&
    ttReverseFiber50Chunk31

theorem ttReverseChunkGroup15_ok : ttReverseChunkGroup15 = true := by
  simp [ttReverseChunkGroup15,
    ttReverseFiber50Chunk12_ok,
    ttReverseFiber50Chunk13_ok,
    ttReverseFiber50Chunk14_ok,
    ttReverseFiber50Chunk15_ok,
    ttReverseFiber50Chunk16_ok,
    ttReverseFiber50Chunk17_ok,
    ttReverseFiber50Chunk18_ok,
    ttReverseFiber50Chunk19_ok,
    ttReverseFiber50Chunk20_ok,
    ttReverseFiber50Chunk21_ok,
    ttReverseFiber50Chunk22_ok,
    ttReverseFiber50Chunk23_ok,
    ttReverseFiber50Chunk24_ok,
    ttReverseFiber50Chunk25_ok,
    ttReverseFiber50Chunk26_ok,
    ttReverseFiber50Chunk27_ok,
    ttReverseFiber50Chunk28_ok,
    ttReverseFiber50Chunk29_ok,
    ttReverseFiber50Chunk30_ok,
    ttReverseFiber50Chunk31_ok]

def ttReverseChunkGroup16 : Bool :=
  ttReverseFiber60Chunk0 &&
    ttReverseFiber60Chunk1 &&
    ttReverseFiber60Chunk2 &&
    ttReverseFiber60Chunk3 &&
    ttReverseFiber60Chunk4 &&
    ttReverseFiber60Chunk5 &&
    ttReverseFiber60Chunk6 &&
    ttReverseFiber60Chunk7 &&
    ttReverseFiber60Chunk8 &&
    ttReverseFiber60Chunk9 &&
    ttReverseFiber60Chunk10 &&
    ttReverseFiber60Chunk11 &&
    ttReverseFiber60Chunk12 &&
    ttReverseFiber60Chunk13 &&
    ttReverseFiber60Chunk14 &&
    ttReverseFiber60Chunk15 &&
    ttReverseFiber60Chunk16 &&
    ttReverseFiber60Chunk17 &&
    ttReverseFiber60Chunk18 &&
    ttReverseFiber60Chunk19

theorem ttReverseChunkGroup16_ok : ttReverseChunkGroup16 = true := by
  simp [ttReverseChunkGroup16,
    ttReverseFiber60Chunk0_ok,
    ttReverseFiber60Chunk1_ok,
    ttReverseFiber60Chunk2_ok,
    ttReverseFiber60Chunk3_ok,
    ttReverseFiber60Chunk4_ok,
    ttReverseFiber60Chunk5_ok,
    ttReverseFiber60Chunk6_ok,
    ttReverseFiber60Chunk7_ok,
    ttReverseFiber60Chunk8_ok,
    ttReverseFiber60Chunk9_ok,
    ttReverseFiber60Chunk10_ok,
    ttReverseFiber60Chunk11_ok,
    ttReverseFiber60Chunk12_ok,
    ttReverseFiber60Chunk13_ok,
    ttReverseFiber60Chunk14_ok,
    ttReverseFiber60Chunk15_ok,
    ttReverseFiber60Chunk16_ok,
    ttReverseFiber60Chunk17_ok,
    ttReverseFiber60Chunk18_ok,
    ttReverseFiber60Chunk19_ok]

def ttReverseChunkGroup17 : Bool :=
  ttReverseFiber60Chunk20 &&
    ttReverseFiber60Chunk21 &&
    ttReverseFiber60Chunk22 &&
    ttReverseFiber60Chunk23 &&
    ttReverseFiber60Chunk24 &&
    ttReverseFiber60Chunk25 &&
    ttReverseFiber60Chunk26 &&
    ttReverseFiber60Chunk27 &&
    ttReverseFiber60Chunk28 &&
    ttReverseFiber60Chunk29 &&
    ttReverseFiber60Chunk30 &&
    ttReverseFiber60Chunk31 &&
    ttReverseFiber61Chunk0 &&
    ttReverseFiber61Chunk1 &&
    ttReverseFiber61Chunk2 &&
    ttReverseFiber61Chunk3 &&
    ttReverseFiber62Chunk0 &&
    ttReverseFiber62Chunk1 &&
    ttReverseFiber62Chunk2 &&
    ttReverseFiber62Chunk3

theorem ttReverseChunkGroup17_ok : ttReverseChunkGroup17 = true := by
  simp [ttReverseChunkGroup17,
    ttReverseFiber60Chunk20_ok,
    ttReverseFiber60Chunk21_ok,
    ttReverseFiber60Chunk22_ok,
    ttReverseFiber60Chunk23_ok,
    ttReverseFiber60Chunk24_ok,
    ttReverseFiber60Chunk25_ok,
    ttReverseFiber60Chunk26_ok,
    ttReverseFiber60Chunk27_ok,
    ttReverseFiber60Chunk28_ok,
    ttReverseFiber60Chunk29_ok,
    ttReverseFiber60Chunk30_ok,
    ttReverseFiber60Chunk31_ok,
    ttReverseFiber61Chunk0_ok,
    ttReverseFiber61Chunk1_ok,
    ttReverseFiber61Chunk2_ok,
    ttReverseFiber61Chunk3_ok,
    ttReverseFiber62Chunk0_ok,
    ttReverseFiber62Chunk1_ok,
    ttReverseFiber62Chunk2_ok,
    ttReverseFiber62Chunk3_ok]

def ttReverseChunkGroup18 : Bool :=
  ttReverseFiber69Chunk0 &&
    ttReverseFiber69Chunk1 &&
    ttReverseFiber69Chunk2 &&
    ttReverseFiber69Chunk3 &&
    ttReverseFiber70Chunk0 &&
    ttReverseFiber70Chunk1 &&
    ttReverseFiber70Chunk2 &&
    ttReverseFiber70Chunk3 &&
    ttReverseFiber70Chunk4 &&
    ttReverseFiber70Chunk5 &&
    ttReverseFiber70Chunk6 &&
    ttReverseFiber70Chunk7 &&
    ttReverseFiber70Chunk8 &&
    ttReverseFiber70Chunk9 &&
    ttReverseFiber70Chunk10 &&
    ttReverseFiber70Chunk11 &&
    ttReverseFiber70Chunk12 &&
    ttReverseFiber70Chunk13 &&
    ttReverseFiber70Chunk14 &&
    ttReverseFiber70Chunk15

theorem ttReverseChunkGroup18_ok : ttReverseChunkGroup18 = true := by
  simp [ttReverseChunkGroup18,
    ttReverseFiber69Chunk0_ok,
    ttReverseFiber69Chunk1_ok,
    ttReverseFiber69Chunk2_ok,
    ttReverseFiber69Chunk3_ok,
    ttReverseFiber70Chunk0_ok,
    ttReverseFiber70Chunk1_ok,
    ttReverseFiber70Chunk2_ok,
    ttReverseFiber70Chunk3_ok,
    ttReverseFiber70Chunk4_ok,
    ttReverseFiber70Chunk5_ok,
    ttReverseFiber70Chunk6_ok,
    ttReverseFiber70Chunk7_ok,
    ttReverseFiber70Chunk8_ok,
    ttReverseFiber70Chunk9_ok,
    ttReverseFiber70Chunk10_ok,
    ttReverseFiber70Chunk11_ok,
    ttReverseFiber70Chunk12_ok,
    ttReverseFiber70Chunk13_ok,
    ttReverseFiber70Chunk14_ok,
    ttReverseFiber70Chunk15_ok]

def ttReverseChunkGroup19 : Bool :=
  ttReverseFiber70Chunk16 &&
    ttReverseFiber70Chunk17 &&
    ttReverseFiber70Chunk18 &&
    ttReverseFiber70Chunk19 &&
    ttReverseFiber70Chunk20 &&
    ttReverseFiber70Chunk21 &&
    ttReverseFiber70Chunk22 &&
    ttReverseFiber70Chunk23 &&
    ttReverseFiber70Chunk24 &&
    ttReverseFiber70Chunk25 &&
    ttReverseFiber70Chunk26 &&
    ttReverseFiber70Chunk27 &&
    ttReverseFiber70Chunk28 &&
    ttReverseFiber70Chunk29 &&
    ttReverseFiber70Chunk30 &&
    ttReverseFiber70Chunk31 &&
    ttReverseFiber71Chunk0 &&
    ttReverseFiber71Chunk1 &&
    ttReverseFiber71Chunk2 &&
    ttReverseFiber71Chunk3

theorem ttReverseChunkGroup19_ok : ttReverseChunkGroup19 = true := by
  simp [ttReverseChunkGroup19,
    ttReverseFiber70Chunk16_ok,
    ttReverseFiber70Chunk17_ok,
    ttReverseFiber70Chunk18_ok,
    ttReverseFiber70Chunk19_ok,
    ttReverseFiber70Chunk20_ok,
    ttReverseFiber70Chunk21_ok,
    ttReverseFiber70Chunk22_ok,
    ttReverseFiber70Chunk23_ok,
    ttReverseFiber70Chunk24_ok,
    ttReverseFiber70Chunk25_ok,
    ttReverseFiber70Chunk26_ok,
    ttReverseFiber70Chunk27_ok,
    ttReverseFiber70Chunk28_ok,
    ttReverseFiber70Chunk29_ok,
    ttReverseFiber70Chunk30_ok,
    ttReverseFiber70Chunk31_ok,
    ttReverseFiber71Chunk0_ok,
    ttReverseFiber71Chunk1_ok,
    ttReverseFiber71Chunk2_ok,
    ttReverseFiber71Chunk3_ok]

def ttReverseChunkGroup20 : Bool :=
  ttReverseFiber72Chunk0 &&
    ttReverseFiber72Chunk1 &&
    ttReverseFiber72Chunk2 &&
    ttReverseFiber72Chunk3 &&
    ttReverseFiber72Chunk4 &&
    ttReverseFiber72Chunk5 &&
    ttReverseFiber72Chunk6 &&
    ttReverseFiber72Chunk7 &&
    ttReverseFiber72Chunk8 &&
    ttReverseFiber72Chunk9 &&
    ttReverseFiber72Chunk10 &&
    ttReverseFiber72Chunk11 &&
    ttReverseFiber72Chunk12 &&
    ttReverseFiber72Chunk13 &&
    ttReverseFiber72Chunk14 &&
    ttReverseFiber72Chunk15 &&
    ttReverseFiber72Chunk16 &&
    ttReverseFiber72Chunk17 &&
    ttReverseFiber72Chunk18 &&
    ttReverseFiber72Chunk19

theorem ttReverseChunkGroup20_ok : ttReverseChunkGroup20 = true := by
  simp [ttReverseChunkGroup20,
    ttReverseFiber72Chunk0_ok,
    ttReverseFiber72Chunk1_ok,
    ttReverseFiber72Chunk2_ok,
    ttReverseFiber72Chunk3_ok,
    ttReverseFiber72Chunk4_ok,
    ttReverseFiber72Chunk5_ok,
    ttReverseFiber72Chunk6_ok,
    ttReverseFiber72Chunk7_ok,
    ttReverseFiber72Chunk8_ok,
    ttReverseFiber72Chunk9_ok,
    ttReverseFiber72Chunk10_ok,
    ttReverseFiber72Chunk11_ok,
    ttReverseFiber72Chunk12_ok,
    ttReverseFiber72Chunk13_ok,
    ttReverseFiber72Chunk14_ok,
    ttReverseFiber72Chunk15_ok,
    ttReverseFiber72Chunk16_ok,
    ttReverseFiber72Chunk17_ok,
    ttReverseFiber72Chunk18_ok,
    ttReverseFiber72Chunk19_ok]

def ttReverseChunkGroup21 : Bool :=
  ttReverseFiber72Chunk20 &&
    ttReverseFiber72Chunk21 &&
    ttReverseFiber72Chunk22 &&
    ttReverseFiber72Chunk23 &&
    ttReverseFiber72Chunk24 &&
    ttReverseFiber72Chunk25 &&
    ttReverseFiber72Chunk26 &&
    ttReverseFiber72Chunk27 &&
    ttReverseFiber72Chunk28 &&
    ttReverseFiber72Chunk29 &&
    ttReverseFiber72Chunk30 &&
    ttReverseFiber72Chunk31 &&
    ttReverseFiber73Chunk0 &&
    ttReverseFiber73Chunk1 &&
    ttReverseFiber73Chunk2 &&
    ttReverseFiber73Chunk3 &&
    ttReverseFiber74Chunk0 &&
    ttReverseFiber74Chunk1 &&
    ttReverseFiber74Chunk2 &&
    ttReverseFiber74Chunk3

theorem ttReverseChunkGroup21_ok : ttReverseChunkGroup21 = true := by
  simp [ttReverseChunkGroup21,
    ttReverseFiber72Chunk20_ok,
    ttReverseFiber72Chunk21_ok,
    ttReverseFiber72Chunk22_ok,
    ttReverseFiber72Chunk23_ok,
    ttReverseFiber72Chunk24_ok,
    ttReverseFiber72Chunk25_ok,
    ttReverseFiber72Chunk26_ok,
    ttReverseFiber72Chunk27_ok,
    ttReverseFiber72Chunk28_ok,
    ttReverseFiber72Chunk29_ok,
    ttReverseFiber72Chunk30_ok,
    ttReverseFiber72Chunk31_ok,
    ttReverseFiber73Chunk0_ok,
    ttReverseFiber73Chunk1_ok,
    ttReverseFiber73Chunk2_ok,
    ttReverseFiber73Chunk3_ok,
    ttReverseFiber74Chunk0_ok,
    ttReverseFiber74Chunk1_ok,
    ttReverseFiber74Chunk2_ok,
    ttReverseFiber74Chunk3_ok]

def ttReverseChunkGroup22 : Bool :=
  ttReverseFiber75Chunk0 &&
    ttReverseFiber75Chunk1 &&
    ttReverseFiber75Chunk2 &&
    ttReverseFiber75Chunk3 &&
    ttReverseFiber76Chunk0 &&
    ttReverseFiber76Chunk1 &&
    ttReverseFiber76Chunk2 &&
    ttReverseFiber76Chunk3 &&
    ttReverseFiber76Chunk4 &&
    ttReverseFiber76Chunk5 &&
    ttReverseFiber76Chunk6 &&
    ttReverseFiber76Chunk7 &&
    ttReverseFiber76Chunk8 &&
    ttReverseFiber76Chunk9 &&
    ttReverseFiber76Chunk10 &&
    ttReverseFiber76Chunk11 &&
    ttReverseFiber76Chunk12 &&
    ttReverseFiber76Chunk13 &&
    ttReverseFiber76Chunk14 &&
    ttReverseFiber76Chunk15

theorem ttReverseChunkGroup22_ok : ttReverseChunkGroup22 = true := by
  simp [ttReverseChunkGroup22,
    ttReverseFiber75Chunk0_ok,
    ttReverseFiber75Chunk1_ok,
    ttReverseFiber75Chunk2_ok,
    ttReverseFiber75Chunk3_ok,
    ttReverseFiber76Chunk0_ok,
    ttReverseFiber76Chunk1_ok,
    ttReverseFiber76Chunk2_ok,
    ttReverseFiber76Chunk3_ok,
    ttReverseFiber76Chunk4_ok,
    ttReverseFiber76Chunk5_ok,
    ttReverseFiber76Chunk6_ok,
    ttReverseFiber76Chunk7_ok,
    ttReverseFiber76Chunk8_ok,
    ttReverseFiber76Chunk9_ok,
    ttReverseFiber76Chunk10_ok,
    ttReverseFiber76Chunk11_ok,
    ttReverseFiber76Chunk12_ok,
    ttReverseFiber76Chunk13_ok,
    ttReverseFiber76Chunk14_ok,
    ttReverseFiber76Chunk15_ok]

def ttReverseChunkGroup23 : Bool :=
  ttReverseFiber76Chunk16 &&
    ttReverseFiber76Chunk17 &&
    ttReverseFiber76Chunk18 &&
    ttReverseFiber76Chunk19 &&
    ttReverseFiber76Chunk20 &&
    ttReverseFiber76Chunk21 &&
    ttReverseFiber76Chunk22 &&
    ttReverseFiber76Chunk23 &&
    ttReverseFiber76Chunk24 &&
    ttReverseFiber76Chunk25 &&
    ttReverseFiber76Chunk26 &&
    ttReverseFiber76Chunk27 &&
    ttReverseFiber76Chunk28 &&
    ttReverseFiber76Chunk29 &&
    ttReverseFiber76Chunk30 &&
    ttReverseFiber76Chunk31 &&
    ttReverseFiber77Chunk0 &&
    ttReverseFiber77Chunk1 &&
    ttReverseFiber77Chunk2 &&
    ttReverseFiber77Chunk3

theorem ttReverseChunkGroup23_ok : ttReverseChunkGroup23 = true := by
  simp [ttReverseChunkGroup23,
    ttReverseFiber76Chunk16_ok,
    ttReverseFiber76Chunk17_ok,
    ttReverseFiber76Chunk18_ok,
    ttReverseFiber76Chunk19_ok,
    ttReverseFiber76Chunk20_ok,
    ttReverseFiber76Chunk21_ok,
    ttReverseFiber76Chunk22_ok,
    ttReverseFiber76Chunk23_ok,
    ttReverseFiber76Chunk24_ok,
    ttReverseFiber76Chunk25_ok,
    ttReverseFiber76Chunk26_ok,
    ttReverseFiber76Chunk27_ok,
    ttReverseFiber76Chunk28_ok,
    ttReverseFiber76Chunk29_ok,
    ttReverseFiber76Chunk30_ok,
    ttReverseFiber76Chunk31_ok,
    ttReverseFiber77Chunk0_ok,
    ttReverseFiber77Chunk1_ok,
    ttReverseFiber77Chunk2_ok,
    ttReverseFiber77Chunk3_ok]

def ttReverseAllFiberChunkAudit : Bool :=
  ttReverseChunkGroup0 &&
    ttReverseChunkGroup1 &&
    ttReverseChunkGroup2 &&
    ttReverseChunkGroup3 &&
    ttReverseChunkGroup4 &&
    ttReverseChunkGroup5 &&
    ttReverseChunkGroup6 &&
    ttReverseChunkGroup7 &&
    ttReverseChunkGroup8 &&
    ttReverseChunkGroup9 &&
    ttReverseChunkGroup10 &&
    ttReverseChunkGroup11 &&
    ttReverseChunkGroup12 &&
    ttReverseChunkGroup13 &&
    ttReverseChunkGroup14 &&
    ttReverseChunkGroup15 &&
    ttReverseChunkGroup16 &&
    ttReverseChunkGroup17 &&
    ttReverseChunkGroup18 &&
    ttReverseChunkGroup19 &&
    ttReverseChunkGroup20 &&
    ttReverseChunkGroup21 &&
    ttReverseChunkGroup22 &&
    ttReverseChunkGroup23

theorem ttReverseAllFiberChunkAudit_ok :
    ttReverseAllFiberChunkAudit = true := by
  simp [ttReverseAllFiberChunkAudit,
    ttReverseChunkGroup0_ok,
    ttReverseChunkGroup1_ok,
    ttReverseChunkGroup2_ok,
    ttReverseChunkGroup3_ok,
    ttReverseChunkGroup4_ok,
    ttReverseChunkGroup5_ok,
    ttReverseChunkGroup6_ok,
    ttReverseChunkGroup7_ok,
    ttReverseChunkGroup8_ok,
    ttReverseChunkGroup9_ok,
    ttReverseChunkGroup10_ok,
    ttReverseChunkGroup11_ok,
    ttReverseChunkGroup12_ok,
    ttReverseChunkGroup13_ok,
    ttReverseChunkGroup14_ok,
    ttReverseChunkGroup15_ok,
    ttReverseChunkGroup16_ok,
    ttReverseChunkGroup17_ok,
    ttReverseChunkGroup18_ok,
    ttReverseChunkGroup19_ok,
    ttReverseChunkGroup20_ok,
    ttReverseChunkGroup21_ok,
    ttReverseChunkGroup22_ok,
    ttReverseChunkGroup23_ok]

end GoertzelLemma818CompositeReverseAudit

end Mettapedia.GraphTheory.FourColor
