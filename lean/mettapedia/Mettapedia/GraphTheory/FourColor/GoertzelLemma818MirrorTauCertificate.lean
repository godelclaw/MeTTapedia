import Mettapedia.GraphTheory.FourColor.GoertzelLemma818CompositeCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: generated `mirror-normal` length-2 certificate

This file checks the generated direct parent/path table for all 81
fixed-input keys of the `mirror-normal` composite.  The checks are row-split;
the all-chain frontier/DFA lift is a separate theorem.
-/

namespace GoertzelLemma818MirrorTauCertificate

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def mtWord : List TauOrient :=
  [TauOrient.mirror, TauOrient.normal]

def mtNonemptyFiberCount : Nat := 36
def mtCompositeStateCount : Nat := 1152
def mtMaxParentDepth : Nat := 4

def mtRowValid (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) : Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := directStates row.sourceLeft row.sourceRight
    let t := directStates row.parentLeft row.parentRight
    compatibleChainStates mtWord s && compatibleChainStates mtWord t &&
      chainInputKey mtWord s == key && chainInputKey mtWord t == key &&
        (row.source == row.parent || chainSpecifiedKempeStep mtWord s t row.move)

def mtFiber0Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.r]

def mtFiber0Expected : List Nat :=
  []

def mtFiber0Rows : List DirectChainParentRow :=
  []

def mtFiber0RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber0Rows i default

def mtFiber0SourcesCheck : Bool :=
  (mtFiber0Rows.map fun row => row.source) == mtFiber0Expected

theorem mtFiber0SourcesCheck_ok :
    mtFiber0SourcesCheck = true := by
  decide

def mtFiber0RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber0Key mtFiber0Expected (mtFiber0RowAt i)

def mtFiber0ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber0Rows mtMaxParentDepth (listGetD mtFiber0Expected i 0) == 0

def mtFiber0CertificateAudit : Bool :=
  mtFiber0SourcesCheck

theorem mtFiber0CertificateAudit_ok :
    mtFiber0CertificateAudit = true := by
  simp [mtFiber0CertificateAudit,
    mtFiber0SourcesCheck_ok]

def mtFiber1Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.b]

def mtFiber1Expected : List Nat :=
  []

def mtFiber1Rows : List DirectChainParentRow :=
  []

def mtFiber1RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber1Rows i default

def mtFiber1SourcesCheck : Bool :=
  (mtFiber1Rows.map fun row => row.source) == mtFiber1Expected

theorem mtFiber1SourcesCheck_ok :
    mtFiber1SourcesCheck = true := by
  decide

def mtFiber1RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber1Key mtFiber1Expected (mtFiber1RowAt i)

def mtFiber1ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber1Rows mtMaxParentDepth (listGetD mtFiber1Expected i 0) == 0

def mtFiber1CertificateAudit : Bool :=
  mtFiber1SourcesCheck

theorem mtFiber1CertificateAudit_ok :
    mtFiber1CertificateAudit = true := by
  simp [mtFiber1CertificateAudit,
    mtFiber1SourcesCheck_ok]

def mtFiber2Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.p]

def mtFiber2Expected : List Nat :=
  []

def mtFiber2Rows : List DirectChainParentRow :=
  []

def mtFiber2RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber2Rows i default

def mtFiber2SourcesCheck : Bool :=
  (mtFiber2Rows.map fun row => row.source) == mtFiber2Expected

theorem mtFiber2SourcesCheck_ok :
    mtFiber2SourcesCheck = true := by
  decide

def mtFiber2RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber2Key mtFiber2Expected (mtFiber2RowAt i)

def mtFiber2ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber2Rows mtMaxParentDepth (listGetD mtFiber2Expected i 0) == 0

def mtFiber2CertificateAudit : Bool :=
  mtFiber2SourcesCheck

theorem mtFiber2CertificateAudit_ok :
    mtFiber2CertificateAudit = true := by
  simp [mtFiber2CertificateAudit,
    mtFiber2SourcesCheck_ok]

def mtFiber3Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.r]

def mtFiber3Expected : List Nat :=
  [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]

def mtFiber3Rows : List DirectChainParentRow :=
  [ directRow 720 720 120 44 120 44 default
  , directRow 721 720 120 45 120 44 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 722 721 120 46 120 45 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 723 720 120 47 120 44 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 724 720 121 36 120 44 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 725 721 121 37 120 45 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 726 722 121 38 120 46 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 727 723 121 39 120 47 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 728 720 122 60 120 44 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 729 721 122 61 120 45 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 730 722 122 62 120 46 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 731 723 122 63 120 47 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 732 724 123 52 121 36 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 733 725 123 53 121 37 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 734 726 123 54 121 38 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 735 727 123 55 121 39 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber3RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber3Rows i default

def mtFiber3SourcesCheck : Bool :=
  (mtFiber3Rows.map fun row => row.source) == mtFiber3Expected

theorem mtFiber3SourcesCheck_ok :
    mtFiber3SourcesCheck = true := by
  decide

def mtFiber3RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt i)

theorem mtFiber3Row_0_ok : mtFiber3RowCheck 0 = true := by decide
theorem mtFiber3Row_1_ok : mtFiber3RowCheck 1 = true := by decide
theorem mtFiber3Row_2_ok : mtFiber3RowCheck 2 = true := by decide
theorem mtFiber3Row_3_ok : mtFiber3RowCheck 3 = true := by decide
theorem mtFiber3Row_4_ok : mtFiber3RowCheck 4 = true := by decide
theorem mtFiber3Row_5_ok : mtFiber3RowCheck 5 = true := by decide
theorem mtFiber3Row_6_ok : mtFiber3RowCheck 6 = true := by decide
theorem mtFiber3Row_7_ok : mtFiber3RowCheck 7 = true := by decide
theorem mtFiber3Row_8_ok : mtFiber3RowCheck 8 = true := by decide
theorem mtFiber3Row_9_ok : mtFiber3RowCheck 9 = true := by decide
theorem mtFiber3Row_10_ok : mtFiber3RowCheck 10 = true := by decide
theorem mtFiber3Row_11_ok : mtFiber3RowCheck 11 = true := by decide
theorem mtFiber3Row_12_ok : mtFiber3RowCheck 12 = true := by decide
theorem mtFiber3Row_13_ok : mtFiber3RowCheck 13 = true := by decide
theorem mtFiber3Row_14_ok : mtFiber3RowCheck 14 = true := by decide
theorem mtFiber3Row_15_ok : mtFiber3RowCheck 15 = true := by decide

def mtFiber3ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber3Rows mtMaxParentDepth (listGetD mtFiber3Expected i 0) == 720

theorem mtFiber3Parent_0_ok : mtFiber3ParentCheck 0 = true := by decide
theorem mtFiber3Parent_1_ok : mtFiber3ParentCheck 1 = true := by decide
theorem mtFiber3Parent_2_ok : mtFiber3ParentCheck 2 = true := by decide
theorem mtFiber3Parent_3_ok : mtFiber3ParentCheck 3 = true := by decide
theorem mtFiber3Parent_4_ok : mtFiber3ParentCheck 4 = true := by decide
theorem mtFiber3Parent_5_ok : mtFiber3ParentCheck 5 = true := by decide
theorem mtFiber3Parent_6_ok : mtFiber3ParentCheck 6 = true := by decide
theorem mtFiber3Parent_7_ok : mtFiber3ParentCheck 7 = true := by decide
theorem mtFiber3Parent_8_ok : mtFiber3ParentCheck 8 = true := by decide
theorem mtFiber3Parent_9_ok : mtFiber3ParentCheck 9 = true := by decide
theorem mtFiber3Parent_10_ok : mtFiber3ParentCheck 10 = true := by decide
theorem mtFiber3Parent_11_ok : mtFiber3ParentCheck 11 = true := by decide
theorem mtFiber3Parent_12_ok : mtFiber3ParentCheck 12 = true := by decide
theorem mtFiber3Parent_13_ok : mtFiber3ParentCheck 13 = true := by decide
theorem mtFiber3Parent_14_ok : mtFiber3ParentCheck 14 = true := by decide
theorem mtFiber3Parent_15_ok : mtFiber3ParentCheck 15 = true := by decide

def mtFiber3CertificateAudit : Bool :=
  mtFiber3SourcesCheck &&
    mtFiber3RowCheck 0 &&
    mtFiber3RowCheck 1 &&
    mtFiber3RowCheck 2 &&
    mtFiber3RowCheck 3 &&
    mtFiber3RowCheck 4 &&
    mtFiber3RowCheck 5 &&
    mtFiber3RowCheck 6 &&
    mtFiber3RowCheck 7 &&
    mtFiber3RowCheck 8 &&
    mtFiber3RowCheck 9 &&
    mtFiber3RowCheck 10 &&
    mtFiber3RowCheck 11 &&
    mtFiber3RowCheck 12 &&
    mtFiber3RowCheck 13 &&
    mtFiber3RowCheck 14 &&
    mtFiber3RowCheck 15 &&
    mtFiber3ParentCheck 0 &&
    mtFiber3ParentCheck 1 &&
    mtFiber3ParentCheck 2 &&
    mtFiber3ParentCheck 3 &&
    mtFiber3ParentCheck 4 &&
    mtFiber3ParentCheck 5 &&
    mtFiber3ParentCheck 6 &&
    mtFiber3ParentCheck 7 &&
    mtFiber3ParentCheck 8 &&
    mtFiber3ParentCheck 9 &&
    mtFiber3ParentCheck 10 &&
    mtFiber3ParentCheck 11 &&
    mtFiber3ParentCheck 12 &&
    mtFiber3ParentCheck 13 &&
    mtFiber3ParentCheck 14 &&
    mtFiber3ParentCheck 15

theorem mtFiber3CertificateAudit_ok :
    mtFiber3CertificateAudit = true := by
  simp [mtFiber3CertificateAudit,
    mtFiber3SourcesCheck_ok,
    mtFiber3Row_0_ok,
    mtFiber3Row_1_ok,
    mtFiber3Row_2_ok,
    mtFiber3Row_3_ok,
    mtFiber3Row_4_ok,
    mtFiber3Row_5_ok,
    mtFiber3Row_6_ok,
    mtFiber3Row_7_ok,
    mtFiber3Row_8_ok,
    mtFiber3Row_9_ok,
    mtFiber3Row_10_ok,
    mtFiber3Row_11_ok,
    mtFiber3Row_12_ok,
    mtFiber3Row_13_ok,
    mtFiber3Row_14_ok,
    mtFiber3Row_15_ok,
    mtFiber3Parent_0_ok,
    mtFiber3Parent_1_ok,
    mtFiber3Parent_2_ok,
    mtFiber3Parent_3_ok,
    mtFiber3Parent_4_ok,
    mtFiber3Parent_5_ok,
    mtFiber3Parent_6_ok,
    mtFiber3Parent_7_ok,
    mtFiber3Parent_8_ok,
    mtFiber3Parent_9_ok,
    mtFiber3Parent_10_ok,
    mtFiber3Parent_11_ok,
    mtFiber3Parent_12_ok,
    mtFiber3Parent_13_ok,
    mtFiber3Parent_14_ok,
    mtFiber3Parent_15_ok]

def mtFiber4Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.b]

def mtFiber4Expected : List Nat :=
  [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]

def mtFiber4Rows : List DirectChainParentRow :=
  [ directRow 48 48 8 156 8 156 default
  , directRow 49 48 8 157 8 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 50 49 8 158 8 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 51 48 8 159 8 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 52 48 8 172 8 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 53 49 8 173 8 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 54 52 8 174 8 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 55 51 8 175 8 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 56 48 9 148 8 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 57 49 9 149 8 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 58 50 9 150 8 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 59 51 9 151 8 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 60 52 9 164 8 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 61 53 9 165 8 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 62 54 9 166 8 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 63 55 9 167 8 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 64 48 10 140 8 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 65 49 10 141 8 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 66 50 10 142 8 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 67 51 10 143 8 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 68 52 10 188 8 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 69 53 10 189 8 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 70 54 10 190 8 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 71 55 10 191 8 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 72 56 11 132 9 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 73 57 11 133 9 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 74 58 11 134 9 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 75 59 11 135 9 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 76 60 11 180 9 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 77 61 11 181 9 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 78 62 11 182 9 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 79 63 11 183 9 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 336 48 56 88 8 156 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 337 49 56 89 8 157 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 338 336 56 90 56 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 339 51 56 91 8 159 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 340 52 56 108 8 172 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 341 53 56 109 8 173 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 342 337 56 110 56 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 343 336 56 111 56 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 344 56 57 80 9 148 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 345 57 57 81 9 149 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 346 344 57 82 57 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 347 59 57 83 9 151 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 348 60 57 100 9 164 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 349 61 57 101 9 165 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 350 345 57 102 57 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 351 344 57 103 57 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 352 64 58 72 10 140 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 353 65 58 73 10 141 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 354 352 58 74 58 72 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 355 67 58 75 10 143 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 356 68 58 124 10 188 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 357 69 58 125 10 189 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 358 353 58 126 58 73 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 359 352 58 127 58 72 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 360 336 59 64 56 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 361 337 59 65 56 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 362 338 59 66 56 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 363 339 59 67 56 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 364 340 59 116 56 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 365 341 59 117 56 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 366 342 59 118 56 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 367 343 59 119 56 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber4RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber4Rows i default

def mtFiber4SourcesCheck : Bool :=
  (mtFiber4Rows.map fun row => row.source) == mtFiber4Expected

theorem mtFiber4SourcesCheck_ok :
    mtFiber4SourcesCheck = true := by
  decide

def mtFiber4RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt i)

theorem mtFiber4Row_0_ok : mtFiber4RowCheck 0 = true := by decide
theorem mtFiber4Row_1_ok : mtFiber4RowCheck 1 = true := by decide
theorem mtFiber4Row_2_ok : mtFiber4RowCheck 2 = true := by decide
theorem mtFiber4Row_3_ok : mtFiber4RowCheck 3 = true := by decide
theorem mtFiber4Row_4_ok : mtFiber4RowCheck 4 = true := by decide
theorem mtFiber4Row_5_ok : mtFiber4RowCheck 5 = true := by decide
theorem mtFiber4Row_6_ok : mtFiber4RowCheck 6 = true := by decide
theorem mtFiber4Row_7_ok : mtFiber4RowCheck 7 = true := by decide
theorem mtFiber4Row_8_ok : mtFiber4RowCheck 8 = true := by decide
theorem mtFiber4Row_9_ok : mtFiber4RowCheck 9 = true := by decide
theorem mtFiber4Row_10_ok : mtFiber4RowCheck 10 = true := by decide
theorem mtFiber4Row_11_ok : mtFiber4RowCheck 11 = true := by decide
theorem mtFiber4Row_12_ok : mtFiber4RowCheck 12 = true := by decide
theorem mtFiber4Row_13_ok : mtFiber4RowCheck 13 = true := by decide
theorem mtFiber4Row_14_ok : mtFiber4RowCheck 14 = true := by decide
theorem mtFiber4Row_15_ok : mtFiber4RowCheck 15 = true := by decide
theorem mtFiber4Row_16_ok : mtFiber4RowCheck 16 = true := by decide
theorem mtFiber4Row_17_ok : mtFiber4RowCheck 17 = true := by decide
theorem mtFiber4Row_18_ok : mtFiber4RowCheck 18 = true := by decide
theorem mtFiber4Row_19_ok : mtFiber4RowCheck 19 = true := by decide
theorem mtFiber4Row_20_ok : mtFiber4RowCheck 20 = true := by decide
theorem mtFiber4Row_21_ok : mtFiber4RowCheck 21 = true := by decide
theorem mtFiber4Row_22_ok : mtFiber4RowCheck 22 = true := by decide
theorem mtFiber4Row_23_ok : mtFiber4RowCheck 23 = true := by decide
theorem mtFiber4Row_24_ok : mtFiber4RowCheck 24 = true := by decide
theorem mtFiber4Row_25_ok : mtFiber4RowCheck 25 = true := by decide
theorem mtFiber4Row_26_ok : mtFiber4RowCheck 26 = true := by decide
theorem mtFiber4Row_27_ok : mtFiber4RowCheck 27 = true := by decide
theorem mtFiber4Row_28_ok : mtFiber4RowCheck 28 = true := by decide
theorem mtFiber4Row_29_ok : mtFiber4RowCheck 29 = true := by decide
theorem mtFiber4Row_30_ok : mtFiber4RowCheck 30 = true := by decide
theorem mtFiber4Row_31_ok : mtFiber4RowCheck 31 = true := by decide
theorem mtFiber4Row_32_ok : mtFiber4RowCheck 32 = true := by decide
theorem mtFiber4Row_33_ok : mtFiber4RowCheck 33 = true := by decide
theorem mtFiber4Row_34_ok : mtFiber4RowCheck 34 = true := by decide
theorem mtFiber4Row_35_ok : mtFiber4RowCheck 35 = true := by decide
theorem mtFiber4Row_36_ok : mtFiber4RowCheck 36 = true := by decide
theorem mtFiber4Row_37_ok : mtFiber4RowCheck 37 = true := by decide
theorem mtFiber4Row_38_ok : mtFiber4RowCheck 38 = true := by decide
theorem mtFiber4Row_39_ok : mtFiber4RowCheck 39 = true := by decide
theorem mtFiber4Row_40_ok : mtFiber4RowCheck 40 = true := by decide
theorem mtFiber4Row_41_ok : mtFiber4RowCheck 41 = true := by decide
theorem mtFiber4Row_42_ok : mtFiber4RowCheck 42 = true := by decide
theorem mtFiber4Row_43_ok : mtFiber4RowCheck 43 = true := by decide
theorem mtFiber4Row_44_ok : mtFiber4RowCheck 44 = true := by decide
theorem mtFiber4Row_45_ok : mtFiber4RowCheck 45 = true := by decide
theorem mtFiber4Row_46_ok : mtFiber4RowCheck 46 = true := by decide
theorem mtFiber4Row_47_ok : mtFiber4RowCheck 47 = true := by decide
theorem mtFiber4Row_48_ok : mtFiber4RowCheck 48 = true := by decide
theorem mtFiber4Row_49_ok : mtFiber4RowCheck 49 = true := by decide
theorem mtFiber4Row_50_ok : mtFiber4RowCheck 50 = true := by decide
theorem mtFiber4Row_51_ok : mtFiber4RowCheck 51 = true := by decide
theorem mtFiber4Row_52_ok : mtFiber4RowCheck 52 = true := by decide
theorem mtFiber4Row_53_ok : mtFiber4RowCheck 53 = true := by decide
theorem mtFiber4Row_54_ok : mtFiber4RowCheck 54 = true := by decide
theorem mtFiber4Row_55_ok : mtFiber4RowCheck 55 = true := by decide
theorem mtFiber4Row_56_ok : mtFiber4RowCheck 56 = true := by decide
theorem mtFiber4Row_57_ok : mtFiber4RowCheck 57 = true := by decide
theorem mtFiber4Row_58_ok : mtFiber4RowCheck 58 = true := by decide
theorem mtFiber4Row_59_ok : mtFiber4RowCheck 59 = true := by decide
theorem mtFiber4Row_60_ok : mtFiber4RowCheck 60 = true := by decide
theorem mtFiber4Row_61_ok : mtFiber4RowCheck 61 = true := by decide
theorem mtFiber4Row_62_ok : mtFiber4RowCheck 62 = true := by decide
theorem mtFiber4Row_63_ok : mtFiber4RowCheck 63 = true := by decide

def mtFiber4ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber4Rows mtMaxParentDepth (listGetD mtFiber4Expected i 0) == 48

theorem mtFiber4Parent_0_ok : mtFiber4ParentCheck 0 = true := by decide
theorem mtFiber4Parent_1_ok : mtFiber4ParentCheck 1 = true := by decide
theorem mtFiber4Parent_2_ok : mtFiber4ParentCheck 2 = true := by decide
theorem mtFiber4Parent_3_ok : mtFiber4ParentCheck 3 = true := by decide
theorem mtFiber4Parent_4_ok : mtFiber4ParentCheck 4 = true := by decide
theorem mtFiber4Parent_5_ok : mtFiber4ParentCheck 5 = true := by decide
theorem mtFiber4Parent_6_ok : mtFiber4ParentCheck 6 = true := by decide
theorem mtFiber4Parent_7_ok : mtFiber4ParentCheck 7 = true := by decide
theorem mtFiber4Parent_8_ok : mtFiber4ParentCheck 8 = true := by decide
theorem mtFiber4Parent_9_ok : mtFiber4ParentCheck 9 = true := by decide
theorem mtFiber4Parent_10_ok : mtFiber4ParentCheck 10 = true := by decide
theorem mtFiber4Parent_11_ok : mtFiber4ParentCheck 11 = true := by decide
theorem mtFiber4Parent_12_ok : mtFiber4ParentCheck 12 = true := by decide
theorem mtFiber4Parent_13_ok : mtFiber4ParentCheck 13 = true := by decide
theorem mtFiber4Parent_14_ok : mtFiber4ParentCheck 14 = true := by decide
theorem mtFiber4Parent_15_ok : mtFiber4ParentCheck 15 = true := by decide
theorem mtFiber4Parent_16_ok : mtFiber4ParentCheck 16 = true := by decide
theorem mtFiber4Parent_17_ok : mtFiber4ParentCheck 17 = true := by decide
theorem mtFiber4Parent_18_ok : mtFiber4ParentCheck 18 = true := by decide
theorem mtFiber4Parent_19_ok : mtFiber4ParentCheck 19 = true := by decide
theorem mtFiber4Parent_20_ok : mtFiber4ParentCheck 20 = true := by decide
theorem mtFiber4Parent_21_ok : mtFiber4ParentCheck 21 = true := by decide
theorem mtFiber4Parent_22_ok : mtFiber4ParentCheck 22 = true := by decide
theorem mtFiber4Parent_23_ok : mtFiber4ParentCheck 23 = true := by decide
theorem mtFiber4Parent_24_ok : mtFiber4ParentCheck 24 = true := by decide
theorem mtFiber4Parent_25_ok : mtFiber4ParentCheck 25 = true := by decide
theorem mtFiber4Parent_26_ok : mtFiber4ParentCheck 26 = true := by decide
theorem mtFiber4Parent_27_ok : mtFiber4ParentCheck 27 = true := by decide
theorem mtFiber4Parent_28_ok : mtFiber4ParentCheck 28 = true := by decide
theorem mtFiber4Parent_29_ok : mtFiber4ParentCheck 29 = true := by decide
theorem mtFiber4Parent_30_ok : mtFiber4ParentCheck 30 = true := by decide
theorem mtFiber4Parent_31_ok : mtFiber4ParentCheck 31 = true := by decide
theorem mtFiber4Parent_32_ok : mtFiber4ParentCheck 32 = true := by decide
theorem mtFiber4Parent_33_ok : mtFiber4ParentCheck 33 = true := by decide
theorem mtFiber4Parent_34_ok : mtFiber4ParentCheck 34 = true := by decide
theorem mtFiber4Parent_35_ok : mtFiber4ParentCheck 35 = true := by decide
theorem mtFiber4Parent_36_ok : mtFiber4ParentCheck 36 = true := by decide
theorem mtFiber4Parent_37_ok : mtFiber4ParentCheck 37 = true := by decide
theorem mtFiber4Parent_38_ok : mtFiber4ParentCheck 38 = true := by decide
theorem mtFiber4Parent_39_ok : mtFiber4ParentCheck 39 = true := by decide
theorem mtFiber4Parent_40_ok : mtFiber4ParentCheck 40 = true := by decide
theorem mtFiber4Parent_41_ok : mtFiber4ParentCheck 41 = true := by decide
theorem mtFiber4Parent_42_ok : mtFiber4ParentCheck 42 = true := by decide
theorem mtFiber4Parent_43_ok : mtFiber4ParentCheck 43 = true := by decide
theorem mtFiber4Parent_44_ok : mtFiber4ParentCheck 44 = true := by decide
theorem mtFiber4Parent_45_ok : mtFiber4ParentCheck 45 = true := by decide
theorem mtFiber4Parent_46_ok : mtFiber4ParentCheck 46 = true := by decide
theorem mtFiber4Parent_47_ok : mtFiber4ParentCheck 47 = true := by decide
theorem mtFiber4Parent_48_ok : mtFiber4ParentCheck 48 = true := by decide
theorem mtFiber4Parent_49_ok : mtFiber4ParentCheck 49 = true := by decide
theorem mtFiber4Parent_50_ok : mtFiber4ParentCheck 50 = true := by decide
theorem mtFiber4Parent_51_ok : mtFiber4ParentCheck 51 = true := by decide
theorem mtFiber4Parent_52_ok : mtFiber4ParentCheck 52 = true := by decide
theorem mtFiber4Parent_53_ok : mtFiber4ParentCheck 53 = true := by decide
theorem mtFiber4Parent_54_ok : mtFiber4ParentCheck 54 = true := by decide
theorem mtFiber4Parent_55_ok : mtFiber4ParentCheck 55 = true := by decide
theorem mtFiber4Parent_56_ok : mtFiber4ParentCheck 56 = true := by decide
theorem mtFiber4Parent_57_ok : mtFiber4ParentCheck 57 = true := by decide
theorem mtFiber4Parent_58_ok : mtFiber4ParentCheck 58 = true := by decide
theorem mtFiber4Parent_59_ok : mtFiber4ParentCheck 59 = true := by decide
theorem mtFiber4Parent_60_ok : mtFiber4ParentCheck 60 = true := by decide
theorem mtFiber4Parent_61_ok : mtFiber4ParentCheck 61 = true := by decide
theorem mtFiber4Parent_62_ok : mtFiber4ParentCheck 62 = true := by decide
theorem mtFiber4Parent_63_ok : mtFiber4ParentCheck 63 = true := by decide

def mtFiber4CertificateAudit : Bool :=
  mtFiber4SourcesCheck &&
    mtFiber4RowCheck 0 &&
    mtFiber4RowCheck 1 &&
    mtFiber4RowCheck 2 &&
    mtFiber4RowCheck 3 &&
    mtFiber4RowCheck 4 &&
    mtFiber4RowCheck 5 &&
    mtFiber4RowCheck 6 &&
    mtFiber4RowCheck 7 &&
    mtFiber4RowCheck 8 &&
    mtFiber4RowCheck 9 &&
    mtFiber4RowCheck 10 &&
    mtFiber4RowCheck 11 &&
    mtFiber4RowCheck 12 &&
    mtFiber4RowCheck 13 &&
    mtFiber4RowCheck 14 &&
    mtFiber4RowCheck 15 &&
    mtFiber4RowCheck 16 &&
    mtFiber4RowCheck 17 &&
    mtFiber4RowCheck 18 &&
    mtFiber4RowCheck 19 &&
    mtFiber4RowCheck 20 &&
    mtFiber4RowCheck 21 &&
    mtFiber4RowCheck 22 &&
    mtFiber4RowCheck 23 &&
    mtFiber4RowCheck 24 &&
    mtFiber4RowCheck 25 &&
    mtFiber4RowCheck 26 &&
    mtFiber4RowCheck 27 &&
    mtFiber4RowCheck 28 &&
    mtFiber4RowCheck 29 &&
    mtFiber4RowCheck 30 &&
    mtFiber4RowCheck 31 &&
    mtFiber4RowCheck 32 &&
    mtFiber4RowCheck 33 &&
    mtFiber4RowCheck 34 &&
    mtFiber4RowCheck 35 &&
    mtFiber4RowCheck 36 &&
    mtFiber4RowCheck 37 &&
    mtFiber4RowCheck 38 &&
    mtFiber4RowCheck 39 &&
    mtFiber4RowCheck 40 &&
    mtFiber4RowCheck 41 &&
    mtFiber4RowCheck 42 &&
    mtFiber4RowCheck 43 &&
    mtFiber4RowCheck 44 &&
    mtFiber4RowCheck 45 &&
    mtFiber4RowCheck 46 &&
    mtFiber4RowCheck 47 &&
    mtFiber4RowCheck 48 &&
    mtFiber4RowCheck 49 &&
    mtFiber4RowCheck 50 &&
    mtFiber4RowCheck 51 &&
    mtFiber4RowCheck 52 &&
    mtFiber4RowCheck 53 &&
    mtFiber4RowCheck 54 &&
    mtFiber4RowCheck 55 &&
    mtFiber4RowCheck 56 &&
    mtFiber4RowCheck 57 &&
    mtFiber4RowCheck 58 &&
    mtFiber4RowCheck 59 &&
    mtFiber4RowCheck 60 &&
    mtFiber4RowCheck 61 &&
    mtFiber4RowCheck 62 &&
    mtFiber4RowCheck 63 &&
    mtFiber4ParentCheck 0 &&
    mtFiber4ParentCheck 1 &&
    mtFiber4ParentCheck 2 &&
    mtFiber4ParentCheck 3 &&
    mtFiber4ParentCheck 4 &&
    mtFiber4ParentCheck 5 &&
    mtFiber4ParentCheck 6 &&
    mtFiber4ParentCheck 7 &&
    mtFiber4ParentCheck 8 &&
    mtFiber4ParentCheck 9 &&
    mtFiber4ParentCheck 10 &&
    mtFiber4ParentCheck 11 &&
    mtFiber4ParentCheck 12 &&
    mtFiber4ParentCheck 13 &&
    mtFiber4ParentCheck 14 &&
    mtFiber4ParentCheck 15 &&
    mtFiber4ParentCheck 16 &&
    mtFiber4ParentCheck 17 &&
    mtFiber4ParentCheck 18 &&
    mtFiber4ParentCheck 19 &&
    mtFiber4ParentCheck 20 &&
    mtFiber4ParentCheck 21 &&
    mtFiber4ParentCheck 22 &&
    mtFiber4ParentCheck 23 &&
    mtFiber4ParentCheck 24 &&
    mtFiber4ParentCheck 25 &&
    mtFiber4ParentCheck 26 &&
    mtFiber4ParentCheck 27 &&
    mtFiber4ParentCheck 28 &&
    mtFiber4ParentCheck 29 &&
    mtFiber4ParentCheck 30 &&
    mtFiber4ParentCheck 31 &&
    mtFiber4ParentCheck 32 &&
    mtFiber4ParentCheck 33 &&
    mtFiber4ParentCheck 34 &&
    mtFiber4ParentCheck 35 &&
    mtFiber4ParentCheck 36 &&
    mtFiber4ParentCheck 37 &&
    mtFiber4ParentCheck 38 &&
    mtFiber4ParentCheck 39 &&
    mtFiber4ParentCheck 40 &&
    mtFiber4ParentCheck 41 &&
    mtFiber4ParentCheck 42 &&
    mtFiber4ParentCheck 43 &&
    mtFiber4ParentCheck 44 &&
    mtFiber4ParentCheck 45 &&
    mtFiber4ParentCheck 46 &&
    mtFiber4ParentCheck 47 &&
    mtFiber4ParentCheck 48 &&
    mtFiber4ParentCheck 49 &&
    mtFiber4ParentCheck 50 &&
    mtFiber4ParentCheck 51 &&
    mtFiber4ParentCheck 52 &&
    mtFiber4ParentCheck 53 &&
    mtFiber4ParentCheck 54 &&
    mtFiber4ParentCheck 55 &&
    mtFiber4ParentCheck 56 &&
    mtFiber4ParentCheck 57 &&
    mtFiber4ParentCheck 58 &&
    mtFiber4ParentCheck 59 &&
    mtFiber4ParentCheck 60 &&
    mtFiber4ParentCheck 61 &&
    mtFiber4ParentCheck 62 &&
    mtFiber4ParentCheck 63

theorem mtFiber4CertificateAudit_ok :
    mtFiber4CertificateAudit = true := by
  simp [mtFiber4CertificateAudit,
    mtFiber4SourcesCheck_ok,
    mtFiber4Row_0_ok,
    mtFiber4Row_1_ok,
    mtFiber4Row_2_ok,
    mtFiber4Row_3_ok,
    mtFiber4Row_4_ok,
    mtFiber4Row_5_ok,
    mtFiber4Row_6_ok,
    mtFiber4Row_7_ok,
    mtFiber4Row_8_ok,
    mtFiber4Row_9_ok,
    mtFiber4Row_10_ok,
    mtFiber4Row_11_ok,
    mtFiber4Row_12_ok,
    mtFiber4Row_13_ok,
    mtFiber4Row_14_ok,
    mtFiber4Row_15_ok,
    mtFiber4Row_16_ok,
    mtFiber4Row_17_ok,
    mtFiber4Row_18_ok,
    mtFiber4Row_19_ok,
    mtFiber4Row_20_ok,
    mtFiber4Row_21_ok,
    mtFiber4Row_22_ok,
    mtFiber4Row_23_ok,
    mtFiber4Row_24_ok,
    mtFiber4Row_25_ok,
    mtFiber4Row_26_ok,
    mtFiber4Row_27_ok,
    mtFiber4Row_28_ok,
    mtFiber4Row_29_ok,
    mtFiber4Row_30_ok,
    mtFiber4Row_31_ok,
    mtFiber4Row_32_ok,
    mtFiber4Row_33_ok,
    mtFiber4Row_34_ok,
    mtFiber4Row_35_ok,
    mtFiber4Row_36_ok,
    mtFiber4Row_37_ok,
    mtFiber4Row_38_ok,
    mtFiber4Row_39_ok,
    mtFiber4Row_40_ok,
    mtFiber4Row_41_ok,
    mtFiber4Row_42_ok,
    mtFiber4Row_43_ok,
    mtFiber4Row_44_ok,
    mtFiber4Row_45_ok,
    mtFiber4Row_46_ok,
    mtFiber4Row_47_ok,
    mtFiber4Row_48_ok,
    mtFiber4Row_49_ok,
    mtFiber4Row_50_ok,
    mtFiber4Row_51_ok,
    mtFiber4Row_52_ok,
    mtFiber4Row_53_ok,
    mtFiber4Row_54_ok,
    mtFiber4Row_55_ok,
    mtFiber4Row_56_ok,
    mtFiber4Row_57_ok,
    mtFiber4Row_58_ok,
    mtFiber4Row_59_ok,
    mtFiber4Row_60_ok,
    mtFiber4Row_61_ok,
    mtFiber4Row_62_ok,
    mtFiber4Row_63_ok,
    mtFiber4Parent_0_ok,
    mtFiber4Parent_1_ok,
    mtFiber4Parent_2_ok,
    mtFiber4Parent_3_ok,
    mtFiber4Parent_4_ok,
    mtFiber4Parent_5_ok,
    mtFiber4Parent_6_ok,
    mtFiber4Parent_7_ok,
    mtFiber4Parent_8_ok,
    mtFiber4Parent_9_ok,
    mtFiber4Parent_10_ok,
    mtFiber4Parent_11_ok,
    mtFiber4Parent_12_ok,
    mtFiber4Parent_13_ok,
    mtFiber4Parent_14_ok,
    mtFiber4Parent_15_ok,
    mtFiber4Parent_16_ok,
    mtFiber4Parent_17_ok,
    mtFiber4Parent_18_ok,
    mtFiber4Parent_19_ok,
    mtFiber4Parent_20_ok,
    mtFiber4Parent_21_ok,
    mtFiber4Parent_22_ok,
    mtFiber4Parent_23_ok,
    mtFiber4Parent_24_ok,
    mtFiber4Parent_25_ok,
    mtFiber4Parent_26_ok,
    mtFiber4Parent_27_ok,
    mtFiber4Parent_28_ok,
    mtFiber4Parent_29_ok,
    mtFiber4Parent_30_ok,
    mtFiber4Parent_31_ok,
    mtFiber4Parent_32_ok,
    mtFiber4Parent_33_ok,
    mtFiber4Parent_34_ok,
    mtFiber4Parent_35_ok,
    mtFiber4Parent_36_ok,
    mtFiber4Parent_37_ok,
    mtFiber4Parent_38_ok,
    mtFiber4Parent_39_ok,
    mtFiber4Parent_40_ok,
    mtFiber4Parent_41_ok,
    mtFiber4Parent_42_ok,
    mtFiber4Parent_43_ok,
    mtFiber4Parent_44_ok,
    mtFiber4Parent_45_ok,
    mtFiber4Parent_46_ok,
    mtFiber4Parent_47_ok,
    mtFiber4Parent_48_ok,
    mtFiber4Parent_49_ok,
    mtFiber4Parent_50_ok,
    mtFiber4Parent_51_ok,
    mtFiber4Parent_52_ok,
    mtFiber4Parent_53_ok,
    mtFiber4Parent_54_ok,
    mtFiber4Parent_55_ok,
    mtFiber4Parent_56_ok,
    mtFiber4Parent_57_ok,
    mtFiber4Parent_58_ok,
    mtFiber4Parent_59_ok,
    mtFiber4Parent_60_ok,
    mtFiber4Parent_61_ok,
    mtFiber4Parent_62_ok,
    mtFiber4Parent_63_ok]

def mtFiber5Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.p]

def mtFiber5Expected : List Nat :=
  []

def mtFiber5Rows : List DirectChainParentRow :=
  []

def mtFiber5RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber5Rows i default

def mtFiber5SourcesCheck : Bool :=
  (mtFiber5Rows.map fun row => row.source) == mtFiber5Expected

theorem mtFiber5SourcesCheck_ok :
    mtFiber5SourcesCheck = true := by
  decide

def mtFiber5RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber5Key mtFiber5Expected (mtFiber5RowAt i)

def mtFiber5ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber5Rows mtMaxParentDepth (listGetD mtFiber5Expected i 0) == 0

def mtFiber5CertificateAudit : Bool :=
  mtFiber5SourcesCheck

theorem mtFiber5CertificateAudit_ok :
    mtFiber5CertificateAudit = true := by
  simp [mtFiber5CertificateAudit,
    mtFiber5SourcesCheck_ok]

def mtFiber6Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.r]

def mtFiber6Expected : List Nat :=
  [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]

def mtFiber6Rows : List DirectChainParentRow :=
  [ directRow 1104 1104 184 28 184 28 default
  , directRow 1105 1104 184 29 184 28 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 1106 1104 184 30 184 28 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 1107 1105 184 31 184 29 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 1108 1104 185 20 184 28 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1109 1105 185 21 184 29 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1110 1106 185 22 184 30 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1111 1107 185 23 184 31 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1112 1104 186 12 184 28 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1113 1105 186 13 184 29 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1114 1106 186 14 184 30 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1115 1107 186 15 184 31 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1116 1108 187 4 185 20 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1117 1109 187 5 185 21 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1118 1110 187 6 185 22 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1119 1111 187 7 185 23 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber6RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber6Rows i default

def mtFiber6SourcesCheck : Bool :=
  (mtFiber6Rows.map fun row => row.source) == mtFiber6Expected

theorem mtFiber6SourcesCheck_ok :
    mtFiber6SourcesCheck = true := by
  decide

def mtFiber6RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt i)

theorem mtFiber6Row_0_ok : mtFiber6RowCheck 0 = true := by decide
theorem mtFiber6Row_1_ok : mtFiber6RowCheck 1 = true := by decide
theorem mtFiber6Row_2_ok : mtFiber6RowCheck 2 = true := by decide
theorem mtFiber6Row_3_ok : mtFiber6RowCheck 3 = true := by decide
theorem mtFiber6Row_4_ok : mtFiber6RowCheck 4 = true := by decide
theorem mtFiber6Row_5_ok : mtFiber6RowCheck 5 = true := by decide
theorem mtFiber6Row_6_ok : mtFiber6RowCheck 6 = true := by decide
theorem mtFiber6Row_7_ok : mtFiber6RowCheck 7 = true := by decide
theorem mtFiber6Row_8_ok : mtFiber6RowCheck 8 = true := by decide
theorem mtFiber6Row_9_ok : mtFiber6RowCheck 9 = true := by decide
theorem mtFiber6Row_10_ok : mtFiber6RowCheck 10 = true := by decide
theorem mtFiber6Row_11_ok : mtFiber6RowCheck 11 = true := by decide
theorem mtFiber6Row_12_ok : mtFiber6RowCheck 12 = true := by decide
theorem mtFiber6Row_13_ok : mtFiber6RowCheck 13 = true := by decide
theorem mtFiber6Row_14_ok : mtFiber6RowCheck 14 = true := by decide
theorem mtFiber6Row_15_ok : mtFiber6RowCheck 15 = true := by decide

def mtFiber6ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber6Rows mtMaxParentDepth (listGetD mtFiber6Expected i 0) == 1104

theorem mtFiber6Parent_0_ok : mtFiber6ParentCheck 0 = true := by decide
theorem mtFiber6Parent_1_ok : mtFiber6ParentCheck 1 = true := by decide
theorem mtFiber6Parent_2_ok : mtFiber6ParentCheck 2 = true := by decide
theorem mtFiber6Parent_3_ok : mtFiber6ParentCheck 3 = true := by decide
theorem mtFiber6Parent_4_ok : mtFiber6ParentCheck 4 = true := by decide
theorem mtFiber6Parent_5_ok : mtFiber6ParentCheck 5 = true := by decide
theorem mtFiber6Parent_6_ok : mtFiber6ParentCheck 6 = true := by decide
theorem mtFiber6Parent_7_ok : mtFiber6ParentCheck 7 = true := by decide
theorem mtFiber6Parent_8_ok : mtFiber6ParentCheck 8 = true := by decide
theorem mtFiber6Parent_9_ok : mtFiber6ParentCheck 9 = true := by decide
theorem mtFiber6Parent_10_ok : mtFiber6ParentCheck 10 = true := by decide
theorem mtFiber6Parent_11_ok : mtFiber6ParentCheck 11 = true := by decide
theorem mtFiber6Parent_12_ok : mtFiber6ParentCheck 12 = true := by decide
theorem mtFiber6Parent_13_ok : mtFiber6ParentCheck 13 = true := by decide
theorem mtFiber6Parent_14_ok : mtFiber6ParentCheck 14 = true := by decide
theorem mtFiber6Parent_15_ok : mtFiber6ParentCheck 15 = true := by decide

def mtFiber6CertificateAudit : Bool :=
  mtFiber6SourcesCheck &&
    mtFiber6RowCheck 0 &&
    mtFiber6RowCheck 1 &&
    mtFiber6RowCheck 2 &&
    mtFiber6RowCheck 3 &&
    mtFiber6RowCheck 4 &&
    mtFiber6RowCheck 5 &&
    mtFiber6RowCheck 6 &&
    mtFiber6RowCheck 7 &&
    mtFiber6RowCheck 8 &&
    mtFiber6RowCheck 9 &&
    mtFiber6RowCheck 10 &&
    mtFiber6RowCheck 11 &&
    mtFiber6RowCheck 12 &&
    mtFiber6RowCheck 13 &&
    mtFiber6RowCheck 14 &&
    mtFiber6RowCheck 15 &&
    mtFiber6ParentCheck 0 &&
    mtFiber6ParentCheck 1 &&
    mtFiber6ParentCheck 2 &&
    mtFiber6ParentCheck 3 &&
    mtFiber6ParentCheck 4 &&
    mtFiber6ParentCheck 5 &&
    mtFiber6ParentCheck 6 &&
    mtFiber6ParentCheck 7 &&
    mtFiber6ParentCheck 8 &&
    mtFiber6ParentCheck 9 &&
    mtFiber6ParentCheck 10 &&
    mtFiber6ParentCheck 11 &&
    mtFiber6ParentCheck 12 &&
    mtFiber6ParentCheck 13 &&
    mtFiber6ParentCheck 14 &&
    mtFiber6ParentCheck 15

theorem mtFiber6CertificateAudit_ok :
    mtFiber6CertificateAudit = true := by
  simp [mtFiber6CertificateAudit,
    mtFiber6SourcesCheck_ok,
    mtFiber6Row_0_ok,
    mtFiber6Row_1_ok,
    mtFiber6Row_2_ok,
    mtFiber6Row_3_ok,
    mtFiber6Row_4_ok,
    mtFiber6Row_5_ok,
    mtFiber6Row_6_ok,
    mtFiber6Row_7_ok,
    mtFiber6Row_8_ok,
    mtFiber6Row_9_ok,
    mtFiber6Row_10_ok,
    mtFiber6Row_11_ok,
    mtFiber6Row_12_ok,
    mtFiber6Row_13_ok,
    mtFiber6Row_14_ok,
    mtFiber6Row_15_ok,
    mtFiber6Parent_0_ok,
    mtFiber6Parent_1_ok,
    mtFiber6Parent_2_ok,
    mtFiber6Parent_3_ok,
    mtFiber6Parent_4_ok,
    mtFiber6Parent_5_ok,
    mtFiber6Parent_6_ok,
    mtFiber6Parent_7_ok,
    mtFiber6Parent_8_ok,
    mtFiber6Parent_9_ok,
    mtFiber6Parent_10_ok,
    mtFiber6Parent_11_ok,
    mtFiber6Parent_12_ok,
    mtFiber6Parent_13_ok,
    mtFiber6Parent_14_ok,
    mtFiber6Parent_15_ok]

def mtFiber7Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.b]

def mtFiber7Expected : List Nat :=
  []

def mtFiber7Rows : List DirectChainParentRow :=
  []

def mtFiber7RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber7Rows i default

def mtFiber7SourcesCheck : Bool :=
  (mtFiber7Rows.map fun row => row.source) == mtFiber7Expected

theorem mtFiber7SourcesCheck_ok :
    mtFiber7SourcesCheck = true := by
  decide

def mtFiber7RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber7Key mtFiber7Expected (mtFiber7RowAt i)

def mtFiber7ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber7Rows mtMaxParentDepth (listGetD mtFiber7Expected i 0) == 0

def mtFiber7CertificateAudit : Bool :=
  mtFiber7SourcesCheck

theorem mtFiber7CertificateAudit_ok :
    mtFiber7CertificateAudit = true := by
  simp [mtFiber7CertificateAudit,
    mtFiber7SourcesCheck_ok]

def mtFiber8Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.p]

def mtFiber8Expected : List Nat :=
  [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]

def mtFiber8Rows : List DirectChainParentRow :=
  [ directRow 144 144 24 156 24 156 default
  , directRow 145 144 24 157 24 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 146 145 24 158 24 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 147 144 24 159 24 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 148 144 24 172 24 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 149 145 24 173 24 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 150 148 24 174 24 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 151 147 24 175 24 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 152 144 25 148 24 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 153 145 25 149 24 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 154 146 25 150 24 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 155 147 25 151 24 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 156 148 25 164 24 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 157 149 25 165 24 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 158 150 25 166 24 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 159 151 25 167 24 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 160 144 26 140 24 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 161 145 26 141 24 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 162 146 26 142 24 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 163 147 26 143 24 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 164 148 26 188 24 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 165 149 26 189 24 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 166 150 26 190 24 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 167 151 26 191 24 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 168 152 27 132 25 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 169 153 27 133 25 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 170 154 27 134 25 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 171 155 27 135 25 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 172 156 27 180 25 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 173 157 27 181 25 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 174 158 27 182 25 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 175 159 27 183 25 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 240 144 40 88 24 156 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 241 145 40 89 24 157 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 242 240 40 90 40 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 243 147 40 91 24 159 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 244 148 40 108 24 172 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 245 149 40 109 24 173 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 246 241 40 110 40 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 247 240 40 111 40 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 248 152 41 80 25 148 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 249 153 41 81 25 149 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 250 248 41 82 41 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 251 155 41 83 25 151 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 252 156 41 100 25 164 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 253 157 41 101 25 165 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 254 249 41 102 41 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 255 248 41 103 41 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 256 160 42 72 26 140 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 257 161 42 73 26 141 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 258 256 42 74 42 72 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 259 163 42 75 26 143 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 260 164 42 124 26 188 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 261 165 42 125 26 189 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 262 257 42 126 42 73 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 263 256 42 127 42 72 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 264 240 43 64 40 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 265 241 43 65 40 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 266 242 43 66 40 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 267 243 43 67 40 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 268 244 43 116 40 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 269 245 43 117 40 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 270 246 43 118 40 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 271 247 43 119 40 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber8RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber8Rows i default

def mtFiber8SourcesCheck : Bool :=
  (mtFiber8Rows.map fun row => row.source) == mtFiber8Expected

theorem mtFiber8SourcesCheck_ok :
    mtFiber8SourcesCheck = true := by
  decide

def mtFiber8RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt i)

theorem mtFiber8Row_0_ok : mtFiber8RowCheck 0 = true := by decide
theorem mtFiber8Row_1_ok : mtFiber8RowCheck 1 = true := by decide
theorem mtFiber8Row_2_ok : mtFiber8RowCheck 2 = true := by decide
theorem mtFiber8Row_3_ok : mtFiber8RowCheck 3 = true := by decide
theorem mtFiber8Row_4_ok : mtFiber8RowCheck 4 = true := by decide
theorem mtFiber8Row_5_ok : mtFiber8RowCheck 5 = true := by decide
theorem mtFiber8Row_6_ok : mtFiber8RowCheck 6 = true := by decide
theorem mtFiber8Row_7_ok : mtFiber8RowCheck 7 = true := by decide
theorem mtFiber8Row_8_ok : mtFiber8RowCheck 8 = true := by decide
theorem mtFiber8Row_9_ok : mtFiber8RowCheck 9 = true := by decide
theorem mtFiber8Row_10_ok : mtFiber8RowCheck 10 = true := by decide
theorem mtFiber8Row_11_ok : mtFiber8RowCheck 11 = true := by decide
theorem mtFiber8Row_12_ok : mtFiber8RowCheck 12 = true := by decide
theorem mtFiber8Row_13_ok : mtFiber8RowCheck 13 = true := by decide
theorem mtFiber8Row_14_ok : mtFiber8RowCheck 14 = true := by decide
theorem mtFiber8Row_15_ok : mtFiber8RowCheck 15 = true := by decide
theorem mtFiber8Row_16_ok : mtFiber8RowCheck 16 = true := by decide
theorem mtFiber8Row_17_ok : mtFiber8RowCheck 17 = true := by decide
theorem mtFiber8Row_18_ok : mtFiber8RowCheck 18 = true := by decide
theorem mtFiber8Row_19_ok : mtFiber8RowCheck 19 = true := by decide
theorem mtFiber8Row_20_ok : mtFiber8RowCheck 20 = true := by decide
theorem mtFiber8Row_21_ok : mtFiber8RowCheck 21 = true := by decide
theorem mtFiber8Row_22_ok : mtFiber8RowCheck 22 = true := by decide
theorem mtFiber8Row_23_ok : mtFiber8RowCheck 23 = true := by decide
theorem mtFiber8Row_24_ok : mtFiber8RowCheck 24 = true := by decide
theorem mtFiber8Row_25_ok : mtFiber8RowCheck 25 = true := by decide
theorem mtFiber8Row_26_ok : mtFiber8RowCheck 26 = true := by decide
theorem mtFiber8Row_27_ok : mtFiber8RowCheck 27 = true := by decide
theorem mtFiber8Row_28_ok : mtFiber8RowCheck 28 = true := by decide
theorem mtFiber8Row_29_ok : mtFiber8RowCheck 29 = true := by decide
theorem mtFiber8Row_30_ok : mtFiber8RowCheck 30 = true := by decide
theorem mtFiber8Row_31_ok : mtFiber8RowCheck 31 = true := by decide
theorem mtFiber8Row_32_ok : mtFiber8RowCheck 32 = true := by decide
theorem mtFiber8Row_33_ok : mtFiber8RowCheck 33 = true := by decide
theorem mtFiber8Row_34_ok : mtFiber8RowCheck 34 = true := by decide
theorem mtFiber8Row_35_ok : mtFiber8RowCheck 35 = true := by decide
theorem mtFiber8Row_36_ok : mtFiber8RowCheck 36 = true := by decide
theorem mtFiber8Row_37_ok : mtFiber8RowCheck 37 = true := by decide
theorem mtFiber8Row_38_ok : mtFiber8RowCheck 38 = true := by decide
theorem mtFiber8Row_39_ok : mtFiber8RowCheck 39 = true := by decide
theorem mtFiber8Row_40_ok : mtFiber8RowCheck 40 = true := by decide
theorem mtFiber8Row_41_ok : mtFiber8RowCheck 41 = true := by decide
theorem mtFiber8Row_42_ok : mtFiber8RowCheck 42 = true := by decide
theorem mtFiber8Row_43_ok : mtFiber8RowCheck 43 = true := by decide
theorem mtFiber8Row_44_ok : mtFiber8RowCheck 44 = true := by decide
theorem mtFiber8Row_45_ok : mtFiber8RowCheck 45 = true := by decide
theorem mtFiber8Row_46_ok : mtFiber8RowCheck 46 = true := by decide
theorem mtFiber8Row_47_ok : mtFiber8RowCheck 47 = true := by decide
theorem mtFiber8Row_48_ok : mtFiber8RowCheck 48 = true := by decide
theorem mtFiber8Row_49_ok : mtFiber8RowCheck 49 = true := by decide
theorem mtFiber8Row_50_ok : mtFiber8RowCheck 50 = true := by decide
theorem mtFiber8Row_51_ok : mtFiber8RowCheck 51 = true := by decide
theorem mtFiber8Row_52_ok : mtFiber8RowCheck 52 = true := by decide
theorem mtFiber8Row_53_ok : mtFiber8RowCheck 53 = true := by decide
theorem mtFiber8Row_54_ok : mtFiber8RowCheck 54 = true := by decide
theorem mtFiber8Row_55_ok : mtFiber8RowCheck 55 = true := by decide
theorem mtFiber8Row_56_ok : mtFiber8RowCheck 56 = true := by decide
theorem mtFiber8Row_57_ok : mtFiber8RowCheck 57 = true := by decide
theorem mtFiber8Row_58_ok : mtFiber8RowCheck 58 = true := by decide
theorem mtFiber8Row_59_ok : mtFiber8RowCheck 59 = true := by decide
theorem mtFiber8Row_60_ok : mtFiber8RowCheck 60 = true := by decide
theorem mtFiber8Row_61_ok : mtFiber8RowCheck 61 = true := by decide
theorem mtFiber8Row_62_ok : mtFiber8RowCheck 62 = true := by decide
theorem mtFiber8Row_63_ok : mtFiber8RowCheck 63 = true := by decide

def mtFiber8ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber8Rows mtMaxParentDepth (listGetD mtFiber8Expected i 0) == 144

theorem mtFiber8Parent_0_ok : mtFiber8ParentCheck 0 = true := by decide
theorem mtFiber8Parent_1_ok : mtFiber8ParentCheck 1 = true := by decide
theorem mtFiber8Parent_2_ok : mtFiber8ParentCheck 2 = true := by decide
theorem mtFiber8Parent_3_ok : mtFiber8ParentCheck 3 = true := by decide
theorem mtFiber8Parent_4_ok : mtFiber8ParentCheck 4 = true := by decide
theorem mtFiber8Parent_5_ok : mtFiber8ParentCheck 5 = true := by decide
theorem mtFiber8Parent_6_ok : mtFiber8ParentCheck 6 = true := by decide
theorem mtFiber8Parent_7_ok : mtFiber8ParentCheck 7 = true := by decide
theorem mtFiber8Parent_8_ok : mtFiber8ParentCheck 8 = true := by decide
theorem mtFiber8Parent_9_ok : mtFiber8ParentCheck 9 = true := by decide
theorem mtFiber8Parent_10_ok : mtFiber8ParentCheck 10 = true := by decide
theorem mtFiber8Parent_11_ok : mtFiber8ParentCheck 11 = true := by decide
theorem mtFiber8Parent_12_ok : mtFiber8ParentCheck 12 = true := by decide
theorem mtFiber8Parent_13_ok : mtFiber8ParentCheck 13 = true := by decide
theorem mtFiber8Parent_14_ok : mtFiber8ParentCheck 14 = true := by decide
theorem mtFiber8Parent_15_ok : mtFiber8ParentCheck 15 = true := by decide
theorem mtFiber8Parent_16_ok : mtFiber8ParentCheck 16 = true := by decide
theorem mtFiber8Parent_17_ok : mtFiber8ParentCheck 17 = true := by decide
theorem mtFiber8Parent_18_ok : mtFiber8ParentCheck 18 = true := by decide
theorem mtFiber8Parent_19_ok : mtFiber8ParentCheck 19 = true := by decide
theorem mtFiber8Parent_20_ok : mtFiber8ParentCheck 20 = true := by decide
theorem mtFiber8Parent_21_ok : mtFiber8ParentCheck 21 = true := by decide
theorem mtFiber8Parent_22_ok : mtFiber8ParentCheck 22 = true := by decide
theorem mtFiber8Parent_23_ok : mtFiber8ParentCheck 23 = true := by decide
theorem mtFiber8Parent_24_ok : mtFiber8ParentCheck 24 = true := by decide
theorem mtFiber8Parent_25_ok : mtFiber8ParentCheck 25 = true := by decide
theorem mtFiber8Parent_26_ok : mtFiber8ParentCheck 26 = true := by decide
theorem mtFiber8Parent_27_ok : mtFiber8ParentCheck 27 = true := by decide
theorem mtFiber8Parent_28_ok : mtFiber8ParentCheck 28 = true := by decide
theorem mtFiber8Parent_29_ok : mtFiber8ParentCheck 29 = true := by decide
theorem mtFiber8Parent_30_ok : mtFiber8ParentCheck 30 = true := by decide
theorem mtFiber8Parent_31_ok : mtFiber8ParentCheck 31 = true := by decide
theorem mtFiber8Parent_32_ok : mtFiber8ParentCheck 32 = true := by decide
theorem mtFiber8Parent_33_ok : mtFiber8ParentCheck 33 = true := by decide
theorem mtFiber8Parent_34_ok : mtFiber8ParentCheck 34 = true := by decide
theorem mtFiber8Parent_35_ok : mtFiber8ParentCheck 35 = true := by decide
theorem mtFiber8Parent_36_ok : mtFiber8ParentCheck 36 = true := by decide
theorem mtFiber8Parent_37_ok : mtFiber8ParentCheck 37 = true := by decide
theorem mtFiber8Parent_38_ok : mtFiber8ParentCheck 38 = true := by decide
theorem mtFiber8Parent_39_ok : mtFiber8ParentCheck 39 = true := by decide
theorem mtFiber8Parent_40_ok : mtFiber8ParentCheck 40 = true := by decide
theorem mtFiber8Parent_41_ok : mtFiber8ParentCheck 41 = true := by decide
theorem mtFiber8Parent_42_ok : mtFiber8ParentCheck 42 = true := by decide
theorem mtFiber8Parent_43_ok : mtFiber8ParentCheck 43 = true := by decide
theorem mtFiber8Parent_44_ok : mtFiber8ParentCheck 44 = true := by decide
theorem mtFiber8Parent_45_ok : mtFiber8ParentCheck 45 = true := by decide
theorem mtFiber8Parent_46_ok : mtFiber8ParentCheck 46 = true := by decide
theorem mtFiber8Parent_47_ok : mtFiber8ParentCheck 47 = true := by decide
theorem mtFiber8Parent_48_ok : mtFiber8ParentCheck 48 = true := by decide
theorem mtFiber8Parent_49_ok : mtFiber8ParentCheck 49 = true := by decide
theorem mtFiber8Parent_50_ok : mtFiber8ParentCheck 50 = true := by decide
theorem mtFiber8Parent_51_ok : mtFiber8ParentCheck 51 = true := by decide
theorem mtFiber8Parent_52_ok : mtFiber8ParentCheck 52 = true := by decide
theorem mtFiber8Parent_53_ok : mtFiber8ParentCheck 53 = true := by decide
theorem mtFiber8Parent_54_ok : mtFiber8ParentCheck 54 = true := by decide
theorem mtFiber8Parent_55_ok : mtFiber8ParentCheck 55 = true := by decide
theorem mtFiber8Parent_56_ok : mtFiber8ParentCheck 56 = true := by decide
theorem mtFiber8Parent_57_ok : mtFiber8ParentCheck 57 = true := by decide
theorem mtFiber8Parent_58_ok : mtFiber8ParentCheck 58 = true := by decide
theorem mtFiber8Parent_59_ok : mtFiber8ParentCheck 59 = true := by decide
theorem mtFiber8Parent_60_ok : mtFiber8ParentCheck 60 = true := by decide
theorem mtFiber8Parent_61_ok : mtFiber8ParentCheck 61 = true := by decide
theorem mtFiber8Parent_62_ok : mtFiber8ParentCheck 62 = true := by decide
theorem mtFiber8Parent_63_ok : mtFiber8ParentCheck 63 = true := by decide

def mtFiber8CertificateAudit : Bool :=
  mtFiber8SourcesCheck &&
    mtFiber8RowCheck 0 &&
    mtFiber8RowCheck 1 &&
    mtFiber8RowCheck 2 &&
    mtFiber8RowCheck 3 &&
    mtFiber8RowCheck 4 &&
    mtFiber8RowCheck 5 &&
    mtFiber8RowCheck 6 &&
    mtFiber8RowCheck 7 &&
    mtFiber8RowCheck 8 &&
    mtFiber8RowCheck 9 &&
    mtFiber8RowCheck 10 &&
    mtFiber8RowCheck 11 &&
    mtFiber8RowCheck 12 &&
    mtFiber8RowCheck 13 &&
    mtFiber8RowCheck 14 &&
    mtFiber8RowCheck 15 &&
    mtFiber8RowCheck 16 &&
    mtFiber8RowCheck 17 &&
    mtFiber8RowCheck 18 &&
    mtFiber8RowCheck 19 &&
    mtFiber8RowCheck 20 &&
    mtFiber8RowCheck 21 &&
    mtFiber8RowCheck 22 &&
    mtFiber8RowCheck 23 &&
    mtFiber8RowCheck 24 &&
    mtFiber8RowCheck 25 &&
    mtFiber8RowCheck 26 &&
    mtFiber8RowCheck 27 &&
    mtFiber8RowCheck 28 &&
    mtFiber8RowCheck 29 &&
    mtFiber8RowCheck 30 &&
    mtFiber8RowCheck 31 &&
    mtFiber8RowCheck 32 &&
    mtFiber8RowCheck 33 &&
    mtFiber8RowCheck 34 &&
    mtFiber8RowCheck 35 &&
    mtFiber8RowCheck 36 &&
    mtFiber8RowCheck 37 &&
    mtFiber8RowCheck 38 &&
    mtFiber8RowCheck 39 &&
    mtFiber8RowCheck 40 &&
    mtFiber8RowCheck 41 &&
    mtFiber8RowCheck 42 &&
    mtFiber8RowCheck 43 &&
    mtFiber8RowCheck 44 &&
    mtFiber8RowCheck 45 &&
    mtFiber8RowCheck 46 &&
    mtFiber8RowCheck 47 &&
    mtFiber8RowCheck 48 &&
    mtFiber8RowCheck 49 &&
    mtFiber8RowCheck 50 &&
    mtFiber8RowCheck 51 &&
    mtFiber8RowCheck 52 &&
    mtFiber8RowCheck 53 &&
    mtFiber8RowCheck 54 &&
    mtFiber8RowCheck 55 &&
    mtFiber8RowCheck 56 &&
    mtFiber8RowCheck 57 &&
    mtFiber8RowCheck 58 &&
    mtFiber8RowCheck 59 &&
    mtFiber8RowCheck 60 &&
    mtFiber8RowCheck 61 &&
    mtFiber8RowCheck 62 &&
    mtFiber8RowCheck 63 &&
    mtFiber8ParentCheck 0 &&
    mtFiber8ParentCheck 1 &&
    mtFiber8ParentCheck 2 &&
    mtFiber8ParentCheck 3 &&
    mtFiber8ParentCheck 4 &&
    mtFiber8ParentCheck 5 &&
    mtFiber8ParentCheck 6 &&
    mtFiber8ParentCheck 7 &&
    mtFiber8ParentCheck 8 &&
    mtFiber8ParentCheck 9 &&
    mtFiber8ParentCheck 10 &&
    mtFiber8ParentCheck 11 &&
    mtFiber8ParentCheck 12 &&
    mtFiber8ParentCheck 13 &&
    mtFiber8ParentCheck 14 &&
    mtFiber8ParentCheck 15 &&
    mtFiber8ParentCheck 16 &&
    mtFiber8ParentCheck 17 &&
    mtFiber8ParentCheck 18 &&
    mtFiber8ParentCheck 19 &&
    mtFiber8ParentCheck 20 &&
    mtFiber8ParentCheck 21 &&
    mtFiber8ParentCheck 22 &&
    mtFiber8ParentCheck 23 &&
    mtFiber8ParentCheck 24 &&
    mtFiber8ParentCheck 25 &&
    mtFiber8ParentCheck 26 &&
    mtFiber8ParentCheck 27 &&
    mtFiber8ParentCheck 28 &&
    mtFiber8ParentCheck 29 &&
    mtFiber8ParentCheck 30 &&
    mtFiber8ParentCheck 31 &&
    mtFiber8ParentCheck 32 &&
    mtFiber8ParentCheck 33 &&
    mtFiber8ParentCheck 34 &&
    mtFiber8ParentCheck 35 &&
    mtFiber8ParentCheck 36 &&
    mtFiber8ParentCheck 37 &&
    mtFiber8ParentCheck 38 &&
    mtFiber8ParentCheck 39 &&
    mtFiber8ParentCheck 40 &&
    mtFiber8ParentCheck 41 &&
    mtFiber8ParentCheck 42 &&
    mtFiber8ParentCheck 43 &&
    mtFiber8ParentCheck 44 &&
    mtFiber8ParentCheck 45 &&
    mtFiber8ParentCheck 46 &&
    mtFiber8ParentCheck 47 &&
    mtFiber8ParentCheck 48 &&
    mtFiber8ParentCheck 49 &&
    mtFiber8ParentCheck 50 &&
    mtFiber8ParentCheck 51 &&
    mtFiber8ParentCheck 52 &&
    mtFiber8ParentCheck 53 &&
    mtFiber8ParentCheck 54 &&
    mtFiber8ParentCheck 55 &&
    mtFiber8ParentCheck 56 &&
    mtFiber8ParentCheck 57 &&
    mtFiber8ParentCheck 58 &&
    mtFiber8ParentCheck 59 &&
    mtFiber8ParentCheck 60 &&
    mtFiber8ParentCheck 61 &&
    mtFiber8ParentCheck 62 &&
    mtFiber8ParentCheck 63

theorem mtFiber8CertificateAudit_ok :
    mtFiber8CertificateAudit = true := by
  simp [mtFiber8CertificateAudit,
    mtFiber8SourcesCheck_ok,
    mtFiber8Row_0_ok,
    mtFiber8Row_1_ok,
    mtFiber8Row_2_ok,
    mtFiber8Row_3_ok,
    mtFiber8Row_4_ok,
    mtFiber8Row_5_ok,
    mtFiber8Row_6_ok,
    mtFiber8Row_7_ok,
    mtFiber8Row_8_ok,
    mtFiber8Row_9_ok,
    mtFiber8Row_10_ok,
    mtFiber8Row_11_ok,
    mtFiber8Row_12_ok,
    mtFiber8Row_13_ok,
    mtFiber8Row_14_ok,
    mtFiber8Row_15_ok,
    mtFiber8Row_16_ok,
    mtFiber8Row_17_ok,
    mtFiber8Row_18_ok,
    mtFiber8Row_19_ok,
    mtFiber8Row_20_ok,
    mtFiber8Row_21_ok,
    mtFiber8Row_22_ok,
    mtFiber8Row_23_ok,
    mtFiber8Row_24_ok,
    mtFiber8Row_25_ok,
    mtFiber8Row_26_ok,
    mtFiber8Row_27_ok,
    mtFiber8Row_28_ok,
    mtFiber8Row_29_ok,
    mtFiber8Row_30_ok,
    mtFiber8Row_31_ok,
    mtFiber8Row_32_ok,
    mtFiber8Row_33_ok,
    mtFiber8Row_34_ok,
    mtFiber8Row_35_ok,
    mtFiber8Row_36_ok,
    mtFiber8Row_37_ok,
    mtFiber8Row_38_ok,
    mtFiber8Row_39_ok,
    mtFiber8Row_40_ok,
    mtFiber8Row_41_ok,
    mtFiber8Row_42_ok,
    mtFiber8Row_43_ok,
    mtFiber8Row_44_ok,
    mtFiber8Row_45_ok,
    mtFiber8Row_46_ok,
    mtFiber8Row_47_ok,
    mtFiber8Row_48_ok,
    mtFiber8Row_49_ok,
    mtFiber8Row_50_ok,
    mtFiber8Row_51_ok,
    mtFiber8Row_52_ok,
    mtFiber8Row_53_ok,
    mtFiber8Row_54_ok,
    mtFiber8Row_55_ok,
    mtFiber8Row_56_ok,
    mtFiber8Row_57_ok,
    mtFiber8Row_58_ok,
    mtFiber8Row_59_ok,
    mtFiber8Row_60_ok,
    mtFiber8Row_61_ok,
    mtFiber8Row_62_ok,
    mtFiber8Row_63_ok,
    mtFiber8Parent_0_ok,
    mtFiber8Parent_1_ok,
    mtFiber8Parent_2_ok,
    mtFiber8Parent_3_ok,
    mtFiber8Parent_4_ok,
    mtFiber8Parent_5_ok,
    mtFiber8Parent_6_ok,
    mtFiber8Parent_7_ok,
    mtFiber8Parent_8_ok,
    mtFiber8Parent_9_ok,
    mtFiber8Parent_10_ok,
    mtFiber8Parent_11_ok,
    mtFiber8Parent_12_ok,
    mtFiber8Parent_13_ok,
    mtFiber8Parent_14_ok,
    mtFiber8Parent_15_ok,
    mtFiber8Parent_16_ok,
    mtFiber8Parent_17_ok,
    mtFiber8Parent_18_ok,
    mtFiber8Parent_19_ok,
    mtFiber8Parent_20_ok,
    mtFiber8Parent_21_ok,
    mtFiber8Parent_22_ok,
    mtFiber8Parent_23_ok,
    mtFiber8Parent_24_ok,
    mtFiber8Parent_25_ok,
    mtFiber8Parent_26_ok,
    mtFiber8Parent_27_ok,
    mtFiber8Parent_28_ok,
    mtFiber8Parent_29_ok,
    mtFiber8Parent_30_ok,
    mtFiber8Parent_31_ok,
    mtFiber8Parent_32_ok,
    mtFiber8Parent_33_ok,
    mtFiber8Parent_34_ok,
    mtFiber8Parent_35_ok,
    mtFiber8Parent_36_ok,
    mtFiber8Parent_37_ok,
    mtFiber8Parent_38_ok,
    mtFiber8Parent_39_ok,
    mtFiber8Parent_40_ok,
    mtFiber8Parent_41_ok,
    mtFiber8Parent_42_ok,
    mtFiber8Parent_43_ok,
    mtFiber8Parent_44_ok,
    mtFiber8Parent_45_ok,
    mtFiber8Parent_46_ok,
    mtFiber8Parent_47_ok,
    mtFiber8Parent_48_ok,
    mtFiber8Parent_49_ok,
    mtFiber8Parent_50_ok,
    mtFiber8Parent_51_ok,
    mtFiber8Parent_52_ok,
    mtFiber8Parent_53_ok,
    mtFiber8Parent_54_ok,
    mtFiber8Parent_55_ok,
    mtFiber8Parent_56_ok,
    mtFiber8Parent_57_ok,
    mtFiber8Parent_58_ok,
    mtFiber8Parent_59_ok,
    mtFiber8Parent_60_ok,
    mtFiber8Parent_61_ok,
    mtFiber8Parent_62_ok,
    mtFiber8Parent_63_ok]

def mtFiber9Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.r]

def mtFiber9Expected : List Nat :=
  [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]

def mtFiber9Rows : List DirectChainParentRow :=
  [ directRow 672 672 112 44 112 44 default
  , directRow 673 672 112 45 112 44 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 674 673 112 46 112 45 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 675 672 112 47 112 44 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 676 672 113 36 112 44 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 677 673 113 37 112 45 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 678 674 113 38 112 46 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 679 675 113 39 112 47 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 680 672 114 60 112 44 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 681 673 114 61 112 45 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 682 674 114 62 112 46 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 683 675 114 63 112 47 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 684 676 115 52 113 36 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 685 677 115 53 113 37 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 686 678 115 54 113 38 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 687 679 115 55 113 39 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber9RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber9Rows i default

def mtFiber9SourcesCheck : Bool :=
  (mtFiber9Rows.map fun row => row.source) == mtFiber9Expected

theorem mtFiber9SourcesCheck_ok :
    mtFiber9SourcesCheck = true := by
  decide

def mtFiber9RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt i)

theorem mtFiber9Row_0_ok : mtFiber9RowCheck 0 = true := by decide
theorem mtFiber9Row_1_ok : mtFiber9RowCheck 1 = true := by decide
theorem mtFiber9Row_2_ok : mtFiber9RowCheck 2 = true := by decide
theorem mtFiber9Row_3_ok : mtFiber9RowCheck 3 = true := by decide
theorem mtFiber9Row_4_ok : mtFiber9RowCheck 4 = true := by decide
theorem mtFiber9Row_5_ok : mtFiber9RowCheck 5 = true := by decide
theorem mtFiber9Row_6_ok : mtFiber9RowCheck 6 = true := by decide
theorem mtFiber9Row_7_ok : mtFiber9RowCheck 7 = true := by decide
theorem mtFiber9Row_8_ok : mtFiber9RowCheck 8 = true := by decide
theorem mtFiber9Row_9_ok : mtFiber9RowCheck 9 = true := by decide
theorem mtFiber9Row_10_ok : mtFiber9RowCheck 10 = true := by decide
theorem mtFiber9Row_11_ok : mtFiber9RowCheck 11 = true := by decide
theorem mtFiber9Row_12_ok : mtFiber9RowCheck 12 = true := by decide
theorem mtFiber9Row_13_ok : mtFiber9RowCheck 13 = true := by decide
theorem mtFiber9Row_14_ok : mtFiber9RowCheck 14 = true := by decide
theorem mtFiber9Row_15_ok : mtFiber9RowCheck 15 = true := by decide

def mtFiber9ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber9Rows mtMaxParentDepth (listGetD mtFiber9Expected i 0) == 672

theorem mtFiber9Parent_0_ok : mtFiber9ParentCheck 0 = true := by decide
theorem mtFiber9Parent_1_ok : mtFiber9ParentCheck 1 = true := by decide
theorem mtFiber9Parent_2_ok : mtFiber9ParentCheck 2 = true := by decide
theorem mtFiber9Parent_3_ok : mtFiber9ParentCheck 3 = true := by decide
theorem mtFiber9Parent_4_ok : mtFiber9ParentCheck 4 = true := by decide
theorem mtFiber9Parent_5_ok : mtFiber9ParentCheck 5 = true := by decide
theorem mtFiber9Parent_6_ok : mtFiber9ParentCheck 6 = true := by decide
theorem mtFiber9Parent_7_ok : mtFiber9ParentCheck 7 = true := by decide
theorem mtFiber9Parent_8_ok : mtFiber9ParentCheck 8 = true := by decide
theorem mtFiber9Parent_9_ok : mtFiber9ParentCheck 9 = true := by decide
theorem mtFiber9Parent_10_ok : mtFiber9ParentCheck 10 = true := by decide
theorem mtFiber9Parent_11_ok : mtFiber9ParentCheck 11 = true := by decide
theorem mtFiber9Parent_12_ok : mtFiber9ParentCheck 12 = true := by decide
theorem mtFiber9Parent_13_ok : mtFiber9ParentCheck 13 = true := by decide
theorem mtFiber9Parent_14_ok : mtFiber9ParentCheck 14 = true := by decide
theorem mtFiber9Parent_15_ok : mtFiber9ParentCheck 15 = true := by decide

def mtFiber9CertificateAudit : Bool :=
  mtFiber9SourcesCheck &&
    mtFiber9RowCheck 0 &&
    mtFiber9RowCheck 1 &&
    mtFiber9RowCheck 2 &&
    mtFiber9RowCheck 3 &&
    mtFiber9RowCheck 4 &&
    mtFiber9RowCheck 5 &&
    mtFiber9RowCheck 6 &&
    mtFiber9RowCheck 7 &&
    mtFiber9RowCheck 8 &&
    mtFiber9RowCheck 9 &&
    mtFiber9RowCheck 10 &&
    mtFiber9RowCheck 11 &&
    mtFiber9RowCheck 12 &&
    mtFiber9RowCheck 13 &&
    mtFiber9RowCheck 14 &&
    mtFiber9RowCheck 15 &&
    mtFiber9ParentCheck 0 &&
    mtFiber9ParentCheck 1 &&
    mtFiber9ParentCheck 2 &&
    mtFiber9ParentCheck 3 &&
    mtFiber9ParentCheck 4 &&
    mtFiber9ParentCheck 5 &&
    mtFiber9ParentCheck 6 &&
    mtFiber9ParentCheck 7 &&
    mtFiber9ParentCheck 8 &&
    mtFiber9ParentCheck 9 &&
    mtFiber9ParentCheck 10 &&
    mtFiber9ParentCheck 11 &&
    mtFiber9ParentCheck 12 &&
    mtFiber9ParentCheck 13 &&
    mtFiber9ParentCheck 14 &&
    mtFiber9ParentCheck 15

theorem mtFiber9CertificateAudit_ok :
    mtFiber9CertificateAudit = true := by
  simp [mtFiber9CertificateAudit,
    mtFiber9SourcesCheck_ok,
    mtFiber9Row_0_ok,
    mtFiber9Row_1_ok,
    mtFiber9Row_2_ok,
    mtFiber9Row_3_ok,
    mtFiber9Row_4_ok,
    mtFiber9Row_5_ok,
    mtFiber9Row_6_ok,
    mtFiber9Row_7_ok,
    mtFiber9Row_8_ok,
    mtFiber9Row_9_ok,
    mtFiber9Row_10_ok,
    mtFiber9Row_11_ok,
    mtFiber9Row_12_ok,
    mtFiber9Row_13_ok,
    mtFiber9Row_14_ok,
    mtFiber9Row_15_ok,
    mtFiber9Parent_0_ok,
    mtFiber9Parent_1_ok,
    mtFiber9Parent_2_ok,
    mtFiber9Parent_3_ok,
    mtFiber9Parent_4_ok,
    mtFiber9Parent_5_ok,
    mtFiber9Parent_6_ok,
    mtFiber9Parent_7_ok,
    mtFiber9Parent_8_ok,
    mtFiber9Parent_9_ok,
    mtFiber9Parent_10_ok,
    mtFiber9Parent_11_ok,
    mtFiber9Parent_12_ok,
    mtFiber9Parent_13_ok,
    mtFiber9Parent_14_ok,
    mtFiber9Parent_15_ok]

def mtFiber10Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.b]

def mtFiber10Expected : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]

def mtFiber10Rows : List DirectChainParentRow :=
  [ directRow 0 0 0 156 0 156 default
  , directRow 1 0 0 157 0 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 2 1 0 158 0 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 3 0 0 159 0 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 4 0 0 172 0 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 5 1 0 173 0 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 6 4 0 174 0 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 7 3 0 175 0 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 8 0 1 148 0 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 9 1 1 149 0 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 10 2 1 150 0 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 11 3 1 151 0 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 12 4 1 164 0 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 13 5 1 165 0 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 14 6 1 166 0 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 15 7 1 167 0 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 16 0 2 140 0 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 17 1 2 141 0 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 18 2 2 142 0 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 19 3 2 143 0 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 20 4 2 188 0 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 21 5 2 189 0 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 22 6 2 190 0 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 23 7 2 191 0 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 24 8 3 132 1 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 25 9 3 133 1 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 26 10 3 134 1 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 27 11 3 135 1 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 28 12 3 180 1 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 29 13 3 181 1 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 30 14 3 182 1 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 31 15 3 183 1 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 288 0 48 88 0 156 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 289 1 48 89 0 157 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 290 288 48 90 48 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 291 3 48 91 0 159 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 292 4 48 108 0 172 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 293 5 48 109 0 173 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 294 289 48 110 48 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 295 288 48 111 48 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 296 8 49 80 1 148 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 297 9 49 81 1 149 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 298 296 49 82 49 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 299 11 49 83 1 151 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 300 12 49 100 1 164 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 301 13 49 101 1 165 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 302 297 49 102 49 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 303 296 49 103 49 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 304 16 50 72 2 140 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 305 17 50 73 2 141 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 306 304 50 74 50 72 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 307 19 50 75 2 143 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 308 20 50 124 2 188 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 309 21 50 125 2 189 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 310 305 50 126 50 73 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 311 304 50 127 50 72 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 312 288 51 64 48 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 313 289 51 65 48 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 314 290 51 66 48 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 315 291 51 67 48 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 316 292 51 116 48 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 317 293 51 117 48 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 318 294 51 118 48 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 319 295 51 119 48 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber10RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber10Rows i default

def mtFiber10SourcesCheck : Bool :=
  (mtFiber10Rows.map fun row => row.source) == mtFiber10Expected

theorem mtFiber10SourcesCheck_ok :
    mtFiber10SourcesCheck = true := by
  decide

def mtFiber10RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt i)

theorem mtFiber10Row_0_ok : mtFiber10RowCheck 0 = true := by decide
theorem mtFiber10Row_1_ok : mtFiber10RowCheck 1 = true := by decide
theorem mtFiber10Row_2_ok : mtFiber10RowCheck 2 = true := by decide
theorem mtFiber10Row_3_ok : mtFiber10RowCheck 3 = true := by decide
theorem mtFiber10Row_4_ok : mtFiber10RowCheck 4 = true := by decide
theorem mtFiber10Row_5_ok : mtFiber10RowCheck 5 = true := by decide
theorem mtFiber10Row_6_ok : mtFiber10RowCheck 6 = true := by decide
theorem mtFiber10Row_7_ok : mtFiber10RowCheck 7 = true := by decide
theorem mtFiber10Row_8_ok : mtFiber10RowCheck 8 = true := by decide
theorem mtFiber10Row_9_ok : mtFiber10RowCheck 9 = true := by decide
theorem mtFiber10Row_10_ok : mtFiber10RowCheck 10 = true := by decide
theorem mtFiber10Row_11_ok : mtFiber10RowCheck 11 = true := by decide
theorem mtFiber10Row_12_ok : mtFiber10RowCheck 12 = true := by decide
theorem mtFiber10Row_13_ok : mtFiber10RowCheck 13 = true := by decide
theorem mtFiber10Row_14_ok : mtFiber10RowCheck 14 = true := by decide
theorem mtFiber10Row_15_ok : mtFiber10RowCheck 15 = true := by decide
theorem mtFiber10Row_16_ok : mtFiber10RowCheck 16 = true := by decide
theorem mtFiber10Row_17_ok : mtFiber10RowCheck 17 = true := by decide
theorem mtFiber10Row_18_ok : mtFiber10RowCheck 18 = true := by decide
theorem mtFiber10Row_19_ok : mtFiber10RowCheck 19 = true := by decide
theorem mtFiber10Row_20_ok : mtFiber10RowCheck 20 = true := by decide
theorem mtFiber10Row_21_ok : mtFiber10RowCheck 21 = true := by decide
theorem mtFiber10Row_22_ok : mtFiber10RowCheck 22 = true := by decide
theorem mtFiber10Row_23_ok : mtFiber10RowCheck 23 = true := by decide
theorem mtFiber10Row_24_ok : mtFiber10RowCheck 24 = true := by decide
theorem mtFiber10Row_25_ok : mtFiber10RowCheck 25 = true := by decide
theorem mtFiber10Row_26_ok : mtFiber10RowCheck 26 = true := by decide
theorem mtFiber10Row_27_ok : mtFiber10RowCheck 27 = true := by decide
theorem mtFiber10Row_28_ok : mtFiber10RowCheck 28 = true := by decide
theorem mtFiber10Row_29_ok : mtFiber10RowCheck 29 = true := by decide
theorem mtFiber10Row_30_ok : mtFiber10RowCheck 30 = true := by decide
theorem mtFiber10Row_31_ok : mtFiber10RowCheck 31 = true := by decide
theorem mtFiber10Row_32_ok : mtFiber10RowCheck 32 = true := by decide
theorem mtFiber10Row_33_ok : mtFiber10RowCheck 33 = true := by decide
theorem mtFiber10Row_34_ok : mtFiber10RowCheck 34 = true := by decide
theorem mtFiber10Row_35_ok : mtFiber10RowCheck 35 = true := by decide
theorem mtFiber10Row_36_ok : mtFiber10RowCheck 36 = true := by decide
theorem mtFiber10Row_37_ok : mtFiber10RowCheck 37 = true := by decide
theorem mtFiber10Row_38_ok : mtFiber10RowCheck 38 = true := by decide
theorem mtFiber10Row_39_ok : mtFiber10RowCheck 39 = true := by decide
theorem mtFiber10Row_40_ok : mtFiber10RowCheck 40 = true := by decide
theorem mtFiber10Row_41_ok : mtFiber10RowCheck 41 = true := by decide
theorem mtFiber10Row_42_ok : mtFiber10RowCheck 42 = true := by decide
theorem mtFiber10Row_43_ok : mtFiber10RowCheck 43 = true := by decide
theorem mtFiber10Row_44_ok : mtFiber10RowCheck 44 = true := by decide
theorem mtFiber10Row_45_ok : mtFiber10RowCheck 45 = true := by decide
theorem mtFiber10Row_46_ok : mtFiber10RowCheck 46 = true := by decide
theorem mtFiber10Row_47_ok : mtFiber10RowCheck 47 = true := by decide
theorem mtFiber10Row_48_ok : mtFiber10RowCheck 48 = true := by decide
theorem mtFiber10Row_49_ok : mtFiber10RowCheck 49 = true := by decide
theorem mtFiber10Row_50_ok : mtFiber10RowCheck 50 = true := by decide
theorem mtFiber10Row_51_ok : mtFiber10RowCheck 51 = true := by decide
theorem mtFiber10Row_52_ok : mtFiber10RowCheck 52 = true := by decide
theorem mtFiber10Row_53_ok : mtFiber10RowCheck 53 = true := by decide
theorem mtFiber10Row_54_ok : mtFiber10RowCheck 54 = true := by decide
theorem mtFiber10Row_55_ok : mtFiber10RowCheck 55 = true := by decide
theorem mtFiber10Row_56_ok : mtFiber10RowCheck 56 = true := by decide
theorem mtFiber10Row_57_ok : mtFiber10RowCheck 57 = true := by decide
theorem mtFiber10Row_58_ok : mtFiber10RowCheck 58 = true := by decide
theorem mtFiber10Row_59_ok : mtFiber10RowCheck 59 = true := by decide
theorem mtFiber10Row_60_ok : mtFiber10RowCheck 60 = true := by decide
theorem mtFiber10Row_61_ok : mtFiber10RowCheck 61 = true := by decide
theorem mtFiber10Row_62_ok : mtFiber10RowCheck 62 = true := by decide
theorem mtFiber10Row_63_ok : mtFiber10RowCheck 63 = true := by decide

def mtFiber10ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber10Rows mtMaxParentDepth (listGetD mtFiber10Expected i 0) == 0

theorem mtFiber10Parent_0_ok : mtFiber10ParentCheck 0 = true := by decide
theorem mtFiber10Parent_1_ok : mtFiber10ParentCheck 1 = true := by decide
theorem mtFiber10Parent_2_ok : mtFiber10ParentCheck 2 = true := by decide
theorem mtFiber10Parent_3_ok : mtFiber10ParentCheck 3 = true := by decide
theorem mtFiber10Parent_4_ok : mtFiber10ParentCheck 4 = true := by decide
theorem mtFiber10Parent_5_ok : mtFiber10ParentCheck 5 = true := by decide
theorem mtFiber10Parent_6_ok : mtFiber10ParentCheck 6 = true := by decide
theorem mtFiber10Parent_7_ok : mtFiber10ParentCheck 7 = true := by decide
theorem mtFiber10Parent_8_ok : mtFiber10ParentCheck 8 = true := by decide
theorem mtFiber10Parent_9_ok : mtFiber10ParentCheck 9 = true := by decide
theorem mtFiber10Parent_10_ok : mtFiber10ParentCheck 10 = true := by decide
theorem mtFiber10Parent_11_ok : mtFiber10ParentCheck 11 = true := by decide
theorem mtFiber10Parent_12_ok : mtFiber10ParentCheck 12 = true := by decide
theorem mtFiber10Parent_13_ok : mtFiber10ParentCheck 13 = true := by decide
theorem mtFiber10Parent_14_ok : mtFiber10ParentCheck 14 = true := by decide
theorem mtFiber10Parent_15_ok : mtFiber10ParentCheck 15 = true := by decide
theorem mtFiber10Parent_16_ok : mtFiber10ParentCheck 16 = true := by decide
theorem mtFiber10Parent_17_ok : mtFiber10ParentCheck 17 = true := by decide
theorem mtFiber10Parent_18_ok : mtFiber10ParentCheck 18 = true := by decide
theorem mtFiber10Parent_19_ok : mtFiber10ParentCheck 19 = true := by decide
theorem mtFiber10Parent_20_ok : mtFiber10ParentCheck 20 = true := by decide
theorem mtFiber10Parent_21_ok : mtFiber10ParentCheck 21 = true := by decide
theorem mtFiber10Parent_22_ok : mtFiber10ParentCheck 22 = true := by decide
theorem mtFiber10Parent_23_ok : mtFiber10ParentCheck 23 = true := by decide
theorem mtFiber10Parent_24_ok : mtFiber10ParentCheck 24 = true := by decide
theorem mtFiber10Parent_25_ok : mtFiber10ParentCheck 25 = true := by decide
theorem mtFiber10Parent_26_ok : mtFiber10ParentCheck 26 = true := by decide
theorem mtFiber10Parent_27_ok : mtFiber10ParentCheck 27 = true := by decide
theorem mtFiber10Parent_28_ok : mtFiber10ParentCheck 28 = true := by decide
theorem mtFiber10Parent_29_ok : mtFiber10ParentCheck 29 = true := by decide
theorem mtFiber10Parent_30_ok : mtFiber10ParentCheck 30 = true := by decide
theorem mtFiber10Parent_31_ok : mtFiber10ParentCheck 31 = true := by decide
theorem mtFiber10Parent_32_ok : mtFiber10ParentCheck 32 = true := by decide
theorem mtFiber10Parent_33_ok : mtFiber10ParentCheck 33 = true := by decide
theorem mtFiber10Parent_34_ok : mtFiber10ParentCheck 34 = true := by decide
theorem mtFiber10Parent_35_ok : mtFiber10ParentCheck 35 = true := by decide
theorem mtFiber10Parent_36_ok : mtFiber10ParentCheck 36 = true := by decide
theorem mtFiber10Parent_37_ok : mtFiber10ParentCheck 37 = true := by decide
theorem mtFiber10Parent_38_ok : mtFiber10ParentCheck 38 = true := by decide
theorem mtFiber10Parent_39_ok : mtFiber10ParentCheck 39 = true := by decide
theorem mtFiber10Parent_40_ok : mtFiber10ParentCheck 40 = true := by decide
theorem mtFiber10Parent_41_ok : mtFiber10ParentCheck 41 = true := by decide
theorem mtFiber10Parent_42_ok : mtFiber10ParentCheck 42 = true := by decide
theorem mtFiber10Parent_43_ok : mtFiber10ParentCheck 43 = true := by decide
theorem mtFiber10Parent_44_ok : mtFiber10ParentCheck 44 = true := by decide
theorem mtFiber10Parent_45_ok : mtFiber10ParentCheck 45 = true := by decide
theorem mtFiber10Parent_46_ok : mtFiber10ParentCheck 46 = true := by decide
theorem mtFiber10Parent_47_ok : mtFiber10ParentCheck 47 = true := by decide
theorem mtFiber10Parent_48_ok : mtFiber10ParentCheck 48 = true := by decide
theorem mtFiber10Parent_49_ok : mtFiber10ParentCheck 49 = true := by decide
theorem mtFiber10Parent_50_ok : mtFiber10ParentCheck 50 = true := by decide
theorem mtFiber10Parent_51_ok : mtFiber10ParentCheck 51 = true := by decide
theorem mtFiber10Parent_52_ok : mtFiber10ParentCheck 52 = true := by decide
theorem mtFiber10Parent_53_ok : mtFiber10ParentCheck 53 = true := by decide
theorem mtFiber10Parent_54_ok : mtFiber10ParentCheck 54 = true := by decide
theorem mtFiber10Parent_55_ok : mtFiber10ParentCheck 55 = true := by decide
theorem mtFiber10Parent_56_ok : mtFiber10ParentCheck 56 = true := by decide
theorem mtFiber10Parent_57_ok : mtFiber10ParentCheck 57 = true := by decide
theorem mtFiber10Parent_58_ok : mtFiber10ParentCheck 58 = true := by decide
theorem mtFiber10Parent_59_ok : mtFiber10ParentCheck 59 = true := by decide
theorem mtFiber10Parent_60_ok : mtFiber10ParentCheck 60 = true := by decide
theorem mtFiber10Parent_61_ok : mtFiber10ParentCheck 61 = true := by decide
theorem mtFiber10Parent_62_ok : mtFiber10ParentCheck 62 = true := by decide
theorem mtFiber10Parent_63_ok : mtFiber10ParentCheck 63 = true := by decide

def mtFiber10CertificateAudit : Bool :=
  mtFiber10SourcesCheck &&
    mtFiber10RowCheck 0 &&
    mtFiber10RowCheck 1 &&
    mtFiber10RowCheck 2 &&
    mtFiber10RowCheck 3 &&
    mtFiber10RowCheck 4 &&
    mtFiber10RowCheck 5 &&
    mtFiber10RowCheck 6 &&
    mtFiber10RowCheck 7 &&
    mtFiber10RowCheck 8 &&
    mtFiber10RowCheck 9 &&
    mtFiber10RowCheck 10 &&
    mtFiber10RowCheck 11 &&
    mtFiber10RowCheck 12 &&
    mtFiber10RowCheck 13 &&
    mtFiber10RowCheck 14 &&
    mtFiber10RowCheck 15 &&
    mtFiber10RowCheck 16 &&
    mtFiber10RowCheck 17 &&
    mtFiber10RowCheck 18 &&
    mtFiber10RowCheck 19 &&
    mtFiber10RowCheck 20 &&
    mtFiber10RowCheck 21 &&
    mtFiber10RowCheck 22 &&
    mtFiber10RowCheck 23 &&
    mtFiber10RowCheck 24 &&
    mtFiber10RowCheck 25 &&
    mtFiber10RowCheck 26 &&
    mtFiber10RowCheck 27 &&
    mtFiber10RowCheck 28 &&
    mtFiber10RowCheck 29 &&
    mtFiber10RowCheck 30 &&
    mtFiber10RowCheck 31 &&
    mtFiber10RowCheck 32 &&
    mtFiber10RowCheck 33 &&
    mtFiber10RowCheck 34 &&
    mtFiber10RowCheck 35 &&
    mtFiber10RowCheck 36 &&
    mtFiber10RowCheck 37 &&
    mtFiber10RowCheck 38 &&
    mtFiber10RowCheck 39 &&
    mtFiber10RowCheck 40 &&
    mtFiber10RowCheck 41 &&
    mtFiber10RowCheck 42 &&
    mtFiber10RowCheck 43 &&
    mtFiber10RowCheck 44 &&
    mtFiber10RowCheck 45 &&
    mtFiber10RowCheck 46 &&
    mtFiber10RowCheck 47 &&
    mtFiber10RowCheck 48 &&
    mtFiber10RowCheck 49 &&
    mtFiber10RowCheck 50 &&
    mtFiber10RowCheck 51 &&
    mtFiber10RowCheck 52 &&
    mtFiber10RowCheck 53 &&
    mtFiber10RowCheck 54 &&
    mtFiber10RowCheck 55 &&
    mtFiber10RowCheck 56 &&
    mtFiber10RowCheck 57 &&
    mtFiber10RowCheck 58 &&
    mtFiber10RowCheck 59 &&
    mtFiber10RowCheck 60 &&
    mtFiber10RowCheck 61 &&
    mtFiber10RowCheck 62 &&
    mtFiber10RowCheck 63 &&
    mtFiber10ParentCheck 0 &&
    mtFiber10ParentCheck 1 &&
    mtFiber10ParentCheck 2 &&
    mtFiber10ParentCheck 3 &&
    mtFiber10ParentCheck 4 &&
    mtFiber10ParentCheck 5 &&
    mtFiber10ParentCheck 6 &&
    mtFiber10ParentCheck 7 &&
    mtFiber10ParentCheck 8 &&
    mtFiber10ParentCheck 9 &&
    mtFiber10ParentCheck 10 &&
    mtFiber10ParentCheck 11 &&
    mtFiber10ParentCheck 12 &&
    mtFiber10ParentCheck 13 &&
    mtFiber10ParentCheck 14 &&
    mtFiber10ParentCheck 15 &&
    mtFiber10ParentCheck 16 &&
    mtFiber10ParentCheck 17 &&
    mtFiber10ParentCheck 18 &&
    mtFiber10ParentCheck 19 &&
    mtFiber10ParentCheck 20 &&
    mtFiber10ParentCheck 21 &&
    mtFiber10ParentCheck 22 &&
    mtFiber10ParentCheck 23 &&
    mtFiber10ParentCheck 24 &&
    mtFiber10ParentCheck 25 &&
    mtFiber10ParentCheck 26 &&
    mtFiber10ParentCheck 27 &&
    mtFiber10ParentCheck 28 &&
    mtFiber10ParentCheck 29 &&
    mtFiber10ParentCheck 30 &&
    mtFiber10ParentCheck 31 &&
    mtFiber10ParentCheck 32 &&
    mtFiber10ParentCheck 33 &&
    mtFiber10ParentCheck 34 &&
    mtFiber10ParentCheck 35 &&
    mtFiber10ParentCheck 36 &&
    mtFiber10ParentCheck 37 &&
    mtFiber10ParentCheck 38 &&
    mtFiber10ParentCheck 39 &&
    mtFiber10ParentCheck 40 &&
    mtFiber10ParentCheck 41 &&
    mtFiber10ParentCheck 42 &&
    mtFiber10ParentCheck 43 &&
    mtFiber10ParentCheck 44 &&
    mtFiber10ParentCheck 45 &&
    mtFiber10ParentCheck 46 &&
    mtFiber10ParentCheck 47 &&
    mtFiber10ParentCheck 48 &&
    mtFiber10ParentCheck 49 &&
    mtFiber10ParentCheck 50 &&
    mtFiber10ParentCheck 51 &&
    mtFiber10ParentCheck 52 &&
    mtFiber10ParentCheck 53 &&
    mtFiber10ParentCheck 54 &&
    mtFiber10ParentCheck 55 &&
    mtFiber10ParentCheck 56 &&
    mtFiber10ParentCheck 57 &&
    mtFiber10ParentCheck 58 &&
    mtFiber10ParentCheck 59 &&
    mtFiber10ParentCheck 60 &&
    mtFiber10ParentCheck 61 &&
    mtFiber10ParentCheck 62 &&
    mtFiber10ParentCheck 63

theorem mtFiber10CertificateAudit_ok :
    mtFiber10CertificateAudit = true := by
  simp [mtFiber10CertificateAudit,
    mtFiber10SourcesCheck_ok,
    mtFiber10Row_0_ok,
    mtFiber10Row_1_ok,
    mtFiber10Row_2_ok,
    mtFiber10Row_3_ok,
    mtFiber10Row_4_ok,
    mtFiber10Row_5_ok,
    mtFiber10Row_6_ok,
    mtFiber10Row_7_ok,
    mtFiber10Row_8_ok,
    mtFiber10Row_9_ok,
    mtFiber10Row_10_ok,
    mtFiber10Row_11_ok,
    mtFiber10Row_12_ok,
    mtFiber10Row_13_ok,
    mtFiber10Row_14_ok,
    mtFiber10Row_15_ok,
    mtFiber10Row_16_ok,
    mtFiber10Row_17_ok,
    mtFiber10Row_18_ok,
    mtFiber10Row_19_ok,
    mtFiber10Row_20_ok,
    mtFiber10Row_21_ok,
    mtFiber10Row_22_ok,
    mtFiber10Row_23_ok,
    mtFiber10Row_24_ok,
    mtFiber10Row_25_ok,
    mtFiber10Row_26_ok,
    mtFiber10Row_27_ok,
    mtFiber10Row_28_ok,
    mtFiber10Row_29_ok,
    mtFiber10Row_30_ok,
    mtFiber10Row_31_ok,
    mtFiber10Row_32_ok,
    mtFiber10Row_33_ok,
    mtFiber10Row_34_ok,
    mtFiber10Row_35_ok,
    mtFiber10Row_36_ok,
    mtFiber10Row_37_ok,
    mtFiber10Row_38_ok,
    mtFiber10Row_39_ok,
    mtFiber10Row_40_ok,
    mtFiber10Row_41_ok,
    mtFiber10Row_42_ok,
    mtFiber10Row_43_ok,
    mtFiber10Row_44_ok,
    mtFiber10Row_45_ok,
    mtFiber10Row_46_ok,
    mtFiber10Row_47_ok,
    mtFiber10Row_48_ok,
    mtFiber10Row_49_ok,
    mtFiber10Row_50_ok,
    mtFiber10Row_51_ok,
    mtFiber10Row_52_ok,
    mtFiber10Row_53_ok,
    mtFiber10Row_54_ok,
    mtFiber10Row_55_ok,
    mtFiber10Row_56_ok,
    mtFiber10Row_57_ok,
    mtFiber10Row_58_ok,
    mtFiber10Row_59_ok,
    mtFiber10Row_60_ok,
    mtFiber10Row_61_ok,
    mtFiber10Row_62_ok,
    mtFiber10Row_63_ok,
    mtFiber10Parent_0_ok,
    mtFiber10Parent_1_ok,
    mtFiber10Parent_2_ok,
    mtFiber10Parent_3_ok,
    mtFiber10Parent_4_ok,
    mtFiber10Parent_5_ok,
    mtFiber10Parent_6_ok,
    mtFiber10Parent_7_ok,
    mtFiber10Parent_8_ok,
    mtFiber10Parent_9_ok,
    mtFiber10Parent_10_ok,
    mtFiber10Parent_11_ok,
    mtFiber10Parent_12_ok,
    mtFiber10Parent_13_ok,
    mtFiber10Parent_14_ok,
    mtFiber10Parent_15_ok,
    mtFiber10Parent_16_ok,
    mtFiber10Parent_17_ok,
    mtFiber10Parent_18_ok,
    mtFiber10Parent_19_ok,
    mtFiber10Parent_20_ok,
    mtFiber10Parent_21_ok,
    mtFiber10Parent_22_ok,
    mtFiber10Parent_23_ok,
    mtFiber10Parent_24_ok,
    mtFiber10Parent_25_ok,
    mtFiber10Parent_26_ok,
    mtFiber10Parent_27_ok,
    mtFiber10Parent_28_ok,
    mtFiber10Parent_29_ok,
    mtFiber10Parent_30_ok,
    mtFiber10Parent_31_ok,
    mtFiber10Parent_32_ok,
    mtFiber10Parent_33_ok,
    mtFiber10Parent_34_ok,
    mtFiber10Parent_35_ok,
    mtFiber10Parent_36_ok,
    mtFiber10Parent_37_ok,
    mtFiber10Parent_38_ok,
    mtFiber10Parent_39_ok,
    mtFiber10Parent_40_ok,
    mtFiber10Parent_41_ok,
    mtFiber10Parent_42_ok,
    mtFiber10Parent_43_ok,
    mtFiber10Parent_44_ok,
    mtFiber10Parent_45_ok,
    mtFiber10Parent_46_ok,
    mtFiber10Parent_47_ok,
    mtFiber10Parent_48_ok,
    mtFiber10Parent_49_ok,
    mtFiber10Parent_50_ok,
    mtFiber10Parent_51_ok,
    mtFiber10Parent_52_ok,
    mtFiber10Parent_53_ok,
    mtFiber10Parent_54_ok,
    mtFiber10Parent_55_ok,
    mtFiber10Parent_56_ok,
    mtFiber10Parent_57_ok,
    mtFiber10Parent_58_ok,
    mtFiber10Parent_59_ok,
    mtFiber10Parent_60_ok,
    mtFiber10Parent_61_ok,
    mtFiber10Parent_62_ok,
    mtFiber10Parent_63_ok]

def mtFiber11Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.p]

def mtFiber11Expected : List Nat :=
  []

def mtFiber11Rows : List DirectChainParentRow :=
  []

def mtFiber11RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber11Rows i default

def mtFiber11SourcesCheck : Bool :=
  (mtFiber11Rows.map fun row => row.source) == mtFiber11Expected

theorem mtFiber11SourcesCheck_ok :
    mtFiber11SourcesCheck = true := by
  decide

def mtFiber11RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber11Key mtFiber11Expected (mtFiber11RowAt i)

def mtFiber11ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber11Rows mtMaxParentDepth (listGetD mtFiber11Expected i 0) == 0

def mtFiber11CertificateAudit : Bool :=
  mtFiber11SourcesCheck

theorem mtFiber11CertificateAudit_ok :
    mtFiber11CertificateAudit = true := by
  simp [mtFiber11CertificateAudit,
    mtFiber11SourcesCheck_ok]

def mtFiber12Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.r]

def mtFiber12Expected : List Nat :=
  []

def mtFiber12Rows : List DirectChainParentRow :=
  []

def mtFiber12RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber12Rows i default

def mtFiber12SourcesCheck : Bool :=
  (mtFiber12Rows.map fun row => row.source) == mtFiber12Expected

theorem mtFiber12SourcesCheck_ok :
    mtFiber12SourcesCheck = true := by
  decide

def mtFiber12RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber12Key mtFiber12Expected (mtFiber12RowAt i)

def mtFiber12ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber12Rows mtMaxParentDepth (listGetD mtFiber12Expected i 0) == 0

def mtFiber12CertificateAudit : Bool :=
  mtFiber12SourcesCheck

theorem mtFiber12CertificateAudit_ok :
    mtFiber12CertificateAudit = true := by
  simp [mtFiber12CertificateAudit,
    mtFiber12SourcesCheck_ok]

def mtFiber13Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.b]

def mtFiber13Expected : List Nat :=
  []

def mtFiber13Rows : List DirectChainParentRow :=
  []

def mtFiber13RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber13Rows i default

def mtFiber13SourcesCheck : Bool :=
  (mtFiber13Rows.map fun row => row.source) == mtFiber13Expected

theorem mtFiber13SourcesCheck_ok :
    mtFiber13SourcesCheck = true := by
  decide

def mtFiber13RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber13Key mtFiber13Expected (mtFiber13RowAt i)

def mtFiber13ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber13Rows mtMaxParentDepth (listGetD mtFiber13Expected i 0) == 0

def mtFiber13CertificateAudit : Bool :=
  mtFiber13SourcesCheck

theorem mtFiber13CertificateAudit_ok :
    mtFiber13CertificateAudit = true := by
  simp [mtFiber13CertificateAudit,
    mtFiber13SourcesCheck_ok]

def mtFiber14Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.p]

def mtFiber14Expected : List Nat :=
  []

def mtFiber14Rows : List DirectChainParentRow :=
  []

def mtFiber14RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber14Rows i default

def mtFiber14SourcesCheck : Bool :=
  (mtFiber14Rows.map fun row => row.source) == mtFiber14Expected

theorem mtFiber14SourcesCheck_ok :
    mtFiber14SourcesCheck = true := by
  decide

def mtFiber14RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber14Key mtFiber14Expected (mtFiber14RowAt i)

def mtFiber14ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber14Rows mtMaxParentDepth (listGetD mtFiber14Expected i 0) == 0

def mtFiber14CertificateAudit : Bool :=
  mtFiber14SourcesCheck

theorem mtFiber14CertificateAudit_ok :
    mtFiber14CertificateAudit = true := by
  simp [mtFiber14CertificateAudit,
    mtFiber14SourcesCheck_ok]

def mtFiber15Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.r]

def mtFiber15Expected : List Nat :=
  []

def mtFiber15Rows : List DirectChainParentRow :=
  []

def mtFiber15RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber15Rows i default

def mtFiber15SourcesCheck : Bool :=
  (mtFiber15Rows.map fun row => row.source) == mtFiber15Expected

theorem mtFiber15SourcesCheck_ok :
    mtFiber15SourcesCheck = true := by
  decide

def mtFiber15RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber15Key mtFiber15Expected (mtFiber15RowAt i)

def mtFiber15ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber15Rows mtMaxParentDepth (listGetD mtFiber15Expected i 0) == 0

def mtFiber15CertificateAudit : Bool :=
  mtFiber15SourcesCheck

theorem mtFiber15CertificateAudit_ok :
    mtFiber15CertificateAudit = true := by
  simp [mtFiber15CertificateAudit,
    mtFiber15SourcesCheck_ok]

def mtFiber16Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.b]

def mtFiber16Expected : List Nat :=
  [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]

def mtFiber16Rows : List DirectChainParentRow :=
  [ directRow 1008 1008 168 28 168 28 default
  , directRow 1009 1008 168 29 168 28 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 1010 1008 168 30 168 28 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 1011 1009 168 31 168 29 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 1012 1008 169 20 168 28 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1013 1009 169 21 168 29 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1014 1010 169 22 168 30 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1015 1011 169 23 168 31 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1016 1008 170 12 168 28 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1017 1009 170 13 168 29 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1018 1010 170 14 168 30 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1019 1011 170 15 168 31 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1020 1012 171 4 169 20 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1021 1013 171 5 169 21 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1022 1014 171 6 169 22 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1023 1015 171 7 169 23 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber16RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber16Rows i default

def mtFiber16SourcesCheck : Bool :=
  (mtFiber16Rows.map fun row => row.source) == mtFiber16Expected

theorem mtFiber16SourcesCheck_ok :
    mtFiber16SourcesCheck = true := by
  decide

def mtFiber16RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt i)

theorem mtFiber16Row_0_ok : mtFiber16RowCheck 0 = true := by decide
theorem mtFiber16Row_1_ok : mtFiber16RowCheck 1 = true := by decide
theorem mtFiber16Row_2_ok : mtFiber16RowCheck 2 = true := by decide
theorem mtFiber16Row_3_ok : mtFiber16RowCheck 3 = true := by decide
theorem mtFiber16Row_4_ok : mtFiber16RowCheck 4 = true := by decide
theorem mtFiber16Row_5_ok : mtFiber16RowCheck 5 = true := by decide
theorem mtFiber16Row_6_ok : mtFiber16RowCheck 6 = true := by decide
theorem mtFiber16Row_7_ok : mtFiber16RowCheck 7 = true := by decide
theorem mtFiber16Row_8_ok : mtFiber16RowCheck 8 = true := by decide
theorem mtFiber16Row_9_ok : mtFiber16RowCheck 9 = true := by decide
theorem mtFiber16Row_10_ok : mtFiber16RowCheck 10 = true := by decide
theorem mtFiber16Row_11_ok : mtFiber16RowCheck 11 = true := by decide
theorem mtFiber16Row_12_ok : mtFiber16RowCheck 12 = true := by decide
theorem mtFiber16Row_13_ok : mtFiber16RowCheck 13 = true := by decide
theorem mtFiber16Row_14_ok : mtFiber16RowCheck 14 = true := by decide
theorem mtFiber16Row_15_ok : mtFiber16RowCheck 15 = true := by decide

def mtFiber16ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber16Rows mtMaxParentDepth (listGetD mtFiber16Expected i 0) == 1008

theorem mtFiber16Parent_0_ok : mtFiber16ParentCheck 0 = true := by decide
theorem mtFiber16Parent_1_ok : mtFiber16ParentCheck 1 = true := by decide
theorem mtFiber16Parent_2_ok : mtFiber16ParentCheck 2 = true := by decide
theorem mtFiber16Parent_3_ok : mtFiber16ParentCheck 3 = true := by decide
theorem mtFiber16Parent_4_ok : mtFiber16ParentCheck 4 = true := by decide
theorem mtFiber16Parent_5_ok : mtFiber16ParentCheck 5 = true := by decide
theorem mtFiber16Parent_6_ok : mtFiber16ParentCheck 6 = true := by decide
theorem mtFiber16Parent_7_ok : mtFiber16ParentCheck 7 = true := by decide
theorem mtFiber16Parent_8_ok : mtFiber16ParentCheck 8 = true := by decide
theorem mtFiber16Parent_9_ok : mtFiber16ParentCheck 9 = true := by decide
theorem mtFiber16Parent_10_ok : mtFiber16ParentCheck 10 = true := by decide
theorem mtFiber16Parent_11_ok : mtFiber16ParentCheck 11 = true := by decide
theorem mtFiber16Parent_12_ok : mtFiber16ParentCheck 12 = true := by decide
theorem mtFiber16Parent_13_ok : mtFiber16ParentCheck 13 = true := by decide
theorem mtFiber16Parent_14_ok : mtFiber16ParentCheck 14 = true := by decide
theorem mtFiber16Parent_15_ok : mtFiber16ParentCheck 15 = true := by decide

def mtFiber16CertificateAudit : Bool :=
  mtFiber16SourcesCheck &&
    mtFiber16RowCheck 0 &&
    mtFiber16RowCheck 1 &&
    mtFiber16RowCheck 2 &&
    mtFiber16RowCheck 3 &&
    mtFiber16RowCheck 4 &&
    mtFiber16RowCheck 5 &&
    mtFiber16RowCheck 6 &&
    mtFiber16RowCheck 7 &&
    mtFiber16RowCheck 8 &&
    mtFiber16RowCheck 9 &&
    mtFiber16RowCheck 10 &&
    mtFiber16RowCheck 11 &&
    mtFiber16RowCheck 12 &&
    mtFiber16RowCheck 13 &&
    mtFiber16RowCheck 14 &&
    mtFiber16RowCheck 15 &&
    mtFiber16ParentCheck 0 &&
    mtFiber16ParentCheck 1 &&
    mtFiber16ParentCheck 2 &&
    mtFiber16ParentCheck 3 &&
    mtFiber16ParentCheck 4 &&
    mtFiber16ParentCheck 5 &&
    mtFiber16ParentCheck 6 &&
    mtFiber16ParentCheck 7 &&
    mtFiber16ParentCheck 8 &&
    mtFiber16ParentCheck 9 &&
    mtFiber16ParentCheck 10 &&
    mtFiber16ParentCheck 11 &&
    mtFiber16ParentCheck 12 &&
    mtFiber16ParentCheck 13 &&
    mtFiber16ParentCheck 14 &&
    mtFiber16ParentCheck 15

theorem mtFiber16CertificateAudit_ok :
    mtFiber16CertificateAudit = true := by
  simp [mtFiber16CertificateAudit,
    mtFiber16SourcesCheck_ok,
    mtFiber16Row_0_ok,
    mtFiber16Row_1_ok,
    mtFiber16Row_2_ok,
    mtFiber16Row_3_ok,
    mtFiber16Row_4_ok,
    mtFiber16Row_5_ok,
    mtFiber16Row_6_ok,
    mtFiber16Row_7_ok,
    mtFiber16Row_8_ok,
    mtFiber16Row_9_ok,
    mtFiber16Row_10_ok,
    mtFiber16Row_11_ok,
    mtFiber16Row_12_ok,
    mtFiber16Row_13_ok,
    mtFiber16Row_14_ok,
    mtFiber16Row_15_ok,
    mtFiber16Parent_0_ok,
    mtFiber16Parent_1_ok,
    mtFiber16Parent_2_ok,
    mtFiber16Parent_3_ok,
    mtFiber16Parent_4_ok,
    mtFiber16Parent_5_ok,
    mtFiber16Parent_6_ok,
    mtFiber16Parent_7_ok,
    mtFiber16Parent_8_ok,
    mtFiber16Parent_9_ok,
    mtFiber16Parent_10_ok,
    mtFiber16Parent_11_ok,
    mtFiber16Parent_12_ok,
    mtFiber16Parent_13_ok,
    mtFiber16Parent_14_ok,
    mtFiber16Parent_15_ok]

def mtFiber17Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.p]

def mtFiber17Expected : List Nat :=
  [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]

def mtFiber17Rows : List DirectChainParentRow :=
  [ directRow 624 624 104 44 104 44 default
  , directRow 625 624 104 45 104 44 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 626 625 104 46 104 45 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 627 624 104 47 104 44 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 628 624 105 36 104 44 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 629 625 105 37 104 45 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 630 626 105 38 104 46 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 631 627 105 39 104 47 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 632 624 106 60 104 44 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 633 625 106 61 104 45 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 634 626 106 62 104 46 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 635 627 106 63 104 47 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 636 628 107 52 105 36 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 637 629 107 53 105 37 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 638 630 107 54 105 38 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 639 631 107 55 105 39 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber17RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber17Rows i default

def mtFiber17SourcesCheck : Bool :=
  (mtFiber17Rows.map fun row => row.source) == mtFiber17Expected

theorem mtFiber17SourcesCheck_ok :
    mtFiber17SourcesCheck = true := by
  decide

def mtFiber17RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt i)

theorem mtFiber17Row_0_ok : mtFiber17RowCheck 0 = true := by decide
theorem mtFiber17Row_1_ok : mtFiber17RowCheck 1 = true := by decide
theorem mtFiber17Row_2_ok : mtFiber17RowCheck 2 = true := by decide
theorem mtFiber17Row_3_ok : mtFiber17RowCheck 3 = true := by decide
theorem mtFiber17Row_4_ok : mtFiber17RowCheck 4 = true := by decide
theorem mtFiber17Row_5_ok : mtFiber17RowCheck 5 = true := by decide
theorem mtFiber17Row_6_ok : mtFiber17RowCheck 6 = true := by decide
theorem mtFiber17Row_7_ok : mtFiber17RowCheck 7 = true := by decide
theorem mtFiber17Row_8_ok : mtFiber17RowCheck 8 = true := by decide
theorem mtFiber17Row_9_ok : mtFiber17RowCheck 9 = true := by decide
theorem mtFiber17Row_10_ok : mtFiber17RowCheck 10 = true := by decide
theorem mtFiber17Row_11_ok : mtFiber17RowCheck 11 = true := by decide
theorem mtFiber17Row_12_ok : mtFiber17RowCheck 12 = true := by decide
theorem mtFiber17Row_13_ok : mtFiber17RowCheck 13 = true := by decide
theorem mtFiber17Row_14_ok : mtFiber17RowCheck 14 = true := by decide
theorem mtFiber17Row_15_ok : mtFiber17RowCheck 15 = true := by decide

def mtFiber17ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber17Rows mtMaxParentDepth (listGetD mtFiber17Expected i 0) == 624

theorem mtFiber17Parent_0_ok : mtFiber17ParentCheck 0 = true := by decide
theorem mtFiber17Parent_1_ok : mtFiber17ParentCheck 1 = true := by decide
theorem mtFiber17Parent_2_ok : mtFiber17ParentCheck 2 = true := by decide
theorem mtFiber17Parent_3_ok : mtFiber17ParentCheck 3 = true := by decide
theorem mtFiber17Parent_4_ok : mtFiber17ParentCheck 4 = true := by decide
theorem mtFiber17Parent_5_ok : mtFiber17ParentCheck 5 = true := by decide
theorem mtFiber17Parent_6_ok : mtFiber17ParentCheck 6 = true := by decide
theorem mtFiber17Parent_7_ok : mtFiber17ParentCheck 7 = true := by decide
theorem mtFiber17Parent_8_ok : mtFiber17ParentCheck 8 = true := by decide
theorem mtFiber17Parent_9_ok : mtFiber17ParentCheck 9 = true := by decide
theorem mtFiber17Parent_10_ok : mtFiber17ParentCheck 10 = true := by decide
theorem mtFiber17Parent_11_ok : mtFiber17ParentCheck 11 = true := by decide
theorem mtFiber17Parent_12_ok : mtFiber17ParentCheck 12 = true := by decide
theorem mtFiber17Parent_13_ok : mtFiber17ParentCheck 13 = true := by decide
theorem mtFiber17Parent_14_ok : mtFiber17ParentCheck 14 = true := by decide
theorem mtFiber17Parent_15_ok : mtFiber17ParentCheck 15 = true := by decide

def mtFiber17CertificateAudit : Bool :=
  mtFiber17SourcesCheck &&
    mtFiber17RowCheck 0 &&
    mtFiber17RowCheck 1 &&
    mtFiber17RowCheck 2 &&
    mtFiber17RowCheck 3 &&
    mtFiber17RowCheck 4 &&
    mtFiber17RowCheck 5 &&
    mtFiber17RowCheck 6 &&
    mtFiber17RowCheck 7 &&
    mtFiber17RowCheck 8 &&
    mtFiber17RowCheck 9 &&
    mtFiber17RowCheck 10 &&
    mtFiber17RowCheck 11 &&
    mtFiber17RowCheck 12 &&
    mtFiber17RowCheck 13 &&
    mtFiber17RowCheck 14 &&
    mtFiber17RowCheck 15 &&
    mtFiber17ParentCheck 0 &&
    mtFiber17ParentCheck 1 &&
    mtFiber17ParentCheck 2 &&
    mtFiber17ParentCheck 3 &&
    mtFiber17ParentCheck 4 &&
    mtFiber17ParentCheck 5 &&
    mtFiber17ParentCheck 6 &&
    mtFiber17ParentCheck 7 &&
    mtFiber17ParentCheck 8 &&
    mtFiber17ParentCheck 9 &&
    mtFiber17ParentCheck 10 &&
    mtFiber17ParentCheck 11 &&
    mtFiber17ParentCheck 12 &&
    mtFiber17ParentCheck 13 &&
    mtFiber17ParentCheck 14 &&
    mtFiber17ParentCheck 15

theorem mtFiber17CertificateAudit_ok :
    mtFiber17CertificateAudit = true := by
  simp [mtFiber17CertificateAudit,
    mtFiber17SourcesCheck_ok,
    mtFiber17Row_0_ok,
    mtFiber17Row_1_ok,
    mtFiber17Row_2_ok,
    mtFiber17Row_3_ok,
    mtFiber17Row_4_ok,
    mtFiber17Row_5_ok,
    mtFiber17Row_6_ok,
    mtFiber17Row_7_ok,
    mtFiber17Row_8_ok,
    mtFiber17Row_9_ok,
    mtFiber17Row_10_ok,
    mtFiber17Row_11_ok,
    mtFiber17Row_12_ok,
    mtFiber17Row_13_ok,
    mtFiber17Row_14_ok,
    mtFiber17Row_15_ok,
    mtFiber17Parent_0_ok,
    mtFiber17Parent_1_ok,
    mtFiber17Parent_2_ok,
    mtFiber17Parent_3_ok,
    mtFiber17Parent_4_ok,
    mtFiber17Parent_5_ok,
    mtFiber17Parent_6_ok,
    mtFiber17Parent_7_ok,
    mtFiber17Parent_8_ok,
    mtFiber17Parent_9_ok,
    mtFiber17Parent_10_ok,
    mtFiber17Parent_11_ok,
    mtFiber17Parent_12_ok,
    mtFiber17Parent_13_ok,
    mtFiber17Parent_14_ok,
    mtFiber17Parent_15_ok]

def mtFiber18Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.r]

def mtFiber18Expected : List Nat :=
  [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]

def mtFiber18Rows : List DirectChainParentRow :=
  [ directRow 1056 1056 176 28 176 28 default
  , directRow 1057 1056 176 29 176 28 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 1058 1056 176 30 176 28 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 1059 1057 176 31 176 29 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 1060 1056 177 20 176 28 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1061 1057 177 21 176 29 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1062 1058 177 22 176 30 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1063 1059 177 23 176 31 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 1064 1056 178 12 176 28 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1065 1057 178 13 176 29 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1066 1058 178 14 176 30 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1067 1059 178 15 176 31 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1068 1060 179 4 177 20 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1069 1061 179 5 177 21 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1070 1062 179 6 177 22 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1071 1063 179 7 177 23 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber18RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber18Rows i default

def mtFiber18SourcesCheck : Bool :=
  (mtFiber18Rows.map fun row => row.source) == mtFiber18Expected

theorem mtFiber18SourcesCheck_ok :
    mtFiber18SourcesCheck = true := by
  decide

def mtFiber18RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt i)

theorem mtFiber18Row_0_ok : mtFiber18RowCheck 0 = true := by decide
theorem mtFiber18Row_1_ok : mtFiber18RowCheck 1 = true := by decide
theorem mtFiber18Row_2_ok : mtFiber18RowCheck 2 = true := by decide
theorem mtFiber18Row_3_ok : mtFiber18RowCheck 3 = true := by decide
theorem mtFiber18Row_4_ok : mtFiber18RowCheck 4 = true := by decide
theorem mtFiber18Row_5_ok : mtFiber18RowCheck 5 = true := by decide
theorem mtFiber18Row_6_ok : mtFiber18RowCheck 6 = true := by decide
theorem mtFiber18Row_7_ok : mtFiber18RowCheck 7 = true := by decide
theorem mtFiber18Row_8_ok : mtFiber18RowCheck 8 = true := by decide
theorem mtFiber18Row_9_ok : mtFiber18RowCheck 9 = true := by decide
theorem mtFiber18Row_10_ok : mtFiber18RowCheck 10 = true := by decide
theorem mtFiber18Row_11_ok : mtFiber18RowCheck 11 = true := by decide
theorem mtFiber18Row_12_ok : mtFiber18RowCheck 12 = true := by decide
theorem mtFiber18Row_13_ok : mtFiber18RowCheck 13 = true := by decide
theorem mtFiber18Row_14_ok : mtFiber18RowCheck 14 = true := by decide
theorem mtFiber18Row_15_ok : mtFiber18RowCheck 15 = true := by decide

def mtFiber18ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber18Rows mtMaxParentDepth (listGetD mtFiber18Expected i 0) == 1056

theorem mtFiber18Parent_0_ok : mtFiber18ParentCheck 0 = true := by decide
theorem mtFiber18Parent_1_ok : mtFiber18ParentCheck 1 = true := by decide
theorem mtFiber18Parent_2_ok : mtFiber18ParentCheck 2 = true := by decide
theorem mtFiber18Parent_3_ok : mtFiber18ParentCheck 3 = true := by decide
theorem mtFiber18Parent_4_ok : mtFiber18ParentCheck 4 = true := by decide
theorem mtFiber18Parent_5_ok : mtFiber18ParentCheck 5 = true := by decide
theorem mtFiber18Parent_6_ok : mtFiber18ParentCheck 6 = true := by decide
theorem mtFiber18Parent_7_ok : mtFiber18ParentCheck 7 = true := by decide
theorem mtFiber18Parent_8_ok : mtFiber18ParentCheck 8 = true := by decide
theorem mtFiber18Parent_9_ok : mtFiber18ParentCheck 9 = true := by decide
theorem mtFiber18Parent_10_ok : mtFiber18ParentCheck 10 = true := by decide
theorem mtFiber18Parent_11_ok : mtFiber18ParentCheck 11 = true := by decide
theorem mtFiber18Parent_12_ok : mtFiber18ParentCheck 12 = true := by decide
theorem mtFiber18Parent_13_ok : mtFiber18ParentCheck 13 = true := by decide
theorem mtFiber18Parent_14_ok : mtFiber18ParentCheck 14 = true := by decide
theorem mtFiber18Parent_15_ok : mtFiber18ParentCheck 15 = true := by decide

def mtFiber18CertificateAudit : Bool :=
  mtFiber18SourcesCheck &&
    mtFiber18RowCheck 0 &&
    mtFiber18RowCheck 1 &&
    mtFiber18RowCheck 2 &&
    mtFiber18RowCheck 3 &&
    mtFiber18RowCheck 4 &&
    mtFiber18RowCheck 5 &&
    mtFiber18RowCheck 6 &&
    mtFiber18RowCheck 7 &&
    mtFiber18RowCheck 8 &&
    mtFiber18RowCheck 9 &&
    mtFiber18RowCheck 10 &&
    mtFiber18RowCheck 11 &&
    mtFiber18RowCheck 12 &&
    mtFiber18RowCheck 13 &&
    mtFiber18RowCheck 14 &&
    mtFiber18RowCheck 15 &&
    mtFiber18ParentCheck 0 &&
    mtFiber18ParentCheck 1 &&
    mtFiber18ParentCheck 2 &&
    mtFiber18ParentCheck 3 &&
    mtFiber18ParentCheck 4 &&
    mtFiber18ParentCheck 5 &&
    mtFiber18ParentCheck 6 &&
    mtFiber18ParentCheck 7 &&
    mtFiber18ParentCheck 8 &&
    mtFiber18ParentCheck 9 &&
    mtFiber18ParentCheck 10 &&
    mtFiber18ParentCheck 11 &&
    mtFiber18ParentCheck 12 &&
    mtFiber18ParentCheck 13 &&
    mtFiber18ParentCheck 14 &&
    mtFiber18ParentCheck 15

theorem mtFiber18CertificateAudit_ok :
    mtFiber18CertificateAudit = true := by
  simp [mtFiber18CertificateAudit,
    mtFiber18SourcesCheck_ok,
    mtFiber18Row_0_ok,
    mtFiber18Row_1_ok,
    mtFiber18Row_2_ok,
    mtFiber18Row_3_ok,
    mtFiber18Row_4_ok,
    mtFiber18Row_5_ok,
    mtFiber18Row_6_ok,
    mtFiber18Row_7_ok,
    mtFiber18Row_8_ok,
    mtFiber18Row_9_ok,
    mtFiber18Row_10_ok,
    mtFiber18Row_11_ok,
    mtFiber18Row_12_ok,
    mtFiber18Row_13_ok,
    mtFiber18Row_14_ok,
    mtFiber18Row_15_ok,
    mtFiber18Parent_0_ok,
    mtFiber18Parent_1_ok,
    mtFiber18Parent_2_ok,
    mtFiber18Parent_3_ok,
    mtFiber18Parent_4_ok,
    mtFiber18Parent_5_ok,
    mtFiber18Parent_6_ok,
    mtFiber18Parent_7_ok,
    mtFiber18Parent_8_ok,
    mtFiber18Parent_9_ok,
    mtFiber18Parent_10_ok,
    mtFiber18Parent_11_ok,
    mtFiber18Parent_12_ok,
    mtFiber18Parent_13_ok,
    mtFiber18Parent_14_ok,
    mtFiber18Parent_15_ok]

def mtFiber19Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.b]

def mtFiber19Expected : List Nat :=
  []

def mtFiber19Rows : List DirectChainParentRow :=
  []

def mtFiber19RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber19Rows i default

def mtFiber19SourcesCheck : Bool :=
  (mtFiber19Rows.map fun row => row.source) == mtFiber19Expected

theorem mtFiber19SourcesCheck_ok :
    mtFiber19SourcesCheck = true := by
  decide

def mtFiber19RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber19Key mtFiber19Expected (mtFiber19RowAt i)

def mtFiber19ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber19Rows mtMaxParentDepth (listGetD mtFiber19Expected i 0) == 0

def mtFiber19CertificateAudit : Bool :=
  mtFiber19SourcesCheck

theorem mtFiber19CertificateAudit_ok :
    mtFiber19CertificateAudit = true := by
  simp [mtFiber19CertificateAudit,
    mtFiber19SourcesCheck_ok]

def mtFiber20Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.p]

def mtFiber20Expected : List Nat :=
  [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]

def mtFiber20Rows : List DirectChainParentRow :=
  [ directRow 96 96 16 156 16 156 default
  , directRow 97 96 16 157 16 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 98 97 16 158 16 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 99 96 16 159 16 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 100 96 16 172 16 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 101 97 16 173 16 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 102 100 16 174 16 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 103 99 16 175 16 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 104 96 17 148 16 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 105 97 17 149 16 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 106 98 17 150 16 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 107 99 17 151 16 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 108 100 17 164 16 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 109 101 17 165 16 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 110 102 17 166 16 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 111 103 17 167 16 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 112 96 18 140 16 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 113 97 18 141 16 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 114 98 18 142 16 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 115 99 18 143 16 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 116 100 18 188 16 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 117 101 18 189 16 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 118 102 18 190 16 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 119 103 18 191 16 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 120 104 19 132 17 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 121 105 19 133 17 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 122 106 19 134 17 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 123 107 19 135 17 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 124 108 19 180 17 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 125 109 19 181 17 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 126 110 19 182 17 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 127 111 19 183 17 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 192 96 32 88 16 156 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 193 97 32 89 16 157 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 194 192 32 90 32 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 195 99 32 91 16 159 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 196 100 32 108 16 172 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 197 101 32 109 16 173 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 198 193 32 110 32 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 199 192 32 111 32 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 200 104 33 80 17 148 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 201 105 33 81 17 149 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 202 200 33 82 33 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 203 107 33 83 17 151 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 204 108 33 100 17 164 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 205 109 33 101 17 165 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 206 201 33 102 33 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 207 200 33 103 33 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 208 112 34 72 18 140 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 209 113 34 73 18 141 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 210 208 34 74 34 72 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 211 115 34 75 18 143 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 212 116 34 124 18 188 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 213 117 34 125 18 189 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 214 209 34 126 34 73 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 215 208 34 127 34 72 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 216 192 35 64 32 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 217 193 35 65 32 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 218 194 35 66 32 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 219 195 35 67 32 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 220 196 35 116 32 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 221 197 35 117 32 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 222 198 35 118 32 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 223 199 35 119 32 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber20RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber20Rows i default

def mtFiber20SourcesCheck : Bool :=
  (mtFiber20Rows.map fun row => row.source) == mtFiber20Expected

theorem mtFiber20SourcesCheck_ok :
    mtFiber20SourcesCheck = true := by
  decide

def mtFiber20RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt i)

theorem mtFiber20Row_0_ok : mtFiber20RowCheck 0 = true := by decide
theorem mtFiber20Row_1_ok : mtFiber20RowCheck 1 = true := by decide
theorem mtFiber20Row_2_ok : mtFiber20RowCheck 2 = true := by decide
theorem mtFiber20Row_3_ok : mtFiber20RowCheck 3 = true := by decide
theorem mtFiber20Row_4_ok : mtFiber20RowCheck 4 = true := by decide
theorem mtFiber20Row_5_ok : mtFiber20RowCheck 5 = true := by decide
theorem mtFiber20Row_6_ok : mtFiber20RowCheck 6 = true := by decide
theorem mtFiber20Row_7_ok : mtFiber20RowCheck 7 = true := by decide
theorem mtFiber20Row_8_ok : mtFiber20RowCheck 8 = true := by decide
theorem mtFiber20Row_9_ok : mtFiber20RowCheck 9 = true := by decide
theorem mtFiber20Row_10_ok : mtFiber20RowCheck 10 = true := by decide
theorem mtFiber20Row_11_ok : mtFiber20RowCheck 11 = true := by decide
theorem mtFiber20Row_12_ok : mtFiber20RowCheck 12 = true := by decide
theorem mtFiber20Row_13_ok : mtFiber20RowCheck 13 = true := by decide
theorem mtFiber20Row_14_ok : mtFiber20RowCheck 14 = true := by decide
theorem mtFiber20Row_15_ok : mtFiber20RowCheck 15 = true := by decide
theorem mtFiber20Row_16_ok : mtFiber20RowCheck 16 = true := by decide
theorem mtFiber20Row_17_ok : mtFiber20RowCheck 17 = true := by decide
theorem mtFiber20Row_18_ok : mtFiber20RowCheck 18 = true := by decide
theorem mtFiber20Row_19_ok : mtFiber20RowCheck 19 = true := by decide
theorem mtFiber20Row_20_ok : mtFiber20RowCheck 20 = true := by decide
theorem mtFiber20Row_21_ok : mtFiber20RowCheck 21 = true := by decide
theorem mtFiber20Row_22_ok : mtFiber20RowCheck 22 = true := by decide
theorem mtFiber20Row_23_ok : mtFiber20RowCheck 23 = true := by decide
theorem mtFiber20Row_24_ok : mtFiber20RowCheck 24 = true := by decide
theorem mtFiber20Row_25_ok : mtFiber20RowCheck 25 = true := by decide
theorem mtFiber20Row_26_ok : mtFiber20RowCheck 26 = true := by decide
theorem mtFiber20Row_27_ok : mtFiber20RowCheck 27 = true := by decide
theorem mtFiber20Row_28_ok : mtFiber20RowCheck 28 = true := by decide
theorem mtFiber20Row_29_ok : mtFiber20RowCheck 29 = true := by decide
theorem mtFiber20Row_30_ok : mtFiber20RowCheck 30 = true := by decide
theorem mtFiber20Row_31_ok : mtFiber20RowCheck 31 = true := by decide
theorem mtFiber20Row_32_ok : mtFiber20RowCheck 32 = true := by decide
theorem mtFiber20Row_33_ok : mtFiber20RowCheck 33 = true := by decide
theorem mtFiber20Row_34_ok : mtFiber20RowCheck 34 = true := by decide
theorem mtFiber20Row_35_ok : mtFiber20RowCheck 35 = true := by decide
theorem mtFiber20Row_36_ok : mtFiber20RowCheck 36 = true := by decide
theorem mtFiber20Row_37_ok : mtFiber20RowCheck 37 = true := by decide
theorem mtFiber20Row_38_ok : mtFiber20RowCheck 38 = true := by decide
theorem mtFiber20Row_39_ok : mtFiber20RowCheck 39 = true := by decide
theorem mtFiber20Row_40_ok : mtFiber20RowCheck 40 = true := by decide
theorem mtFiber20Row_41_ok : mtFiber20RowCheck 41 = true := by decide
theorem mtFiber20Row_42_ok : mtFiber20RowCheck 42 = true := by decide
theorem mtFiber20Row_43_ok : mtFiber20RowCheck 43 = true := by decide
theorem mtFiber20Row_44_ok : mtFiber20RowCheck 44 = true := by decide
theorem mtFiber20Row_45_ok : mtFiber20RowCheck 45 = true := by decide
theorem mtFiber20Row_46_ok : mtFiber20RowCheck 46 = true := by decide
theorem mtFiber20Row_47_ok : mtFiber20RowCheck 47 = true := by decide
theorem mtFiber20Row_48_ok : mtFiber20RowCheck 48 = true := by decide
theorem mtFiber20Row_49_ok : mtFiber20RowCheck 49 = true := by decide
theorem mtFiber20Row_50_ok : mtFiber20RowCheck 50 = true := by decide
theorem mtFiber20Row_51_ok : mtFiber20RowCheck 51 = true := by decide
theorem mtFiber20Row_52_ok : mtFiber20RowCheck 52 = true := by decide
theorem mtFiber20Row_53_ok : mtFiber20RowCheck 53 = true := by decide
theorem mtFiber20Row_54_ok : mtFiber20RowCheck 54 = true := by decide
theorem mtFiber20Row_55_ok : mtFiber20RowCheck 55 = true := by decide
theorem mtFiber20Row_56_ok : mtFiber20RowCheck 56 = true := by decide
theorem mtFiber20Row_57_ok : mtFiber20RowCheck 57 = true := by decide
theorem mtFiber20Row_58_ok : mtFiber20RowCheck 58 = true := by decide
theorem mtFiber20Row_59_ok : mtFiber20RowCheck 59 = true := by decide
theorem mtFiber20Row_60_ok : mtFiber20RowCheck 60 = true := by decide
theorem mtFiber20Row_61_ok : mtFiber20RowCheck 61 = true := by decide
theorem mtFiber20Row_62_ok : mtFiber20RowCheck 62 = true := by decide
theorem mtFiber20Row_63_ok : mtFiber20RowCheck 63 = true := by decide

def mtFiber20ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber20Rows mtMaxParentDepth (listGetD mtFiber20Expected i 0) == 96

theorem mtFiber20Parent_0_ok : mtFiber20ParentCheck 0 = true := by decide
theorem mtFiber20Parent_1_ok : mtFiber20ParentCheck 1 = true := by decide
theorem mtFiber20Parent_2_ok : mtFiber20ParentCheck 2 = true := by decide
theorem mtFiber20Parent_3_ok : mtFiber20ParentCheck 3 = true := by decide
theorem mtFiber20Parent_4_ok : mtFiber20ParentCheck 4 = true := by decide
theorem mtFiber20Parent_5_ok : mtFiber20ParentCheck 5 = true := by decide
theorem mtFiber20Parent_6_ok : mtFiber20ParentCheck 6 = true := by decide
theorem mtFiber20Parent_7_ok : mtFiber20ParentCheck 7 = true := by decide
theorem mtFiber20Parent_8_ok : mtFiber20ParentCheck 8 = true := by decide
theorem mtFiber20Parent_9_ok : mtFiber20ParentCheck 9 = true := by decide
theorem mtFiber20Parent_10_ok : mtFiber20ParentCheck 10 = true := by decide
theorem mtFiber20Parent_11_ok : mtFiber20ParentCheck 11 = true := by decide
theorem mtFiber20Parent_12_ok : mtFiber20ParentCheck 12 = true := by decide
theorem mtFiber20Parent_13_ok : mtFiber20ParentCheck 13 = true := by decide
theorem mtFiber20Parent_14_ok : mtFiber20ParentCheck 14 = true := by decide
theorem mtFiber20Parent_15_ok : mtFiber20ParentCheck 15 = true := by decide
theorem mtFiber20Parent_16_ok : mtFiber20ParentCheck 16 = true := by decide
theorem mtFiber20Parent_17_ok : mtFiber20ParentCheck 17 = true := by decide
theorem mtFiber20Parent_18_ok : mtFiber20ParentCheck 18 = true := by decide
theorem mtFiber20Parent_19_ok : mtFiber20ParentCheck 19 = true := by decide
theorem mtFiber20Parent_20_ok : mtFiber20ParentCheck 20 = true := by decide
theorem mtFiber20Parent_21_ok : mtFiber20ParentCheck 21 = true := by decide
theorem mtFiber20Parent_22_ok : mtFiber20ParentCheck 22 = true := by decide
theorem mtFiber20Parent_23_ok : mtFiber20ParentCheck 23 = true := by decide
theorem mtFiber20Parent_24_ok : mtFiber20ParentCheck 24 = true := by decide
theorem mtFiber20Parent_25_ok : mtFiber20ParentCheck 25 = true := by decide
theorem mtFiber20Parent_26_ok : mtFiber20ParentCheck 26 = true := by decide
theorem mtFiber20Parent_27_ok : mtFiber20ParentCheck 27 = true := by decide
theorem mtFiber20Parent_28_ok : mtFiber20ParentCheck 28 = true := by decide
theorem mtFiber20Parent_29_ok : mtFiber20ParentCheck 29 = true := by decide
theorem mtFiber20Parent_30_ok : mtFiber20ParentCheck 30 = true := by decide
theorem mtFiber20Parent_31_ok : mtFiber20ParentCheck 31 = true := by decide
theorem mtFiber20Parent_32_ok : mtFiber20ParentCheck 32 = true := by decide
theorem mtFiber20Parent_33_ok : mtFiber20ParentCheck 33 = true := by decide
theorem mtFiber20Parent_34_ok : mtFiber20ParentCheck 34 = true := by decide
theorem mtFiber20Parent_35_ok : mtFiber20ParentCheck 35 = true := by decide
theorem mtFiber20Parent_36_ok : mtFiber20ParentCheck 36 = true := by decide
theorem mtFiber20Parent_37_ok : mtFiber20ParentCheck 37 = true := by decide
theorem mtFiber20Parent_38_ok : mtFiber20ParentCheck 38 = true := by decide
theorem mtFiber20Parent_39_ok : mtFiber20ParentCheck 39 = true := by decide
theorem mtFiber20Parent_40_ok : mtFiber20ParentCheck 40 = true := by decide
theorem mtFiber20Parent_41_ok : mtFiber20ParentCheck 41 = true := by decide
theorem mtFiber20Parent_42_ok : mtFiber20ParentCheck 42 = true := by decide
theorem mtFiber20Parent_43_ok : mtFiber20ParentCheck 43 = true := by decide
theorem mtFiber20Parent_44_ok : mtFiber20ParentCheck 44 = true := by decide
theorem mtFiber20Parent_45_ok : mtFiber20ParentCheck 45 = true := by decide
theorem mtFiber20Parent_46_ok : mtFiber20ParentCheck 46 = true := by decide
theorem mtFiber20Parent_47_ok : mtFiber20ParentCheck 47 = true := by decide
theorem mtFiber20Parent_48_ok : mtFiber20ParentCheck 48 = true := by decide
theorem mtFiber20Parent_49_ok : mtFiber20ParentCheck 49 = true := by decide
theorem mtFiber20Parent_50_ok : mtFiber20ParentCheck 50 = true := by decide
theorem mtFiber20Parent_51_ok : mtFiber20ParentCheck 51 = true := by decide
theorem mtFiber20Parent_52_ok : mtFiber20ParentCheck 52 = true := by decide
theorem mtFiber20Parent_53_ok : mtFiber20ParentCheck 53 = true := by decide
theorem mtFiber20Parent_54_ok : mtFiber20ParentCheck 54 = true := by decide
theorem mtFiber20Parent_55_ok : mtFiber20ParentCheck 55 = true := by decide
theorem mtFiber20Parent_56_ok : mtFiber20ParentCheck 56 = true := by decide
theorem mtFiber20Parent_57_ok : mtFiber20ParentCheck 57 = true := by decide
theorem mtFiber20Parent_58_ok : mtFiber20ParentCheck 58 = true := by decide
theorem mtFiber20Parent_59_ok : mtFiber20ParentCheck 59 = true := by decide
theorem mtFiber20Parent_60_ok : mtFiber20ParentCheck 60 = true := by decide
theorem mtFiber20Parent_61_ok : mtFiber20ParentCheck 61 = true := by decide
theorem mtFiber20Parent_62_ok : mtFiber20ParentCheck 62 = true := by decide
theorem mtFiber20Parent_63_ok : mtFiber20ParentCheck 63 = true := by decide

def mtFiber20CertificateAudit : Bool :=
  mtFiber20SourcesCheck &&
    mtFiber20RowCheck 0 &&
    mtFiber20RowCheck 1 &&
    mtFiber20RowCheck 2 &&
    mtFiber20RowCheck 3 &&
    mtFiber20RowCheck 4 &&
    mtFiber20RowCheck 5 &&
    mtFiber20RowCheck 6 &&
    mtFiber20RowCheck 7 &&
    mtFiber20RowCheck 8 &&
    mtFiber20RowCheck 9 &&
    mtFiber20RowCheck 10 &&
    mtFiber20RowCheck 11 &&
    mtFiber20RowCheck 12 &&
    mtFiber20RowCheck 13 &&
    mtFiber20RowCheck 14 &&
    mtFiber20RowCheck 15 &&
    mtFiber20RowCheck 16 &&
    mtFiber20RowCheck 17 &&
    mtFiber20RowCheck 18 &&
    mtFiber20RowCheck 19 &&
    mtFiber20RowCheck 20 &&
    mtFiber20RowCheck 21 &&
    mtFiber20RowCheck 22 &&
    mtFiber20RowCheck 23 &&
    mtFiber20RowCheck 24 &&
    mtFiber20RowCheck 25 &&
    mtFiber20RowCheck 26 &&
    mtFiber20RowCheck 27 &&
    mtFiber20RowCheck 28 &&
    mtFiber20RowCheck 29 &&
    mtFiber20RowCheck 30 &&
    mtFiber20RowCheck 31 &&
    mtFiber20RowCheck 32 &&
    mtFiber20RowCheck 33 &&
    mtFiber20RowCheck 34 &&
    mtFiber20RowCheck 35 &&
    mtFiber20RowCheck 36 &&
    mtFiber20RowCheck 37 &&
    mtFiber20RowCheck 38 &&
    mtFiber20RowCheck 39 &&
    mtFiber20RowCheck 40 &&
    mtFiber20RowCheck 41 &&
    mtFiber20RowCheck 42 &&
    mtFiber20RowCheck 43 &&
    mtFiber20RowCheck 44 &&
    mtFiber20RowCheck 45 &&
    mtFiber20RowCheck 46 &&
    mtFiber20RowCheck 47 &&
    mtFiber20RowCheck 48 &&
    mtFiber20RowCheck 49 &&
    mtFiber20RowCheck 50 &&
    mtFiber20RowCheck 51 &&
    mtFiber20RowCheck 52 &&
    mtFiber20RowCheck 53 &&
    mtFiber20RowCheck 54 &&
    mtFiber20RowCheck 55 &&
    mtFiber20RowCheck 56 &&
    mtFiber20RowCheck 57 &&
    mtFiber20RowCheck 58 &&
    mtFiber20RowCheck 59 &&
    mtFiber20RowCheck 60 &&
    mtFiber20RowCheck 61 &&
    mtFiber20RowCheck 62 &&
    mtFiber20RowCheck 63 &&
    mtFiber20ParentCheck 0 &&
    mtFiber20ParentCheck 1 &&
    mtFiber20ParentCheck 2 &&
    mtFiber20ParentCheck 3 &&
    mtFiber20ParentCheck 4 &&
    mtFiber20ParentCheck 5 &&
    mtFiber20ParentCheck 6 &&
    mtFiber20ParentCheck 7 &&
    mtFiber20ParentCheck 8 &&
    mtFiber20ParentCheck 9 &&
    mtFiber20ParentCheck 10 &&
    mtFiber20ParentCheck 11 &&
    mtFiber20ParentCheck 12 &&
    mtFiber20ParentCheck 13 &&
    mtFiber20ParentCheck 14 &&
    mtFiber20ParentCheck 15 &&
    mtFiber20ParentCheck 16 &&
    mtFiber20ParentCheck 17 &&
    mtFiber20ParentCheck 18 &&
    mtFiber20ParentCheck 19 &&
    mtFiber20ParentCheck 20 &&
    mtFiber20ParentCheck 21 &&
    mtFiber20ParentCheck 22 &&
    mtFiber20ParentCheck 23 &&
    mtFiber20ParentCheck 24 &&
    mtFiber20ParentCheck 25 &&
    mtFiber20ParentCheck 26 &&
    mtFiber20ParentCheck 27 &&
    mtFiber20ParentCheck 28 &&
    mtFiber20ParentCheck 29 &&
    mtFiber20ParentCheck 30 &&
    mtFiber20ParentCheck 31 &&
    mtFiber20ParentCheck 32 &&
    mtFiber20ParentCheck 33 &&
    mtFiber20ParentCheck 34 &&
    mtFiber20ParentCheck 35 &&
    mtFiber20ParentCheck 36 &&
    mtFiber20ParentCheck 37 &&
    mtFiber20ParentCheck 38 &&
    mtFiber20ParentCheck 39 &&
    mtFiber20ParentCheck 40 &&
    mtFiber20ParentCheck 41 &&
    mtFiber20ParentCheck 42 &&
    mtFiber20ParentCheck 43 &&
    mtFiber20ParentCheck 44 &&
    mtFiber20ParentCheck 45 &&
    mtFiber20ParentCheck 46 &&
    mtFiber20ParentCheck 47 &&
    mtFiber20ParentCheck 48 &&
    mtFiber20ParentCheck 49 &&
    mtFiber20ParentCheck 50 &&
    mtFiber20ParentCheck 51 &&
    mtFiber20ParentCheck 52 &&
    mtFiber20ParentCheck 53 &&
    mtFiber20ParentCheck 54 &&
    mtFiber20ParentCheck 55 &&
    mtFiber20ParentCheck 56 &&
    mtFiber20ParentCheck 57 &&
    mtFiber20ParentCheck 58 &&
    mtFiber20ParentCheck 59 &&
    mtFiber20ParentCheck 60 &&
    mtFiber20ParentCheck 61 &&
    mtFiber20ParentCheck 62 &&
    mtFiber20ParentCheck 63

theorem mtFiber20CertificateAudit_ok :
    mtFiber20CertificateAudit = true := by
  simp [mtFiber20CertificateAudit,
    mtFiber20SourcesCheck_ok,
    mtFiber20Row_0_ok,
    mtFiber20Row_1_ok,
    mtFiber20Row_2_ok,
    mtFiber20Row_3_ok,
    mtFiber20Row_4_ok,
    mtFiber20Row_5_ok,
    mtFiber20Row_6_ok,
    mtFiber20Row_7_ok,
    mtFiber20Row_8_ok,
    mtFiber20Row_9_ok,
    mtFiber20Row_10_ok,
    mtFiber20Row_11_ok,
    mtFiber20Row_12_ok,
    mtFiber20Row_13_ok,
    mtFiber20Row_14_ok,
    mtFiber20Row_15_ok,
    mtFiber20Row_16_ok,
    mtFiber20Row_17_ok,
    mtFiber20Row_18_ok,
    mtFiber20Row_19_ok,
    mtFiber20Row_20_ok,
    mtFiber20Row_21_ok,
    mtFiber20Row_22_ok,
    mtFiber20Row_23_ok,
    mtFiber20Row_24_ok,
    mtFiber20Row_25_ok,
    mtFiber20Row_26_ok,
    mtFiber20Row_27_ok,
    mtFiber20Row_28_ok,
    mtFiber20Row_29_ok,
    mtFiber20Row_30_ok,
    mtFiber20Row_31_ok,
    mtFiber20Row_32_ok,
    mtFiber20Row_33_ok,
    mtFiber20Row_34_ok,
    mtFiber20Row_35_ok,
    mtFiber20Row_36_ok,
    mtFiber20Row_37_ok,
    mtFiber20Row_38_ok,
    mtFiber20Row_39_ok,
    mtFiber20Row_40_ok,
    mtFiber20Row_41_ok,
    mtFiber20Row_42_ok,
    mtFiber20Row_43_ok,
    mtFiber20Row_44_ok,
    mtFiber20Row_45_ok,
    mtFiber20Row_46_ok,
    mtFiber20Row_47_ok,
    mtFiber20Row_48_ok,
    mtFiber20Row_49_ok,
    mtFiber20Row_50_ok,
    mtFiber20Row_51_ok,
    mtFiber20Row_52_ok,
    mtFiber20Row_53_ok,
    mtFiber20Row_54_ok,
    mtFiber20Row_55_ok,
    mtFiber20Row_56_ok,
    mtFiber20Row_57_ok,
    mtFiber20Row_58_ok,
    mtFiber20Row_59_ok,
    mtFiber20Row_60_ok,
    mtFiber20Row_61_ok,
    mtFiber20Row_62_ok,
    mtFiber20Row_63_ok,
    mtFiber20Parent_0_ok,
    mtFiber20Parent_1_ok,
    mtFiber20Parent_2_ok,
    mtFiber20Parent_3_ok,
    mtFiber20Parent_4_ok,
    mtFiber20Parent_5_ok,
    mtFiber20Parent_6_ok,
    mtFiber20Parent_7_ok,
    mtFiber20Parent_8_ok,
    mtFiber20Parent_9_ok,
    mtFiber20Parent_10_ok,
    mtFiber20Parent_11_ok,
    mtFiber20Parent_12_ok,
    mtFiber20Parent_13_ok,
    mtFiber20Parent_14_ok,
    mtFiber20Parent_15_ok,
    mtFiber20Parent_16_ok,
    mtFiber20Parent_17_ok,
    mtFiber20Parent_18_ok,
    mtFiber20Parent_19_ok,
    mtFiber20Parent_20_ok,
    mtFiber20Parent_21_ok,
    mtFiber20Parent_22_ok,
    mtFiber20Parent_23_ok,
    mtFiber20Parent_24_ok,
    mtFiber20Parent_25_ok,
    mtFiber20Parent_26_ok,
    mtFiber20Parent_27_ok,
    mtFiber20Parent_28_ok,
    mtFiber20Parent_29_ok,
    mtFiber20Parent_30_ok,
    mtFiber20Parent_31_ok,
    mtFiber20Parent_32_ok,
    mtFiber20Parent_33_ok,
    mtFiber20Parent_34_ok,
    mtFiber20Parent_35_ok,
    mtFiber20Parent_36_ok,
    mtFiber20Parent_37_ok,
    mtFiber20Parent_38_ok,
    mtFiber20Parent_39_ok,
    mtFiber20Parent_40_ok,
    mtFiber20Parent_41_ok,
    mtFiber20Parent_42_ok,
    mtFiber20Parent_43_ok,
    mtFiber20Parent_44_ok,
    mtFiber20Parent_45_ok,
    mtFiber20Parent_46_ok,
    mtFiber20Parent_47_ok,
    mtFiber20Parent_48_ok,
    mtFiber20Parent_49_ok,
    mtFiber20Parent_50_ok,
    mtFiber20Parent_51_ok,
    mtFiber20Parent_52_ok,
    mtFiber20Parent_53_ok,
    mtFiber20Parent_54_ok,
    mtFiber20Parent_55_ok,
    mtFiber20Parent_56_ok,
    mtFiber20Parent_57_ok,
    mtFiber20Parent_58_ok,
    mtFiber20Parent_59_ok,
    mtFiber20Parent_60_ok,
    mtFiber20Parent_61_ok,
    mtFiber20Parent_62_ok,
    mtFiber20Parent_63_ok]

def mtFiber21Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.r]

def mtFiber21Expected : List Nat :=
  []

def mtFiber21Rows : List DirectChainParentRow :=
  []

def mtFiber21RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber21Rows i default

def mtFiber21SourcesCheck : Bool :=
  (mtFiber21Rows.map fun row => row.source) == mtFiber21Expected

theorem mtFiber21SourcesCheck_ok :
    mtFiber21SourcesCheck = true := by
  decide

def mtFiber21RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber21Key mtFiber21Expected (mtFiber21RowAt i)

def mtFiber21ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber21Rows mtMaxParentDepth (listGetD mtFiber21Expected i 0) == 0

def mtFiber21CertificateAudit : Bool :=
  mtFiber21SourcesCheck

theorem mtFiber21CertificateAudit_ok :
    mtFiber21CertificateAudit = true := by
  simp [mtFiber21CertificateAudit,
    mtFiber21SourcesCheck_ok]

def mtFiber22Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.b]

def mtFiber22Expected : List Nat :=
  [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]

def mtFiber22Rows : List DirectChainParentRow :=
  [ directRow 960 960 160 28 160 28 default
  , directRow 961 960 160 29 160 28 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 962 960 160 30 160 28 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 963 961 160 31 160 29 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 964 960 161 20 160 28 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 965 961 161 21 160 29 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 966 962 161 22 160 30 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 967 963 161 23 160 31 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 968 960 162 12 160 28 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 969 961 162 13 160 29 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 970 962 162 14 160 30 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 971 963 162 15 160 31 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 972 964 163 4 161 20 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 973 965 163 5 161 21 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 974 966 163 6 161 22 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 975 967 163 7 161 23 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber22RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber22Rows i default

def mtFiber22SourcesCheck : Bool :=
  (mtFiber22Rows.map fun row => row.source) == mtFiber22Expected

theorem mtFiber22SourcesCheck_ok :
    mtFiber22SourcesCheck = true := by
  decide

def mtFiber22RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt i)

theorem mtFiber22Row_0_ok : mtFiber22RowCheck 0 = true := by decide
theorem mtFiber22Row_1_ok : mtFiber22RowCheck 1 = true := by decide
theorem mtFiber22Row_2_ok : mtFiber22RowCheck 2 = true := by decide
theorem mtFiber22Row_3_ok : mtFiber22RowCheck 3 = true := by decide
theorem mtFiber22Row_4_ok : mtFiber22RowCheck 4 = true := by decide
theorem mtFiber22Row_5_ok : mtFiber22RowCheck 5 = true := by decide
theorem mtFiber22Row_6_ok : mtFiber22RowCheck 6 = true := by decide
theorem mtFiber22Row_7_ok : mtFiber22RowCheck 7 = true := by decide
theorem mtFiber22Row_8_ok : mtFiber22RowCheck 8 = true := by decide
theorem mtFiber22Row_9_ok : mtFiber22RowCheck 9 = true := by decide
theorem mtFiber22Row_10_ok : mtFiber22RowCheck 10 = true := by decide
theorem mtFiber22Row_11_ok : mtFiber22RowCheck 11 = true := by decide
theorem mtFiber22Row_12_ok : mtFiber22RowCheck 12 = true := by decide
theorem mtFiber22Row_13_ok : mtFiber22RowCheck 13 = true := by decide
theorem mtFiber22Row_14_ok : mtFiber22RowCheck 14 = true := by decide
theorem mtFiber22Row_15_ok : mtFiber22RowCheck 15 = true := by decide

def mtFiber22ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber22Rows mtMaxParentDepth (listGetD mtFiber22Expected i 0) == 960

theorem mtFiber22Parent_0_ok : mtFiber22ParentCheck 0 = true := by decide
theorem mtFiber22Parent_1_ok : mtFiber22ParentCheck 1 = true := by decide
theorem mtFiber22Parent_2_ok : mtFiber22ParentCheck 2 = true := by decide
theorem mtFiber22Parent_3_ok : mtFiber22ParentCheck 3 = true := by decide
theorem mtFiber22Parent_4_ok : mtFiber22ParentCheck 4 = true := by decide
theorem mtFiber22Parent_5_ok : mtFiber22ParentCheck 5 = true := by decide
theorem mtFiber22Parent_6_ok : mtFiber22ParentCheck 6 = true := by decide
theorem mtFiber22Parent_7_ok : mtFiber22ParentCheck 7 = true := by decide
theorem mtFiber22Parent_8_ok : mtFiber22ParentCheck 8 = true := by decide
theorem mtFiber22Parent_9_ok : mtFiber22ParentCheck 9 = true := by decide
theorem mtFiber22Parent_10_ok : mtFiber22ParentCheck 10 = true := by decide
theorem mtFiber22Parent_11_ok : mtFiber22ParentCheck 11 = true := by decide
theorem mtFiber22Parent_12_ok : mtFiber22ParentCheck 12 = true := by decide
theorem mtFiber22Parent_13_ok : mtFiber22ParentCheck 13 = true := by decide
theorem mtFiber22Parent_14_ok : mtFiber22ParentCheck 14 = true := by decide
theorem mtFiber22Parent_15_ok : mtFiber22ParentCheck 15 = true := by decide

def mtFiber22CertificateAudit : Bool :=
  mtFiber22SourcesCheck &&
    mtFiber22RowCheck 0 &&
    mtFiber22RowCheck 1 &&
    mtFiber22RowCheck 2 &&
    mtFiber22RowCheck 3 &&
    mtFiber22RowCheck 4 &&
    mtFiber22RowCheck 5 &&
    mtFiber22RowCheck 6 &&
    mtFiber22RowCheck 7 &&
    mtFiber22RowCheck 8 &&
    mtFiber22RowCheck 9 &&
    mtFiber22RowCheck 10 &&
    mtFiber22RowCheck 11 &&
    mtFiber22RowCheck 12 &&
    mtFiber22RowCheck 13 &&
    mtFiber22RowCheck 14 &&
    mtFiber22RowCheck 15 &&
    mtFiber22ParentCheck 0 &&
    mtFiber22ParentCheck 1 &&
    mtFiber22ParentCheck 2 &&
    mtFiber22ParentCheck 3 &&
    mtFiber22ParentCheck 4 &&
    mtFiber22ParentCheck 5 &&
    mtFiber22ParentCheck 6 &&
    mtFiber22ParentCheck 7 &&
    mtFiber22ParentCheck 8 &&
    mtFiber22ParentCheck 9 &&
    mtFiber22ParentCheck 10 &&
    mtFiber22ParentCheck 11 &&
    mtFiber22ParentCheck 12 &&
    mtFiber22ParentCheck 13 &&
    mtFiber22ParentCheck 14 &&
    mtFiber22ParentCheck 15

theorem mtFiber22CertificateAudit_ok :
    mtFiber22CertificateAudit = true := by
  simp [mtFiber22CertificateAudit,
    mtFiber22SourcesCheck_ok,
    mtFiber22Row_0_ok,
    mtFiber22Row_1_ok,
    mtFiber22Row_2_ok,
    mtFiber22Row_3_ok,
    mtFiber22Row_4_ok,
    mtFiber22Row_5_ok,
    mtFiber22Row_6_ok,
    mtFiber22Row_7_ok,
    mtFiber22Row_8_ok,
    mtFiber22Row_9_ok,
    mtFiber22Row_10_ok,
    mtFiber22Row_11_ok,
    mtFiber22Row_12_ok,
    mtFiber22Row_13_ok,
    mtFiber22Row_14_ok,
    mtFiber22Row_15_ok,
    mtFiber22Parent_0_ok,
    mtFiber22Parent_1_ok,
    mtFiber22Parent_2_ok,
    mtFiber22Parent_3_ok,
    mtFiber22Parent_4_ok,
    mtFiber22Parent_5_ok,
    mtFiber22Parent_6_ok,
    mtFiber22Parent_7_ok,
    mtFiber22Parent_8_ok,
    mtFiber22Parent_9_ok,
    mtFiber22Parent_10_ok,
    mtFiber22Parent_11_ok,
    mtFiber22Parent_12_ok,
    mtFiber22Parent_13_ok,
    mtFiber22Parent_14_ok,
    mtFiber22Parent_15_ok]

def mtFiber23Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.p]

def mtFiber23Expected : List Nat :=
  [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]

def mtFiber23Rows : List DirectChainParentRow :=
  [ directRow 576 576 96 44 96 44 default
  , directRow 577 576 96 45 96 44 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 578 577 96 46 96 45 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 579 576 96 47 96 44 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 580 576 97 36 96 44 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 581 577 97 37 96 45 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 582 578 97 38 96 46 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 583 579 97 39 96 47 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 584 576 98 60 96 44 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 585 577 98 61 96 45 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 586 578 98 62 96 46 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 587 579 98 63 96 47 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 588 580 99 52 97 36 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 589 581 99 53 97 37 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 590 582 99 54 97 38 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 591 583 99 55 97 39 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber23RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber23Rows i default

def mtFiber23SourcesCheck : Bool :=
  (mtFiber23Rows.map fun row => row.source) == mtFiber23Expected

theorem mtFiber23SourcesCheck_ok :
    mtFiber23SourcesCheck = true := by
  decide

def mtFiber23RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt i)

theorem mtFiber23Row_0_ok : mtFiber23RowCheck 0 = true := by decide
theorem mtFiber23Row_1_ok : mtFiber23RowCheck 1 = true := by decide
theorem mtFiber23Row_2_ok : mtFiber23RowCheck 2 = true := by decide
theorem mtFiber23Row_3_ok : mtFiber23RowCheck 3 = true := by decide
theorem mtFiber23Row_4_ok : mtFiber23RowCheck 4 = true := by decide
theorem mtFiber23Row_5_ok : mtFiber23RowCheck 5 = true := by decide
theorem mtFiber23Row_6_ok : mtFiber23RowCheck 6 = true := by decide
theorem mtFiber23Row_7_ok : mtFiber23RowCheck 7 = true := by decide
theorem mtFiber23Row_8_ok : mtFiber23RowCheck 8 = true := by decide
theorem mtFiber23Row_9_ok : mtFiber23RowCheck 9 = true := by decide
theorem mtFiber23Row_10_ok : mtFiber23RowCheck 10 = true := by decide
theorem mtFiber23Row_11_ok : mtFiber23RowCheck 11 = true := by decide
theorem mtFiber23Row_12_ok : mtFiber23RowCheck 12 = true := by decide
theorem mtFiber23Row_13_ok : mtFiber23RowCheck 13 = true := by decide
theorem mtFiber23Row_14_ok : mtFiber23RowCheck 14 = true := by decide
theorem mtFiber23Row_15_ok : mtFiber23RowCheck 15 = true := by decide

def mtFiber23ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber23Rows mtMaxParentDepth (listGetD mtFiber23Expected i 0) == 576

theorem mtFiber23Parent_0_ok : mtFiber23ParentCheck 0 = true := by decide
theorem mtFiber23Parent_1_ok : mtFiber23ParentCheck 1 = true := by decide
theorem mtFiber23Parent_2_ok : mtFiber23ParentCheck 2 = true := by decide
theorem mtFiber23Parent_3_ok : mtFiber23ParentCheck 3 = true := by decide
theorem mtFiber23Parent_4_ok : mtFiber23ParentCheck 4 = true := by decide
theorem mtFiber23Parent_5_ok : mtFiber23ParentCheck 5 = true := by decide
theorem mtFiber23Parent_6_ok : mtFiber23ParentCheck 6 = true := by decide
theorem mtFiber23Parent_7_ok : mtFiber23ParentCheck 7 = true := by decide
theorem mtFiber23Parent_8_ok : mtFiber23ParentCheck 8 = true := by decide
theorem mtFiber23Parent_9_ok : mtFiber23ParentCheck 9 = true := by decide
theorem mtFiber23Parent_10_ok : mtFiber23ParentCheck 10 = true := by decide
theorem mtFiber23Parent_11_ok : mtFiber23ParentCheck 11 = true := by decide
theorem mtFiber23Parent_12_ok : mtFiber23ParentCheck 12 = true := by decide
theorem mtFiber23Parent_13_ok : mtFiber23ParentCheck 13 = true := by decide
theorem mtFiber23Parent_14_ok : mtFiber23ParentCheck 14 = true := by decide
theorem mtFiber23Parent_15_ok : mtFiber23ParentCheck 15 = true := by decide

def mtFiber23CertificateAudit : Bool :=
  mtFiber23SourcesCheck &&
    mtFiber23RowCheck 0 &&
    mtFiber23RowCheck 1 &&
    mtFiber23RowCheck 2 &&
    mtFiber23RowCheck 3 &&
    mtFiber23RowCheck 4 &&
    mtFiber23RowCheck 5 &&
    mtFiber23RowCheck 6 &&
    mtFiber23RowCheck 7 &&
    mtFiber23RowCheck 8 &&
    mtFiber23RowCheck 9 &&
    mtFiber23RowCheck 10 &&
    mtFiber23RowCheck 11 &&
    mtFiber23RowCheck 12 &&
    mtFiber23RowCheck 13 &&
    mtFiber23RowCheck 14 &&
    mtFiber23RowCheck 15 &&
    mtFiber23ParentCheck 0 &&
    mtFiber23ParentCheck 1 &&
    mtFiber23ParentCheck 2 &&
    mtFiber23ParentCheck 3 &&
    mtFiber23ParentCheck 4 &&
    mtFiber23ParentCheck 5 &&
    mtFiber23ParentCheck 6 &&
    mtFiber23ParentCheck 7 &&
    mtFiber23ParentCheck 8 &&
    mtFiber23ParentCheck 9 &&
    mtFiber23ParentCheck 10 &&
    mtFiber23ParentCheck 11 &&
    mtFiber23ParentCheck 12 &&
    mtFiber23ParentCheck 13 &&
    mtFiber23ParentCheck 14 &&
    mtFiber23ParentCheck 15

theorem mtFiber23CertificateAudit_ok :
    mtFiber23CertificateAudit = true := by
  simp [mtFiber23CertificateAudit,
    mtFiber23SourcesCheck_ok,
    mtFiber23Row_0_ok,
    mtFiber23Row_1_ok,
    mtFiber23Row_2_ok,
    mtFiber23Row_3_ok,
    mtFiber23Row_4_ok,
    mtFiber23Row_5_ok,
    mtFiber23Row_6_ok,
    mtFiber23Row_7_ok,
    mtFiber23Row_8_ok,
    mtFiber23Row_9_ok,
    mtFiber23Row_10_ok,
    mtFiber23Row_11_ok,
    mtFiber23Row_12_ok,
    mtFiber23Row_13_ok,
    mtFiber23Row_14_ok,
    mtFiber23Row_15_ok,
    mtFiber23Parent_0_ok,
    mtFiber23Parent_1_ok,
    mtFiber23Parent_2_ok,
    mtFiber23Parent_3_ok,
    mtFiber23Parent_4_ok,
    mtFiber23Parent_5_ok,
    mtFiber23Parent_6_ok,
    mtFiber23Parent_7_ok,
    mtFiber23Parent_8_ok,
    mtFiber23Parent_9_ok,
    mtFiber23Parent_10_ok,
    mtFiber23Parent_11_ok,
    mtFiber23Parent_12_ok,
    mtFiber23Parent_13_ok,
    mtFiber23Parent_14_ok,
    mtFiber23Parent_15_ok]

def mtFiber24Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.r]

def mtFiber24Expected : List Nat :=
  []

def mtFiber24Rows : List DirectChainParentRow :=
  []

def mtFiber24RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber24Rows i default

def mtFiber24SourcesCheck : Bool :=
  (mtFiber24Rows.map fun row => row.source) == mtFiber24Expected

theorem mtFiber24SourcesCheck_ok :
    mtFiber24SourcesCheck = true := by
  decide

def mtFiber24RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber24Key mtFiber24Expected (mtFiber24RowAt i)

def mtFiber24ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber24Rows mtMaxParentDepth (listGetD mtFiber24Expected i 0) == 0

def mtFiber24CertificateAudit : Bool :=
  mtFiber24SourcesCheck

theorem mtFiber24CertificateAudit_ok :
    mtFiber24CertificateAudit = true := by
  simp [mtFiber24CertificateAudit,
    mtFiber24SourcesCheck_ok]

def mtFiber25Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.b]

def mtFiber25Expected : List Nat :=
  []

def mtFiber25Rows : List DirectChainParentRow :=
  []

def mtFiber25RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber25Rows i default

def mtFiber25SourcesCheck : Bool :=
  (mtFiber25Rows.map fun row => row.source) == mtFiber25Expected

theorem mtFiber25SourcesCheck_ok :
    mtFiber25SourcesCheck = true := by
  decide

def mtFiber25RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber25Key mtFiber25Expected (mtFiber25RowAt i)

def mtFiber25ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber25Rows mtMaxParentDepth (listGetD mtFiber25Expected i 0) == 0

def mtFiber25CertificateAudit : Bool :=
  mtFiber25SourcesCheck

theorem mtFiber25CertificateAudit_ok :
    mtFiber25CertificateAudit = true := by
  simp [mtFiber25CertificateAudit,
    mtFiber25SourcesCheck_ok]

def mtFiber26Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.p]

def mtFiber26Expected : List Nat :=
  []

def mtFiber26Rows : List DirectChainParentRow :=
  []

def mtFiber26RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber26Rows i default

def mtFiber26SourcesCheck : Bool :=
  (mtFiber26Rows.map fun row => row.source) == mtFiber26Expected

theorem mtFiber26SourcesCheck_ok :
    mtFiber26SourcesCheck = true := by
  decide

def mtFiber26RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber26Key mtFiber26Expected (mtFiber26RowAt i)

def mtFiber26ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber26Rows mtMaxParentDepth (listGetD mtFiber26Expected i 0) == 0

def mtFiber26CertificateAudit : Bool :=
  mtFiber26SourcesCheck

theorem mtFiber26CertificateAudit_ok :
    mtFiber26CertificateAudit = true := by
  simp [mtFiber26CertificateAudit,
    mtFiber26SourcesCheck_ok]

def mtFiber27Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.r]

def mtFiber27Expected : List Nat :=
  []

def mtFiber27Rows : List DirectChainParentRow :=
  []

def mtFiber27RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber27Rows i default

def mtFiber27SourcesCheck : Bool :=
  (mtFiber27Rows.map fun row => row.source) == mtFiber27Expected

theorem mtFiber27SourcesCheck_ok :
    mtFiber27SourcesCheck = true := by
  decide

def mtFiber27RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber27Key mtFiber27Expected (mtFiber27RowAt i)

def mtFiber27ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber27Rows mtMaxParentDepth (listGetD mtFiber27Expected i 0) == 0

def mtFiber27CertificateAudit : Bool :=
  mtFiber27SourcesCheck

theorem mtFiber27CertificateAudit_ok :
    mtFiber27CertificateAudit = true := by
  simp [mtFiber27CertificateAudit,
    mtFiber27SourcesCheck_ok]

def mtFiber28Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.b]

def mtFiber28Expected : List Nat :=
  []

def mtFiber28Rows : List DirectChainParentRow :=
  []

def mtFiber28RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber28Rows i default

def mtFiber28SourcesCheck : Bool :=
  (mtFiber28Rows.map fun row => row.source) == mtFiber28Expected

theorem mtFiber28SourcesCheck_ok :
    mtFiber28SourcesCheck = true := by
  decide

def mtFiber28RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber28Key mtFiber28Expected (mtFiber28RowAt i)

def mtFiber28ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber28Rows mtMaxParentDepth (listGetD mtFiber28Expected i 0) == 0

def mtFiber28CertificateAudit : Bool :=
  mtFiber28SourcesCheck

theorem mtFiber28CertificateAudit_ok :
    mtFiber28CertificateAudit = true := by
  simp [mtFiber28CertificateAudit,
    mtFiber28SourcesCheck_ok]

def mtFiber29Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.p]

def mtFiber29Expected : List Nat :=
  []

def mtFiber29Rows : List DirectChainParentRow :=
  []

def mtFiber29RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber29Rows i default

def mtFiber29SourcesCheck : Bool :=
  (mtFiber29Rows.map fun row => row.source) == mtFiber29Expected

theorem mtFiber29SourcesCheck_ok :
    mtFiber29SourcesCheck = true := by
  decide

def mtFiber29RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber29Key mtFiber29Expected (mtFiber29RowAt i)

def mtFiber29ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber29Rows mtMaxParentDepth (listGetD mtFiber29Expected i 0) == 0

def mtFiber29CertificateAudit : Bool :=
  mtFiber29SourcesCheck

theorem mtFiber29CertificateAudit_ok :
    mtFiber29CertificateAudit = true := by
  simp [mtFiber29CertificateAudit,
    mtFiber29SourcesCheck_ok]

def mtFiber30Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.r]

def mtFiber30Expected : List Nat :=
  [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]

def mtFiber30Rows : List DirectChainParentRow :=
  [ directRow 432 432 72 156 72 156 default
  , directRow 433 432 72 157 72 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 434 433 72 158 72 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 435 432 72 159 72 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 436 432 72 172 72 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 437 433 72 173 72 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 438 436 72 174 72 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 439 435 72 175 72 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 440 432 73 148 72 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 441 433 73 149 72 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 442 434 73 150 72 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 443 435 73 151 72 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 444 436 73 164 72 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 445 437 73 165 72 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 446 438 73 166 72 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 447 439 73 167 72 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 448 432 74 140 72 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 449 433 74 141 72 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 450 434 74 142 72 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 451 435 74 143 72 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 452 436 74 188 72 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 453 437 74 189 72 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 454 438 74 190 72 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 455 439 74 191 72 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 456 440 75 132 73 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 457 441 75 133 73 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 458 442 75 134 73 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 459 443 75 135 73 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 460 444 75 180 73 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 461 445 75 181 73 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 462 446 75 182 73 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 463 447 75 183 73 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 736 740 124 24 124 40 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 737 741 124 25 124 41 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 738 452 124 26 74 188 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 739 453 124 27 74 189 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 740 448 124 40 74 140 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 741 449 124 41 74 141 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 742 450 124 42 74 142 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 743 451 124 43 74 143 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 744 748 125 16 125 32 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 745 749 125 17 125 33 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 746 762 125 18 127 2 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 747 763 125 19 127 3 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 748 764 125 32 127 48 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 749 765 125 33 127 49 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 750 766 125 34 127 50 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 751 767 125 35 127 51 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 752 756 126 8 126 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 753 757 126 9 126 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 754 444 126 10 73 164 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 755 445 126 11 73 165 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 756 440 126 56 73 148 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 757 441 126 57 73 149 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 758 442 126 58 73 150 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 759 443 126 59 73 151 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 760 764 127 0 127 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 761 765 127 1 127 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 762 436 127 2 72 172 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 763 437 127 3 72 173 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 764 432 127 48 72 156 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 765 433 127 49 72 157 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 766 434 127 50 72 158 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 767 435 127 51 72 159 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mtFiber30RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber30Rows i default

def mtFiber30SourcesCheck : Bool :=
  (mtFiber30Rows.map fun row => row.source) == mtFiber30Expected

theorem mtFiber30SourcesCheck_ok :
    mtFiber30SourcesCheck = true := by
  decide

def mtFiber30RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt i)

theorem mtFiber30Row_0_ok : mtFiber30RowCheck 0 = true := by decide
theorem mtFiber30Row_1_ok : mtFiber30RowCheck 1 = true := by decide
theorem mtFiber30Row_2_ok : mtFiber30RowCheck 2 = true := by decide
theorem mtFiber30Row_3_ok : mtFiber30RowCheck 3 = true := by decide
theorem mtFiber30Row_4_ok : mtFiber30RowCheck 4 = true := by decide
theorem mtFiber30Row_5_ok : mtFiber30RowCheck 5 = true := by decide
theorem mtFiber30Row_6_ok : mtFiber30RowCheck 6 = true := by decide
theorem mtFiber30Row_7_ok : mtFiber30RowCheck 7 = true := by decide
theorem mtFiber30Row_8_ok : mtFiber30RowCheck 8 = true := by decide
theorem mtFiber30Row_9_ok : mtFiber30RowCheck 9 = true := by decide
theorem mtFiber30Row_10_ok : mtFiber30RowCheck 10 = true := by decide
theorem mtFiber30Row_11_ok : mtFiber30RowCheck 11 = true := by decide
theorem mtFiber30Row_12_ok : mtFiber30RowCheck 12 = true := by decide
theorem mtFiber30Row_13_ok : mtFiber30RowCheck 13 = true := by decide
theorem mtFiber30Row_14_ok : mtFiber30RowCheck 14 = true := by decide
theorem mtFiber30Row_15_ok : mtFiber30RowCheck 15 = true := by decide
theorem mtFiber30Row_16_ok : mtFiber30RowCheck 16 = true := by decide
theorem mtFiber30Row_17_ok : mtFiber30RowCheck 17 = true := by decide
theorem mtFiber30Row_18_ok : mtFiber30RowCheck 18 = true := by decide
theorem mtFiber30Row_19_ok : mtFiber30RowCheck 19 = true := by decide
theorem mtFiber30Row_20_ok : mtFiber30RowCheck 20 = true := by decide
theorem mtFiber30Row_21_ok : mtFiber30RowCheck 21 = true := by decide
theorem mtFiber30Row_22_ok : mtFiber30RowCheck 22 = true := by decide
theorem mtFiber30Row_23_ok : mtFiber30RowCheck 23 = true := by decide
theorem mtFiber30Row_24_ok : mtFiber30RowCheck 24 = true := by decide
theorem mtFiber30Row_25_ok : mtFiber30RowCheck 25 = true := by decide
theorem mtFiber30Row_26_ok : mtFiber30RowCheck 26 = true := by decide
theorem mtFiber30Row_27_ok : mtFiber30RowCheck 27 = true := by decide
theorem mtFiber30Row_28_ok : mtFiber30RowCheck 28 = true := by decide
theorem mtFiber30Row_29_ok : mtFiber30RowCheck 29 = true := by decide
theorem mtFiber30Row_30_ok : mtFiber30RowCheck 30 = true := by decide
theorem mtFiber30Row_31_ok : mtFiber30RowCheck 31 = true := by decide
theorem mtFiber30Row_32_ok : mtFiber30RowCheck 32 = true := by decide
theorem mtFiber30Row_33_ok : mtFiber30RowCheck 33 = true := by decide
theorem mtFiber30Row_34_ok : mtFiber30RowCheck 34 = true := by decide
theorem mtFiber30Row_35_ok : mtFiber30RowCheck 35 = true := by decide
theorem mtFiber30Row_36_ok : mtFiber30RowCheck 36 = true := by decide
theorem mtFiber30Row_37_ok : mtFiber30RowCheck 37 = true := by decide
theorem mtFiber30Row_38_ok : mtFiber30RowCheck 38 = true := by decide
theorem mtFiber30Row_39_ok : mtFiber30RowCheck 39 = true := by decide
theorem mtFiber30Row_40_ok : mtFiber30RowCheck 40 = true := by decide
theorem mtFiber30Row_41_ok : mtFiber30RowCheck 41 = true := by decide
theorem mtFiber30Row_42_ok : mtFiber30RowCheck 42 = true := by decide
theorem mtFiber30Row_43_ok : mtFiber30RowCheck 43 = true := by decide
theorem mtFiber30Row_44_ok : mtFiber30RowCheck 44 = true := by decide
theorem mtFiber30Row_45_ok : mtFiber30RowCheck 45 = true := by decide
theorem mtFiber30Row_46_ok : mtFiber30RowCheck 46 = true := by decide
theorem mtFiber30Row_47_ok : mtFiber30RowCheck 47 = true := by decide
theorem mtFiber30Row_48_ok : mtFiber30RowCheck 48 = true := by decide
theorem mtFiber30Row_49_ok : mtFiber30RowCheck 49 = true := by decide
theorem mtFiber30Row_50_ok : mtFiber30RowCheck 50 = true := by decide
theorem mtFiber30Row_51_ok : mtFiber30RowCheck 51 = true := by decide
theorem mtFiber30Row_52_ok : mtFiber30RowCheck 52 = true := by decide
theorem mtFiber30Row_53_ok : mtFiber30RowCheck 53 = true := by decide
theorem mtFiber30Row_54_ok : mtFiber30RowCheck 54 = true := by decide
theorem mtFiber30Row_55_ok : mtFiber30RowCheck 55 = true := by decide
theorem mtFiber30Row_56_ok : mtFiber30RowCheck 56 = true := by decide
theorem mtFiber30Row_57_ok : mtFiber30RowCheck 57 = true := by decide
theorem mtFiber30Row_58_ok : mtFiber30RowCheck 58 = true := by decide
theorem mtFiber30Row_59_ok : mtFiber30RowCheck 59 = true := by decide
theorem mtFiber30Row_60_ok : mtFiber30RowCheck 60 = true := by decide
theorem mtFiber30Row_61_ok : mtFiber30RowCheck 61 = true := by decide
theorem mtFiber30Row_62_ok : mtFiber30RowCheck 62 = true := by decide
theorem mtFiber30Row_63_ok : mtFiber30RowCheck 63 = true := by decide

def mtFiber30ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber30Rows mtMaxParentDepth (listGetD mtFiber30Expected i 0) == 432

theorem mtFiber30Parent_0_ok : mtFiber30ParentCheck 0 = true := by decide
theorem mtFiber30Parent_1_ok : mtFiber30ParentCheck 1 = true := by decide
theorem mtFiber30Parent_2_ok : mtFiber30ParentCheck 2 = true := by decide
theorem mtFiber30Parent_3_ok : mtFiber30ParentCheck 3 = true := by decide
theorem mtFiber30Parent_4_ok : mtFiber30ParentCheck 4 = true := by decide
theorem mtFiber30Parent_5_ok : mtFiber30ParentCheck 5 = true := by decide
theorem mtFiber30Parent_6_ok : mtFiber30ParentCheck 6 = true := by decide
theorem mtFiber30Parent_7_ok : mtFiber30ParentCheck 7 = true := by decide
theorem mtFiber30Parent_8_ok : mtFiber30ParentCheck 8 = true := by decide
theorem mtFiber30Parent_9_ok : mtFiber30ParentCheck 9 = true := by decide
theorem mtFiber30Parent_10_ok : mtFiber30ParentCheck 10 = true := by decide
theorem mtFiber30Parent_11_ok : mtFiber30ParentCheck 11 = true := by decide
theorem mtFiber30Parent_12_ok : mtFiber30ParentCheck 12 = true := by decide
theorem mtFiber30Parent_13_ok : mtFiber30ParentCheck 13 = true := by decide
theorem mtFiber30Parent_14_ok : mtFiber30ParentCheck 14 = true := by decide
theorem mtFiber30Parent_15_ok : mtFiber30ParentCheck 15 = true := by decide
theorem mtFiber30Parent_16_ok : mtFiber30ParentCheck 16 = true := by decide
theorem mtFiber30Parent_17_ok : mtFiber30ParentCheck 17 = true := by decide
theorem mtFiber30Parent_18_ok : mtFiber30ParentCheck 18 = true := by decide
theorem mtFiber30Parent_19_ok : mtFiber30ParentCheck 19 = true := by decide
theorem mtFiber30Parent_20_ok : mtFiber30ParentCheck 20 = true := by decide
theorem mtFiber30Parent_21_ok : mtFiber30ParentCheck 21 = true := by decide
theorem mtFiber30Parent_22_ok : mtFiber30ParentCheck 22 = true := by decide
theorem mtFiber30Parent_23_ok : mtFiber30ParentCheck 23 = true := by decide
theorem mtFiber30Parent_24_ok : mtFiber30ParentCheck 24 = true := by decide
theorem mtFiber30Parent_25_ok : mtFiber30ParentCheck 25 = true := by decide
theorem mtFiber30Parent_26_ok : mtFiber30ParentCheck 26 = true := by decide
theorem mtFiber30Parent_27_ok : mtFiber30ParentCheck 27 = true := by decide
theorem mtFiber30Parent_28_ok : mtFiber30ParentCheck 28 = true := by decide
theorem mtFiber30Parent_29_ok : mtFiber30ParentCheck 29 = true := by decide
theorem mtFiber30Parent_30_ok : mtFiber30ParentCheck 30 = true := by decide
theorem mtFiber30Parent_31_ok : mtFiber30ParentCheck 31 = true := by decide
theorem mtFiber30Parent_32_ok : mtFiber30ParentCheck 32 = true := by decide
theorem mtFiber30Parent_33_ok : mtFiber30ParentCheck 33 = true := by decide
theorem mtFiber30Parent_34_ok : mtFiber30ParentCheck 34 = true := by decide
theorem mtFiber30Parent_35_ok : mtFiber30ParentCheck 35 = true := by decide
theorem mtFiber30Parent_36_ok : mtFiber30ParentCheck 36 = true := by decide
theorem mtFiber30Parent_37_ok : mtFiber30ParentCheck 37 = true := by decide
theorem mtFiber30Parent_38_ok : mtFiber30ParentCheck 38 = true := by decide
theorem mtFiber30Parent_39_ok : mtFiber30ParentCheck 39 = true := by decide
theorem mtFiber30Parent_40_ok : mtFiber30ParentCheck 40 = true := by decide
theorem mtFiber30Parent_41_ok : mtFiber30ParentCheck 41 = true := by decide
theorem mtFiber30Parent_42_ok : mtFiber30ParentCheck 42 = true := by decide
theorem mtFiber30Parent_43_ok : mtFiber30ParentCheck 43 = true := by decide
theorem mtFiber30Parent_44_ok : mtFiber30ParentCheck 44 = true := by decide
theorem mtFiber30Parent_45_ok : mtFiber30ParentCheck 45 = true := by decide
theorem mtFiber30Parent_46_ok : mtFiber30ParentCheck 46 = true := by decide
theorem mtFiber30Parent_47_ok : mtFiber30ParentCheck 47 = true := by decide
theorem mtFiber30Parent_48_ok : mtFiber30ParentCheck 48 = true := by decide
theorem mtFiber30Parent_49_ok : mtFiber30ParentCheck 49 = true := by decide
theorem mtFiber30Parent_50_ok : mtFiber30ParentCheck 50 = true := by decide
theorem mtFiber30Parent_51_ok : mtFiber30ParentCheck 51 = true := by decide
theorem mtFiber30Parent_52_ok : mtFiber30ParentCheck 52 = true := by decide
theorem mtFiber30Parent_53_ok : mtFiber30ParentCheck 53 = true := by decide
theorem mtFiber30Parent_54_ok : mtFiber30ParentCheck 54 = true := by decide
theorem mtFiber30Parent_55_ok : mtFiber30ParentCheck 55 = true := by decide
theorem mtFiber30Parent_56_ok : mtFiber30ParentCheck 56 = true := by decide
theorem mtFiber30Parent_57_ok : mtFiber30ParentCheck 57 = true := by decide
theorem mtFiber30Parent_58_ok : mtFiber30ParentCheck 58 = true := by decide
theorem mtFiber30Parent_59_ok : mtFiber30ParentCheck 59 = true := by decide
theorem mtFiber30Parent_60_ok : mtFiber30ParentCheck 60 = true := by decide
theorem mtFiber30Parent_61_ok : mtFiber30ParentCheck 61 = true := by decide
theorem mtFiber30Parent_62_ok : mtFiber30ParentCheck 62 = true := by decide
theorem mtFiber30Parent_63_ok : mtFiber30ParentCheck 63 = true := by decide

def mtFiber30CertificateAudit : Bool :=
  mtFiber30SourcesCheck &&
    mtFiber30RowCheck 0 &&
    mtFiber30RowCheck 1 &&
    mtFiber30RowCheck 2 &&
    mtFiber30RowCheck 3 &&
    mtFiber30RowCheck 4 &&
    mtFiber30RowCheck 5 &&
    mtFiber30RowCheck 6 &&
    mtFiber30RowCheck 7 &&
    mtFiber30RowCheck 8 &&
    mtFiber30RowCheck 9 &&
    mtFiber30RowCheck 10 &&
    mtFiber30RowCheck 11 &&
    mtFiber30RowCheck 12 &&
    mtFiber30RowCheck 13 &&
    mtFiber30RowCheck 14 &&
    mtFiber30RowCheck 15 &&
    mtFiber30RowCheck 16 &&
    mtFiber30RowCheck 17 &&
    mtFiber30RowCheck 18 &&
    mtFiber30RowCheck 19 &&
    mtFiber30RowCheck 20 &&
    mtFiber30RowCheck 21 &&
    mtFiber30RowCheck 22 &&
    mtFiber30RowCheck 23 &&
    mtFiber30RowCheck 24 &&
    mtFiber30RowCheck 25 &&
    mtFiber30RowCheck 26 &&
    mtFiber30RowCheck 27 &&
    mtFiber30RowCheck 28 &&
    mtFiber30RowCheck 29 &&
    mtFiber30RowCheck 30 &&
    mtFiber30RowCheck 31 &&
    mtFiber30RowCheck 32 &&
    mtFiber30RowCheck 33 &&
    mtFiber30RowCheck 34 &&
    mtFiber30RowCheck 35 &&
    mtFiber30RowCheck 36 &&
    mtFiber30RowCheck 37 &&
    mtFiber30RowCheck 38 &&
    mtFiber30RowCheck 39 &&
    mtFiber30RowCheck 40 &&
    mtFiber30RowCheck 41 &&
    mtFiber30RowCheck 42 &&
    mtFiber30RowCheck 43 &&
    mtFiber30RowCheck 44 &&
    mtFiber30RowCheck 45 &&
    mtFiber30RowCheck 46 &&
    mtFiber30RowCheck 47 &&
    mtFiber30RowCheck 48 &&
    mtFiber30RowCheck 49 &&
    mtFiber30RowCheck 50 &&
    mtFiber30RowCheck 51 &&
    mtFiber30RowCheck 52 &&
    mtFiber30RowCheck 53 &&
    mtFiber30RowCheck 54 &&
    mtFiber30RowCheck 55 &&
    mtFiber30RowCheck 56 &&
    mtFiber30RowCheck 57 &&
    mtFiber30RowCheck 58 &&
    mtFiber30RowCheck 59 &&
    mtFiber30RowCheck 60 &&
    mtFiber30RowCheck 61 &&
    mtFiber30RowCheck 62 &&
    mtFiber30RowCheck 63 &&
    mtFiber30ParentCheck 0 &&
    mtFiber30ParentCheck 1 &&
    mtFiber30ParentCheck 2 &&
    mtFiber30ParentCheck 3 &&
    mtFiber30ParentCheck 4 &&
    mtFiber30ParentCheck 5 &&
    mtFiber30ParentCheck 6 &&
    mtFiber30ParentCheck 7 &&
    mtFiber30ParentCheck 8 &&
    mtFiber30ParentCheck 9 &&
    mtFiber30ParentCheck 10 &&
    mtFiber30ParentCheck 11 &&
    mtFiber30ParentCheck 12 &&
    mtFiber30ParentCheck 13 &&
    mtFiber30ParentCheck 14 &&
    mtFiber30ParentCheck 15 &&
    mtFiber30ParentCheck 16 &&
    mtFiber30ParentCheck 17 &&
    mtFiber30ParentCheck 18 &&
    mtFiber30ParentCheck 19 &&
    mtFiber30ParentCheck 20 &&
    mtFiber30ParentCheck 21 &&
    mtFiber30ParentCheck 22 &&
    mtFiber30ParentCheck 23 &&
    mtFiber30ParentCheck 24 &&
    mtFiber30ParentCheck 25 &&
    mtFiber30ParentCheck 26 &&
    mtFiber30ParentCheck 27 &&
    mtFiber30ParentCheck 28 &&
    mtFiber30ParentCheck 29 &&
    mtFiber30ParentCheck 30 &&
    mtFiber30ParentCheck 31 &&
    mtFiber30ParentCheck 32 &&
    mtFiber30ParentCheck 33 &&
    mtFiber30ParentCheck 34 &&
    mtFiber30ParentCheck 35 &&
    mtFiber30ParentCheck 36 &&
    mtFiber30ParentCheck 37 &&
    mtFiber30ParentCheck 38 &&
    mtFiber30ParentCheck 39 &&
    mtFiber30ParentCheck 40 &&
    mtFiber30ParentCheck 41 &&
    mtFiber30ParentCheck 42 &&
    mtFiber30ParentCheck 43 &&
    mtFiber30ParentCheck 44 &&
    mtFiber30ParentCheck 45 &&
    mtFiber30ParentCheck 46 &&
    mtFiber30ParentCheck 47 &&
    mtFiber30ParentCheck 48 &&
    mtFiber30ParentCheck 49 &&
    mtFiber30ParentCheck 50 &&
    mtFiber30ParentCheck 51 &&
    mtFiber30ParentCheck 52 &&
    mtFiber30ParentCheck 53 &&
    mtFiber30ParentCheck 54 &&
    mtFiber30ParentCheck 55 &&
    mtFiber30ParentCheck 56 &&
    mtFiber30ParentCheck 57 &&
    mtFiber30ParentCheck 58 &&
    mtFiber30ParentCheck 59 &&
    mtFiber30ParentCheck 60 &&
    mtFiber30ParentCheck 61 &&
    mtFiber30ParentCheck 62 &&
    mtFiber30ParentCheck 63

theorem mtFiber30CertificateAudit_ok :
    mtFiber30CertificateAudit = true := by
  simp [mtFiber30CertificateAudit,
    mtFiber30SourcesCheck_ok,
    mtFiber30Row_0_ok,
    mtFiber30Row_1_ok,
    mtFiber30Row_2_ok,
    mtFiber30Row_3_ok,
    mtFiber30Row_4_ok,
    mtFiber30Row_5_ok,
    mtFiber30Row_6_ok,
    mtFiber30Row_7_ok,
    mtFiber30Row_8_ok,
    mtFiber30Row_9_ok,
    mtFiber30Row_10_ok,
    mtFiber30Row_11_ok,
    mtFiber30Row_12_ok,
    mtFiber30Row_13_ok,
    mtFiber30Row_14_ok,
    mtFiber30Row_15_ok,
    mtFiber30Row_16_ok,
    mtFiber30Row_17_ok,
    mtFiber30Row_18_ok,
    mtFiber30Row_19_ok,
    mtFiber30Row_20_ok,
    mtFiber30Row_21_ok,
    mtFiber30Row_22_ok,
    mtFiber30Row_23_ok,
    mtFiber30Row_24_ok,
    mtFiber30Row_25_ok,
    mtFiber30Row_26_ok,
    mtFiber30Row_27_ok,
    mtFiber30Row_28_ok,
    mtFiber30Row_29_ok,
    mtFiber30Row_30_ok,
    mtFiber30Row_31_ok,
    mtFiber30Row_32_ok,
    mtFiber30Row_33_ok,
    mtFiber30Row_34_ok,
    mtFiber30Row_35_ok,
    mtFiber30Row_36_ok,
    mtFiber30Row_37_ok,
    mtFiber30Row_38_ok,
    mtFiber30Row_39_ok,
    mtFiber30Row_40_ok,
    mtFiber30Row_41_ok,
    mtFiber30Row_42_ok,
    mtFiber30Row_43_ok,
    mtFiber30Row_44_ok,
    mtFiber30Row_45_ok,
    mtFiber30Row_46_ok,
    mtFiber30Row_47_ok,
    mtFiber30Row_48_ok,
    mtFiber30Row_49_ok,
    mtFiber30Row_50_ok,
    mtFiber30Row_51_ok,
    mtFiber30Row_52_ok,
    mtFiber30Row_53_ok,
    mtFiber30Row_54_ok,
    mtFiber30Row_55_ok,
    mtFiber30Row_56_ok,
    mtFiber30Row_57_ok,
    mtFiber30Row_58_ok,
    mtFiber30Row_59_ok,
    mtFiber30Row_60_ok,
    mtFiber30Row_61_ok,
    mtFiber30Row_62_ok,
    mtFiber30Row_63_ok,
    mtFiber30Parent_0_ok,
    mtFiber30Parent_1_ok,
    mtFiber30Parent_2_ok,
    mtFiber30Parent_3_ok,
    mtFiber30Parent_4_ok,
    mtFiber30Parent_5_ok,
    mtFiber30Parent_6_ok,
    mtFiber30Parent_7_ok,
    mtFiber30Parent_8_ok,
    mtFiber30Parent_9_ok,
    mtFiber30Parent_10_ok,
    mtFiber30Parent_11_ok,
    mtFiber30Parent_12_ok,
    mtFiber30Parent_13_ok,
    mtFiber30Parent_14_ok,
    mtFiber30Parent_15_ok,
    mtFiber30Parent_16_ok,
    mtFiber30Parent_17_ok,
    mtFiber30Parent_18_ok,
    mtFiber30Parent_19_ok,
    mtFiber30Parent_20_ok,
    mtFiber30Parent_21_ok,
    mtFiber30Parent_22_ok,
    mtFiber30Parent_23_ok,
    mtFiber30Parent_24_ok,
    mtFiber30Parent_25_ok,
    mtFiber30Parent_26_ok,
    mtFiber30Parent_27_ok,
    mtFiber30Parent_28_ok,
    mtFiber30Parent_29_ok,
    mtFiber30Parent_30_ok,
    mtFiber30Parent_31_ok,
    mtFiber30Parent_32_ok,
    mtFiber30Parent_33_ok,
    mtFiber30Parent_34_ok,
    mtFiber30Parent_35_ok,
    mtFiber30Parent_36_ok,
    mtFiber30Parent_37_ok,
    mtFiber30Parent_38_ok,
    mtFiber30Parent_39_ok,
    mtFiber30Parent_40_ok,
    mtFiber30Parent_41_ok,
    mtFiber30Parent_42_ok,
    mtFiber30Parent_43_ok,
    mtFiber30Parent_44_ok,
    mtFiber30Parent_45_ok,
    mtFiber30Parent_46_ok,
    mtFiber30Parent_47_ok,
    mtFiber30Parent_48_ok,
    mtFiber30Parent_49_ok,
    mtFiber30Parent_50_ok,
    mtFiber30Parent_51_ok,
    mtFiber30Parent_52_ok,
    mtFiber30Parent_53_ok,
    mtFiber30Parent_54_ok,
    mtFiber30Parent_55_ok,
    mtFiber30Parent_56_ok,
    mtFiber30Parent_57_ok,
    mtFiber30Parent_58_ok,
    mtFiber30Parent_59_ok,
    mtFiber30Parent_60_ok,
    mtFiber30Parent_61_ok,
    mtFiber30Parent_62_ok,
    mtFiber30Parent_63_ok]

def mtFiber31Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.b]

def mtFiber31Expected : List Nat :=
  [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]

def mtFiber31Rows : List DirectChainParentRow :=
  [ directRow 368 368 60 104 60 104 default
  , directRow 369 368 60 105 60 104 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 370 368 60 106 60 104 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 371 369 60 107 60 105 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 372 368 61 96 60 104 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 373 369 61 97 60 105 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 374 370 61 98 60 106 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 375 371 61 99 60 107 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 376 372 62 120 61 96 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 377 373 62 121 61 97 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 378 374 62 122 61 98 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 379 375 62 123 61 99 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 380 368 63 112 60 104 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 381 369 63 113 60 105 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 382 370 63 114 60 106 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 383 371 63 115 60 107 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber31RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber31Rows i default

def mtFiber31SourcesCheck : Bool :=
  (mtFiber31Rows.map fun row => row.source) == mtFiber31Expected

theorem mtFiber31SourcesCheck_ok :
    mtFiber31SourcesCheck = true := by
  decide

def mtFiber31RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt i)

theorem mtFiber31Row_0_ok : mtFiber31RowCheck 0 = true := by decide
theorem mtFiber31Row_1_ok : mtFiber31RowCheck 1 = true := by decide
theorem mtFiber31Row_2_ok : mtFiber31RowCheck 2 = true := by decide
theorem mtFiber31Row_3_ok : mtFiber31RowCheck 3 = true := by decide
theorem mtFiber31Row_4_ok : mtFiber31RowCheck 4 = true := by decide
theorem mtFiber31Row_5_ok : mtFiber31RowCheck 5 = true := by decide
theorem mtFiber31Row_6_ok : mtFiber31RowCheck 6 = true := by decide
theorem mtFiber31Row_7_ok : mtFiber31RowCheck 7 = true := by decide
theorem mtFiber31Row_8_ok : mtFiber31RowCheck 8 = true := by decide
theorem mtFiber31Row_9_ok : mtFiber31RowCheck 9 = true := by decide
theorem mtFiber31Row_10_ok : mtFiber31RowCheck 10 = true := by decide
theorem mtFiber31Row_11_ok : mtFiber31RowCheck 11 = true := by decide
theorem mtFiber31Row_12_ok : mtFiber31RowCheck 12 = true := by decide
theorem mtFiber31Row_13_ok : mtFiber31RowCheck 13 = true := by decide
theorem mtFiber31Row_14_ok : mtFiber31RowCheck 14 = true := by decide
theorem mtFiber31Row_15_ok : mtFiber31RowCheck 15 = true := by decide

def mtFiber31ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber31Rows mtMaxParentDepth (listGetD mtFiber31Expected i 0) == 368

theorem mtFiber31Parent_0_ok : mtFiber31ParentCheck 0 = true := by decide
theorem mtFiber31Parent_1_ok : mtFiber31ParentCheck 1 = true := by decide
theorem mtFiber31Parent_2_ok : mtFiber31ParentCheck 2 = true := by decide
theorem mtFiber31Parent_3_ok : mtFiber31ParentCheck 3 = true := by decide
theorem mtFiber31Parent_4_ok : mtFiber31ParentCheck 4 = true := by decide
theorem mtFiber31Parent_5_ok : mtFiber31ParentCheck 5 = true := by decide
theorem mtFiber31Parent_6_ok : mtFiber31ParentCheck 6 = true := by decide
theorem mtFiber31Parent_7_ok : mtFiber31ParentCheck 7 = true := by decide
theorem mtFiber31Parent_8_ok : mtFiber31ParentCheck 8 = true := by decide
theorem mtFiber31Parent_9_ok : mtFiber31ParentCheck 9 = true := by decide
theorem mtFiber31Parent_10_ok : mtFiber31ParentCheck 10 = true := by decide
theorem mtFiber31Parent_11_ok : mtFiber31ParentCheck 11 = true := by decide
theorem mtFiber31Parent_12_ok : mtFiber31ParentCheck 12 = true := by decide
theorem mtFiber31Parent_13_ok : mtFiber31ParentCheck 13 = true := by decide
theorem mtFiber31Parent_14_ok : mtFiber31ParentCheck 14 = true := by decide
theorem mtFiber31Parent_15_ok : mtFiber31ParentCheck 15 = true := by decide

def mtFiber31CertificateAudit : Bool :=
  mtFiber31SourcesCheck &&
    mtFiber31RowCheck 0 &&
    mtFiber31RowCheck 1 &&
    mtFiber31RowCheck 2 &&
    mtFiber31RowCheck 3 &&
    mtFiber31RowCheck 4 &&
    mtFiber31RowCheck 5 &&
    mtFiber31RowCheck 6 &&
    mtFiber31RowCheck 7 &&
    mtFiber31RowCheck 8 &&
    mtFiber31RowCheck 9 &&
    mtFiber31RowCheck 10 &&
    mtFiber31RowCheck 11 &&
    mtFiber31RowCheck 12 &&
    mtFiber31RowCheck 13 &&
    mtFiber31RowCheck 14 &&
    mtFiber31RowCheck 15 &&
    mtFiber31ParentCheck 0 &&
    mtFiber31ParentCheck 1 &&
    mtFiber31ParentCheck 2 &&
    mtFiber31ParentCheck 3 &&
    mtFiber31ParentCheck 4 &&
    mtFiber31ParentCheck 5 &&
    mtFiber31ParentCheck 6 &&
    mtFiber31ParentCheck 7 &&
    mtFiber31ParentCheck 8 &&
    mtFiber31ParentCheck 9 &&
    mtFiber31ParentCheck 10 &&
    mtFiber31ParentCheck 11 &&
    mtFiber31ParentCheck 12 &&
    mtFiber31ParentCheck 13 &&
    mtFiber31ParentCheck 14 &&
    mtFiber31ParentCheck 15

theorem mtFiber31CertificateAudit_ok :
    mtFiber31CertificateAudit = true := by
  simp [mtFiber31CertificateAudit,
    mtFiber31SourcesCheck_ok,
    mtFiber31Row_0_ok,
    mtFiber31Row_1_ok,
    mtFiber31Row_2_ok,
    mtFiber31Row_3_ok,
    mtFiber31Row_4_ok,
    mtFiber31Row_5_ok,
    mtFiber31Row_6_ok,
    mtFiber31Row_7_ok,
    mtFiber31Row_8_ok,
    mtFiber31Row_9_ok,
    mtFiber31Row_10_ok,
    mtFiber31Row_11_ok,
    mtFiber31Row_12_ok,
    mtFiber31Row_13_ok,
    mtFiber31Row_14_ok,
    mtFiber31Row_15_ok,
    mtFiber31Parent_0_ok,
    mtFiber31Parent_1_ok,
    mtFiber31Parent_2_ok,
    mtFiber31Parent_3_ok,
    mtFiber31Parent_4_ok,
    mtFiber31Parent_5_ok,
    mtFiber31Parent_6_ok,
    mtFiber31Parent_7_ok,
    mtFiber31Parent_8_ok,
    mtFiber31Parent_9_ok,
    mtFiber31Parent_10_ok,
    mtFiber31Parent_11_ok,
    mtFiber31Parent_12_ok,
    mtFiber31Parent_13_ok,
    mtFiber31Parent_14_ok,
    mtFiber31Parent_15_ok]

def mtFiber32Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.p]

def mtFiber32Expected : List Nat :=
  []

def mtFiber32Rows : List DirectChainParentRow :=
  []

def mtFiber32RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber32Rows i default

def mtFiber32SourcesCheck : Bool :=
  (mtFiber32Rows.map fun row => row.source) == mtFiber32Expected

theorem mtFiber32SourcesCheck_ok :
    mtFiber32SourcesCheck = true := by
  decide

def mtFiber32RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber32Key mtFiber32Expected (mtFiber32RowAt i)

def mtFiber32ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber32Rows mtMaxParentDepth (listGetD mtFiber32Expected i 0) == 0

def mtFiber32CertificateAudit : Bool :=
  mtFiber32SourcesCheck

theorem mtFiber32CertificateAudit_ok :
    mtFiber32CertificateAudit = true := by
  simp [mtFiber32CertificateAudit,
    mtFiber32SourcesCheck_ok]

def mtFiber33Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.r]

def mtFiber33Expected : List Nat :=
  [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]

def mtFiber33Rows : List DirectChainParentRow :=
  [ directRow 816 816 136 92 136 92 default
  , directRow 817 816 136 93 136 92 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 818 816 136 94 136 92 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 819 817 136 95 136 93 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 820 816 137 84 136 92 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 821 817 137 85 136 93 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 822 818 137 86 136 94 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 823 819 137 87 136 95 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 824 820 138 76 137 84 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 825 821 138 77 137 85 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 826 822 138 78 137 86 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 827 823 138 79 137 87 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 828 816 139 68 136 92 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 829 817 139 69 136 93 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 830 818 139 70 136 94 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 831 819 139 71 136 95 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber33RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber33Rows i default

def mtFiber33SourcesCheck : Bool :=
  (mtFiber33Rows.map fun row => row.source) == mtFiber33Expected

theorem mtFiber33SourcesCheck_ok :
    mtFiber33SourcesCheck = true := by
  decide

def mtFiber33RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt i)

theorem mtFiber33Row_0_ok : mtFiber33RowCheck 0 = true := by decide
theorem mtFiber33Row_1_ok : mtFiber33RowCheck 1 = true := by decide
theorem mtFiber33Row_2_ok : mtFiber33RowCheck 2 = true := by decide
theorem mtFiber33Row_3_ok : mtFiber33RowCheck 3 = true := by decide
theorem mtFiber33Row_4_ok : mtFiber33RowCheck 4 = true := by decide
theorem mtFiber33Row_5_ok : mtFiber33RowCheck 5 = true := by decide
theorem mtFiber33Row_6_ok : mtFiber33RowCheck 6 = true := by decide
theorem mtFiber33Row_7_ok : mtFiber33RowCheck 7 = true := by decide
theorem mtFiber33Row_8_ok : mtFiber33RowCheck 8 = true := by decide
theorem mtFiber33Row_9_ok : mtFiber33RowCheck 9 = true := by decide
theorem mtFiber33Row_10_ok : mtFiber33RowCheck 10 = true := by decide
theorem mtFiber33Row_11_ok : mtFiber33RowCheck 11 = true := by decide
theorem mtFiber33Row_12_ok : mtFiber33RowCheck 12 = true := by decide
theorem mtFiber33Row_13_ok : mtFiber33RowCheck 13 = true := by decide
theorem mtFiber33Row_14_ok : mtFiber33RowCheck 14 = true := by decide
theorem mtFiber33Row_15_ok : mtFiber33RowCheck 15 = true := by decide

def mtFiber33ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber33Rows mtMaxParentDepth (listGetD mtFiber33Expected i 0) == 816

theorem mtFiber33Parent_0_ok : mtFiber33ParentCheck 0 = true := by decide
theorem mtFiber33Parent_1_ok : mtFiber33ParentCheck 1 = true := by decide
theorem mtFiber33Parent_2_ok : mtFiber33ParentCheck 2 = true := by decide
theorem mtFiber33Parent_3_ok : mtFiber33ParentCheck 3 = true := by decide
theorem mtFiber33Parent_4_ok : mtFiber33ParentCheck 4 = true := by decide
theorem mtFiber33Parent_5_ok : mtFiber33ParentCheck 5 = true := by decide
theorem mtFiber33Parent_6_ok : mtFiber33ParentCheck 6 = true := by decide
theorem mtFiber33Parent_7_ok : mtFiber33ParentCheck 7 = true := by decide
theorem mtFiber33Parent_8_ok : mtFiber33ParentCheck 8 = true := by decide
theorem mtFiber33Parent_9_ok : mtFiber33ParentCheck 9 = true := by decide
theorem mtFiber33Parent_10_ok : mtFiber33ParentCheck 10 = true := by decide
theorem mtFiber33Parent_11_ok : mtFiber33ParentCheck 11 = true := by decide
theorem mtFiber33Parent_12_ok : mtFiber33ParentCheck 12 = true := by decide
theorem mtFiber33Parent_13_ok : mtFiber33ParentCheck 13 = true := by decide
theorem mtFiber33Parent_14_ok : mtFiber33ParentCheck 14 = true := by decide
theorem mtFiber33Parent_15_ok : mtFiber33ParentCheck 15 = true := by decide

def mtFiber33CertificateAudit : Bool :=
  mtFiber33SourcesCheck &&
    mtFiber33RowCheck 0 &&
    mtFiber33RowCheck 1 &&
    mtFiber33RowCheck 2 &&
    mtFiber33RowCheck 3 &&
    mtFiber33RowCheck 4 &&
    mtFiber33RowCheck 5 &&
    mtFiber33RowCheck 6 &&
    mtFiber33RowCheck 7 &&
    mtFiber33RowCheck 8 &&
    mtFiber33RowCheck 9 &&
    mtFiber33RowCheck 10 &&
    mtFiber33RowCheck 11 &&
    mtFiber33RowCheck 12 &&
    mtFiber33RowCheck 13 &&
    mtFiber33RowCheck 14 &&
    mtFiber33RowCheck 15 &&
    mtFiber33ParentCheck 0 &&
    mtFiber33ParentCheck 1 &&
    mtFiber33ParentCheck 2 &&
    mtFiber33ParentCheck 3 &&
    mtFiber33ParentCheck 4 &&
    mtFiber33ParentCheck 5 &&
    mtFiber33ParentCheck 6 &&
    mtFiber33ParentCheck 7 &&
    mtFiber33ParentCheck 8 &&
    mtFiber33ParentCheck 9 &&
    mtFiber33ParentCheck 10 &&
    mtFiber33ParentCheck 11 &&
    mtFiber33ParentCheck 12 &&
    mtFiber33ParentCheck 13 &&
    mtFiber33ParentCheck 14 &&
    mtFiber33ParentCheck 15

theorem mtFiber33CertificateAudit_ok :
    mtFiber33CertificateAudit = true := by
  simp [mtFiber33CertificateAudit,
    mtFiber33SourcesCheck_ok,
    mtFiber33Row_0_ok,
    mtFiber33Row_1_ok,
    mtFiber33Row_2_ok,
    mtFiber33Row_3_ok,
    mtFiber33Row_4_ok,
    mtFiber33Row_5_ok,
    mtFiber33Row_6_ok,
    mtFiber33Row_7_ok,
    mtFiber33Row_8_ok,
    mtFiber33Row_9_ok,
    mtFiber33Row_10_ok,
    mtFiber33Row_11_ok,
    mtFiber33Row_12_ok,
    mtFiber33Row_13_ok,
    mtFiber33Row_14_ok,
    mtFiber33Row_15_ok,
    mtFiber33Parent_0_ok,
    mtFiber33Parent_1_ok,
    mtFiber33Parent_2_ok,
    mtFiber33Parent_3_ok,
    mtFiber33Parent_4_ok,
    mtFiber33Parent_5_ok,
    mtFiber33Parent_6_ok,
    mtFiber33Parent_7_ok,
    mtFiber33Parent_8_ok,
    mtFiber33Parent_9_ok,
    mtFiber33Parent_10_ok,
    mtFiber33Parent_11_ok,
    mtFiber33Parent_12_ok,
    mtFiber33Parent_13_ok,
    mtFiber33Parent_14_ok,
    mtFiber33Parent_15_ok]

def mtFiber34Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.b]

def mtFiber34Expected : List Nat :=
  []

def mtFiber34Rows : List DirectChainParentRow :=
  []

def mtFiber34RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber34Rows i default

def mtFiber34SourcesCheck : Bool :=
  (mtFiber34Rows.map fun row => row.source) == mtFiber34Expected

theorem mtFiber34SourcesCheck_ok :
    mtFiber34SourcesCheck = true := by
  decide

def mtFiber34RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber34Key mtFiber34Expected (mtFiber34RowAt i)

def mtFiber34ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber34Rows mtMaxParentDepth (listGetD mtFiber34Expected i 0) == 0

def mtFiber34CertificateAudit : Bool :=
  mtFiber34SourcesCheck

theorem mtFiber34CertificateAudit_ok :
    mtFiber34CertificateAudit = true := by
  simp [mtFiber34CertificateAudit,
    mtFiber34SourcesCheck_ok]

def mtFiber35Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.p]

def mtFiber35Expected : List Nat :=
  [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]

def mtFiber35Rows : List DirectChainParentRow :=
  [ directRow 272 272 44 104 44 104 default
  , directRow 273 272 44 105 44 104 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 274 272 44 106 44 104 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 275 273 44 107 44 105 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 276 272 45 96 44 104 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 277 273 45 97 44 105 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 278 274 45 98 44 106 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 279 275 45 99 44 107 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 280 276 46 120 45 96 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 281 277 46 121 45 97 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 282 278 46 122 45 98 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 283 279 46 123 45 99 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 284 272 47 112 44 104 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 285 273 47 113 44 105 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 286 274 47 114 44 106 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 287 275 47 115 44 107 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber35RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber35Rows i default

def mtFiber35SourcesCheck : Bool :=
  (mtFiber35Rows.map fun row => row.source) == mtFiber35Expected

theorem mtFiber35SourcesCheck_ok :
    mtFiber35SourcesCheck = true := by
  decide

def mtFiber35RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt i)

theorem mtFiber35Row_0_ok : mtFiber35RowCheck 0 = true := by decide
theorem mtFiber35Row_1_ok : mtFiber35RowCheck 1 = true := by decide
theorem mtFiber35Row_2_ok : mtFiber35RowCheck 2 = true := by decide
theorem mtFiber35Row_3_ok : mtFiber35RowCheck 3 = true := by decide
theorem mtFiber35Row_4_ok : mtFiber35RowCheck 4 = true := by decide
theorem mtFiber35Row_5_ok : mtFiber35RowCheck 5 = true := by decide
theorem mtFiber35Row_6_ok : mtFiber35RowCheck 6 = true := by decide
theorem mtFiber35Row_7_ok : mtFiber35RowCheck 7 = true := by decide
theorem mtFiber35Row_8_ok : mtFiber35RowCheck 8 = true := by decide
theorem mtFiber35Row_9_ok : mtFiber35RowCheck 9 = true := by decide
theorem mtFiber35Row_10_ok : mtFiber35RowCheck 10 = true := by decide
theorem mtFiber35Row_11_ok : mtFiber35RowCheck 11 = true := by decide
theorem mtFiber35Row_12_ok : mtFiber35RowCheck 12 = true := by decide
theorem mtFiber35Row_13_ok : mtFiber35RowCheck 13 = true := by decide
theorem mtFiber35Row_14_ok : mtFiber35RowCheck 14 = true := by decide
theorem mtFiber35Row_15_ok : mtFiber35RowCheck 15 = true := by decide

def mtFiber35ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber35Rows mtMaxParentDepth (listGetD mtFiber35Expected i 0) == 272

theorem mtFiber35Parent_0_ok : mtFiber35ParentCheck 0 = true := by decide
theorem mtFiber35Parent_1_ok : mtFiber35ParentCheck 1 = true := by decide
theorem mtFiber35Parent_2_ok : mtFiber35ParentCheck 2 = true := by decide
theorem mtFiber35Parent_3_ok : mtFiber35ParentCheck 3 = true := by decide
theorem mtFiber35Parent_4_ok : mtFiber35ParentCheck 4 = true := by decide
theorem mtFiber35Parent_5_ok : mtFiber35ParentCheck 5 = true := by decide
theorem mtFiber35Parent_6_ok : mtFiber35ParentCheck 6 = true := by decide
theorem mtFiber35Parent_7_ok : mtFiber35ParentCheck 7 = true := by decide
theorem mtFiber35Parent_8_ok : mtFiber35ParentCheck 8 = true := by decide
theorem mtFiber35Parent_9_ok : mtFiber35ParentCheck 9 = true := by decide
theorem mtFiber35Parent_10_ok : mtFiber35ParentCheck 10 = true := by decide
theorem mtFiber35Parent_11_ok : mtFiber35ParentCheck 11 = true := by decide
theorem mtFiber35Parent_12_ok : mtFiber35ParentCheck 12 = true := by decide
theorem mtFiber35Parent_13_ok : mtFiber35ParentCheck 13 = true := by decide
theorem mtFiber35Parent_14_ok : mtFiber35ParentCheck 14 = true := by decide
theorem mtFiber35Parent_15_ok : mtFiber35ParentCheck 15 = true := by decide

def mtFiber35CertificateAudit : Bool :=
  mtFiber35SourcesCheck &&
    mtFiber35RowCheck 0 &&
    mtFiber35RowCheck 1 &&
    mtFiber35RowCheck 2 &&
    mtFiber35RowCheck 3 &&
    mtFiber35RowCheck 4 &&
    mtFiber35RowCheck 5 &&
    mtFiber35RowCheck 6 &&
    mtFiber35RowCheck 7 &&
    mtFiber35RowCheck 8 &&
    mtFiber35RowCheck 9 &&
    mtFiber35RowCheck 10 &&
    mtFiber35RowCheck 11 &&
    mtFiber35RowCheck 12 &&
    mtFiber35RowCheck 13 &&
    mtFiber35RowCheck 14 &&
    mtFiber35RowCheck 15 &&
    mtFiber35ParentCheck 0 &&
    mtFiber35ParentCheck 1 &&
    mtFiber35ParentCheck 2 &&
    mtFiber35ParentCheck 3 &&
    mtFiber35ParentCheck 4 &&
    mtFiber35ParentCheck 5 &&
    mtFiber35ParentCheck 6 &&
    mtFiber35ParentCheck 7 &&
    mtFiber35ParentCheck 8 &&
    mtFiber35ParentCheck 9 &&
    mtFiber35ParentCheck 10 &&
    mtFiber35ParentCheck 11 &&
    mtFiber35ParentCheck 12 &&
    mtFiber35ParentCheck 13 &&
    mtFiber35ParentCheck 14 &&
    mtFiber35ParentCheck 15

theorem mtFiber35CertificateAudit_ok :
    mtFiber35CertificateAudit = true := by
  simp [mtFiber35CertificateAudit,
    mtFiber35SourcesCheck_ok,
    mtFiber35Row_0_ok,
    mtFiber35Row_1_ok,
    mtFiber35Row_2_ok,
    mtFiber35Row_3_ok,
    mtFiber35Row_4_ok,
    mtFiber35Row_5_ok,
    mtFiber35Row_6_ok,
    mtFiber35Row_7_ok,
    mtFiber35Row_8_ok,
    mtFiber35Row_9_ok,
    mtFiber35Row_10_ok,
    mtFiber35Row_11_ok,
    mtFiber35Row_12_ok,
    mtFiber35Row_13_ok,
    mtFiber35Row_14_ok,
    mtFiber35Row_15_ok,
    mtFiber35Parent_0_ok,
    mtFiber35Parent_1_ok,
    mtFiber35Parent_2_ok,
    mtFiber35Parent_3_ok,
    mtFiber35Parent_4_ok,
    mtFiber35Parent_5_ok,
    mtFiber35Parent_6_ok,
    mtFiber35Parent_7_ok,
    mtFiber35Parent_8_ok,
    mtFiber35Parent_9_ok,
    mtFiber35Parent_10_ok,
    mtFiber35Parent_11_ok,
    mtFiber35Parent_12_ok,
    mtFiber35Parent_13_ok,
    mtFiber35Parent_14_ok,
    mtFiber35Parent_15_ok]

def mtFiber36Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.r]

def mtFiber36Expected : List Nat :=
  [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]

def mtFiber36Rows : List DirectChainParentRow :=
  [ directRow 384 384 64 156 64 156 default
  , directRow 385 384 64 157 64 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 386 385 64 158 64 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 387 384 64 159 64 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 388 384 64 172 64 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 389 385 64 173 64 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 390 388 64 174 64 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 391 387 64 175 64 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 392 384 65 148 64 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 393 385 65 149 64 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 394 386 65 150 64 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 395 387 65 151 64 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 396 388 65 164 64 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 397 389 65 165 64 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 398 390 65 166 64 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 399 391 65 167 64 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 400 384 66 140 64 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 401 385 66 141 64 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 402 386 66 142 64 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 403 387 66 143 64 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 404 388 66 188 64 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 405 389 66 189 64 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 406 390 66 190 64 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 407 391 66 191 64 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 408 392 67 132 65 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 409 393 67 133 65 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 410 394 67 134 65 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 411 395 67 135 65 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 412 396 67 180 65 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 413 397 67 181 65 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 414 398 67 182 65 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 415 399 67 183 65 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 688 692 116 24 116 40 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 689 693 116 25 116 41 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 690 404 116 26 66 188 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 691 405 116 27 66 189 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 692 400 116 40 66 140 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 693 401 116 41 66 141 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 694 402 116 42 66 142 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 695 403 116 43 66 143 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 696 700 117 16 117 32 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 697 701 117 17 117 33 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 698 714 117 18 119 2 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 699 715 117 19 119 3 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 700 716 117 32 119 48 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 701 717 117 33 119 49 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 702 718 117 34 119 50 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 703 719 117 35 119 51 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 704 708 118 8 118 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 705 709 118 9 118 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 706 396 118 10 65 164 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 707 397 118 11 65 165 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 708 392 118 56 65 148 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 709 393 118 57 65 149 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 710 394 118 58 65 150 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 711 395 118 59 65 151 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 712 716 119 0 119 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 713 717 119 1 119 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 714 388 119 2 64 172 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 715 389 119 3 64 173 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 716 384 119 48 64 156 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 717 385 119 49 64 157 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 718 386 119 50 64 158 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 719 387 119 51 64 159 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mtFiber36RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber36Rows i default

def mtFiber36SourcesCheck : Bool :=
  (mtFiber36Rows.map fun row => row.source) == mtFiber36Expected

theorem mtFiber36SourcesCheck_ok :
    mtFiber36SourcesCheck = true := by
  decide

def mtFiber36RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt i)

theorem mtFiber36Row_0_ok : mtFiber36RowCheck 0 = true := by decide
theorem mtFiber36Row_1_ok : mtFiber36RowCheck 1 = true := by decide
theorem mtFiber36Row_2_ok : mtFiber36RowCheck 2 = true := by decide
theorem mtFiber36Row_3_ok : mtFiber36RowCheck 3 = true := by decide
theorem mtFiber36Row_4_ok : mtFiber36RowCheck 4 = true := by decide
theorem mtFiber36Row_5_ok : mtFiber36RowCheck 5 = true := by decide
theorem mtFiber36Row_6_ok : mtFiber36RowCheck 6 = true := by decide
theorem mtFiber36Row_7_ok : mtFiber36RowCheck 7 = true := by decide
theorem mtFiber36Row_8_ok : mtFiber36RowCheck 8 = true := by decide
theorem mtFiber36Row_9_ok : mtFiber36RowCheck 9 = true := by decide
theorem mtFiber36Row_10_ok : mtFiber36RowCheck 10 = true := by decide
theorem mtFiber36Row_11_ok : mtFiber36RowCheck 11 = true := by decide
theorem mtFiber36Row_12_ok : mtFiber36RowCheck 12 = true := by decide
theorem mtFiber36Row_13_ok : mtFiber36RowCheck 13 = true := by decide
theorem mtFiber36Row_14_ok : mtFiber36RowCheck 14 = true := by decide
theorem mtFiber36Row_15_ok : mtFiber36RowCheck 15 = true := by decide
theorem mtFiber36Row_16_ok : mtFiber36RowCheck 16 = true := by decide
theorem mtFiber36Row_17_ok : mtFiber36RowCheck 17 = true := by decide
theorem mtFiber36Row_18_ok : mtFiber36RowCheck 18 = true := by decide
theorem mtFiber36Row_19_ok : mtFiber36RowCheck 19 = true := by decide
theorem mtFiber36Row_20_ok : mtFiber36RowCheck 20 = true := by decide
theorem mtFiber36Row_21_ok : mtFiber36RowCheck 21 = true := by decide
theorem mtFiber36Row_22_ok : mtFiber36RowCheck 22 = true := by decide
theorem mtFiber36Row_23_ok : mtFiber36RowCheck 23 = true := by decide
theorem mtFiber36Row_24_ok : mtFiber36RowCheck 24 = true := by decide
theorem mtFiber36Row_25_ok : mtFiber36RowCheck 25 = true := by decide
theorem mtFiber36Row_26_ok : mtFiber36RowCheck 26 = true := by decide
theorem mtFiber36Row_27_ok : mtFiber36RowCheck 27 = true := by decide
theorem mtFiber36Row_28_ok : mtFiber36RowCheck 28 = true := by decide
theorem mtFiber36Row_29_ok : mtFiber36RowCheck 29 = true := by decide
theorem mtFiber36Row_30_ok : mtFiber36RowCheck 30 = true := by decide
theorem mtFiber36Row_31_ok : mtFiber36RowCheck 31 = true := by decide
theorem mtFiber36Row_32_ok : mtFiber36RowCheck 32 = true := by decide
theorem mtFiber36Row_33_ok : mtFiber36RowCheck 33 = true := by decide
theorem mtFiber36Row_34_ok : mtFiber36RowCheck 34 = true := by decide
theorem mtFiber36Row_35_ok : mtFiber36RowCheck 35 = true := by decide
theorem mtFiber36Row_36_ok : mtFiber36RowCheck 36 = true := by decide
theorem mtFiber36Row_37_ok : mtFiber36RowCheck 37 = true := by decide
theorem mtFiber36Row_38_ok : mtFiber36RowCheck 38 = true := by decide
theorem mtFiber36Row_39_ok : mtFiber36RowCheck 39 = true := by decide
theorem mtFiber36Row_40_ok : mtFiber36RowCheck 40 = true := by decide
theorem mtFiber36Row_41_ok : mtFiber36RowCheck 41 = true := by decide
theorem mtFiber36Row_42_ok : mtFiber36RowCheck 42 = true := by decide
theorem mtFiber36Row_43_ok : mtFiber36RowCheck 43 = true := by decide
theorem mtFiber36Row_44_ok : mtFiber36RowCheck 44 = true := by decide
theorem mtFiber36Row_45_ok : mtFiber36RowCheck 45 = true := by decide
theorem mtFiber36Row_46_ok : mtFiber36RowCheck 46 = true := by decide
theorem mtFiber36Row_47_ok : mtFiber36RowCheck 47 = true := by decide
theorem mtFiber36Row_48_ok : mtFiber36RowCheck 48 = true := by decide
theorem mtFiber36Row_49_ok : mtFiber36RowCheck 49 = true := by decide
theorem mtFiber36Row_50_ok : mtFiber36RowCheck 50 = true := by decide
theorem mtFiber36Row_51_ok : mtFiber36RowCheck 51 = true := by decide
theorem mtFiber36Row_52_ok : mtFiber36RowCheck 52 = true := by decide
theorem mtFiber36Row_53_ok : mtFiber36RowCheck 53 = true := by decide
theorem mtFiber36Row_54_ok : mtFiber36RowCheck 54 = true := by decide
theorem mtFiber36Row_55_ok : mtFiber36RowCheck 55 = true := by decide
theorem mtFiber36Row_56_ok : mtFiber36RowCheck 56 = true := by decide
theorem mtFiber36Row_57_ok : mtFiber36RowCheck 57 = true := by decide
theorem mtFiber36Row_58_ok : mtFiber36RowCheck 58 = true := by decide
theorem mtFiber36Row_59_ok : mtFiber36RowCheck 59 = true := by decide
theorem mtFiber36Row_60_ok : mtFiber36RowCheck 60 = true := by decide
theorem mtFiber36Row_61_ok : mtFiber36RowCheck 61 = true := by decide
theorem mtFiber36Row_62_ok : mtFiber36RowCheck 62 = true := by decide
theorem mtFiber36Row_63_ok : mtFiber36RowCheck 63 = true := by decide

def mtFiber36ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber36Rows mtMaxParentDepth (listGetD mtFiber36Expected i 0) == 384

theorem mtFiber36Parent_0_ok : mtFiber36ParentCheck 0 = true := by decide
theorem mtFiber36Parent_1_ok : mtFiber36ParentCheck 1 = true := by decide
theorem mtFiber36Parent_2_ok : mtFiber36ParentCheck 2 = true := by decide
theorem mtFiber36Parent_3_ok : mtFiber36ParentCheck 3 = true := by decide
theorem mtFiber36Parent_4_ok : mtFiber36ParentCheck 4 = true := by decide
theorem mtFiber36Parent_5_ok : mtFiber36ParentCheck 5 = true := by decide
theorem mtFiber36Parent_6_ok : mtFiber36ParentCheck 6 = true := by decide
theorem mtFiber36Parent_7_ok : mtFiber36ParentCheck 7 = true := by decide
theorem mtFiber36Parent_8_ok : mtFiber36ParentCheck 8 = true := by decide
theorem mtFiber36Parent_9_ok : mtFiber36ParentCheck 9 = true := by decide
theorem mtFiber36Parent_10_ok : mtFiber36ParentCheck 10 = true := by decide
theorem mtFiber36Parent_11_ok : mtFiber36ParentCheck 11 = true := by decide
theorem mtFiber36Parent_12_ok : mtFiber36ParentCheck 12 = true := by decide
theorem mtFiber36Parent_13_ok : mtFiber36ParentCheck 13 = true := by decide
theorem mtFiber36Parent_14_ok : mtFiber36ParentCheck 14 = true := by decide
theorem mtFiber36Parent_15_ok : mtFiber36ParentCheck 15 = true := by decide
theorem mtFiber36Parent_16_ok : mtFiber36ParentCheck 16 = true := by decide
theorem mtFiber36Parent_17_ok : mtFiber36ParentCheck 17 = true := by decide
theorem mtFiber36Parent_18_ok : mtFiber36ParentCheck 18 = true := by decide
theorem mtFiber36Parent_19_ok : mtFiber36ParentCheck 19 = true := by decide
theorem mtFiber36Parent_20_ok : mtFiber36ParentCheck 20 = true := by decide
theorem mtFiber36Parent_21_ok : mtFiber36ParentCheck 21 = true := by decide
theorem mtFiber36Parent_22_ok : mtFiber36ParentCheck 22 = true := by decide
theorem mtFiber36Parent_23_ok : mtFiber36ParentCheck 23 = true := by decide
theorem mtFiber36Parent_24_ok : mtFiber36ParentCheck 24 = true := by decide
theorem mtFiber36Parent_25_ok : mtFiber36ParentCheck 25 = true := by decide
theorem mtFiber36Parent_26_ok : mtFiber36ParentCheck 26 = true := by decide
theorem mtFiber36Parent_27_ok : mtFiber36ParentCheck 27 = true := by decide
theorem mtFiber36Parent_28_ok : mtFiber36ParentCheck 28 = true := by decide
theorem mtFiber36Parent_29_ok : mtFiber36ParentCheck 29 = true := by decide
theorem mtFiber36Parent_30_ok : mtFiber36ParentCheck 30 = true := by decide
theorem mtFiber36Parent_31_ok : mtFiber36ParentCheck 31 = true := by decide
theorem mtFiber36Parent_32_ok : mtFiber36ParentCheck 32 = true := by decide
theorem mtFiber36Parent_33_ok : mtFiber36ParentCheck 33 = true := by decide
theorem mtFiber36Parent_34_ok : mtFiber36ParentCheck 34 = true := by decide
theorem mtFiber36Parent_35_ok : mtFiber36ParentCheck 35 = true := by decide
theorem mtFiber36Parent_36_ok : mtFiber36ParentCheck 36 = true := by decide
theorem mtFiber36Parent_37_ok : mtFiber36ParentCheck 37 = true := by decide
theorem mtFiber36Parent_38_ok : mtFiber36ParentCheck 38 = true := by decide
theorem mtFiber36Parent_39_ok : mtFiber36ParentCheck 39 = true := by decide
theorem mtFiber36Parent_40_ok : mtFiber36ParentCheck 40 = true := by decide
theorem mtFiber36Parent_41_ok : mtFiber36ParentCheck 41 = true := by decide
theorem mtFiber36Parent_42_ok : mtFiber36ParentCheck 42 = true := by decide
theorem mtFiber36Parent_43_ok : mtFiber36ParentCheck 43 = true := by decide
theorem mtFiber36Parent_44_ok : mtFiber36ParentCheck 44 = true := by decide
theorem mtFiber36Parent_45_ok : mtFiber36ParentCheck 45 = true := by decide
theorem mtFiber36Parent_46_ok : mtFiber36ParentCheck 46 = true := by decide
theorem mtFiber36Parent_47_ok : mtFiber36ParentCheck 47 = true := by decide
theorem mtFiber36Parent_48_ok : mtFiber36ParentCheck 48 = true := by decide
theorem mtFiber36Parent_49_ok : mtFiber36ParentCheck 49 = true := by decide
theorem mtFiber36Parent_50_ok : mtFiber36ParentCheck 50 = true := by decide
theorem mtFiber36Parent_51_ok : mtFiber36ParentCheck 51 = true := by decide
theorem mtFiber36Parent_52_ok : mtFiber36ParentCheck 52 = true := by decide
theorem mtFiber36Parent_53_ok : mtFiber36ParentCheck 53 = true := by decide
theorem mtFiber36Parent_54_ok : mtFiber36ParentCheck 54 = true := by decide
theorem mtFiber36Parent_55_ok : mtFiber36ParentCheck 55 = true := by decide
theorem mtFiber36Parent_56_ok : mtFiber36ParentCheck 56 = true := by decide
theorem mtFiber36Parent_57_ok : mtFiber36ParentCheck 57 = true := by decide
theorem mtFiber36Parent_58_ok : mtFiber36ParentCheck 58 = true := by decide
theorem mtFiber36Parent_59_ok : mtFiber36ParentCheck 59 = true := by decide
theorem mtFiber36Parent_60_ok : mtFiber36ParentCheck 60 = true := by decide
theorem mtFiber36Parent_61_ok : mtFiber36ParentCheck 61 = true := by decide
theorem mtFiber36Parent_62_ok : mtFiber36ParentCheck 62 = true := by decide
theorem mtFiber36Parent_63_ok : mtFiber36ParentCheck 63 = true := by decide

def mtFiber36CertificateAudit : Bool :=
  mtFiber36SourcesCheck &&
    mtFiber36RowCheck 0 &&
    mtFiber36RowCheck 1 &&
    mtFiber36RowCheck 2 &&
    mtFiber36RowCheck 3 &&
    mtFiber36RowCheck 4 &&
    mtFiber36RowCheck 5 &&
    mtFiber36RowCheck 6 &&
    mtFiber36RowCheck 7 &&
    mtFiber36RowCheck 8 &&
    mtFiber36RowCheck 9 &&
    mtFiber36RowCheck 10 &&
    mtFiber36RowCheck 11 &&
    mtFiber36RowCheck 12 &&
    mtFiber36RowCheck 13 &&
    mtFiber36RowCheck 14 &&
    mtFiber36RowCheck 15 &&
    mtFiber36RowCheck 16 &&
    mtFiber36RowCheck 17 &&
    mtFiber36RowCheck 18 &&
    mtFiber36RowCheck 19 &&
    mtFiber36RowCheck 20 &&
    mtFiber36RowCheck 21 &&
    mtFiber36RowCheck 22 &&
    mtFiber36RowCheck 23 &&
    mtFiber36RowCheck 24 &&
    mtFiber36RowCheck 25 &&
    mtFiber36RowCheck 26 &&
    mtFiber36RowCheck 27 &&
    mtFiber36RowCheck 28 &&
    mtFiber36RowCheck 29 &&
    mtFiber36RowCheck 30 &&
    mtFiber36RowCheck 31 &&
    mtFiber36RowCheck 32 &&
    mtFiber36RowCheck 33 &&
    mtFiber36RowCheck 34 &&
    mtFiber36RowCheck 35 &&
    mtFiber36RowCheck 36 &&
    mtFiber36RowCheck 37 &&
    mtFiber36RowCheck 38 &&
    mtFiber36RowCheck 39 &&
    mtFiber36RowCheck 40 &&
    mtFiber36RowCheck 41 &&
    mtFiber36RowCheck 42 &&
    mtFiber36RowCheck 43 &&
    mtFiber36RowCheck 44 &&
    mtFiber36RowCheck 45 &&
    mtFiber36RowCheck 46 &&
    mtFiber36RowCheck 47 &&
    mtFiber36RowCheck 48 &&
    mtFiber36RowCheck 49 &&
    mtFiber36RowCheck 50 &&
    mtFiber36RowCheck 51 &&
    mtFiber36RowCheck 52 &&
    mtFiber36RowCheck 53 &&
    mtFiber36RowCheck 54 &&
    mtFiber36RowCheck 55 &&
    mtFiber36RowCheck 56 &&
    mtFiber36RowCheck 57 &&
    mtFiber36RowCheck 58 &&
    mtFiber36RowCheck 59 &&
    mtFiber36RowCheck 60 &&
    mtFiber36RowCheck 61 &&
    mtFiber36RowCheck 62 &&
    mtFiber36RowCheck 63 &&
    mtFiber36ParentCheck 0 &&
    mtFiber36ParentCheck 1 &&
    mtFiber36ParentCheck 2 &&
    mtFiber36ParentCheck 3 &&
    mtFiber36ParentCheck 4 &&
    mtFiber36ParentCheck 5 &&
    mtFiber36ParentCheck 6 &&
    mtFiber36ParentCheck 7 &&
    mtFiber36ParentCheck 8 &&
    mtFiber36ParentCheck 9 &&
    mtFiber36ParentCheck 10 &&
    mtFiber36ParentCheck 11 &&
    mtFiber36ParentCheck 12 &&
    mtFiber36ParentCheck 13 &&
    mtFiber36ParentCheck 14 &&
    mtFiber36ParentCheck 15 &&
    mtFiber36ParentCheck 16 &&
    mtFiber36ParentCheck 17 &&
    mtFiber36ParentCheck 18 &&
    mtFiber36ParentCheck 19 &&
    mtFiber36ParentCheck 20 &&
    mtFiber36ParentCheck 21 &&
    mtFiber36ParentCheck 22 &&
    mtFiber36ParentCheck 23 &&
    mtFiber36ParentCheck 24 &&
    mtFiber36ParentCheck 25 &&
    mtFiber36ParentCheck 26 &&
    mtFiber36ParentCheck 27 &&
    mtFiber36ParentCheck 28 &&
    mtFiber36ParentCheck 29 &&
    mtFiber36ParentCheck 30 &&
    mtFiber36ParentCheck 31 &&
    mtFiber36ParentCheck 32 &&
    mtFiber36ParentCheck 33 &&
    mtFiber36ParentCheck 34 &&
    mtFiber36ParentCheck 35 &&
    mtFiber36ParentCheck 36 &&
    mtFiber36ParentCheck 37 &&
    mtFiber36ParentCheck 38 &&
    mtFiber36ParentCheck 39 &&
    mtFiber36ParentCheck 40 &&
    mtFiber36ParentCheck 41 &&
    mtFiber36ParentCheck 42 &&
    mtFiber36ParentCheck 43 &&
    mtFiber36ParentCheck 44 &&
    mtFiber36ParentCheck 45 &&
    mtFiber36ParentCheck 46 &&
    mtFiber36ParentCheck 47 &&
    mtFiber36ParentCheck 48 &&
    mtFiber36ParentCheck 49 &&
    mtFiber36ParentCheck 50 &&
    mtFiber36ParentCheck 51 &&
    mtFiber36ParentCheck 52 &&
    mtFiber36ParentCheck 53 &&
    mtFiber36ParentCheck 54 &&
    mtFiber36ParentCheck 55 &&
    mtFiber36ParentCheck 56 &&
    mtFiber36ParentCheck 57 &&
    mtFiber36ParentCheck 58 &&
    mtFiber36ParentCheck 59 &&
    mtFiber36ParentCheck 60 &&
    mtFiber36ParentCheck 61 &&
    mtFiber36ParentCheck 62 &&
    mtFiber36ParentCheck 63

theorem mtFiber36CertificateAudit_ok :
    mtFiber36CertificateAudit = true := by
  simp [mtFiber36CertificateAudit,
    mtFiber36SourcesCheck_ok,
    mtFiber36Row_0_ok,
    mtFiber36Row_1_ok,
    mtFiber36Row_2_ok,
    mtFiber36Row_3_ok,
    mtFiber36Row_4_ok,
    mtFiber36Row_5_ok,
    mtFiber36Row_6_ok,
    mtFiber36Row_7_ok,
    mtFiber36Row_8_ok,
    mtFiber36Row_9_ok,
    mtFiber36Row_10_ok,
    mtFiber36Row_11_ok,
    mtFiber36Row_12_ok,
    mtFiber36Row_13_ok,
    mtFiber36Row_14_ok,
    mtFiber36Row_15_ok,
    mtFiber36Row_16_ok,
    mtFiber36Row_17_ok,
    mtFiber36Row_18_ok,
    mtFiber36Row_19_ok,
    mtFiber36Row_20_ok,
    mtFiber36Row_21_ok,
    mtFiber36Row_22_ok,
    mtFiber36Row_23_ok,
    mtFiber36Row_24_ok,
    mtFiber36Row_25_ok,
    mtFiber36Row_26_ok,
    mtFiber36Row_27_ok,
    mtFiber36Row_28_ok,
    mtFiber36Row_29_ok,
    mtFiber36Row_30_ok,
    mtFiber36Row_31_ok,
    mtFiber36Row_32_ok,
    mtFiber36Row_33_ok,
    mtFiber36Row_34_ok,
    mtFiber36Row_35_ok,
    mtFiber36Row_36_ok,
    mtFiber36Row_37_ok,
    mtFiber36Row_38_ok,
    mtFiber36Row_39_ok,
    mtFiber36Row_40_ok,
    mtFiber36Row_41_ok,
    mtFiber36Row_42_ok,
    mtFiber36Row_43_ok,
    mtFiber36Row_44_ok,
    mtFiber36Row_45_ok,
    mtFiber36Row_46_ok,
    mtFiber36Row_47_ok,
    mtFiber36Row_48_ok,
    mtFiber36Row_49_ok,
    mtFiber36Row_50_ok,
    mtFiber36Row_51_ok,
    mtFiber36Row_52_ok,
    mtFiber36Row_53_ok,
    mtFiber36Row_54_ok,
    mtFiber36Row_55_ok,
    mtFiber36Row_56_ok,
    mtFiber36Row_57_ok,
    mtFiber36Row_58_ok,
    mtFiber36Row_59_ok,
    mtFiber36Row_60_ok,
    mtFiber36Row_61_ok,
    mtFiber36Row_62_ok,
    mtFiber36Row_63_ok,
    mtFiber36Parent_0_ok,
    mtFiber36Parent_1_ok,
    mtFiber36Parent_2_ok,
    mtFiber36Parent_3_ok,
    mtFiber36Parent_4_ok,
    mtFiber36Parent_5_ok,
    mtFiber36Parent_6_ok,
    mtFiber36Parent_7_ok,
    mtFiber36Parent_8_ok,
    mtFiber36Parent_9_ok,
    mtFiber36Parent_10_ok,
    mtFiber36Parent_11_ok,
    mtFiber36Parent_12_ok,
    mtFiber36Parent_13_ok,
    mtFiber36Parent_14_ok,
    mtFiber36Parent_15_ok,
    mtFiber36Parent_16_ok,
    mtFiber36Parent_17_ok,
    mtFiber36Parent_18_ok,
    mtFiber36Parent_19_ok,
    mtFiber36Parent_20_ok,
    mtFiber36Parent_21_ok,
    mtFiber36Parent_22_ok,
    mtFiber36Parent_23_ok,
    mtFiber36Parent_24_ok,
    mtFiber36Parent_25_ok,
    mtFiber36Parent_26_ok,
    mtFiber36Parent_27_ok,
    mtFiber36Parent_28_ok,
    mtFiber36Parent_29_ok,
    mtFiber36Parent_30_ok,
    mtFiber36Parent_31_ok,
    mtFiber36Parent_32_ok,
    mtFiber36Parent_33_ok,
    mtFiber36Parent_34_ok,
    mtFiber36Parent_35_ok,
    mtFiber36Parent_36_ok,
    mtFiber36Parent_37_ok,
    mtFiber36Parent_38_ok,
    mtFiber36Parent_39_ok,
    mtFiber36Parent_40_ok,
    mtFiber36Parent_41_ok,
    mtFiber36Parent_42_ok,
    mtFiber36Parent_43_ok,
    mtFiber36Parent_44_ok,
    mtFiber36Parent_45_ok,
    mtFiber36Parent_46_ok,
    mtFiber36Parent_47_ok,
    mtFiber36Parent_48_ok,
    mtFiber36Parent_49_ok,
    mtFiber36Parent_50_ok,
    mtFiber36Parent_51_ok,
    mtFiber36Parent_52_ok,
    mtFiber36Parent_53_ok,
    mtFiber36Parent_54_ok,
    mtFiber36Parent_55_ok,
    mtFiber36Parent_56_ok,
    mtFiber36Parent_57_ok,
    mtFiber36Parent_58_ok,
    mtFiber36Parent_59_ok,
    mtFiber36Parent_60_ok,
    mtFiber36Parent_61_ok,
    mtFiber36Parent_62_ok,
    mtFiber36Parent_63_ok]

def mtFiber37Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.b]

def mtFiber37Expected : List Nat :=
  [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]

def mtFiber37Rows : List DirectChainParentRow :=
  [ directRow 320 320 52 104 52 104 default
  , directRow 321 320 52 105 52 104 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 322 320 52 106 52 104 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 323 321 52 107 52 105 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 324 320 53 96 52 104 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 325 321 53 97 52 105 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 326 322 53 98 52 106 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 327 323 53 99 52 107 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 328 324 54 120 53 96 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 329 325 54 121 53 97 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 330 326 54 122 53 98 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 331 327 54 123 53 99 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 332 320 55 112 52 104 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 333 321 55 113 52 105 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 334 322 55 114 52 106 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 335 323 55 115 52 107 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber37RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber37Rows i default

def mtFiber37SourcesCheck : Bool :=
  (mtFiber37Rows.map fun row => row.source) == mtFiber37Expected

theorem mtFiber37SourcesCheck_ok :
    mtFiber37SourcesCheck = true := by
  decide

def mtFiber37RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt i)

theorem mtFiber37Row_0_ok : mtFiber37RowCheck 0 = true := by decide
theorem mtFiber37Row_1_ok : mtFiber37RowCheck 1 = true := by decide
theorem mtFiber37Row_2_ok : mtFiber37RowCheck 2 = true := by decide
theorem mtFiber37Row_3_ok : mtFiber37RowCheck 3 = true := by decide
theorem mtFiber37Row_4_ok : mtFiber37RowCheck 4 = true := by decide
theorem mtFiber37Row_5_ok : mtFiber37RowCheck 5 = true := by decide
theorem mtFiber37Row_6_ok : mtFiber37RowCheck 6 = true := by decide
theorem mtFiber37Row_7_ok : mtFiber37RowCheck 7 = true := by decide
theorem mtFiber37Row_8_ok : mtFiber37RowCheck 8 = true := by decide
theorem mtFiber37Row_9_ok : mtFiber37RowCheck 9 = true := by decide
theorem mtFiber37Row_10_ok : mtFiber37RowCheck 10 = true := by decide
theorem mtFiber37Row_11_ok : mtFiber37RowCheck 11 = true := by decide
theorem mtFiber37Row_12_ok : mtFiber37RowCheck 12 = true := by decide
theorem mtFiber37Row_13_ok : mtFiber37RowCheck 13 = true := by decide
theorem mtFiber37Row_14_ok : mtFiber37RowCheck 14 = true := by decide
theorem mtFiber37Row_15_ok : mtFiber37RowCheck 15 = true := by decide

def mtFiber37ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber37Rows mtMaxParentDepth (listGetD mtFiber37Expected i 0) == 320

theorem mtFiber37Parent_0_ok : mtFiber37ParentCheck 0 = true := by decide
theorem mtFiber37Parent_1_ok : mtFiber37ParentCheck 1 = true := by decide
theorem mtFiber37Parent_2_ok : mtFiber37ParentCheck 2 = true := by decide
theorem mtFiber37Parent_3_ok : mtFiber37ParentCheck 3 = true := by decide
theorem mtFiber37Parent_4_ok : mtFiber37ParentCheck 4 = true := by decide
theorem mtFiber37Parent_5_ok : mtFiber37ParentCheck 5 = true := by decide
theorem mtFiber37Parent_6_ok : mtFiber37ParentCheck 6 = true := by decide
theorem mtFiber37Parent_7_ok : mtFiber37ParentCheck 7 = true := by decide
theorem mtFiber37Parent_8_ok : mtFiber37ParentCheck 8 = true := by decide
theorem mtFiber37Parent_9_ok : mtFiber37ParentCheck 9 = true := by decide
theorem mtFiber37Parent_10_ok : mtFiber37ParentCheck 10 = true := by decide
theorem mtFiber37Parent_11_ok : mtFiber37ParentCheck 11 = true := by decide
theorem mtFiber37Parent_12_ok : mtFiber37ParentCheck 12 = true := by decide
theorem mtFiber37Parent_13_ok : mtFiber37ParentCheck 13 = true := by decide
theorem mtFiber37Parent_14_ok : mtFiber37ParentCheck 14 = true := by decide
theorem mtFiber37Parent_15_ok : mtFiber37ParentCheck 15 = true := by decide

def mtFiber37CertificateAudit : Bool :=
  mtFiber37SourcesCheck &&
    mtFiber37RowCheck 0 &&
    mtFiber37RowCheck 1 &&
    mtFiber37RowCheck 2 &&
    mtFiber37RowCheck 3 &&
    mtFiber37RowCheck 4 &&
    mtFiber37RowCheck 5 &&
    mtFiber37RowCheck 6 &&
    mtFiber37RowCheck 7 &&
    mtFiber37RowCheck 8 &&
    mtFiber37RowCheck 9 &&
    mtFiber37RowCheck 10 &&
    mtFiber37RowCheck 11 &&
    mtFiber37RowCheck 12 &&
    mtFiber37RowCheck 13 &&
    mtFiber37RowCheck 14 &&
    mtFiber37RowCheck 15 &&
    mtFiber37ParentCheck 0 &&
    mtFiber37ParentCheck 1 &&
    mtFiber37ParentCheck 2 &&
    mtFiber37ParentCheck 3 &&
    mtFiber37ParentCheck 4 &&
    mtFiber37ParentCheck 5 &&
    mtFiber37ParentCheck 6 &&
    mtFiber37ParentCheck 7 &&
    mtFiber37ParentCheck 8 &&
    mtFiber37ParentCheck 9 &&
    mtFiber37ParentCheck 10 &&
    mtFiber37ParentCheck 11 &&
    mtFiber37ParentCheck 12 &&
    mtFiber37ParentCheck 13 &&
    mtFiber37ParentCheck 14 &&
    mtFiber37ParentCheck 15

theorem mtFiber37CertificateAudit_ok :
    mtFiber37CertificateAudit = true := by
  simp [mtFiber37CertificateAudit,
    mtFiber37SourcesCheck_ok,
    mtFiber37Row_0_ok,
    mtFiber37Row_1_ok,
    mtFiber37Row_2_ok,
    mtFiber37Row_3_ok,
    mtFiber37Row_4_ok,
    mtFiber37Row_5_ok,
    mtFiber37Row_6_ok,
    mtFiber37Row_7_ok,
    mtFiber37Row_8_ok,
    mtFiber37Row_9_ok,
    mtFiber37Row_10_ok,
    mtFiber37Row_11_ok,
    mtFiber37Row_12_ok,
    mtFiber37Row_13_ok,
    mtFiber37Row_14_ok,
    mtFiber37Row_15_ok,
    mtFiber37Parent_0_ok,
    mtFiber37Parent_1_ok,
    mtFiber37Parent_2_ok,
    mtFiber37Parent_3_ok,
    mtFiber37Parent_4_ok,
    mtFiber37Parent_5_ok,
    mtFiber37Parent_6_ok,
    mtFiber37Parent_7_ok,
    mtFiber37Parent_8_ok,
    mtFiber37Parent_9_ok,
    mtFiber37Parent_10_ok,
    mtFiber37Parent_11_ok,
    mtFiber37Parent_12_ok,
    mtFiber37Parent_13_ok,
    mtFiber37Parent_14_ok,
    mtFiber37Parent_15_ok]

def mtFiber38Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.p]

def mtFiber38Expected : List Nat :=
  []

def mtFiber38Rows : List DirectChainParentRow :=
  []

def mtFiber38RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber38Rows i default

def mtFiber38SourcesCheck : Bool :=
  (mtFiber38Rows.map fun row => row.source) == mtFiber38Expected

theorem mtFiber38SourcesCheck_ok :
    mtFiber38SourcesCheck = true := by
  decide

def mtFiber38RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber38Key mtFiber38Expected (mtFiber38RowAt i)

def mtFiber38ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber38Rows mtMaxParentDepth (listGetD mtFiber38Expected i 0) == 0

def mtFiber38CertificateAudit : Bool :=
  mtFiber38SourcesCheck

theorem mtFiber38CertificateAudit_ok :
    mtFiber38CertificateAudit = true := by
  simp [mtFiber38CertificateAudit,
    mtFiber38SourcesCheck_ok]

def mtFiber39Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.r]

def mtFiber39Expected : List Nat :=
  []

def mtFiber39Rows : List DirectChainParentRow :=
  []

def mtFiber39RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber39Rows i default

def mtFiber39SourcesCheck : Bool :=
  (mtFiber39Rows.map fun row => row.source) == mtFiber39Expected

theorem mtFiber39SourcesCheck_ok :
    mtFiber39SourcesCheck = true := by
  decide

def mtFiber39RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber39Key mtFiber39Expected (mtFiber39RowAt i)

def mtFiber39ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber39Rows mtMaxParentDepth (listGetD mtFiber39Expected i 0) == 0

def mtFiber39CertificateAudit : Bool :=
  mtFiber39SourcesCheck

theorem mtFiber39CertificateAudit_ok :
    mtFiber39CertificateAudit = true := by
  simp [mtFiber39CertificateAudit,
    mtFiber39SourcesCheck_ok]

def mtFiber40Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.b]

def mtFiber40Expected : List Nat :=
  []

def mtFiber40Rows : List DirectChainParentRow :=
  []

def mtFiber40RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber40Rows i default

def mtFiber40SourcesCheck : Bool :=
  (mtFiber40Rows.map fun row => row.source) == mtFiber40Expected

theorem mtFiber40SourcesCheck_ok :
    mtFiber40SourcesCheck = true := by
  decide

def mtFiber40RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber40Key mtFiber40Expected (mtFiber40RowAt i)

def mtFiber40ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber40Rows mtMaxParentDepth (listGetD mtFiber40Expected i 0) == 0

def mtFiber40CertificateAudit : Bool :=
  mtFiber40SourcesCheck

theorem mtFiber40CertificateAudit_ok :
    mtFiber40CertificateAudit = true := by
  simp [mtFiber40CertificateAudit,
    mtFiber40SourcesCheck_ok]

def mtFiber41Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.p]

def mtFiber41Expected : List Nat :=
  []

def mtFiber41Rows : List DirectChainParentRow :=
  []

def mtFiber41RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber41Rows i default

def mtFiber41SourcesCheck : Bool :=
  (mtFiber41Rows.map fun row => row.source) == mtFiber41Expected

theorem mtFiber41SourcesCheck_ok :
    mtFiber41SourcesCheck = true := by
  decide

def mtFiber41RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber41Key mtFiber41Expected (mtFiber41RowAt i)

def mtFiber41ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber41Rows mtMaxParentDepth (listGetD mtFiber41Expected i 0) == 0

def mtFiber41CertificateAudit : Bool :=
  mtFiber41SourcesCheck

theorem mtFiber41CertificateAudit_ok :
    mtFiber41CertificateAudit = true := by
  simp [mtFiber41CertificateAudit,
    mtFiber41SourcesCheck_ok]

def mtFiber42Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.r]

def mtFiber42Expected : List Nat :=
  []

def mtFiber42Rows : List DirectChainParentRow :=
  []

def mtFiber42RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber42Rows i default

def mtFiber42SourcesCheck : Bool :=
  (mtFiber42Rows.map fun row => row.source) == mtFiber42Expected

theorem mtFiber42SourcesCheck_ok :
    mtFiber42SourcesCheck = true := by
  decide

def mtFiber42RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber42Key mtFiber42Expected (mtFiber42RowAt i)

def mtFiber42ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber42Rows mtMaxParentDepth (listGetD mtFiber42Expected i 0) == 0

def mtFiber42CertificateAudit : Bool :=
  mtFiber42SourcesCheck

theorem mtFiber42CertificateAudit_ok :
    mtFiber42CertificateAudit = true := by
  simp [mtFiber42CertificateAudit,
    mtFiber42SourcesCheck_ok]

def mtFiber43Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.b]

def mtFiber43Expected : List Nat :=
  [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]

def mtFiber43Rows : List DirectChainParentRow :=
  [ directRow 912 912 152 92 152 92 default
  , directRow 913 912 152 93 152 92 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 914 912 152 94 152 92 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 915 913 152 95 152 93 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 916 912 153 84 152 92 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 917 913 153 85 152 93 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 918 914 153 86 152 94 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 919 915 153 87 152 95 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 920 916 154 76 153 84 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 921 917 154 77 153 85 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 922 918 154 78 153 86 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 923 919 154 79 153 87 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 924 912 155 68 152 92 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 925 913 155 69 152 93 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 926 914 155 70 152 94 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 927 915 155 71 152 95 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber43RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber43Rows i default

def mtFiber43SourcesCheck : Bool :=
  (mtFiber43Rows.map fun row => row.source) == mtFiber43Expected

theorem mtFiber43SourcesCheck_ok :
    mtFiber43SourcesCheck = true := by
  decide

def mtFiber43RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt i)

theorem mtFiber43Row_0_ok : mtFiber43RowCheck 0 = true := by decide
theorem mtFiber43Row_1_ok : mtFiber43RowCheck 1 = true := by decide
theorem mtFiber43Row_2_ok : mtFiber43RowCheck 2 = true := by decide
theorem mtFiber43Row_3_ok : mtFiber43RowCheck 3 = true := by decide
theorem mtFiber43Row_4_ok : mtFiber43RowCheck 4 = true := by decide
theorem mtFiber43Row_5_ok : mtFiber43RowCheck 5 = true := by decide
theorem mtFiber43Row_6_ok : mtFiber43RowCheck 6 = true := by decide
theorem mtFiber43Row_7_ok : mtFiber43RowCheck 7 = true := by decide
theorem mtFiber43Row_8_ok : mtFiber43RowCheck 8 = true := by decide
theorem mtFiber43Row_9_ok : mtFiber43RowCheck 9 = true := by decide
theorem mtFiber43Row_10_ok : mtFiber43RowCheck 10 = true := by decide
theorem mtFiber43Row_11_ok : mtFiber43RowCheck 11 = true := by decide
theorem mtFiber43Row_12_ok : mtFiber43RowCheck 12 = true := by decide
theorem mtFiber43Row_13_ok : mtFiber43RowCheck 13 = true := by decide
theorem mtFiber43Row_14_ok : mtFiber43RowCheck 14 = true := by decide
theorem mtFiber43Row_15_ok : mtFiber43RowCheck 15 = true := by decide

def mtFiber43ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber43Rows mtMaxParentDepth (listGetD mtFiber43Expected i 0) == 912

theorem mtFiber43Parent_0_ok : mtFiber43ParentCheck 0 = true := by decide
theorem mtFiber43Parent_1_ok : mtFiber43ParentCheck 1 = true := by decide
theorem mtFiber43Parent_2_ok : mtFiber43ParentCheck 2 = true := by decide
theorem mtFiber43Parent_3_ok : mtFiber43ParentCheck 3 = true := by decide
theorem mtFiber43Parent_4_ok : mtFiber43ParentCheck 4 = true := by decide
theorem mtFiber43Parent_5_ok : mtFiber43ParentCheck 5 = true := by decide
theorem mtFiber43Parent_6_ok : mtFiber43ParentCheck 6 = true := by decide
theorem mtFiber43Parent_7_ok : mtFiber43ParentCheck 7 = true := by decide
theorem mtFiber43Parent_8_ok : mtFiber43ParentCheck 8 = true := by decide
theorem mtFiber43Parent_9_ok : mtFiber43ParentCheck 9 = true := by decide
theorem mtFiber43Parent_10_ok : mtFiber43ParentCheck 10 = true := by decide
theorem mtFiber43Parent_11_ok : mtFiber43ParentCheck 11 = true := by decide
theorem mtFiber43Parent_12_ok : mtFiber43ParentCheck 12 = true := by decide
theorem mtFiber43Parent_13_ok : mtFiber43ParentCheck 13 = true := by decide
theorem mtFiber43Parent_14_ok : mtFiber43ParentCheck 14 = true := by decide
theorem mtFiber43Parent_15_ok : mtFiber43ParentCheck 15 = true := by decide

def mtFiber43CertificateAudit : Bool :=
  mtFiber43SourcesCheck &&
    mtFiber43RowCheck 0 &&
    mtFiber43RowCheck 1 &&
    mtFiber43RowCheck 2 &&
    mtFiber43RowCheck 3 &&
    mtFiber43RowCheck 4 &&
    mtFiber43RowCheck 5 &&
    mtFiber43RowCheck 6 &&
    mtFiber43RowCheck 7 &&
    mtFiber43RowCheck 8 &&
    mtFiber43RowCheck 9 &&
    mtFiber43RowCheck 10 &&
    mtFiber43RowCheck 11 &&
    mtFiber43RowCheck 12 &&
    mtFiber43RowCheck 13 &&
    mtFiber43RowCheck 14 &&
    mtFiber43RowCheck 15 &&
    mtFiber43ParentCheck 0 &&
    mtFiber43ParentCheck 1 &&
    mtFiber43ParentCheck 2 &&
    mtFiber43ParentCheck 3 &&
    mtFiber43ParentCheck 4 &&
    mtFiber43ParentCheck 5 &&
    mtFiber43ParentCheck 6 &&
    mtFiber43ParentCheck 7 &&
    mtFiber43ParentCheck 8 &&
    mtFiber43ParentCheck 9 &&
    mtFiber43ParentCheck 10 &&
    mtFiber43ParentCheck 11 &&
    mtFiber43ParentCheck 12 &&
    mtFiber43ParentCheck 13 &&
    mtFiber43ParentCheck 14 &&
    mtFiber43ParentCheck 15

theorem mtFiber43CertificateAudit_ok :
    mtFiber43CertificateAudit = true := by
  simp [mtFiber43CertificateAudit,
    mtFiber43SourcesCheck_ok,
    mtFiber43Row_0_ok,
    mtFiber43Row_1_ok,
    mtFiber43Row_2_ok,
    mtFiber43Row_3_ok,
    mtFiber43Row_4_ok,
    mtFiber43Row_5_ok,
    mtFiber43Row_6_ok,
    mtFiber43Row_7_ok,
    mtFiber43Row_8_ok,
    mtFiber43Row_9_ok,
    mtFiber43Row_10_ok,
    mtFiber43Row_11_ok,
    mtFiber43Row_12_ok,
    mtFiber43Row_13_ok,
    mtFiber43Row_14_ok,
    mtFiber43Row_15_ok,
    mtFiber43Parent_0_ok,
    mtFiber43Parent_1_ok,
    mtFiber43Parent_2_ok,
    mtFiber43Parent_3_ok,
    mtFiber43Parent_4_ok,
    mtFiber43Parent_5_ok,
    mtFiber43Parent_6_ok,
    mtFiber43Parent_7_ok,
    mtFiber43Parent_8_ok,
    mtFiber43Parent_9_ok,
    mtFiber43Parent_10_ok,
    mtFiber43Parent_11_ok,
    mtFiber43Parent_12_ok,
    mtFiber43Parent_13_ok,
    mtFiber43Parent_14_ok,
    mtFiber43Parent_15_ok]

def mtFiber44Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.p]

def mtFiber44Expected : List Nat :=
  [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]

def mtFiber44Rows : List DirectChainParentRow :=
  [ directRow 528 528 88 156 88 156 default
  , directRow 529 528 88 157 88 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 530 529 88 158 88 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 531 528 88 159 88 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 532 528 88 172 88 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 533 529 88 173 88 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 534 532 88 174 88 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 535 531 88 175 88 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 536 528 89 148 88 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 537 529 89 149 88 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 538 530 89 150 88 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 539 531 89 151 88 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 540 532 89 164 88 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 541 533 89 165 88 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 542 534 89 166 88 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 543 535 89 167 88 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 544 528 90 140 88 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 545 529 90 141 88 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 546 530 90 142 88 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 547 531 90 143 88 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 548 532 90 188 88 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 549 533 90 189 88 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 550 534 90 190 88 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 551 535 90 191 88 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 552 536 91 132 89 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 553 537 91 133 89 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 554 538 91 134 89 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 555 539 91 135 89 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 556 540 91 180 89 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 557 541 91 181 89 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 558 542 91 182 89 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 559 543 91 183 89 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 640 644 108 24 108 40 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 641 645 108 25 108 41 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 642 548 108 26 90 188 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 643 549 108 27 90 189 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 644 544 108 40 90 140 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 645 545 108 41 90 141 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 646 546 108 42 90 142 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 647 547 108 43 90 143 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 648 652 109 16 109 32 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 649 653 109 17 109 33 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 650 666 109 18 111 2 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 651 667 109 19 111 3 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 652 668 109 32 111 48 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 653 669 109 33 111 49 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 654 670 109 34 111 50 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 655 671 109 35 111 51 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 656 660 110 8 110 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 657 661 110 9 110 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 658 540 110 10 89 164 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 659 541 110 11 89 165 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 660 536 110 56 89 148 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 661 537 110 57 89 149 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 662 538 110 58 89 150 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 663 539 110 59 89 151 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 664 668 111 0 111 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 665 669 111 1 111 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 666 532 111 2 88 172 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 667 533 111 3 88 173 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 668 528 111 48 88 156 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 669 529 111 49 88 157 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 670 530 111 50 88 158 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 671 531 111 51 88 159 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mtFiber44RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber44Rows i default

def mtFiber44SourcesCheck : Bool :=
  (mtFiber44Rows.map fun row => row.source) == mtFiber44Expected

theorem mtFiber44SourcesCheck_ok :
    mtFiber44SourcesCheck = true := by
  decide

def mtFiber44RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt i)

theorem mtFiber44Row_0_ok : mtFiber44RowCheck 0 = true := by decide
theorem mtFiber44Row_1_ok : mtFiber44RowCheck 1 = true := by decide
theorem mtFiber44Row_2_ok : mtFiber44RowCheck 2 = true := by decide
theorem mtFiber44Row_3_ok : mtFiber44RowCheck 3 = true := by decide
theorem mtFiber44Row_4_ok : mtFiber44RowCheck 4 = true := by decide
theorem mtFiber44Row_5_ok : mtFiber44RowCheck 5 = true := by decide
theorem mtFiber44Row_6_ok : mtFiber44RowCheck 6 = true := by decide
theorem mtFiber44Row_7_ok : mtFiber44RowCheck 7 = true := by decide
theorem mtFiber44Row_8_ok : mtFiber44RowCheck 8 = true := by decide
theorem mtFiber44Row_9_ok : mtFiber44RowCheck 9 = true := by decide
theorem mtFiber44Row_10_ok : mtFiber44RowCheck 10 = true := by decide
theorem mtFiber44Row_11_ok : mtFiber44RowCheck 11 = true := by decide
theorem mtFiber44Row_12_ok : mtFiber44RowCheck 12 = true := by decide
theorem mtFiber44Row_13_ok : mtFiber44RowCheck 13 = true := by decide
theorem mtFiber44Row_14_ok : mtFiber44RowCheck 14 = true := by decide
theorem mtFiber44Row_15_ok : mtFiber44RowCheck 15 = true := by decide
theorem mtFiber44Row_16_ok : mtFiber44RowCheck 16 = true := by decide
theorem mtFiber44Row_17_ok : mtFiber44RowCheck 17 = true := by decide
theorem mtFiber44Row_18_ok : mtFiber44RowCheck 18 = true := by decide
theorem mtFiber44Row_19_ok : mtFiber44RowCheck 19 = true := by decide
theorem mtFiber44Row_20_ok : mtFiber44RowCheck 20 = true := by decide
theorem mtFiber44Row_21_ok : mtFiber44RowCheck 21 = true := by decide
theorem mtFiber44Row_22_ok : mtFiber44RowCheck 22 = true := by decide
theorem mtFiber44Row_23_ok : mtFiber44RowCheck 23 = true := by decide
theorem mtFiber44Row_24_ok : mtFiber44RowCheck 24 = true := by decide
theorem mtFiber44Row_25_ok : mtFiber44RowCheck 25 = true := by decide
theorem mtFiber44Row_26_ok : mtFiber44RowCheck 26 = true := by decide
theorem mtFiber44Row_27_ok : mtFiber44RowCheck 27 = true := by decide
theorem mtFiber44Row_28_ok : mtFiber44RowCheck 28 = true := by decide
theorem mtFiber44Row_29_ok : mtFiber44RowCheck 29 = true := by decide
theorem mtFiber44Row_30_ok : mtFiber44RowCheck 30 = true := by decide
theorem mtFiber44Row_31_ok : mtFiber44RowCheck 31 = true := by decide
theorem mtFiber44Row_32_ok : mtFiber44RowCheck 32 = true := by decide
theorem mtFiber44Row_33_ok : mtFiber44RowCheck 33 = true := by decide
theorem mtFiber44Row_34_ok : mtFiber44RowCheck 34 = true := by decide
theorem mtFiber44Row_35_ok : mtFiber44RowCheck 35 = true := by decide
theorem mtFiber44Row_36_ok : mtFiber44RowCheck 36 = true := by decide
theorem mtFiber44Row_37_ok : mtFiber44RowCheck 37 = true := by decide
theorem mtFiber44Row_38_ok : mtFiber44RowCheck 38 = true := by decide
theorem mtFiber44Row_39_ok : mtFiber44RowCheck 39 = true := by decide
theorem mtFiber44Row_40_ok : mtFiber44RowCheck 40 = true := by decide
theorem mtFiber44Row_41_ok : mtFiber44RowCheck 41 = true := by decide
theorem mtFiber44Row_42_ok : mtFiber44RowCheck 42 = true := by decide
theorem mtFiber44Row_43_ok : mtFiber44RowCheck 43 = true := by decide
theorem mtFiber44Row_44_ok : mtFiber44RowCheck 44 = true := by decide
theorem mtFiber44Row_45_ok : mtFiber44RowCheck 45 = true := by decide
theorem mtFiber44Row_46_ok : mtFiber44RowCheck 46 = true := by decide
theorem mtFiber44Row_47_ok : mtFiber44RowCheck 47 = true := by decide
theorem mtFiber44Row_48_ok : mtFiber44RowCheck 48 = true := by decide
theorem mtFiber44Row_49_ok : mtFiber44RowCheck 49 = true := by decide
theorem mtFiber44Row_50_ok : mtFiber44RowCheck 50 = true := by decide
theorem mtFiber44Row_51_ok : mtFiber44RowCheck 51 = true := by decide
theorem mtFiber44Row_52_ok : mtFiber44RowCheck 52 = true := by decide
theorem mtFiber44Row_53_ok : mtFiber44RowCheck 53 = true := by decide
theorem mtFiber44Row_54_ok : mtFiber44RowCheck 54 = true := by decide
theorem mtFiber44Row_55_ok : mtFiber44RowCheck 55 = true := by decide
theorem mtFiber44Row_56_ok : mtFiber44RowCheck 56 = true := by decide
theorem mtFiber44Row_57_ok : mtFiber44RowCheck 57 = true := by decide
theorem mtFiber44Row_58_ok : mtFiber44RowCheck 58 = true := by decide
theorem mtFiber44Row_59_ok : mtFiber44RowCheck 59 = true := by decide
theorem mtFiber44Row_60_ok : mtFiber44RowCheck 60 = true := by decide
theorem mtFiber44Row_61_ok : mtFiber44RowCheck 61 = true := by decide
theorem mtFiber44Row_62_ok : mtFiber44RowCheck 62 = true := by decide
theorem mtFiber44Row_63_ok : mtFiber44RowCheck 63 = true := by decide

def mtFiber44ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber44Rows mtMaxParentDepth (listGetD mtFiber44Expected i 0) == 528

theorem mtFiber44Parent_0_ok : mtFiber44ParentCheck 0 = true := by decide
theorem mtFiber44Parent_1_ok : mtFiber44ParentCheck 1 = true := by decide
theorem mtFiber44Parent_2_ok : mtFiber44ParentCheck 2 = true := by decide
theorem mtFiber44Parent_3_ok : mtFiber44ParentCheck 3 = true := by decide
theorem mtFiber44Parent_4_ok : mtFiber44ParentCheck 4 = true := by decide
theorem mtFiber44Parent_5_ok : mtFiber44ParentCheck 5 = true := by decide
theorem mtFiber44Parent_6_ok : mtFiber44ParentCheck 6 = true := by decide
theorem mtFiber44Parent_7_ok : mtFiber44ParentCheck 7 = true := by decide
theorem mtFiber44Parent_8_ok : mtFiber44ParentCheck 8 = true := by decide
theorem mtFiber44Parent_9_ok : mtFiber44ParentCheck 9 = true := by decide
theorem mtFiber44Parent_10_ok : mtFiber44ParentCheck 10 = true := by decide
theorem mtFiber44Parent_11_ok : mtFiber44ParentCheck 11 = true := by decide
theorem mtFiber44Parent_12_ok : mtFiber44ParentCheck 12 = true := by decide
theorem mtFiber44Parent_13_ok : mtFiber44ParentCheck 13 = true := by decide
theorem mtFiber44Parent_14_ok : mtFiber44ParentCheck 14 = true := by decide
theorem mtFiber44Parent_15_ok : mtFiber44ParentCheck 15 = true := by decide
theorem mtFiber44Parent_16_ok : mtFiber44ParentCheck 16 = true := by decide
theorem mtFiber44Parent_17_ok : mtFiber44ParentCheck 17 = true := by decide
theorem mtFiber44Parent_18_ok : mtFiber44ParentCheck 18 = true := by decide
theorem mtFiber44Parent_19_ok : mtFiber44ParentCheck 19 = true := by decide
theorem mtFiber44Parent_20_ok : mtFiber44ParentCheck 20 = true := by decide
theorem mtFiber44Parent_21_ok : mtFiber44ParentCheck 21 = true := by decide
theorem mtFiber44Parent_22_ok : mtFiber44ParentCheck 22 = true := by decide
theorem mtFiber44Parent_23_ok : mtFiber44ParentCheck 23 = true := by decide
theorem mtFiber44Parent_24_ok : mtFiber44ParentCheck 24 = true := by decide
theorem mtFiber44Parent_25_ok : mtFiber44ParentCheck 25 = true := by decide
theorem mtFiber44Parent_26_ok : mtFiber44ParentCheck 26 = true := by decide
theorem mtFiber44Parent_27_ok : mtFiber44ParentCheck 27 = true := by decide
theorem mtFiber44Parent_28_ok : mtFiber44ParentCheck 28 = true := by decide
theorem mtFiber44Parent_29_ok : mtFiber44ParentCheck 29 = true := by decide
theorem mtFiber44Parent_30_ok : mtFiber44ParentCheck 30 = true := by decide
theorem mtFiber44Parent_31_ok : mtFiber44ParentCheck 31 = true := by decide
theorem mtFiber44Parent_32_ok : mtFiber44ParentCheck 32 = true := by decide
theorem mtFiber44Parent_33_ok : mtFiber44ParentCheck 33 = true := by decide
theorem mtFiber44Parent_34_ok : mtFiber44ParentCheck 34 = true := by decide
theorem mtFiber44Parent_35_ok : mtFiber44ParentCheck 35 = true := by decide
theorem mtFiber44Parent_36_ok : mtFiber44ParentCheck 36 = true := by decide
theorem mtFiber44Parent_37_ok : mtFiber44ParentCheck 37 = true := by decide
theorem mtFiber44Parent_38_ok : mtFiber44ParentCheck 38 = true := by decide
theorem mtFiber44Parent_39_ok : mtFiber44ParentCheck 39 = true := by decide
theorem mtFiber44Parent_40_ok : mtFiber44ParentCheck 40 = true := by decide
theorem mtFiber44Parent_41_ok : mtFiber44ParentCheck 41 = true := by decide
theorem mtFiber44Parent_42_ok : mtFiber44ParentCheck 42 = true := by decide
theorem mtFiber44Parent_43_ok : mtFiber44ParentCheck 43 = true := by decide
theorem mtFiber44Parent_44_ok : mtFiber44ParentCheck 44 = true := by decide
theorem mtFiber44Parent_45_ok : mtFiber44ParentCheck 45 = true := by decide
theorem mtFiber44Parent_46_ok : mtFiber44ParentCheck 46 = true := by decide
theorem mtFiber44Parent_47_ok : mtFiber44ParentCheck 47 = true := by decide
theorem mtFiber44Parent_48_ok : mtFiber44ParentCheck 48 = true := by decide
theorem mtFiber44Parent_49_ok : mtFiber44ParentCheck 49 = true := by decide
theorem mtFiber44Parent_50_ok : mtFiber44ParentCheck 50 = true := by decide
theorem mtFiber44Parent_51_ok : mtFiber44ParentCheck 51 = true := by decide
theorem mtFiber44Parent_52_ok : mtFiber44ParentCheck 52 = true := by decide
theorem mtFiber44Parent_53_ok : mtFiber44ParentCheck 53 = true := by decide
theorem mtFiber44Parent_54_ok : mtFiber44ParentCheck 54 = true := by decide
theorem mtFiber44Parent_55_ok : mtFiber44ParentCheck 55 = true := by decide
theorem mtFiber44Parent_56_ok : mtFiber44ParentCheck 56 = true := by decide
theorem mtFiber44Parent_57_ok : mtFiber44ParentCheck 57 = true := by decide
theorem mtFiber44Parent_58_ok : mtFiber44ParentCheck 58 = true := by decide
theorem mtFiber44Parent_59_ok : mtFiber44ParentCheck 59 = true := by decide
theorem mtFiber44Parent_60_ok : mtFiber44ParentCheck 60 = true := by decide
theorem mtFiber44Parent_61_ok : mtFiber44ParentCheck 61 = true := by decide
theorem mtFiber44Parent_62_ok : mtFiber44ParentCheck 62 = true := by decide
theorem mtFiber44Parent_63_ok : mtFiber44ParentCheck 63 = true := by decide

def mtFiber44CertificateAudit : Bool :=
  mtFiber44SourcesCheck &&
    mtFiber44RowCheck 0 &&
    mtFiber44RowCheck 1 &&
    mtFiber44RowCheck 2 &&
    mtFiber44RowCheck 3 &&
    mtFiber44RowCheck 4 &&
    mtFiber44RowCheck 5 &&
    mtFiber44RowCheck 6 &&
    mtFiber44RowCheck 7 &&
    mtFiber44RowCheck 8 &&
    mtFiber44RowCheck 9 &&
    mtFiber44RowCheck 10 &&
    mtFiber44RowCheck 11 &&
    mtFiber44RowCheck 12 &&
    mtFiber44RowCheck 13 &&
    mtFiber44RowCheck 14 &&
    mtFiber44RowCheck 15 &&
    mtFiber44RowCheck 16 &&
    mtFiber44RowCheck 17 &&
    mtFiber44RowCheck 18 &&
    mtFiber44RowCheck 19 &&
    mtFiber44RowCheck 20 &&
    mtFiber44RowCheck 21 &&
    mtFiber44RowCheck 22 &&
    mtFiber44RowCheck 23 &&
    mtFiber44RowCheck 24 &&
    mtFiber44RowCheck 25 &&
    mtFiber44RowCheck 26 &&
    mtFiber44RowCheck 27 &&
    mtFiber44RowCheck 28 &&
    mtFiber44RowCheck 29 &&
    mtFiber44RowCheck 30 &&
    mtFiber44RowCheck 31 &&
    mtFiber44RowCheck 32 &&
    mtFiber44RowCheck 33 &&
    mtFiber44RowCheck 34 &&
    mtFiber44RowCheck 35 &&
    mtFiber44RowCheck 36 &&
    mtFiber44RowCheck 37 &&
    mtFiber44RowCheck 38 &&
    mtFiber44RowCheck 39 &&
    mtFiber44RowCheck 40 &&
    mtFiber44RowCheck 41 &&
    mtFiber44RowCheck 42 &&
    mtFiber44RowCheck 43 &&
    mtFiber44RowCheck 44 &&
    mtFiber44RowCheck 45 &&
    mtFiber44RowCheck 46 &&
    mtFiber44RowCheck 47 &&
    mtFiber44RowCheck 48 &&
    mtFiber44RowCheck 49 &&
    mtFiber44RowCheck 50 &&
    mtFiber44RowCheck 51 &&
    mtFiber44RowCheck 52 &&
    mtFiber44RowCheck 53 &&
    mtFiber44RowCheck 54 &&
    mtFiber44RowCheck 55 &&
    mtFiber44RowCheck 56 &&
    mtFiber44RowCheck 57 &&
    mtFiber44RowCheck 58 &&
    mtFiber44RowCheck 59 &&
    mtFiber44RowCheck 60 &&
    mtFiber44RowCheck 61 &&
    mtFiber44RowCheck 62 &&
    mtFiber44RowCheck 63 &&
    mtFiber44ParentCheck 0 &&
    mtFiber44ParentCheck 1 &&
    mtFiber44ParentCheck 2 &&
    mtFiber44ParentCheck 3 &&
    mtFiber44ParentCheck 4 &&
    mtFiber44ParentCheck 5 &&
    mtFiber44ParentCheck 6 &&
    mtFiber44ParentCheck 7 &&
    mtFiber44ParentCheck 8 &&
    mtFiber44ParentCheck 9 &&
    mtFiber44ParentCheck 10 &&
    mtFiber44ParentCheck 11 &&
    mtFiber44ParentCheck 12 &&
    mtFiber44ParentCheck 13 &&
    mtFiber44ParentCheck 14 &&
    mtFiber44ParentCheck 15 &&
    mtFiber44ParentCheck 16 &&
    mtFiber44ParentCheck 17 &&
    mtFiber44ParentCheck 18 &&
    mtFiber44ParentCheck 19 &&
    mtFiber44ParentCheck 20 &&
    mtFiber44ParentCheck 21 &&
    mtFiber44ParentCheck 22 &&
    mtFiber44ParentCheck 23 &&
    mtFiber44ParentCheck 24 &&
    mtFiber44ParentCheck 25 &&
    mtFiber44ParentCheck 26 &&
    mtFiber44ParentCheck 27 &&
    mtFiber44ParentCheck 28 &&
    mtFiber44ParentCheck 29 &&
    mtFiber44ParentCheck 30 &&
    mtFiber44ParentCheck 31 &&
    mtFiber44ParentCheck 32 &&
    mtFiber44ParentCheck 33 &&
    mtFiber44ParentCheck 34 &&
    mtFiber44ParentCheck 35 &&
    mtFiber44ParentCheck 36 &&
    mtFiber44ParentCheck 37 &&
    mtFiber44ParentCheck 38 &&
    mtFiber44ParentCheck 39 &&
    mtFiber44ParentCheck 40 &&
    mtFiber44ParentCheck 41 &&
    mtFiber44ParentCheck 42 &&
    mtFiber44ParentCheck 43 &&
    mtFiber44ParentCheck 44 &&
    mtFiber44ParentCheck 45 &&
    mtFiber44ParentCheck 46 &&
    mtFiber44ParentCheck 47 &&
    mtFiber44ParentCheck 48 &&
    mtFiber44ParentCheck 49 &&
    mtFiber44ParentCheck 50 &&
    mtFiber44ParentCheck 51 &&
    mtFiber44ParentCheck 52 &&
    mtFiber44ParentCheck 53 &&
    mtFiber44ParentCheck 54 &&
    mtFiber44ParentCheck 55 &&
    mtFiber44ParentCheck 56 &&
    mtFiber44ParentCheck 57 &&
    mtFiber44ParentCheck 58 &&
    mtFiber44ParentCheck 59 &&
    mtFiber44ParentCheck 60 &&
    mtFiber44ParentCheck 61 &&
    mtFiber44ParentCheck 62 &&
    mtFiber44ParentCheck 63

theorem mtFiber44CertificateAudit_ok :
    mtFiber44CertificateAudit = true := by
  simp [mtFiber44CertificateAudit,
    mtFiber44SourcesCheck_ok,
    mtFiber44Row_0_ok,
    mtFiber44Row_1_ok,
    mtFiber44Row_2_ok,
    mtFiber44Row_3_ok,
    mtFiber44Row_4_ok,
    mtFiber44Row_5_ok,
    mtFiber44Row_6_ok,
    mtFiber44Row_7_ok,
    mtFiber44Row_8_ok,
    mtFiber44Row_9_ok,
    mtFiber44Row_10_ok,
    mtFiber44Row_11_ok,
    mtFiber44Row_12_ok,
    mtFiber44Row_13_ok,
    mtFiber44Row_14_ok,
    mtFiber44Row_15_ok,
    mtFiber44Row_16_ok,
    mtFiber44Row_17_ok,
    mtFiber44Row_18_ok,
    mtFiber44Row_19_ok,
    mtFiber44Row_20_ok,
    mtFiber44Row_21_ok,
    mtFiber44Row_22_ok,
    mtFiber44Row_23_ok,
    mtFiber44Row_24_ok,
    mtFiber44Row_25_ok,
    mtFiber44Row_26_ok,
    mtFiber44Row_27_ok,
    mtFiber44Row_28_ok,
    mtFiber44Row_29_ok,
    mtFiber44Row_30_ok,
    mtFiber44Row_31_ok,
    mtFiber44Row_32_ok,
    mtFiber44Row_33_ok,
    mtFiber44Row_34_ok,
    mtFiber44Row_35_ok,
    mtFiber44Row_36_ok,
    mtFiber44Row_37_ok,
    mtFiber44Row_38_ok,
    mtFiber44Row_39_ok,
    mtFiber44Row_40_ok,
    mtFiber44Row_41_ok,
    mtFiber44Row_42_ok,
    mtFiber44Row_43_ok,
    mtFiber44Row_44_ok,
    mtFiber44Row_45_ok,
    mtFiber44Row_46_ok,
    mtFiber44Row_47_ok,
    mtFiber44Row_48_ok,
    mtFiber44Row_49_ok,
    mtFiber44Row_50_ok,
    mtFiber44Row_51_ok,
    mtFiber44Row_52_ok,
    mtFiber44Row_53_ok,
    mtFiber44Row_54_ok,
    mtFiber44Row_55_ok,
    mtFiber44Row_56_ok,
    mtFiber44Row_57_ok,
    mtFiber44Row_58_ok,
    mtFiber44Row_59_ok,
    mtFiber44Row_60_ok,
    mtFiber44Row_61_ok,
    mtFiber44Row_62_ok,
    mtFiber44Row_63_ok,
    mtFiber44Parent_0_ok,
    mtFiber44Parent_1_ok,
    mtFiber44Parent_2_ok,
    mtFiber44Parent_3_ok,
    mtFiber44Parent_4_ok,
    mtFiber44Parent_5_ok,
    mtFiber44Parent_6_ok,
    mtFiber44Parent_7_ok,
    mtFiber44Parent_8_ok,
    mtFiber44Parent_9_ok,
    mtFiber44Parent_10_ok,
    mtFiber44Parent_11_ok,
    mtFiber44Parent_12_ok,
    mtFiber44Parent_13_ok,
    mtFiber44Parent_14_ok,
    mtFiber44Parent_15_ok,
    mtFiber44Parent_16_ok,
    mtFiber44Parent_17_ok,
    mtFiber44Parent_18_ok,
    mtFiber44Parent_19_ok,
    mtFiber44Parent_20_ok,
    mtFiber44Parent_21_ok,
    mtFiber44Parent_22_ok,
    mtFiber44Parent_23_ok,
    mtFiber44Parent_24_ok,
    mtFiber44Parent_25_ok,
    mtFiber44Parent_26_ok,
    mtFiber44Parent_27_ok,
    mtFiber44Parent_28_ok,
    mtFiber44Parent_29_ok,
    mtFiber44Parent_30_ok,
    mtFiber44Parent_31_ok,
    mtFiber44Parent_32_ok,
    mtFiber44Parent_33_ok,
    mtFiber44Parent_34_ok,
    mtFiber44Parent_35_ok,
    mtFiber44Parent_36_ok,
    mtFiber44Parent_37_ok,
    mtFiber44Parent_38_ok,
    mtFiber44Parent_39_ok,
    mtFiber44Parent_40_ok,
    mtFiber44Parent_41_ok,
    mtFiber44Parent_42_ok,
    mtFiber44Parent_43_ok,
    mtFiber44Parent_44_ok,
    mtFiber44Parent_45_ok,
    mtFiber44Parent_46_ok,
    mtFiber44Parent_47_ok,
    mtFiber44Parent_48_ok,
    mtFiber44Parent_49_ok,
    mtFiber44Parent_50_ok,
    mtFiber44Parent_51_ok,
    mtFiber44Parent_52_ok,
    mtFiber44Parent_53_ok,
    mtFiber44Parent_54_ok,
    mtFiber44Parent_55_ok,
    mtFiber44Parent_56_ok,
    mtFiber44Parent_57_ok,
    mtFiber44Parent_58_ok,
    mtFiber44Parent_59_ok,
    mtFiber44Parent_60_ok,
    mtFiber44Parent_61_ok,
    mtFiber44Parent_62_ok,
    mtFiber44Parent_63_ok]

def mtFiber45Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.r]

def mtFiber45Expected : List Nat :=
  [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]

def mtFiber45Rows : List DirectChainParentRow :=
  [ directRow 768 768 128 92 128 92 default
  , directRow 769 768 128 93 128 92 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 770 768 128 94 128 92 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 771 769 128 95 128 93 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 772 768 129 84 128 92 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 773 769 129 85 128 93 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 774 770 129 86 128 94 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 775 771 129 87 128 95 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 776 772 130 76 129 84 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 777 773 130 77 129 85 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 778 774 130 78 129 86 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 779 775 130 79 129 87 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 780 768 131 68 128 92 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 781 769 131 69 128 93 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 782 770 131 70 128 94 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 783 771 131 71 128 95 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber45RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber45Rows i default

def mtFiber45SourcesCheck : Bool :=
  (mtFiber45Rows.map fun row => row.source) == mtFiber45Expected

theorem mtFiber45SourcesCheck_ok :
    mtFiber45SourcesCheck = true := by
  decide

def mtFiber45RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt i)

theorem mtFiber45Row_0_ok : mtFiber45RowCheck 0 = true := by decide
theorem mtFiber45Row_1_ok : mtFiber45RowCheck 1 = true := by decide
theorem mtFiber45Row_2_ok : mtFiber45RowCheck 2 = true := by decide
theorem mtFiber45Row_3_ok : mtFiber45RowCheck 3 = true := by decide
theorem mtFiber45Row_4_ok : mtFiber45RowCheck 4 = true := by decide
theorem mtFiber45Row_5_ok : mtFiber45RowCheck 5 = true := by decide
theorem mtFiber45Row_6_ok : mtFiber45RowCheck 6 = true := by decide
theorem mtFiber45Row_7_ok : mtFiber45RowCheck 7 = true := by decide
theorem mtFiber45Row_8_ok : mtFiber45RowCheck 8 = true := by decide
theorem mtFiber45Row_9_ok : mtFiber45RowCheck 9 = true := by decide
theorem mtFiber45Row_10_ok : mtFiber45RowCheck 10 = true := by decide
theorem mtFiber45Row_11_ok : mtFiber45RowCheck 11 = true := by decide
theorem mtFiber45Row_12_ok : mtFiber45RowCheck 12 = true := by decide
theorem mtFiber45Row_13_ok : mtFiber45RowCheck 13 = true := by decide
theorem mtFiber45Row_14_ok : mtFiber45RowCheck 14 = true := by decide
theorem mtFiber45Row_15_ok : mtFiber45RowCheck 15 = true := by decide

def mtFiber45ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber45Rows mtMaxParentDepth (listGetD mtFiber45Expected i 0) == 768

theorem mtFiber45Parent_0_ok : mtFiber45ParentCheck 0 = true := by decide
theorem mtFiber45Parent_1_ok : mtFiber45ParentCheck 1 = true := by decide
theorem mtFiber45Parent_2_ok : mtFiber45ParentCheck 2 = true := by decide
theorem mtFiber45Parent_3_ok : mtFiber45ParentCheck 3 = true := by decide
theorem mtFiber45Parent_4_ok : mtFiber45ParentCheck 4 = true := by decide
theorem mtFiber45Parent_5_ok : mtFiber45ParentCheck 5 = true := by decide
theorem mtFiber45Parent_6_ok : mtFiber45ParentCheck 6 = true := by decide
theorem mtFiber45Parent_7_ok : mtFiber45ParentCheck 7 = true := by decide
theorem mtFiber45Parent_8_ok : mtFiber45ParentCheck 8 = true := by decide
theorem mtFiber45Parent_9_ok : mtFiber45ParentCheck 9 = true := by decide
theorem mtFiber45Parent_10_ok : mtFiber45ParentCheck 10 = true := by decide
theorem mtFiber45Parent_11_ok : mtFiber45ParentCheck 11 = true := by decide
theorem mtFiber45Parent_12_ok : mtFiber45ParentCheck 12 = true := by decide
theorem mtFiber45Parent_13_ok : mtFiber45ParentCheck 13 = true := by decide
theorem mtFiber45Parent_14_ok : mtFiber45ParentCheck 14 = true := by decide
theorem mtFiber45Parent_15_ok : mtFiber45ParentCheck 15 = true := by decide

def mtFiber45CertificateAudit : Bool :=
  mtFiber45SourcesCheck &&
    mtFiber45RowCheck 0 &&
    mtFiber45RowCheck 1 &&
    mtFiber45RowCheck 2 &&
    mtFiber45RowCheck 3 &&
    mtFiber45RowCheck 4 &&
    mtFiber45RowCheck 5 &&
    mtFiber45RowCheck 6 &&
    mtFiber45RowCheck 7 &&
    mtFiber45RowCheck 8 &&
    mtFiber45RowCheck 9 &&
    mtFiber45RowCheck 10 &&
    mtFiber45RowCheck 11 &&
    mtFiber45RowCheck 12 &&
    mtFiber45RowCheck 13 &&
    mtFiber45RowCheck 14 &&
    mtFiber45RowCheck 15 &&
    mtFiber45ParentCheck 0 &&
    mtFiber45ParentCheck 1 &&
    mtFiber45ParentCheck 2 &&
    mtFiber45ParentCheck 3 &&
    mtFiber45ParentCheck 4 &&
    mtFiber45ParentCheck 5 &&
    mtFiber45ParentCheck 6 &&
    mtFiber45ParentCheck 7 &&
    mtFiber45ParentCheck 8 &&
    mtFiber45ParentCheck 9 &&
    mtFiber45ParentCheck 10 &&
    mtFiber45ParentCheck 11 &&
    mtFiber45ParentCheck 12 &&
    mtFiber45ParentCheck 13 &&
    mtFiber45ParentCheck 14 &&
    mtFiber45ParentCheck 15

theorem mtFiber45CertificateAudit_ok :
    mtFiber45CertificateAudit = true := by
  simp [mtFiber45CertificateAudit,
    mtFiber45SourcesCheck_ok,
    mtFiber45Row_0_ok,
    mtFiber45Row_1_ok,
    mtFiber45Row_2_ok,
    mtFiber45Row_3_ok,
    mtFiber45Row_4_ok,
    mtFiber45Row_5_ok,
    mtFiber45Row_6_ok,
    mtFiber45Row_7_ok,
    mtFiber45Row_8_ok,
    mtFiber45Row_9_ok,
    mtFiber45Row_10_ok,
    mtFiber45Row_11_ok,
    mtFiber45Row_12_ok,
    mtFiber45Row_13_ok,
    mtFiber45Row_14_ok,
    mtFiber45Row_15_ok,
    mtFiber45Parent_0_ok,
    mtFiber45Parent_1_ok,
    mtFiber45Parent_2_ok,
    mtFiber45Parent_3_ok,
    mtFiber45Parent_4_ok,
    mtFiber45Parent_5_ok,
    mtFiber45Parent_6_ok,
    mtFiber45Parent_7_ok,
    mtFiber45Parent_8_ok,
    mtFiber45Parent_9_ok,
    mtFiber45Parent_10_ok,
    mtFiber45Parent_11_ok,
    mtFiber45Parent_12_ok,
    mtFiber45Parent_13_ok,
    mtFiber45Parent_14_ok,
    mtFiber45Parent_15_ok]

def mtFiber46Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.b]

def mtFiber46Expected : List Nat :=
  []

def mtFiber46Rows : List DirectChainParentRow :=
  []

def mtFiber46RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber46Rows i default

def mtFiber46SourcesCheck : Bool :=
  (mtFiber46Rows.map fun row => row.source) == mtFiber46Expected

theorem mtFiber46SourcesCheck_ok :
    mtFiber46SourcesCheck = true := by
  decide

def mtFiber46RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber46Key mtFiber46Expected (mtFiber46RowAt i)

def mtFiber46ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber46Rows mtMaxParentDepth (listGetD mtFiber46Expected i 0) == 0

def mtFiber46CertificateAudit : Bool :=
  mtFiber46SourcesCheck

theorem mtFiber46CertificateAudit_ok :
    mtFiber46CertificateAudit = true := by
  simp [mtFiber46CertificateAudit,
    mtFiber46SourcesCheck_ok]

def mtFiber47Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.p]

def mtFiber47Expected : List Nat :=
  [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]

def mtFiber47Rows : List DirectChainParentRow :=
  [ directRow 224 224 36 104 36 104 default
  , directRow 225 224 36 105 36 104 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 226 224 36 106 36 104 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 227 225 36 107 36 105 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 228 224 37 96 36 104 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 229 225 37 97 36 105 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 230 226 37 98 36 106 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 231 227 37 99 36 107 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 232 228 38 120 37 96 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 233 229 38 121 37 97 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 234 230 38 122 37 98 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 235 231 38 123 37 99 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 236 224 39 112 36 104 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 237 225 39 113 36 105 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 238 226 39 114 36 106 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 239 227 39 115 36 107 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber47RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber47Rows i default

def mtFiber47SourcesCheck : Bool :=
  (mtFiber47Rows.map fun row => row.source) == mtFiber47Expected

theorem mtFiber47SourcesCheck_ok :
    mtFiber47SourcesCheck = true := by
  decide

def mtFiber47RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt i)

theorem mtFiber47Row_0_ok : mtFiber47RowCheck 0 = true := by decide
theorem mtFiber47Row_1_ok : mtFiber47RowCheck 1 = true := by decide
theorem mtFiber47Row_2_ok : mtFiber47RowCheck 2 = true := by decide
theorem mtFiber47Row_3_ok : mtFiber47RowCheck 3 = true := by decide
theorem mtFiber47Row_4_ok : mtFiber47RowCheck 4 = true := by decide
theorem mtFiber47Row_5_ok : mtFiber47RowCheck 5 = true := by decide
theorem mtFiber47Row_6_ok : mtFiber47RowCheck 6 = true := by decide
theorem mtFiber47Row_7_ok : mtFiber47RowCheck 7 = true := by decide
theorem mtFiber47Row_8_ok : mtFiber47RowCheck 8 = true := by decide
theorem mtFiber47Row_9_ok : mtFiber47RowCheck 9 = true := by decide
theorem mtFiber47Row_10_ok : mtFiber47RowCheck 10 = true := by decide
theorem mtFiber47Row_11_ok : mtFiber47RowCheck 11 = true := by decide
theorem mtFiber47Row_12_ok : mtFiber47RowCheck 12 = true := by decide
theorem mtFiber47Row_13_ok : mtFiber47RowCheck 13 = true := by decide
theorem mtFiber47Row_14_ok : mtFiber47RowCheck 14 = true := by decide
theorem mtFiber47Row_15_ok : mtFiber47RowCheck 15 = true := by decide

def mtFiber47ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber47Rows mtMaxParentDepth (listGetD mtFiber47Expected i 0) == 224

theorem mtFiber47Parent_0_ok : mtFiber47ParentCheck 0 = true := by decide
theorem mtFiber47Parent_1_ok : mtFiber47ParentCheck 1 = true := by decide
theorem mtFiber47Parent_2_ok : mtFiber47ParentCheck 2 = true := by decide
theorem mtFiber47Parent_3_ok : mtFiber47ParentCheck 3 = true := by decide
theorem mtFiber47Parent_4_ok : mtFiber47ParentCheck 4 = true := by decide
theorem mtFiber47Parent_5_ok : mtFiber47ParentCheck 5 = true := by decide
theorem mtFiber47Parent_6_ok : mtFiber47ParentCheck 6 = true := by decide
theorem mtFiber47Parent_7_ok : mtFiber47ParentCheck 7 = true := by decide
theorem mtFiber47Parent_8_ok : mtFiber47ParentCheck 8 = true := by decide
theorem mtFiber47Parent_9_ok : mtFiber47ParentCheck 9 = true := by decide
theorem mtFiber47Parent_10_ok : mtFiber47ParentCheck 10 = true := by decide
theorem mtFiber47Parent_11_ok : mtFiber47ParentCheck 11 = true := by decide
theorem mtFiber47Parent_12_ok : mtFiber47ParentCheck 12 = true := by decide
theorem mtFiber47Parent_13_ok : mtFiber47ParentCheck 13 = true := by decide
theorem mtFiber47Parent_14_ok : mtFiber47ParentCheck 14 = true := by decide
theorem mtFiber47Parent_15_ok : mtFiber47ParentCheck 15 = true := by decide

def mtFiber47CertificateAudit : Bool :=
  mtFiber47SourcesCheck &&
    mtFiber47RowCheck 0 &&
    mtFiber47RowCheck 1 &&
    mtFiber47RowCheck 2 &&
    mtFiber47RowCheck 3 &&
    mtFiber47RowCheck 4 &&
    mtFiber47RowCheck 5 &&
    mtFiber47RowCheck 6 &&
    mtFiber47RowCheck 7 &&
    mtFiber47RowCheck 8 &&
    mtFiber47RowCheck 9 &&
    mtFiber47RowCheck 10 &&
    mtFiber47RowCheck 11 &&
    mtFiber47RowCheck 12 &&
    mtFiber47RowCheck 13 &&
    mtFiber47RowCheck 14 &&
    mtFiber47RowCheck 15 &&
    mtFiber47ParentCheck 0 &&
    mtFiber47ParentCheck 1 &&
    mtFiber47ParentCheck 2 &&
    mtFiber47ParentCheck 3 &&
    mtFiber47ParentCheck 4 &&
    mtFiber47ParentCheck 5 &&
    mtFiber47ParentCheck 6 &&
    mtFiber47ParentCheck 7 &&
    mtFiber47ParentCheck 8 &&
    mtFiber47ParentCheck 9 &&
    mtFiber47ParentCheck 10 &&
    mtFiber47ParentCheck 11 &&
    mtFiber47ParentCheck 12 &&
    mtFiber47ParentCheck 13 &&
    mtFiber47ParentCheck 14 &&
    mtFiber47ParentCheck 15

theorem mtFiber47CertificateAudit_ok :
    mtFiber47CertificateAudit = true := by
  simp [mtFiber47CertificateAudit,
    mtFiber47SourcesCheck_ok,
    mtFiber47Row_0_ok,
    mtFiber47Row_1_ok,
    mtFiber47Row_2_ok,
    mtFiber47Row_3_ok,
    mtFiber47Row_4_ok,
    mtFiber47Row_5_ok,
    mtFiber47Row_6_ok,
    mtFiber47Row_7_ok,
    mtFiber47Row_8_ok,
    mtFiber47Row_9_ok,
    mtFiber47Row_10_ok,
    mtFiber47Row_11_ok,
    mtFiber47Row_12_ok,
    mtFiber47Row_13_ok,
    mtFiber47Row_14_ok,
    mtFiber47Row_15_ok,
    mtFiber47Parent_0_ok,
    mtFiber47Parent_1_ok,
    mtFiber47Parent_2_ok,
    mtFiber47Parent_3_ok,
    mtFiber47Parent_4_ok,
    mtFiber47Parent_5_ok,
    mtFiber47Parent_6_ok,
    mtFiber47Parent_7_ok,
    mtFiber47Parent_8_ok,
    mtFiber47Parent_9_ok,
    mtFiber47Parent_10_ok,
    mtFiber47Parent_11_ok,
    mtFiber47Parent_12_ok,
    mtFiber47Parent_13_ok,
    mtFiber47Parent_14_ok,
    mtFiber47Parent_15_ok]

def mtFiber48Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.r]

def mtFiber48Expected : List Nat :=
  []

def mtFiber48Rows : List DirectChainParentRow :=
  []

def mtFiber48RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber48Rows i default

def mtFiber48SourcesCheck : Bool :=
  (mtFiber48Rows.map fun row => row.source) == mtFiber48Expected

theorem mtFiber48SourcesCheck_ok :
    mtFiber48SourcesCheck = true := by
  decide

def mtFiber48RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber48Key mtFiber48Expected (mtFiber48RowAt i)

def mtFiber48ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber48Rows mtMaxParentDepth (listGetD mtFiber48Expected i 0) == 0

def mtFiber48CertificateAudit : Bool :=
  mtFiber48SourcesCheck

theorem mtFiber48CertificateAudit_ok :
    mtFiber48CertificateAudit = true := by
  simp [mtFiber48CertificateAudit,
    mtFiber48SourcesCheck_ok]

def mtFiber49Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.b]

def mtFiber49Expected : List Nat :=
  [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]

def mtFiber49Rows : List DirectChainParentRow :=
  [ directRow 864 864 144 92 144 92 default
  , directRow 865 864 144 93 144 92 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 866 864 144 94 144 92 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 867 865 144 95 144 93 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 868 864 145 84 144 92 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 869 865 145 85 144 93 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 870 866 145 86 144 94 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 871 867 145 87 144 95 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 872 868 146 76 145 84 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 873 869 146 77 145 85 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 874 870 146 78 145 86 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 875 871 146 79 145 87 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 876 864 147 68 144 92 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 877 865 147 69 144 93 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 878 866 147 70 144 94 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 879 867 147 71 144 95 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mtFiber49RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber49Rows i default

def mtFiber49SourcesCheck : Bool :=
  (mtFiber49Rows.map fun row => row.source) == mtFiber49Expected

theorem mtFiber49SourcesCheck_ok :
    mtFiber49SourcesCheck = true := by
  decide

def mtFiber49RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt i)

theorem mtFiber49Row_0_ok : mtFiber49RowCheck 0 = true := by decide
theorem mtFiber49Row_1_ok : mtFiber49RowCheck 1 = true := by decide
theorem mtFiber49Row_2_ok : mtFiber49RowCheck 2 = true := by decide
theorem mtFiber49Row_3_ok : mtFiber49RowCheck 3 = true := by decide
theorem mtFiber49Row_4_ok : mtFiber49RowCheck 4 = true := by decide
theorem mtFiber49Row_5_ok : mtFiber49RowCheck 5 = true := by decide
theorem mtFiber49Row_6_ok : mtFiber49RowCheck 6 = true := by decide
theorem mtFiber49Row_7_ok : mtFiber49RowCheck 7 = true := by decide
theorem mtFiber49Row_8_ok : mtFiber49RowCheck 8 = true := by decide
theorem mtFiber49Row_9_ok : mtFiber49RowCheck 9 = true := by decide
theorem mtFiber49Row_10_ok : mtFiber49RowCheck 10 = true := by decide
theorem mtFiber49Row_11_ok : mtFiber49RowCheck 11 = true := by decide
theorem mtFiber49Row_12_ok : mtFiber49RowCheck 12 = true := by decide
theorem mtFiber49Row_13_ok : mtFiber49RowCheck 13 = true := by decide
theorem mtFiber49Row_14_ok : mtFiber49RowCheck 14 = true := by decide
theorem mtFiber49Row_15_ok : mtFiber49RowCheck 15 = true := by decide

def mtFiber49ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber49Rows mtMaxParentDepth (listGetD mtFiber49Expected i 0) == 864

theorem mtFiber49Parent_0_ok : mtFiber49ParentCheck 0 = true := by decide
theorem mtFiber49Parent_1_ok : mtFiber49ParentCheck 1 = true := by decide
theorem mtFiber49Parent_2_ok : mtFiber49ParentCheck 2 = true := by decide
theorem mtFiber49Parent_3_ok : mtFiber49ParentCheck 3 = true := by decide
theorem mtFiber49Parent_4_ok : mtFiber49ParentCheck 4 = true := by decide
theorem mtFiber49Parent_5_ok : mtFiber49ParentCheck 5 = true := by decide
theorem mtFiber49Parent_6_ok : mtFiber49ParentCheck 6 = true := by decide
theorem mtFiber49Parent_7_ok : mtFiber49ParentCheck 7 = true := by decide
theorem mtFiber49Parent_8_ok : mtFiber49ParentCheck 8 = true := by decide
theorem mtFiber49Parent_9_ok : mtFiber49ParentCheck 9 = true := by decide
theorem mtFiber49Parent_10_ok : mtFiber49ParentCheck 10 = true := by decide
theorem mtFiber49Parent_11_ok : mtFiber49ParentCheck 11 = true := by decide
theorem mtFiber49Parent_12_ok : mtFiber49ParentCheck 12 = true := by decide
theorem mtFiber49Parent_13_ok : mtFiber49ParentCheck 13 = true := by decide
theorem mtFiber49Parent_14_ok : mtFiber49ParentCheck 14 = true := by decide
theorem mtFiber49Parent_15_ok : mtFiber49ParentCheck 15 = true := by decide

def mtFiber49CertificateAudit : Bool :=
  mtFiber49SourcesCheck &&
    mtFiber49RowCheck 0 &&
    mtFiber49RowCheck 1 &&
    mtFiber49RowCheck 2 &&
    mtFiber49RowCheck 3 &&
    mtFiber49RowCheck 4 &&
    mtFiber49RowCheck 5 &&
    mtFiber49RowCheck 6 &&
    mtFiber49RowCheck 7 &&
    mtFiber49RowCheck 8 &&
    mtFiber49RowCheck 9 &&
    mtFiber49RowCheck 10 &&
    mtFiber49RowCheck 11 &&
    mtFiber49RowCheck 12 &&
    mtFiber49RowCheck 13 &&
    mtFiber49RowCheck 14 &&
    mtFiber49RowCheck 15 &&
    mtFiber49ParentCheck 0 &&
    mtFiber49ParentCheck 1 &&
    mtFiber49ParentCheck 2 &&
    mtFiber49ParentCheck 3 &&
    mtFiber49ParentCheck 4 &&
    mtFiber49ParentCheck 5 &&
    mtFiber49ParentCheck 6 &&
    mtFiber49ParentCheck 7 &&
    mtFiber49ParentCheck 8 &&
    mtFiber49ParentCheck 9 &&
    mtFiber49ParentCheck 10 &&
    mtFiber49ParentCheck 11 &&
    mtFiber49ParentCheck 12 &&
    mtFiber49ParentCheck 13 &&
    mtFiber49ParentCheck 14 &&
    mtFiber49ParentCheck 15

theorem mtFiber49CertificateAudit_ok :
    mtFiber49CertificateAudit = true := by
  simp [mtFiber49CertificateAudit,
    mtFiber49SourcesCheck_ok,
    mtFiber49Row_0_ok,
    mtFiber49Row_1_ok,
    mtFiber49Row_2_ok,
    mtFiber49Row_3_ok,
    mtFiber49Row_4_ok,
    mtFiber49Row_5_ok,
    mtFiber49Row_6_ok,
    mtFiber49Row_7_ok,
    mtFiber49Row_8_ok,
    mtFiber49Row_9_ok,
    mtFiber49Row_10_ok,
    mtFiber49Row_11_ok,
    mtFiber49Row_12_ok,
    mtFiber49Row_13_ok,
    mtFiber49Row_14_ok,
    mtFiber49Row_15_ok,
    mtFiber49Parent_0_ok,
    mtFiber49Parent_1_ok,
    mtFiber49Parent_2_ok,
    mtFiber49Parent_3_ok,
    mtFiber49Parent_4_ok,
    mtFiber49Parent_5_ok,
    mtFiber49Parent_6_ok,
    mtFiber49Parent_7_ok,
    mtFiber49Parent_8_ok,
    mtFiber49Parent_9_ok,
    mtFiber49Parent_10_ok,
    mtFiber49Parent_11_ok,
    mtFiber49Parent_12_ok,
    mtFiber49Parent_13_ok,
    mtFiber49Parent_14_ok,
    mtFiber49Parent_15_ok]

def mtFiber50Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.p]

def mtFiber50Expected : List Nat :=
  [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]

def mtFiber50Rows : List DirectChainParentRow :=
  [ directRow 480 480 80 156 80 156 default
  , directRow 481 480 80 157 80 156 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 482 481 80 158 80 157 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 483 480 80 159 80 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 484 480 80 172 80 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 485 481 80 173 80 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 486 484 80 174 80 172 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 487 483 80 175 80 159 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 488 480 81 148 80 156 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 489 481 81 149 80 157 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 490 482 81 150 80 158 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 491 483 81 151 80 159 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 492 484 81 164 80 172 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 493 485 81 165 80 173 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 494 486 81 166 80 174 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 495 487 81 167 80 175 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 496 480 82 140 80 156 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 497 481 82 141 80 157 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 498 482 82 142 80 158 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 499 483 82 143 80 159 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 500 484 82 188 80 172 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 501 485 82 189 80 173 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 502 486 82 190 80 174 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 503 487 82 191 80 175 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 504 488 83 132 81 148 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 505 489 83 133 81 149 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 506 490 83 134 81 150 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 507 491 83 135 81 151 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 508 492 83 180 81 164 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 509 493 83 181 81 165 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 510 494 83 182 81 166 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 511 495 83 183 81 167 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 592 596 100 24 100 40 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 593 597 100 25 100 41 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 594 500 100 26 82 188 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 595 501 100 27 82 189 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 596 496 100 40 82 140 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 597 497 100 41 82 141 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 598 498 100 42 82 142 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 599 499 100 43 82 143 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 600 604 101 16 101 32 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 601 605 101 17 101 33 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 602 618 101 18 103 2 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 603 619 101 19 103 3 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 604 620 101 32 103 48 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 605 621 101 33 103 49 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 606 622 101 34 103 50 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 607 623 101 35 103 51 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 608 612 102 8 102 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 609 613 102 9 102 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 610 492 102 10 81 164 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 611 493 102 11 81 165 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 612 488 102 56 81 148 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 613 489 102 57 81 149 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 614 490 102 58 81 150 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 615 491 102 59 81 151 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 616 620 103 0 103 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 617 621 103 1 103 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 618 484 103 2 80 172 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 619 485 103 3 80 173 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 620 480 103 48 80 156 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 621 481 103 49 80 157 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 622 482 103 50 80 158 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 623 483 103 51 80 159 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mtFiber50RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber50Rows i default

def mtFiber50SourcesCheck : Bool :=
  (mtFiber50Rows.map fun row => row.source) == mtFiber50Expected

theorem mtFiber50SourcesCheck_ok :
    mtFiber50SourcesCheck = true := by
  decide

def mtFiber50RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt i)

theorem mtFiber50Row_0_ok : mtFiber50RowCheck 0 = true := by decide
theorem mtFiber50Row_1_ok : mtFiber50RowCheck 1 = true := by decide
theorem mtFiber50Row_2_ok : mtFiber50RowCheck 2 = true := by decide
theorem mtFiber50Row_3_ok : mtFiber50RowCheck 3 = true := by decide
theorem mtFiber50Row_4_ok : mtFiber50RowCheck 4 = true := by decide
theorem mtFiber50Row_5_ok : mtFiber50RowCheck 5 = true := by decide
theorem mtFiber50Row_6_ok : mtFiber50RowCheck 6 = true := by decide
theorem mtFiber50Row_7_ok : mtFiber50RowCheck 7 = true := by decide
theorem mtFiber50Row_8_ok : mtFiber50RowCheck 8 = true := by decide
theorem mtFiber50Row_9_ok : mtFiber50RowCheck 9 = true := by decide
theorem mtFiber50Row_10_ok : mtFiber50RowCheck 10 = true := by decide
theorem mtFiber50Row_11_ok : mtFiber50RowCheck 11 = true := by decide
theorem mtFiber50Row_12_ok : mtFiber50RowCheck 12 = true := by decide
theorem mtFiber50Row_13_ok : mtFiber50RowCheck 13 = true := by decide
theorem mtFiber50Row_14_ok : mtFiber50RowCheck 14 = true := by decide
theorem mtFiber50Row_15_ok : mtFiber50RowCheck 15 = true := by decide
theorem mtFiber50Row_16_ok : mtFiber50RowCheck 16 = true := by decide
theorem mtFiber50Row_17_ok : mtFiber50RowCheck 17 = true := by decide
theorem mtFiber50Row_18_ok : mtFiber50RowCheck 18 = true := by decide
theorem mtFiber50Row_19_ok : mtFiber50RowCheck 19 = true := by decide
theorem mtFiber50Row_20_ok : mtFiber50RowCheck 20 = true := by decide
theorem mtFiber50Row_21_ok : mtFiber50RowCheck 21 = true := by decide
theorem mtFiber50Row_22_ok : mtFiber50RowCheck 22 = true := by decide
theorem mtFiber50Row_23_ok : mtFiber50RowCheck 23 = true := by decide
theorem mtFiber50Row_24_ok : mtFiber50RowCheck 24 = true := by decide
theorem mtFiber50Row_25_ok : mtFiber50RowCheck 25 = true := by decide
theorem mtFiber50Row_26_ok : mtFiber50RowCheck 26 = true := by decide
theorem mtFiber50Row_27_ok : mtFiber50RowCheck 27 = true := by decide
theorem mtFiber50Row_28_ok : mtFiber50RowCheck 28 = true := by decide
theorem mtFiber50Row_29_ok : mtFiber50RowCheck 29 = true := by decide
theorem mtFiber50Row_30_ok : mtFiber50RowCheck 30 = true := by decide
theorem mtFiber50Row_31_ok : mtFiber50RowCheck 31 = true := by decide
theorem mtFiber50Row_32_ok : mtFiber50RowCheck 32 = true := by decide
theorem mtFiber50Row_33_ok : mtFiber50RowCheck 33 = true := by decide
theorem mtFiber50Row_34_ok : mtFiber50RowCheck 34 = true := by decide
theorem mtFiber50Row_35_ok : mtFiber50RowCheck 35 = true := by decide
theorem mtFiber50Row_36_ok : mtFiber50RowCheck 36 = true := by decide
theorem mtFiber50Row_37_ok : mtFiber50RowCheck 37 = true := by decide
theorem mtFiber50Row_38_ok : mtFiber50RowCheck 38 = true := by decide
theorem mtFiber50Row_39_ok : mtFiber50RowCheck 39 = true := by decide
theorem mtFiber50Row_40_ok : mtFiber50RowCheck 40 = true := by decide
theorem mtFiber50Row_41_ok : mtFiber50RowCheck 41 = true := by decide
theorem mtFiber50Row_42_ok : mtFiber50RowCheck 42 = true := by decide
theorem mtFiber50Row_43_ok : mtFiber50RowCheck 43 = true := by decide
theorem mtFiber50Row_44_ok : mtFiber50RowCheck 44 = true := by decide
theorem mtFiber50Row_45_ok : mtFiber50RowCheck 45 = true := by decide
theorem mtFiber50Row_46_ok : mtFiber50RowCheck 46 = true := by decide
theorem mtFiber50Row_47_ok : mtFiber50RowCheck 47 = true := by decide
theorem mtFiber50Row_48_ok : mtFiber50RowCheck 48 = true := by decide
theorem mtFiber50Row_49_ok : mtFiber50RowCheck 49 = true := by decide
theorem mtFiber50Row_50_ok : mtFiber50RowCheck 50 = true := by decide
theorem mtFiber50Row_51_ok : mtFiber50RowCheck 51 = true := by decide
theorem mtFiber50Row_52_ok : mtFiber50RowCheck 52 = true := by decide
theorem mtFiber50Row_53_ok : mtFiber50RowCheck 53 = true := by decide
theorem mtFiber50Row_54_ok : mtFiber50RowCheck 54 = true := by decide
theorem mtFiber50Row_55_ok : mtFiber50RowCheck 55 = true := by decide
theorem mtFiber50Row_56_ok : mtFiber50RowCheck 56 = true := by decide
theorem mtFiber50Row_57_ok : mtFiber50RowCheck 57 = true := by decide
theorem mtFiber50Row_58_ok : mtFiber50RowCheck 58 = true := by decide
theorem mtFiber50Row_59_ok : mtFiber50RowCheck 59 = true := by decide
theorem mtFiber50Row_60_ok : mtFiber50RowCheck 60 = true := by decide
theorem mtFiber50Row_61_ok : mtFiber50RowCheck 61 = true := by decide
theorem mtFiber50Row_62_ok : mtFiber50RowCheck 62 = true := by decide
theorem mtFiber50Row_63_ok : mtFiber50RowCheck 63 = true := by decide

def mtFiber50ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber50Rows mtMaxParentDepth (listGetD mtFiber50Expected i 0) == 480

theorem mtFiber50Parent_0_ok : mtFiber50ParentCheck 0 = true := by decide
theorem mtFiber50Parent_1_ok : mtFiber50ParentCheck 1 = true := by decide
theorem mtFiber50Parent_2_ok : mtFiber50ParentCheck 2 = true := by decide
theorem mtFiber50Parent_3_ok : mtFiber50ParentCheck 3 = true := by decide
theorem mtFiber50Parent_4_ok : mtFiber50ParentCheck 4 = true := by decide
theorem mtFiber50Parent_5_ok : mtFiber50ParentCheck 5 = true := by decide
theorem mtFiber50Parent_6_ok : mtFiber50ParentCheck 6 = true := by decide
theorem mtFiber50Parent_7_ok : mtFiber50ParentCheck 7 = true := by decide
theorem mtFiber50Parent_8_ok : mtFiber50ParentCheck 8 = true := by decide
theorem mtFiber50Parent_9_ok : mtFiber50ParentCheck 9 = true := by decide
theorem mtFiber50Parent_10_ok : mtFiber50ParentCheck 10 = true := by decide
theorem mtFiber50Parent_11_ok : mtFiber50ParentCheck 11 = true := by decide
theorem mtFiber50Parent_12_ok : mtFiber50ParentCheck 12 = true := by decide
theorem mtFiber50Parent_13_ok : mtFiber50ParentCheck 13 = true := by decide
theorem mtFiber50Parent_14_ok : mtFiber50ParentCheck 14 = true := by decide
theorem mtFiber50Parent_15_ok : mtFiber50ParentCheck 15 = true := by decide
theorem mtFiber50Parent_16_ok : mtFiber50ParentCheck 16 = true := by decide
theorem mtFiber50Parent_17_ok : mtFiber50ParentCheck 17 = true := by decide
theorem mtFiber50Parent_18_ok : mtFiber50ParentCheck 18 = true := by decide
theorem mtFiber50Parent_19_ok : mtFiber50ParentCheck 19 = true := by decide
theorem mtFiber50Parent_20_ok : mtFiber50ParentCheck 20 = true := by decide
theorem mtFiber50Parent_21_ok : mtFiber50ParentCheck 21 = true := by decide
theorem mtFiber50Parent_22_ok : mtFiber50ParentCheck 22 = true := by decide
theorem mtFiber50Parent_23_ok : mtFiber50ParentCheck 23 = true := by decide
theorem mtFiber50Parent_24_ok : mtFiber50ParentCheck 24 = true := by decide
theorem mtFiber50Parent_25_ok : mtFiber50ParentCheck 25 = true := by decide
theorem mtFiber50Parent_26_ok : mtFiber50ParentCheck 26 = true := by decide
theorem mtFiber50Parent_27_ok : mtFiber50ParentCheck 27 = true := by decide
theorem mtFiber50Parent_28_ok : mtFiber50ParentCheck 28 = true := by decide
theorem mtFiber50Parent_29_ok : mtFiber50ParentCheck 29 = true := by decide
theorem mtFiber50Parent_30_ok : mtFiber50ParentCheck 30 = true := by decide
theorem mtFiber50Parent_31_ok : mtFiber50ParentCheck 31 = true := by decide
theorem mtFiber50Parent_32_ok : mtFiber50ParentCheck 32 = true := by decide
theorem mtFiber50Parent_33_ok : mtFiber50ParentCheck 33 = true := by decide
theorem mtFiber50Parent_34_ok : mtFiber50ParentCheck 34 = true := by decide
theorem mtFiber50Parent_35_ok : mtFiber50ParentCheck 35 = true := by decide
theorem mtFiber50Parent_36_ok : mtFiber50ParentCheck 36 = true := by decide
theorem mtFiber50Parent_37_ok : mtFiber50ParentCheck 37 = true := by decide
theorem mtFiber50Parent_38_ok : mtFiber50ParentCheck 38 = true := by decide
theorem mtFiber50Parent_39_ok : mtFiber50ParentCheck 39 = true := by decide
theorem mtFiber50Parent_40_ok : mtFiber50ParentCheck 40 = true := by decide
theorem mtFiber50Parent_41_ok : mtFiber50ParentCheck 41 = true := by decide
theorem mtFiber50Parent_42_ok : mtFiber50ParentCheck 42 = true := by decide
theorem mtFiber50Parent_43_ok : mtFiber50ParentCheck 43 = true := by decide
theorem mtFiber50Parent_44_ok : mtFiber50ParentCheck 44 = true := by decide
theorem mtFiber50Parent_45_ok : mtFiber50ParentCheck 45 = true := by decide
theorem mtFiber50Parent_46_ok : mtFiber50ParentCheck 46 = true := by decide
theorem mtFiber50Parent_47_ok : mtFiber50ParentCheck 47 = true := by decide
theorem mtFiber50Parent_48_ok : mtFiber50ParentCheck 48 = true := by decide
theorem mtFiber50Parent_49_ok : mtFiber50ParentCheck 49 = true := by decide
theorem mtFiber50Parent_50_ok : mtFiber50ParentCheck 50 = true := by decide
theorem mtFiber50Parent_51_ok : mtFiber50ParentCheck 51 = true := by decide
theorem mtFiber50Parent_52_ok : mtFiber50ParentCheck 52 = true := by decide
theorem mtFiber50Parent_53_ok : mtFiber50ParentCheck 53 = true := by decide
theorem mtFiber50Parent_54_ok : mtFiber50ParentCheck 54 = true := by decide
theorem mtFiber50Parent_55_ok : mtFiber50ParentCheck 55 = true := by decide
theorem mtFiber50Parent_56_ok : mtFiber50ParentCheck 56 = true := by decide
theorem mtFiber50Parent_57_ok : mtFiber50ParentCheck 57 = true := by decide
theorem mtFiber50Parent_58_ok : mtFiber50ParentCheck 58 = true := by decide
theorem mtFiber50Parent_59_ok : mtFiber50ParentCheck 59 = true := by decide
theorem mtFiber50Parent_60_ok : mtFiber50ParentCheck 60 = true := by decide
theorem mtFiber50Parent_61_ok : mtFiber50ParentCheck 61 = true := by decide
theorem mtFiber50Parent_62_ok : mtFiber50ParentCheck 62 = true := by decide
theorem mtFiber50Parent_63_ok : mtFiber50ParentCheck 63 = true := by decide

def mtFiber50CertificateAudit : Bool :=
  mtFiber50SourcesCheck &&
    mtFiber50RowCheck 0 &&
    mtFiber50RowCheck 1 &&
    mtFiber50RowCheck 2 &&
    mtFiber50RowCheck 3 &&
    mtFiber50RowCheck 4 &&
    mtFiber50RowCheck 5 &&
    mtFiber50RowCheck 6 &&
    mtFiber50RowCheck 7 &&
    mtFiber50RowCheck 8 &&
    mtFiber50RowCheck 9 &&
    mtFiber50RowCheck 10 &&
    mtFiber50RowCheck 11 &&
    mtFiber50RowCheck 12 &&
    mtFiber50RowCheck 13 &&
    mtFiber50RowCheck 14 &&
    mtFiber50RowCheck 15 &&
    mtFiber50RowCheck 16 &&
    mtFiber50RowCheck 17 &&
    mtFiber50RowCheck 18 &&
    mtFiber50RowCheck 19 &&
    mtFiber50RowCheck 20 &&
    mtFiber50RowCheck 21 &&
    mtFiber50RowCheck 22 &&
    mtFiber50RowCheck 23 &&
    mtFiber50RowCheck 24 &&
    mtFiber50RowCheck 25 &&
    mtFiber50RowCheck 26 &&
    mtFiber50RowCheck 27 &&
    mtFiber50RowCheck 28 &&
    mtFiber50RowCheck 29 &&
    mtFiber50RowCheck 30 &&
    mtFiber50RowCheck 31 &&
    mtFiber50RowCheck 32 &&
    mtFiber50RowCheck 33 &&
    mtFiber50RowCheck 34 &&
    mtFiber50RowCheck 35 &&
    mtFiber50RowCheck 36 &&
    mtFiber50RowCheck 37 &&
    mtFiber50RowCheck 38 &&
    mtFiber50RowCheck 39 &&
    mtFiber50RowCheck 40 &&
    mtFiber50RowCheck 41 &&
    mtFiber50RowCheck 42 &&
    mtFiber50RowCheck 43 &&
    mtFiber50RowCheck 44 &&
    mtFiber50RowCheck 45 &&
    mtFiber50RowCheck 46 &&
    mtFiber50RowCheck 47 &&
    mtFiber50RowCheck 48 &&
    mtFiber50RowCheck 49 &&
    mtFiber50RowCheck 50 &&
    mtFiber50RowCheck 51 &&
    mtFiber50RowCheck 52 &&
    mtFiber50RowCheck 53 &&
    mtFiber50RowCheck 54 &&
    mtFiber50RowCheck 55 &&
    mtFiber50RowCheck 56 &&
    mtFiber50RowCheck 57 &&
    mtFiber50RowCheck 58 &&
    mtFiber50RowCheck 59 &&
    mtFiber50RowCheck 60 &&
    mtFiber50RowCheck 61 &&
    mtFiber50RowCheck 62 &&
    mtFiber50RowCheck 63 &&
    mtFiber50ParentCheck 0 &&
    mtFiber50ParentCheck 1 &&
    mtFiber50ParentCheck 2 &&
    mtFiber50ParentCheck 3 &&
    mtFiber50ParentCheck 4 &&
    mtFiber50ParentCheck 5 &&
    mtFiber50ParentCheck 6 &&
    mtFiber50ParentCheck 7 &&
    mtFiber50ParentCheck 8 &&
    mtFiber50ParentCheck 9 &&
    mtFiber50ParentCheck 10 &&
    mtFiber50ParentCheck 11 &&
    mtFiber50ParentCheck 12 &&
    mtFiber50ParentCheck 13 &&
    mtFiber50ParentCheck 14 &&
    mtFiber50ParentCheck 15 &&
    mtFiber50ParentCheck 16 &&
    mtFiber50ParentCheck 17 &&
    mtFiber50ParentCheck 18 &&
    mtFiber50ParentCheck 19 &&
    mtFiber50ParentCheck 20 &&
    mtFiber50ParentCheck 21 &&
    mtFiber50ParentCheck 22 &&
    mtFiber50ParentCheck 23 &&
    mtFiber50ParentCheck 24 &&
    mtFiber50ParentCheck 25 &&
    mtFiber50ParentCheck 26 &&
    mtFiber50ParentCheck 27 &&
    mtFiber50ParentCheck 28 &&
    mtFiber50ParentCheck 29 &&
    mtFiber50ParentCheck 30 &&
    mtFiber50ParentCheck 31 &&
    mtFiber50ParentCheck 32 &&
    mtFiber50ParentCheck 33 &&
    mtFiber50ParentCheck 34 &&
    mtFiber50ParentCheck 35 &&
    mtFiber50ParentCheck 36 &&
    mtFiber50ParentCheck 37 &&
    mtFiber50ParentCheck 38 &&
    mtFiber50ParentCheck 39 &&
    mtFiber50ParentCheck 40 &&
    mtFiber50ParentCheck 41 &&
    mtFiber50ParentCheck 42 &&
    mtFiber50ParentCheck 43 &&
    mtFiber50ParentCheck 44 &&
    mtFiber50ParentCheck 45 &&
    mtFiber50ParentCheck 46 &&
    mtFiber50ParentCheck 47 &&
    mtFiber50ParentCheck 48 &&
    mtFiber50ParentCheck 49 &&
    mtFiber50ParentCheck 50 &&
    mtFiber50ParentCheck 51 &&
    mtFiber50ParentCheck 52 &&
    mtFiber50ParentCheck 53 &&
    mtFiber50ParentCheck 54 &&
    mtFiber50ParentCheck 55 &&
    mtFiber50ParentCheck 56 &&
    mtFiber50ParentCheck 57 &&
    mtFiber50ParentCheck 58 &&
    mtFiber50ParentCheck 59 &&
    mtFiber50ParentCheck 60 &&
    mtFiber50ParentCheck 61 &&
    mtFiber50ParentCheck 62 &&
    mtFiber50ParentCheck 63

theorem mtFiber50CertificateAudit_ok :
    mtFiber50CertificateAudit = true := by
  simp [mtFiber50CertificateAudit,
    mtFiber50SourcesCheck_ok,
    mtFiber50Row_0_ok,
    mtFiber50Row_1_ok,
    mtFiber50Row_2_ok,
    mtFiber50Row_3_ok,
    mtFiber50Row_4_ok,
    mtFiber50Row_5_ok,
    mtFiber50Row_6_ok,
    mtFiber50Row_7_ok,
    mtFiber50Row_8_ok,
    mtFiber50Row_9_ok,
    mtFiber50Row_10_ok,
    mtFiber50Row_11_ok,
    mtFiber50Row_12_ok,
    mtFiber50Row_13_ok,
    mtFiber50Row_14_ok,
    mtFiber50Row_15_ok,
    mtFiber50Row_16_ok,
    mtFiber50Row_17_ok,
    mtFiber50Row_18_ok,
    mtFiber50Row_19_ok,
    mtFiber50Row_20_ok,
    mtFiber50Row_21_ok,
    mtFiber50Row_22_ok,
    mtFiber50Row_23_ok,
    mtFiber50Row_24_ok,
    mtFiber50Row_25_ok,
    mtFiber50Row_26_ok,
    mtFiber50Row_27_ok,
    mtFiber50Row_28_ok,
    mtFiber50Row_29_ok,
    mtFiber50Row_30_ok,
    mtFiber50Row_31_ok,
    mtFiber50Row_32_ok,
    mtFiber50Row_33_ok,
    mtFiber50Row_34_ok,
    mtFiber50Row_35_ok,
    mtFiber50Row_36_ok,
    mtFiber50Row_37_ok,
    mtFiber50Row_38_ok,
    mtFiber50Row_39_ok,
    mtFiber50Row_40_ok,
    mtFiber50Row_41_ok,
    mtFiber50Row_42_ok,
    mtFiber50Row_43_ok,
    mtFiber50Row_44_ok,
    mtFiber50Row_45_ok,
    mtFiber50Row_46_ok,
    mtFiber50Row_47_ok,
    mtFiber50Row_48_ok,
    mtFiber50Row_49_ok,
    mtFiber50Row_50_ok,
    mtFiber50Row_51_ok,
    mtFiber50Row_52_ok,
    mtFiber50Row_53_ok,
    mtFiber50Row_54_ok,
    mtFiber50Row_55_ok,
    mtFiber50Row_56_ok,
    mtFiber50Row_57_ok,
    mtFiber50Row_58_ok,
    mtFiber50Row_59_ok,
    mtFiber50Row_60_ok,
    mtFiber50Row_61_ok,
    mtFiber50Row_62_ok,
    mtFiber50Row_63_ok,
    mtFiber50Parent_0_ok,
    mtFiber50Parent_1_ok,
    mtFiber50Parent_2_ok,
    mtFiber50Parent_3_ok,
    mtFiber50Parent_4_ok,
    mtFiber50Parent_5_ok,
    mtFiber50Parent_6_ok,
    mtFiber50Parent_7_ok,
    mtFiber50Parent_8_ok,
    mtFiber50Parent_9_ok,
    mtFiber50Parent_10_ok,
    mtFiber50Parent_11_ok,
    mtFiber50Parent_12_ok,
    mtFiber50Parent_13_ok,
    mtFiber50Parent_14_ok,
    mtFiber50Parent_15_ok,
    mtFiber50Parent_16_ok,
    mtFiber50Parent_17_ok,
    mtFiber50Parent_18_ok,
    mtFiber50Parent_19_ok,
    mtFiber50Parent_20_ok,
    mtFiber50Parent_21_ok,
    mtFiber50Parent_22_ok,
    mtFiber50Parent_23_ok,
    mtFiber50Parent_24_ok,
    mtFiber50Parent_25_ok,
    mtFiber50Parent_26_ok,
    mtFiber50Parent_27_ok,
    mtFiber50Parent_28_ok,
    mtFiber50Parent_29_ok,
    mtFiber50Parent_30_ok,
    mtFiber50Parent_31_ok,
    mtFiber50Parent_32_ok,
    mtFiber50Parent_33_ok,
    mtFiber50Parent_34_ok,
    mtFiber50Parent_35_ok,
    mtFiber50Parent_36_ok,
    mtFiber50Parent_37_ok,
    mtFiber50Parent_38_ok,
    mtFiber50Parent_39_ok,
    mtFiber50Parent_40_ok,
    mtFiber50Parent_41_ok,
    mtFiber50Parent_42_ok,
    mtFiber50Parent_43_ok,
    mtFiber50Parent_44_ok,
    mtFiber50Parent_45_ok,
    mtFiber50Parent_46_ok,
    mtFiber50Parent_47_ok,
    mtFiber50Parent_48_ok,
    mtFiber50Parent_49_ok,
    mtFiber50Parent_50_ok,
    mtFiber50Parent_51_ok,
    mtFiber50Parent_52_ok,
    mtFiber50Parent_53_ok,
    mtFiber50Parent_54_ok,
    mtFiber50Parent_55_ok,
    mtFiber50Parent_56_ok,
    mtFiber50Parent_57_ok,
    mtFiber50Parent_58_ok,
    mtFiber50Parent_59_ok,
    mtFiber50Parent_60_ok,
    mtFiber50Parent_61_ok,
    mtFiber50Parent_62_ok,
    mtFiber50Parent_63_ok]

def mtFiber51Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.r]

def mtFiber51Expected : List Nat :=
  []

def mtFiber51Rows : List DirectChainParentRow :=
  []

def mtFiber51RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber51Rows i default

def mtFiber51SourcesCheck : Bool :=
  (mtFiber51Rows.map fun row => row.source) == mtFiber51Expected

theorem mtFiber51SourcesCheck_ok :
    mtFiber51SourcesCheck = true := by
  decide

def mtFiber51RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber51Key mtFiber51Expected (mtFiber51RowAt i)

def mtFiber51ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber51Rows mtMaxParentDepth (listGetD mtFiber51Expected i 0) == 0

def mtFiber51CertificateAudit : Bool :=
  mtFiber51SourcesCheck

theorem mtFiber51CertificateAudit_ok :
    mtFiber51CertificateAudit = true := by
  simp [mtFiber51CertificateAudit,
    mtFiber51SourcesCheck_ok]

def mtFiber52Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.b]

def mtFiber52Expected : List Nat :=
  []

def mtFiber52Rows : List DirectChainParentRow :=
  []

def mtFiber52RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber52Rows i default

def mtFiber52SourcesCheck : Bool :=
  (mtFiber52Rows.map fun row => row.source) == mtFiber52Expected

theorem mtFiber52SourcesCheck_ok :
    mtFiber52SourcesCheck = true := by
  decide

def mtFiber52RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber52Key mtFiber52Expected (mtFiber52RowAt i)

def mtFiber52ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber52Rows mtMaxParentDepth (listGetD mtFiber52Expected i 0) == 0

def mtFiber52CertificateAudit : Bool :=
  mtFiber52SourcesCheck

theorem mtFiber52CertificateAudit_ok :
    mtFiber52CertificateAudit = true := by
  simp [mtFiber52CertificateAudit,
    mtFiber52SourcesCheck_ok]

def mtFiber53Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.p]

def mtFiber53Expected : List Nat :=
  []

def mtFiber53Rows : List DirectChainParentRow :=
  []

def mtFiber53RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber53Rows i default

def mtFiber53SourcesCheck : Bool :=
  (mtFiber53Rows.map fun row => row.source) == mtFiber53Expected

theorem mtFiber53SourcesCheck_ok :
    mtFiber53SourcesCheck = true := by
  decide

def mtFiber53RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber53Key mtFiber53Expected (mtFiber53RowAt i)

def mtFiber53ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber53Rows mtMaxParentDepth (listGetD mtFiber53Expected i 0) == 0

def mtFiber53CertificateAudit : Bool :=
  mtFiber53SourcesCheck

theorem mtFiber53CertificateAudit_ok :
    mtFiber53CertificateAudit = true := by
  simp [mtFiber53CertificateAudit,
    mtFiber53SourcesCheck_ok]

def mtFiber54Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.r]

def mtFiber54Expected : List Nat :=
  []

def mtFiber54Rows : List DirectChainParentRow :=
  []

def mtFiber54RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber54Rows i default

def mtFiber54SourcesCheck : Bool :=
  (mtFiber54Rows.map fun row => row.source) == mtFiber54Expected

theorem mtFiber54SourcesCheck_ok :
    mtFiber54SourcesCheck = true := by
  decide

def mtFiber54RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber54Key mtFiber54Expected (mtFiber54RowAt i)

def mtFiber54ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber54Rows mtMaxParentDepth (listGetD mtFiber54Expected i 0) == 0

def mtFiber54CertificateAudit : Bool :=
  mtFiber54SourcesCheck

theorem mtFiber54CertificateAudit_ok :
    mtFiber54CertificateAudit = true := by
  simp [mtFiber54CertificateAudit,
    mtFiber54SourcesCheck_ok]

def mtFiber55Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.b]

def mtFiber55Expected : List Nat :=
  []

def mtFiber55Rows : List DirectChainParentRow :=
  []

def mtFiber55RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber55Rows i default

def mtFiber55SourcesCheck : Bool :=
  (mtFiber55Rows.map fun row => row.source) == mtFiber55Expected

theorem mtFiber55SourcesCheck_ok :
    mtFiber55SourcesCheck = true := by
  decide

def mtFiber55RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber55Key mtFiber55Expected (mtFiber55RowAt i)

def mtFiber55ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber55Rows mtMaxParentDepth (listGetD mtFiber55Expected i 0) == 0

def mtFiber55CertificateAudit : Bool :=
  mtFiber55SourcesCheck

theorem mtFiber55CertificateAudit_ok :
    mtFiber55CertificateAudit = true := by
  simp [mtFiber55CertificateAudit,
    mtFiber55SourcesCheck_ok]

def mtFiber56Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.p]

def mtFiber56Expected : List Nat :=
  []

def mtFiber56Rows : List DirectChainParentRow :=
  []

def mtFiber56RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber56Rows i default

def mtFiber56SourcesCheck : Bool :=
  (mtFiber56Rows.map fun row => row.source) == mtFiber56Expected

theorem mtFiber56SourcesCheck_ok :
    mtFiber56SourcesCheck = true := by
  decide

def mtFiber56RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber56Key mtFiber56Expected (mtFiber56RowAt i)

def mtFiber56ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber56Rows mtMaxParentDepth (listGetD mtFiber56Expected i 0) == 0

def mtFiber56CertificateAudit : Bool :=
  mtFiber56SourcesCheck

theorem mtFiber56CertificateAudit_ok :
    mtFiber56CertificateAudit = true := by
  simp [mtFiber56CertificateAudit,
    mtFiber56SourcesCheck_ok]

def mtFiber57Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.r]

def mtFiber57Expected : List Nat :=
  [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]

def mtFiber57Rows : List DirectChainParentRow :=
  [ directRow 464 464 76 152 76 152 default
  , directRow 465 464 76 153 76 152 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 466 465 76 154 76 153 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 467 464 76 155 76 152 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 468 464 77 144 76 152 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 469 465 77 145 76 153 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 470 466 77 146 76 154 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 471 467 77 147 76 155 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 472 464 78 136 76 152 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 473 465 78 137 76 153 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 474 466 78 138 76 154 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 475 467 78 139 76 155 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 476 468 79 128 77 144 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 477 469 79 129 77 145 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 478 470 79 130 77 146 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 479 471 79 131 77 147 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber57RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber57Rows i default

def mtFiber57SourcesCheck : Bool :=
  (mtFiber57Rows.map fun row => row.source) == mtFiber57Expected

theorem mtFiber57SourcesCheck_ok :
    mtFiber57SourcesCheck = true := by
  decide

def mtFiber57RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt i)

theorem mtFiber57Row_0_ok : mtFiber57RowCheck 0 = true := by decide
theorem mtFiber57Row_1_ok : mtFiber57RowCheck 1 = true := by decide
theorem mtFiber57Row_2_ok : mtFiber57RowCheck 2 = true := by decide
theorem mtFiber57Row_3_ok : mtFiber57RowCheck 3 = true := by decide
theorem mtFiber57Row_4_ok : mtFiber57RowCheck 4 = true := by decide
theorem mtFiber57Row_5_ok : mtFiber57RowCheck 5 = true := by decide
theorem mtFiber57Row_6_ok : mtFiber57RowCheck 6 = true := by decide
theorem mtFiber57Row_7_ok : mtFiber57RowCheck 7 = true := by decide
theorem mtFiber57Row_8_ok : mtFiber57RowCheck 8 = true := by decide
theorem mtFiber57Row_9_ok : mtFiber57RowCheck 9 = true := by decide
theorem mtFiber57Row_10_ok : mtFiber57RowCheck 10 = true := by decide
theorem mtFiber57Row_11_ok : mtFiber57RowCheck 11 = true := by decide
theorem mtFiber57Row_12_ok : mtFiber57RowCheck 12 = true := by decide
theorem mtFiber57Row_13_ok : mtFiber57RowCheck 13 = true := by decide
theorem mtFiber57Row_14_ok : mtFiber57RowCheck 14 = true := by decide
theorem mtFiber57Row_15_ok : mtFiber57RowCheck 15 = true := by decide

def mtFiber57ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber57Rows mtMaxParentDepth (listGetD mtFiber57Expected i 0) == 464

theorem mtFiber57Parent_0_ok : mtFiber57ParentCheck 0 = true := by decide
theorem mtFiber57Parent_1_ok : mtFiber57ParentCheck 1 = true := by decide
theorem mtFiber57Parent_2_ok : mtFiber57ParentCheck 2 = true := by decide
theorem mtFiber57Parent_3_ok : mtFiber57ParentCheck 3 = true := by decide
theorem mtFiber57Parent_4_ok : mtFiber57ParentCheck 4 = true := by decide
theorem mtFiber57Parent_5_ok : mtFiber57ParentCheck 5 = true := by decide
theorem mtFiber57Parent_6_ok : mtFiber57ParentCheck 6 = true := by decide
theorem mtFiber57Parent_7_ok : mtFiber57ParentCheck 7 = true := by decide
theorem mtFiber57Parent_8_ok : mtFiber57ParentCheck 8 = true := by decide
theorem mtFiber57Parent_9_ok : mtFiber57ParentCheck 9 = true := by decide
theorem mtFiber57Parent_10_ok : mtFiber57ParentCheck 10 = true := by decide
theorem mtFiber57Parent_11_ok : mtFiber57ParentCheck 11 = true := by decide
theorem mtFiber57Parent_12_ok : mtFiber57ParentCheck 12 = true := by decide
theorem mtFiber57Parent_13_ok : mtFiber57ParentCheck 13 = true := by decide
theorem mtFiber57Parent_14_ok : mtFiber57ParentCheck 14 = true := by decide
theorem mtFiber57Parent_15_ok : mtFiber57ParentCheck 15 = true := by decide

def mtFiber57CertificateAudit : Bool :=
  mtFiber57SourcesCheck &&
    mtFiber57RowCheck 0 &&
    mtFiber57RowCheck 1 &&
    mtFiber57RowCheck 2 &&
    mtFiber57RowCheck 3 &&
    mtFiber57RowCheck 4 &&
    mtFiber57RowCheck 5 &&
    mtFiber57RowCheck 6 &&
    mtFiber57RowCheck 7 &&
    mtFiber57RowCheck 8 &&
    mtFiber57RowCheck 9 &&
    mtFiber57RowCheck 10 &&
    mtFiber57RowCheck 11 &&
    mtFiber57RowCheck 12 &&
    mtFiber57RowCheck 13 &&
    mtFiber57RowCheck 14 &&
    mtFiber57RowCheck 15 &&
    mtFiber57ParentCheck 0 &&
    mtFiber57ParentCheck 1 &&
    mtFiber57ParentCheck 2 &&
    mtFiber57ParentCheck 3 &&
    mtFiber57ParentCheck 4 &&
    mtFiber57ParentCheck 5 &&
    mtFiber57ParentCheck 6 &&
    mtFiber57ParentCheck 7 &&
    mtFiber57ParentCheck 8 &&
    mtFiber57ParentCheck 9 &&
    mtFiber57ParentCheck 10 &&
    mtFiber57ParentCheck 11 &&
    mtFiber57ParentCheck 12 &&
    mtFiber57ParentCheck 13 &&
    mtFiber57ParentCheck 14 &&
    mtFiber57ParentCheck 15

theorem mtFiber57CertificateAudit_ok :
    mtFiber57CertificateAudit = true := by
  simp [mtFiber57CertificateAudit,
    mtFiber57SourcesCheck_ok,
    mtFiber57Row_0_ok,
    mtFiber57Row_1_ok,
    mtFiber57Row_2_ok,
    mtFiber57Row_3_ok,
    mtFiber57Row_4_ok,
    mtFiber57Row_5_ok,
    mtFiber57Row_6_ok,
    mtFiber57Row_7_ok,
    mtFiber57Row_8_ok,
    mtFiber57Row_9_ok,
    mtFiber57Row_10_ok,
    mtFiber57Row_11_ok,
    mtFiber57Row_12_ok,
    mtFiber57Row_13_ok,
    mtFiber57Row_14_ok,
    mtFiber57Row_15_ok,
    mtFiber57Parent_0_ok,
    mtFiber57Parent_1_ok,
    mtFiber57Parent_2_ok,
    mtFiber57Parent_3_ok,
    mtFiber57Parent_4_ok,
    mtFiber57Parent_5_ok,
    mtFiber57Parent_6_ok,
    mtFiber57Parent_7_ok,
    mtFiber57Parent_8_ok,
    mtFiber57Parent_9_ok,
    mtFiber57Parent_10_ok,
    mtFiber57Parent_11_ok,
    mtFiber57Parent_12_ok,
    mtFiber57Parent_13_ok,
    mtFiber57Parent_14_ok,
    mtFiber57Parent_15_ok]

def mtFiber58Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.b]

def mtFiber58Expected : List Nat :=
  [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

def mtFiber58Rows : List DirectChainParentRow :=
  [ directRow 80 80 12 168 12 168 default
  , directRow 81 80 12 169 12 168 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 82 80 12 170 12 168 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 83 81 12 171 12 169 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 84 80 13 160 12 168 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 85 81 13 161 12 169 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 86 82 13 162 12 170 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 87 83 13 163 12 171 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 88 80 14 184 12 168 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 89 81 14 185 12 169 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 90 82 14 186 12 170 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 91 83 14 187 12 171 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 92 84 15 176 13 160 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 93 85 15 177 13 161 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 94 86 15 178 13 162 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 95 87 15 179 13 163 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber58RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber58Rows i default

def mtFiber58SourcesCheck : Bool :=
  (mtFiber58Rows.map fun row => row.source) == mtFiber58Expected

theorem mtFiber58SourcesCheck_ok :
    mtFiber58SourcesCheck = true := by
  decide

def mtFiber58RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt i)

theorem mtFiber58Row_0_ok : mtFiber58RowCheck 0 = true := by decide
theorem mtFiber58Row_1_ok : mtFiber58RowCheck 1 = true := by decide
theorem mtFiber58Row_2_ok : mtFiber58RowCheck 2 = true := by decide
theorem mtFiber58Row_3_ok : mtFiber58RowCheck 3 = true := by decide
theorem mtFiber58Row_4_ok : mtFiber58RowCheck 4 = true := by decide
theorem mtFiber58Row_5_ok : mtFiber58RowCheck 5 = true := by decide
theorem mtFiber58Row_6_ok : mtFiber58RowCheck 6 = true := by decide
theorem mtFiber58Row_7_ok : mtFiber58RowCheck 7 = true := by decide
theorem mtFiber58Row_8_ok : mtFiber58RowCheck 8 = true := by decide
theorem mtFiber58Row_9_ok : mtFiber58RowCheck 9 = true := by decide
theorem mtFiber58Row_10_ok : mtFiber58RowCheck 10 = true := by decide
theorem mtFiber58Row_11_ok : mtFiber58RowCheck 11 = true := by decide
theorem mtFiber58Row_12_ok : mtFiber58RowCheck 12 = true := by decide
theorem mtFiber58Row_13_ok : mtFiber58RowCheck 13 = true := by decide
theorem mtFiber58Row_14_ok : mtFiber58RowCheck 14 = true := by decide
theorem mtFiber58Row_15_ok : mtFiber58RowCheck 15 = true := by decide

def mtFiber58ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber58Rows mtMaxParentDepth (listGetD mtFiber58Expected i 0) == 80

theorem mtFiber58Parent_0_ok : mtFiber58ParentCheck 0 = true := by decide
theorem mtFiber58Parent_1_ok : mtFiber58ParentCheck 1 = true := by decide
theorem mtFiber58Parent_2_ok : mtFiber58ParentCheck 2 = true := by decide
theorem mtFiber58Parent_3_ok : mtFiber58ParentCheck 3 = true := by decide
theorem mtFiber58Parent_4_ok : mtFiber58ParentCheck 4 = true := by decide
theorem mtFiber58Parent_5_ok : mtFiber58ParentCheck 5 = true := by decide
theorem mtFiber58Parent_6_ok : mtFiber58ParentCheck 6 = true := by decide
theorem mtFiber58Parent_7_ok : mtFiber58ParentCheck 7 = true := by decide
theorem mtFiber58Parent_8_ok : mtFiber58ParentCheck 8 = true := by decide
theorem mtFiber58Parent_9_ok : mtFiber58ParentCheck 9 = true := by decide
theorem mtFiber58Parent_10_ok : mtFiber58ParentCheck 10 = true := by decide
theorem mtFiber58Parent_11_ok : mtFiber58ParentCheck 11 = true := by decide
theorem mtFiber58Parent_12_ok : mtFiber58ParentCheck 12 = true := by decide
theorem mtFiber58Parent_13_ok : mtFiber58ParentCheck 13 = true := by decide
theorem mtFiber58Parent_14_ok : mtFiber58ParentCheck 14 = true := by decide
theorem mtFiber58Parent_15_ok : mtFiber58ParentCheck 15 = true := by decide

def mtFiber58CertificateAudit : Bool :=
  mtFiber58SourcesCheck &&
    mtFiber58RowCheck 0 &&
    mtFiber58RowCheck 1 &&
    mtFiber58RowCheck 2 &&
    mtFiber58RowCheck 3 &&
    mtFiber58RowCheck 4 &&
    mtFiber58RowCheck 5 &&
    mtFiber58RowCheck 6 &&
    mtFiber58RowCheck 7 &&
    mtFiber58RowCheck 8 &&
    mtFiber58RowCheck 9 &&
    mtFiber58RowCheck 10 &&
    mtFiber58RowCheck 11 &&
    mtFiber58RowCheck 12 &&
    mtFiber58RowCheck 13 &&
    mtFiber58RowCheck 14 &&
    mtFiber58RowCheck 15 &&
    mtFiber58ParentCheck 0 &&
    mtFiber58ParentCheck 1 &&
    mtFiber58ParentCheck 2 &&
    mtFiber58ParentCheck 3 &&
    mtFiber58ParentCheck 4 &&
    mtFiber58ParentCheck 5 &&
    mtFiber58ParentCheck 6 &&
    mtFiber58ParentCheck 7 &&
    mtFiber58ParentCheck 8 &&
    mtFiber58ParentCheck 9 &&
    mtFiber58ParentCheck 10 &&
    mtFiber58ParentCheck 11 &&
    mtFiber58ParentCheck 12 &&
    mtFiber58ParentCheck 13 &&
    mtFiber58ParentCheck 14 &&
    mtFiber58ParentCheck 15

theorem mtFiber58CertificateAudit_ok :
    mtFiber58CertificateAudit = true := by
  simp [mtFiber58CertificateAudit,
    mtFiber58SourcesCheck_ok,
    mtFiber58Row_0_ok,
    mtFiber58Row_1_ok,
    mtFiber58Row_2_ok,
    mtFiber58Row_3_ok,
    mtFiber58Row_4_ok,
    mtFiber58Row_5_ok,
    mtFiber58Row_6_ok,
    mtFiber58Row_7_ok,
    mtFiber58Row_8_ok,
    mtFiber58Row_9_ok,
    mtFiber58Row_10_ok,
    mtFiber58Row_11_ok,
    mtFiber58Row_12_ok,
    mtFiber58Row_13_ok,
    mtFiber58Row_14_ok,
    mtFiber58Row_15_ok,
    mtFiber58Parent_0_ok,
    mtFiber58Parent_1_ok,
    mtFiber58Parent_2_ok,
    mtFiber58Parent_3_ok,
    mtFiber58Parent_4_ok,
    mtFiber58Parent_5_ok,
    mtFiber58Parent_6_ok,
    mtFiber58Parent_7_ok,
    mtFiber58Parent_8_ok,
    mtFiber58Parent_9_ok,
    mtFiber58Parent_10_ok,
    mtFiber58Parent_11_ok,
    mtFiber58Parent_12_ok,
    mtFiber58Parent_13_ok,
    mtFiber58Parent_14_ok,
    mtFiber58Parent_15_ok]

def mtFiber59Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.p]

def mtFiber59Expected : List Nat :=
  []

def mtFiber59Rows : List DirectChainParentRow :=
  []

def mtFiber59RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber59Rows i default

def mtFiber59SourcesCheck : Bool :=
  (mtFiber59Rows.map fun row => row.source) == mtFiber59Expected

theorem mtFiber59SourcesCheck_ok :
    mtFiber59SourcesCheck = true := by
  decide

def mtFiber59RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber59Key mtFiber59Expected (mtFiber59RowAt i)

def mtFiber59ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber59Rows mtMaxParentDepth (listGetD mtFiber59Expected i 0) == 0

def mtFiber59CertificateAudit : Bool :=
  mtFiber59SourcesCheck

theorem mtFiber59CertificateAudit_ok :
    mtFiber59CertificateAudit = true := by
  simp [mtFiber59CertificateAudit,
    mtFiber59SourcesCheck_ok]

def mtFiber60Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.r]

def mtFiber60Expected : List Nat :=
  [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]

def mtFiber60Rows : List DirectChainParentRow :=
  [ directRow 832 832 140 88 140 88 default
  , directRow 833 832 140 89 140 88 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 834 832 140 90 140 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 835 833 140 91 140 89 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 836 834 140 108 140 90 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 837 839 140 109 140 111 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 838 833 140 110 140 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 839 832 140 111 140 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 840 832 141 80 140 88 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 841 833 141 81 140 89 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 842 834 141 82 140 90 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 843 835 141 83 140 91 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 844 836 141 100 140 108 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 845 837 141 101 140 109 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 846 838 141 102 140 110 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 847 839 141 103 140 111 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 848 840 142 72 141 80 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 849 841 142 73 141 81 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 850 842 142 74 141 82 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 851 843 142 75 141 83 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 852 844 142 124 141 100 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 853 845 142 125 141 101 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 854 846 142 126 141 102 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 855 847 142 127 141 103 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 856 832 143 64 140 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 857 833 143 65 140 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 858 834 143 66 140 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 859 835 143 67 140 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 860 836 143 116 140 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 861 837 143 117 140 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 862 838 143 118 140 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 863 839 143 119 140 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 1120 832 188 24 140 88 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1121 833 188 25 140 89 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1122 834 188 26 140 90 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1123 835 188 27 140 91 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1124 1120 188 40 188 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1125 1121 188 41 188 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1126 838 188 42 140 110 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1127 839 188 43 140 111 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1128 840 189 16 141 80 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1129 841 189 17 141 81 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1130 842 189 18 141 82 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1131 843 189 19 141 83 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1132 1128 189 32 189 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1133 1129 189 33 189 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1134 846 189 34 141 102 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1135 847 189 35 141 103 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1136 1120 190 8 188 24 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1137 1121 190 9 188 25 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1138 1122 190 10 188 26 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1139 1123 190 11 188 27 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1140 1124 190 56 188 40 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1141 1125 190 57 188 41 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1142 1126 190 58 188 42 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1143 1127 190 59 188 43 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1144 856 191 0 143 64 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1145 857 191 1 143 65 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1146 858 191 2 143 66 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1147 859 191 3 143 67 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1148 1144 191 48 191 0 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1149 1145 191 49 191 1 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1150 862 191 50 143 118 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1151 863 191 51 143 119 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mtFiber60RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber60Rows i default

def mtFiber60SourcesCheck : Bool :=
  (mtFiber60Rows.map fun row => row.source) == mtFiber60Expected

theorem mtFiber60SourcesCheck_ok :
    mtFiber60SourcesCheck = true := by
  decide

def mtFiber60RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt i)

theorem mtFiber60Row_0_ok : mtFiber60RowCheck 0 = true := by decide
theorem mtFiber60Row_1_ok : mtFiber60RowCheck 1 = true := by decide
theorem mtFiber60Row_2_ok : mtFiber60RowCheck 2 = true := by decide
theorem mtFiber60Row_3_ok : mtFiber60RowCheck 3 = true := by decide
theorem mtFiber60Row_4_ok : mtFiber60RowCheck 4 = true := by decide
theorem mtFiber60Row_5_ok : mtFiber60RowCheck 5 = true := by decide
theorem mtFiber60Row_6_ok : mtFiber60RowCheck 6 = true := by decide
theorem mtFiber60Row_7_ok : mtFiber60RowCheck 7 = true := by decide
theorem mtFiber60Row_8_ok : mtFiber60RowCheck 8 = true := by decide
theorem mtFiber60Row_9_ok : mtFiber60RowCheck 9 = true := by decide
theorem mtFiber60Row_10_ok : mtFiber60RowCheck 10 = true := by decide
theorem mtFiber60Row_11_ok : mtFiber60RowCheck 11 = true := by decide
theorem mtFiber60Row_12_ok : mtFiber60RowCheck 12 = true := by decide
theorem mtFiber60Row_13_ok : mtFiber60RowCheck 13 = true := by decide
theorem mtFiber60Row_14_ok : mtFiber60RowCheck 14 = true := by decide
theorem mtFiber60Row_15_ok : mtFiber60RowCheck 15 = true := by decide
theorem mtFiber60Row_16_ok : mtFiber60RowCheck 16 = true := by decide
theorem mtFiber60Row_17_ok : mtFiber60RowCheck 17 = true := by decide
theorem mtFiber60Row_18_ok : mtFiber60RowCheck 18 = true := by decide
theorem mtFiber60Row_19_ok : mtFiber60RowCheck 19 = true := by decide
theorem mtFiber60Row_20_ok : mtFiber60RowCheck 20 = true := by decide
theorem mtFiber60Row_21_ok : mtFiber60RowCheck 21 = true := by decide
theorem mtFiber60Row_22_ok : mtFiber60RowCheck 22 = true := by decide
theorem mtFiber60Row_23_ok : mtFiber60RowCheck 23 = true := by decide
theorem mtFiber60Row_24_ok : mtFiber60RowCheck 24 = true := by decide
theorem mtFiber60Row_25_ok : mtFiber60RowCheck 25 = true := by decide
theorem mtFiber60Row_26_ok : mtFiber60RowCheck 26 = true := by decide
theorem mtFiber60Row_27_ok : mtFiber60RowCheck 27 = true := by decide
theorem mtFiber60Row_28_ok : mtFiber60RowCheck 28 = true := by decide
theorem mtFiber60Row_29_ok : mtFiber60RowCheck 29 = true := by decide
theorem mtFiber60Row_30_ok : mtFiber60RowCheck 30 = true := by decide
theorem mtFiber60Row_31_ok : mtFiber60RowCheck 31 = true := by decide
theorem mtFiber60Row_32_ok : mtFiber60RowCheck 32 = true := by decide
theorem mtFiber60Row_33_ok : mtFiber60RowCheck 33 = true := by decide
theorem mtFiber60Row_34_ok : mtFiber60RowCheck 34 = true := by decide
theorem mtFiber60Row_35_ok : mtFiber60RowCheck 35 = true := by decide
theorem mtFiber60Row_36_ok : mtFiber60RowCheck 36 = true := by decide
theorem mtFiber60Row_37_ok : mtFiber60RowCheck 37 = true := by decide
theorem mtFiber60Row_38_ok : mtFiber60RowCheck 38 = true := by decide
theorem mtFiber60Row_39_ok : mtFiber60RowCheck 39 = true := by decide
theorem mtFiber60Row_40_ok : mtFiber60RowCheck 40 = true := by decide
theorem mtFiber60Row_41_ok : mtFiber60RowCheck 41 = true := by decide
theorem mtFiber60Row_42_ok : mtFiber60RowCheck 42 = true := by decide
theorem mtFiber60Row_43_ok : mtFiber60RowCheck 43 = true := by decide
theorem mtFiber60Row_44_ok : mtFiber60RowCheck 44 = true := by decide
theorem mtFiber60Row_45_ok : mtFiber60RowCheck 45 = true := by decide
theorem mtFiber60Row_46_ok : mtFiber60RowCheck 46 = true := by decide
theorem mtFiber60Row_47_ok : mtFiber60RowCheck 47 = true := by decide
theorem mtFiber60Row_48_ok : mtFiber60RowCheck 48 = true := by decide
theorem mtFiber60Row_49_ok : mtFiber60RowCheck 49 = true := by decide
theorem mtFiber60Row_50_ok : mtFiber60RowCheck 50 = true := by decide
theorem mtFiber60Row_51_ok : mtFiber60RowCheck 51 = true := by decide
theorem mtFiber60Row_52_ok : mtFiber60RowCheck 52 = true := by decide
theorem mtFiber60Row_53_ok : mtFiber60RowCheck 53 = true := by decide
theorem mtFiber60Row_54_ok : mtFiber60RowCheck 54 = true := by decide
theorem mtFiber60Row_55_ok : mtFiber60RowCheck 55 = true := by decide
theorem mtFiber60Row_56_ok : mtFiber60RowCheck 56 = true := by decide
theorem mtFiber60Row_57_ok : mtFiber60RowCheck 57 = true := by decide
theorem mtFiber60Row_58_ok : mtFiber60RowCheck 58 = true := by decide
theorem mtFiber60Row_59_ok : mtFiber60RowCheck 59 = true := by decide
theorem mtFiber60Row_60_ok : mtFiber60RowCheck 60 = true := by decide
theorem mtFiber60Row_61_ok : mtFiber60RowCheck 61 = true := by decide
theorem mtFiber60Row_62_ok : mtFiber60RowCheck 62 = true := by decide
theorem mtFiber60Row_63_ok : mtFiber60RowCheck 63 = true := by decide

def mtFiber60ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber60Rows mtMaxParentDepth (listGetD mtFiber60Expected i 0) == 832

theorem mtFiber60Parent_0_ok : mtFiber60ParentCheck 0 = true := by decide
theorem mtFiber60Parent_1_ok : mtFiber60ParentCheck 1 = true := by decide
theorem mtFiber60Parent_2_ok : mtFiber60ParentCheck 2 = true := by decide
theorem mtFiber60Parent_3_ok : mtFiber60ParentCheck 3 = true := by decide
theorem mtFiber60Parent_4_ok : mtFiber60ParentCheck 4 = true := by decide
theorem mtFiber60Parent_5_ok : mtFiber60ParentCheck 5 = true := by decide
theorem mtFiber60Parent_6_ok : mtFiber60ParentCheck 6 = true := by decide
theorem mtFiber60Parent_7_ok : mtFiber60ParentCheck 7 = true := by decide
theorem mtFiber60Parent_8_ok : mtFiber60ParentCheck 8 = true := by decide
theorem mtFiber60Parent_9_ok : mtFiber60ParentCheck 9 = true := by decide
theorem mtFiber60Parent_10_ok : mtFiber60ParentCheck 10 = true := by decide
theorem mtFiber60Parent_11_ok : mtFiber60ParentCheck 11 = true := by decide
theorem mtFiber60Parent_12_ok : mtFiber60ParentCheck 12 = true := by decide
theorem mtFiber60Parent_13_ok : mtFiber60ParentCheck 13 = true := by decide
theorem mtFiber60Parent_14_ok : mtFiber60ParentCheck 14 = true := by decide
theorem mtFiber60Parent_15_ok : mtFiber60ParentCheck 15 = true := by decide
theorem mtFiber60Parent_16_ok : mtFiber60ParentCheck 16 = true := by decide
theorem mtFiber60Parent_17_ok : mtFiber60ParentCheck 17 = true := by decide
theorem mtFiber60Parent_18_ok : mtFiber60ParentCheck 18 = true := by decide
theorem mtFiber60Parent_19_ok : mtFiber60ParentCheck 19 = true := by decide
theorem mtFiber60Parent_20_ok : mtFiber60ParentCheck 20 = true := by decide
theorem mtFiber60Parent_21_ok : mtFiber60ParentCheck 21 = true := by decide
theorem mtFiber60Parent_22_ok : mtFiber60ParentCheck 22 = true := by decide
theorem mtFiber60Parent_23_ok : mtFiber60ParentCheck 23 = true := by decide
theorem mtFiber60Parent_24_ok : mtFiber60ParentCheck 24 = true := by decide
theorem mtFiber60Parent_25_ok : mtFiber60ParentCheck 25 = true := by decide
theorem mtFiber60Parent_26_ok : mtFiber60ParentCheck 26 = true := by decide
theorem mtFiber60Parent_27_ok : mtFiber60ParentCheck 27 = true := by decide
theorem mtFiber60Parent_28_ok : mtFiber60ParentCheck 28 = true := by decide
theorem mtFiber60Parent_29_ok : mtFiber60ParentCheck 29 = true := by decide
theorem mtFiber60Parent_30_ok : mtFiber60ParentCheck 30 = true := by decide
theorem mtFiber60Parent_31_ok : mtFiber60ParentCheck 31 = true := by decide
theorem mtFiber60Parent_32_ok : mtFiber60ParentCheck 32 = true := by decide
theorem mtFiber60Parent_33_ok : mtFiber60ParentCheck 33 = true := by decide
theorem mtFiber60Parent_34_ok : mtFiber60ParentCheck 34 = true := by decide
theorem mtFiber60Parent_35_ok : mtFiber60ParentCheck 35 = true := by decide
theorem mtFiber60Parent_36_ok : mtFiber60ParentCheck 36 = true := by decide
theorem mtFiber60Parent_37_ok : mtFiber60ParentCheck 37 = true := by decide
theorem mtFiber60Parent_38_ok : mtFiber60ParentCheck 38 = true := by decide
theorem mtFiber60Parent_39_ok : mtFiber60ParentCheck 39 = true := by decide
theorem mtFiber60Parent_40_ok : mtFiber60ParentCheck 40 = true := by decide
theorem mtFiber60Parent_41_ok : mtFiber60ParentCheck 41 = true := by decide
theorem mtFiber60Parent_42_ok : mtFiber60ParentCheck 42 = true := by decide
theorem mtFiber60Parent_43_ok : mtFiber60ParentCheck 43 = true := by decide
theorem mtFiber60Parent_44_ok : mtFiber60ParentCheck 44 = true := by decide
theorem mtFiber60Parent_45_ok : mtFiber60ParentCheck 45 = true := by decide
theorem mtFiber60Parent_46_ok : mtFiber60ParentCheck 46 = true := by decide
theorem mtFiber60Parent_47_ok : mtFiber60ParentCheck 47 = true := by decide
theorem mtFiber60Parent_48_ok : mtFiber60ParentCheck 48 = true := by decide
theorem mtFiber60Parent_49_ok : mtFiber60ParentCheck 49 = true := by decide
theorem mtFiber60Parent_50_ok : mtFiber60ParentCheck 50 = true := by decide
theorem mtFiber60Parent_51_ok : mtFiber60ParentCheck 51 = true := by decide
theorem mtFiber60Parent_52_ok : mtFiber60ParentCheck 52 = true := by decide
theorem mtFiber60Parent_53_ok : mtFiber60ParentCheck 53 = true := by decide
theorem mtFiber60Parent_54_ok : mtFiber60ParentCheck 54 = true := by decide
theorem mtFiber60Parent_55_ok : mtFiber60ParentCheck 55 = true := by decide
theorem mtFiber60Parent_56_ok : mtFiber60ParentCheck 56 = true := by decide
theorem mtFiber60Parent_57_ok : mtFiber60ParentCheck 57 = true := by decide
theorem mtFiber60Parent_58_ok : mtFiber60ParentCheck 58 = true := by decide
theorem mtFiber60Parent_59_ok : mtFiber60ParentCheck 59 = true := by decide
theorem mtFiber60Parent_60_ok : mtFiber60ParentCheck 60 = true := by decide
theorem mtFiber60Parent_61_ok : mtFiber60ParentCheck 61 = true := by decide
theorem mtFiber60Parent_62_ok : mtFiber60ParentCheck 62 = true := by decide
theorem mtFiber60Parent_63_ok : mtFiber60ParentCheck 63 = true := by decide

def mtFiber60CertificateAudit : Bool :=
  mtFiber60SourcesCheck &&
    mtFiber60RowCheck 0 &&
    mtFiber60RowCheck 1 &&
    mtFiber60RowCheck 2 &&
    mtFiber60RowCheck 3 &&
    mtFiber60RowCheck 4 &&
    mtFiber60RowCheck 5 &&
    mtFiber60RowCheck 6 &&
    mtFiber60RowCheck 7 &&
    mtFiber60RowCheck 8 &&
    mtFiber60RowCheck 9 &&
    mtFiber60RowCheck 10 &&
    mtFiber60RowCheck 11 &&
    mtFiber60RowCheck 12 &&
    mtFiber60RowCheck 13 &&
    mtFiber60RowCheck 14 &&
    mtFiber60RowCheck 15 &&
    mtFiber60RowCheck 16 &&
    mtFiber60RowCheck 17 &&
    mtFiber60RowCheck 18 &&
    mtFiber60RowCheck 19 &&
    mtFiber60RowCheck 20 &&
    mtFiber60RowCheck 21 &&
    mtFiber60RowCheck 22 &&
    mtFiber60RowCheck 23 &&
    mtFiber60RowCheck 24 &&
    mtFiber60RowCheck 25 &&
    mtFiber60RowCheck 26 &&
    mtFiber60RowCheck 27 &&
    mtFiber60RowCheck 28 &&
    mtFiber60RowCheck 29 &&
    mtFiber60RowCheck 30 &&
    mtFiber60RowCheck 31 &&
    mtFiber60RowCheck 32 &&
    mtFiber60RowCheck 33 &&
    mtFiber60RowCheck 34 &&
    mtFiber60RowCheck 35 &&
    mtFiber60RowCheck 36 &&
    mtFiber60RowCheck 37 &&
    mtFiber60RowCheck 38 &&
    mtFiber60RowCheck 39 &&
    mtFiber60RowCheck 40 &&
    mtFiber60RowCheck 41 &&
    mtFiber60RowCheck 42 &&
    mtFiber60RowCheck 43 &&
    mtFiber60RowCheck 44 &&
    mtFiber60RowCheck 45 &&
    mtFiber60RowCheck 46 &&
    mtFiber60RowCheck 47 &&
    mtFiber60RowCheck 48 &&
    mtFiber60RowCheck 49 &&
    mtFiber60RowCheck 50 &&
    mtFiber60RowCheck 51 &&
    mtFiber60RowCheck 52 &&
    mtFiber60RowCheck 53 &&
    mtFiber60RowCheck 54 &&
    mtFiber60RowCheck 55 &&
    mtFiber60RowCheck 56 &&
    mtFiber60RowCheck 57 &&
    mtFiber60RowCheck 58 &&
    mtFiber60RowCheck 59 &&
    mtFiber60RowCheck 60 &&
    mtFiber60RowCheck 61 &&
    mtFiber60RowCheck 62 &&
    mtFiber60RowCheck 63 &&
    mtFiber60ParentCheck 0 &&
    mtFiber60ParentCheck 1 &&
    mtFiber60ParentCheck 2 &&
    mtFiber60ParentCheck 3 &&
    mtFiber60ParentCheck 4 &&
    mtFiber60ParentCheck 5 &&
    mtFiber60ParentCheck 6 &&
    mtFiber60ParentCheck 7 &&
    mtFiber60ParentCheck 8 &&
    mtFiber60ParentCheck 9 &&
    mtFiber60ParentCheck 10 &&
    mtFiber60ParentCheck 11 &&
    mtFiber60ParentCheck 12 &&
    mtFiber60ParentCheck 13 &&
    mtFiber60ParentCheck 14 &&
    mtFiber60ParentCheck 15 &&
    mtFiber60ParentCheck 16 &&
    mtFiber60ParentCheck 17 &&
    mtFiber60ParentCheck 18 &&
    mtFiber60ParentCheck 19 &&
    mtFiber60ParentCheck 20 &&
    mtFiber60ParentCheck 21 &&
    mtFiber60ParentCheck 22 &&
    mtFiber60ParentCheck 23 &&
    mtFiber60ParentCheck 24 &&
    mtFiber60ParentCheck 25 &&
    mtFiber60ParentCheck 26 &&
    mtFiber60ParentCheck 27 &&
    mtFiber60ParentCheck 28 &&
    mtFiber60ParentCheck 29 &&
    mtFiber60ParentCheck 30 &&
    mtFiber60ParentCheck 31 &&
    mtFiber60ParentCheck 32 &&
    mtFiber60ParentCheck 33 &&
    mtFiber60ParentCheck 34 &&
    mtFiber60ParentCheck 35 &&
    mtFiber60ParentCheck 36 &&
    mtFiber60ParentCheck 37 &&
    mtFiber60ParentCheck 38 &&
    mtFiber60ParentCheck 39 &&
    mtFiber60ParentCheck 40 &&
    mtFiber60ParentCheck 41 &&
    mtFiber60ParentCheck 42 &&
    mtFiber60ParentCheck 43 &&
    mtFiber60ParentCheck 44 &&
    mtFiber60ParentCheck 45 &&
    mtFiber60ParentCheck 46 &&
    mtFiber60ParentCheck 47 &&
    mtFiber60ParentCheck 48 &&
    mtFiber60ParentCheck 49 &&
    mtFiber60ParentCheck 50 &&
    mtFiber60ParentCheck 51 &&
    mtFiber60ParentCheck 52 &&
    mtFiber60ParentCheck 53 &&
    mtFiber60ParentCheck 54 &&
    mtFiber60ParentCheck 55 &&
    mtFiber60ParentCheck 56 &&
    mtFiber60ParentCheck 57 &&
    mtFiber60ParentCheck 58 &&
    mtFiber60ParentCheck 59 &&
    mtFiber60ParentCheck 60 &&
    mtFiber60ParentCheck 61 &&
    mtFiber60ParentCheck 62 &&
    mtFiber60ParentCheck 63

theorem mtFiber60CertificateAudit_ok :
    mtFiber60CertificateAudit = true := by
  simp [mtFiber60CertificateAudit,
    mtFiber60SourcesCheck_ok,
    mtFiber60Row_0_ok,
    mtFiber60Row_1_ok,
    mtFiber60Row_2_ok,
    mtFiber60Row_3_ok,
    mtFiber60Row_4_ok,
    mtFiber60Row_5_ok,
    mtFiber60Row_6_ok,
    mtFiber60Row_7_ok,
    mtFiber60Row_8_ok,
    mtFiber60Row_9_ok,
    mtFiber60Row_10_ok,
    mtFiber60Row_11_ok,
    mtFiber60Row_12_ok,
    mtFiber60Row_13_ok,
    mtFiber60Row_14_ok,
    mtFiber60Row_15_ok,
    mtFiber60Row_16_ok,
    mtFiber60Row_17_ok,
    mtFiber60Row_18_ok,
    mtFiber60Row_19_ok,
    mtFiber60Row_20_ok,
    mtFiber60Row_21_ok,
    mtFiber60Row_22_ok,
    mtFiber60Row_23_ok,
    mtFiber60Row_24_ok,
    mtFiber60Row_25_ok,
    mtFiber60Row_26_ok,
    mtFiber60Row_27_ok,
    mtFiber60Row_28_ok,
    mtFiber60Row_29_ok,
    mtFiber60Row_30_ok,
    mtFiber60Row_31_ok,
    mtFiber60Row_32_ok,
    mtFiber60Row_33_ok,
    mtFiber60Row_34_ok,
    mtFiber60Row_35_ok,
    mtFiber60Row_36_ok,
    mtFiber60Row_37_ok,
    mtFiber60Row_38_ok,
    mtFiber60Row_39_ok,
    mtFiber60Row_40_ok,
    mtFiber60Row_41_ok,
    mtFiber60Row_42_ok,
    mtFiber60Row_43_ok,
    mtFiber60Row_44_ok,
    mtFiber60Row_45_ok,
    mtFiber60Row_46_ok,
    mtFiber60Row_47_ok,
    mtFiber60Row_48_ok,
    mtFiber60Row_49_ok,
    mtFiber60Row_50_ok,
    mtFiber60Row_51_ok,
    mtFiber60Row_52_ok,
    mtFiber60Row_53_ok,
    mtFiber60Row_54_ok,
    mtFiber60Row_55_ok,
    mtFiber60Row_56_ok,
    mtFiber60Row_57_ok,
    mtFiber60Row_58_ok,
    mtFiber60Row_59_ok,
    mtFiber60Row_60_ok,
    mtFiber60Row_61_ok,
    mtFiber60Row_62_ok,
    mtFiber60Row_63_ok,
    mtFiber60Parent_0_ok,
    mtFiber60Parent_1_ok,
    mtFiber60Parent_2_ok,
    mtFiber60Parent_3_ok,
    mtFiber60Parent_4_ok,
    mtFiber60Parent_5_ok,
    mtFiber60Parent_6_ok,
    mtFiber60Parent_7_ok,
    mtFiber60Parent_8_ok,
    mtFiber60Parent_9_ok,
    mtFiber60Parent_10_ok,
    mtFiber60Parent_11_ok,
    mtFiber60Parent_12_ok,
    mtFiber60Parent_13_ok,
    mtFiber60Parent_14_ok,
    mtFiber60Parent_15_ok,
    mtFiber60Parent_16_ok,
    mtFiber60Parent_17_ok,
    mtFiber60Parent_18_ok,
    mtFiber60Parent_19_ok,
    mtFiber60Parent_20_ok,
    mtFiber60Parent_21_ok,
    mtFiber60Parent_22_ok,
    mtFiber60Parent_23_ok,
    mtFiber60Parent_24_ok,
    mtFiber60Parent_25_ok,
    mtFiber60Parent_26_ok,
    mtFiber60Parent_27_ok,
    mtFiber60Parent_28_ok,
    mtFiber60Parent_29_ok,
    mtFiber60Parent_30_ok,
    mtFiber60Parent_31_ok,
    mtFiber60Parent_32_ok,
    mtFiber60Parent_33_ok,
    mtFiber60Parent_34_ok,
    mtFiber60Parent_35_ok,
    mtFiber60Parent_36_ok,
    mtFiber60Parent_37_ok,
    mtFiber60Parent_38_ok,
    mtFiber60Parent_39_ok,
    mtFiber60Parent_40_ok,
    mtFiber60Parent_41_ok,
    mtFiber60Parent_42_ok,
    mtFiber60Parent_43_ok,
    mtFiber60Parent_44_ok,
    mtFiber60Parent_45_ok,
    mtFiber60Parent_46_ok,
    mtFiber60Parent_47_ok,
    mtFiber60Parent_48_ok,
    mtFiber60Parent_49_ok,
    mtFiber60Parent_50_ok,
    mtFiber60Parent_51_ok,
    mtFiber60Parent_52_ok,
    mtFiber60Parent_53_ok,
    mtFiber60Parent_54_ok,
    mtFiber60Parent_55_ok,
    mtFiber60Parent_56_ok,
    mtFiber60Parent_57_ok,
    mtFiber60Parent_58_ok,
    mtFiber60Parent_59_ok,
    mtFiber60Parent_60_ok,
    mtFiber60Parent_61_ok,
    mtFiber60Parent_62_ok,
    mtFiber60Parent_63_ok]

def mtFiber61Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.b]

def mtFiber61Expected : List Nat :=
  []

def mtFiber61Rows : List DirectChainParentRow :=
  []

def mtFiber61RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber61Rows i default

def mtFiber61SourcesCheck : Bool :=
  (mtFiber61Rows.map fun row => row.source) == mtFiber61Expected

theorem mtFiber61SourcesCheck_ok :
    mtFiber61SourcesCheck = true := by
  decide

def mtFiber61RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber61Key mtFiber61Expected (mtFiber61RowAt i)

def mtFiber61ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber61Rows mtMaxParentDepth (listGetD mtFiber61Expected i 0) == 0

def mtFiber61CertificateAudit : Bool :=
  mtFiber61SourcesCheck

theorem mtFiber61CertificateAudit_ok :
    mtFiber61CertificateAudit = true := by
  simp [mtFiber61CertificateAudit,
    mtFiber61SourcesCheck_ok]

def mtFiber62Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.p]

def mtFiber62Expected : List Nat :=
  [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]

def mtFiber62Rows : List DirectChainParentRow :=
  [ directRow 176 176 28 168 28 168 default
  , directRow 177 176 28 169 28 168 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 178 176 28 170 28 168 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 179 177 28 171 28 169 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 180 176 29 160 28 168 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 181 177 29 161 28 169 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 182 178 29 162 28 170 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 183 179 29 163 28 171 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 184 176 30 184 28 168 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 185 177 30 185 28 169 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 186 178 30 186 28 170 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 187 179 30 187 28 171 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 188 180 31 176 29 160 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 189 181 31 177 29 161 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 190 182 31 178 29 162 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 191 183 31 179 29 163 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber62RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber62Rows i default

def mtFiber62SourcesCheck : Bool :=
  (mtFiber62Rows.map fun row => row.source) == mtFiber62Expected

theorem mtFiber62SourcesCheck_ok :
    mtFiber62SourcesCheck = true := by
  decide

def mtFiber62RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt i)

theorem mtFiber62Row_0_ok : mtFiber62RowCheck 0 = true := by decide
theorem mtFiber62Row_1_ok : mtFiber62RowCheck 1 = true := by decide
theorem mtFiber62Row_2_ok : mtFiber62RowCheck 2 = true := by decide
theorem mtFiber62Row_3_ok : mtFiber62RowCheck 3 = true := by decide
theorem mtFiber62Row_4_ok : mtFiber62RowCheck 4 = true := by decide
theorem mtFiber62Row_5_ok : mtFiber62RowCheck 5 = true := by decide
theorem mtFiber62Row_6_ok : mtFiber62RowCheck 6 = true := by decide
theorem mtFiber62Row_7_ok : mtFiber62RowCheck 7 = true := by decide
theorem mtFiber62Row_8_ok : mtFiber62RowCheck 8 = true := by decide
theorem mtFiber62Row_9_ok : mtFiber62RowCheck 9 = true := by decide
theorem mtFiber62Row_10_ok : mtFiber62RowCheck 10 = true := by decide
theorem mtFiber62Row_11_ok : mtFiber62RowCheck 11 = true := by decide
theorem mtFiber62Row_12_ok : mtFiber62RowCheck 12 = true := by decide
theorem mtFiber62Row_13_ok : mtFiber62RowCheck 13 = true := by decide
theorem mtFiber62Row_14_ok : mtFiber62RowCheck 14 = true := by decide
theorem mtFiber62Row_15_ok : mtFiber62RowCheck 15 = true := by decide

def mtFiber62ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber62Rows mtMaxParentDepth (listGetD mtFiber62Expected i 0) == 176

theorem mtFiber62Parent_0_ok : mtFiber62ParentCheck 0 = true := by decide
theorem mtFiber62Parent_1_ok : mtFiber62ParentCheck 1 = true := by decide
theorem mtFiber62Parent_2_ok : mtFiber62ParentCheck 2 = true := by decide
theorem mtFiber62Parent_3_ok : mtFiber62ParentCheck 3 = true := by decide
theorem mtFiber62Parent_4_ok : mtFiber62ParentCheck 4 = true := by decide
theorem mtFiber62Parent_5_ok : mtFiber62ParentCheck 5 = true := by decide
theorem mtFiber62Parent_6_ok : mtFiber62ParentCheck 6 = true := by decide
theorem mtFiber62Parent_7_ok : mtFiber62ParentCheck 7 = true := by decide
theorem mtFiber62Parent_8_ok : mtFiber62ParentCheck 8 = true := by decide
theorem mtFiber62Parent_9_ok : mtFiber62ParentCheck 9 = true := by decide
theorem mtFiber62Parent_10_ok : mtFiber62ParentCheck 10 = true := by decide
theorem mtFiber62Parent_11_ok : mtFiber62ParentCheck 11 = true := by decide
theorem mtFiber62Parent_12_ok : mtFiber62ParentCheck 12 = true := by decide
theorem mtFiber62Parent_13_ok : mtFiber62ParentCheck 13 = true := by decide
theorem mtFiber62Parent_14_ok : mtFiber62ParentCheck 14 = true := by decide
theorem mtFiber62Parent_15_ok : mtFiber62ParentCheck 15 = true := by decide

def mtFiber62CertificateAudit : Bool :=
  mtFiber62SourcesCheck &&
    mtFiber62RowCheck 0 &&
    mtFiber62RowCheck 1 &&
    mtFiber62RowCheck 2 &&
    mtFiber62RowCheck 3 &&
    mtFiber62RowCheck 4 &&
    mtFiber62RowCheck 5 &&
    mtFiber62RowCheck 6 &&
    mtFiber62RowCheck 7 &&
    mtFiber62RowCheck 8 &&
    mtFiber62RowCheck 9 &&
    mtFiber62RowCheck 10 &&
    mtFiber62RowCheck 11 &&
    mtFiber62RowCheck 12 &&
    mtFiber62RowCheck 13 &&
    mtFiber62RowCheck 14 &&
    mtFiber62RowCheck 15 &&
    mtFiber62ParentCheck 0 &&
    mtFiber62ParentCheck 1 &&
    mtFiber62ParentCheck 2 &&
    mtFiber62ParentCheck 3 &&
    mtFiber62ParentCheck 4 &&
    mtFiber62ParentCheck 5 &&
    mtFiber62ParentCheck 6 &&
    mtFiber62ParentCheck 7 &&
    mtFiber62ParentCheck 8 &&
    mtFiber62ParentCheck 9 &&
    mtFiber62ParentCheck 10 &&
    mtFiber62ParentCheck 11 &&
    mtFiber62ParentCheck 12 &&
    mtFiber62ParentCheck 13 &&
    mtFiber62ParentCheck 14 &&
    mtFiber62ParentCheck 15

theorem mtFiber62CertificateAudit_ok :
    mtFiber62CertificateAudit = true := by
  simp [mtFiber62CertificateAudit,
    mtFiber62SourcesCheck_ok,
    mtFiber62Row_0_ok,
    mtFiber62Row_1_ok,
    mtFiber62Row_2_ok,
    mtFiber62Row_3_ok,
    mtFiber62Row_4_ok,
    mtFiber62Row_5_ok,
    mtFiber62Row_6_ok,
    mtFiber62Row_7_ok,
    mtFiber62Row_8_ok,
    mtFiber62Row_9_ok,
    mtFiber62Row_10_ok,
    mtFiber62Row_11_ok,
    mtFiber62Row_12_ok,
    mtFiber62Row_13_ok,
    mtFiber62Row_14_ok,
    mtFiber62Row_15_ok,
    mtFiber62Parent_0_ok,
    mtFiber62Parent_1_ok,
    mtFiber62Parent_2_ok,
    mtFiber62Parent_3_ok,
    mtFiber62Parent_4_ok,
    mtFiber62Parent_5_ok,
    mtFiber62Parent_6_ok,
    mtFiber62Parent_7_ok,
    mtFiber62Parent_8_ok,
    mtFiber62Parent_9_ok,
    mtFiber62Parent_10_ok,
    mtFiber62Parent_11_ok,
    mtFiber62Parent_12_ok,
    mtFiber62Parent_13_ok,
    mtFiber62Parent_14_ok,
    mtFiber62Parent_15_ok]

def mtFiber63Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.r]

def mtFiber63Expected : List Nat :=
  [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]

def mtFiber63Rows : List DirectChainParentRow :=
  [ directRow 416 416 68 152 68 152 default
  , directRow 417 416 68 153 68 152 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 418 417 68 154 68 153 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 419 416 68 155 68 152 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 420 416 69 144 68 152 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 421 417 69 145 68 153 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 422 418 69 146 68 154 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 423 419 69 147 68 155 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 424 416 70 136 68 152 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 425 417 70 137 68 153 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 426 418 70 138 68 154 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 427 419 70 139 68 155 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 428 420 71 128 69 144 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 429 421 71 129 69 145 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 430 422 71 130 69 146 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 431 423 71 131 69 147 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber63RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber63Rows i default

def mtFiber63SourcesCheck : Bool :=
  (mtFiber63Rows.map fun row => row.source) == mtFiber63Expected

theorem mtFiber63SourcesCheck_ok :
    mtFiber63SourcesCheck = true := by
  decide

def mtFiber63RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt i)

theorem mtFiber63Row_0_ok : mtFiber63RowCheck 0 = true := by decide
theorem mtFiber63Row_1_ok : mtFiber63RowCheck 1 = true := by decide
theorem mtFiber63Row_2_ok : mtFiber63RowCheck 2 = true := by decide
theorem mtFiber63Row_3_ok : mtFiber63RowCheck 3 = true := by decide
theorem mtFiber63Row_4_ok : mtFiber63RowCheck 4 = true := by decide
theorem mtFiber63Row_5_ok : mtFiber63RowCheck 5 = true := by decide
theorem mtFiber63Row_6_ok : mtFiber63RowCheck 6 = true := by decide
theorem mtFiber63Row_7_ok : mtFiber63RowCheck 7 = true := by decide
theorem mtFiber63Row_8_ok : mtFiber63RowCheck 8 = true := by decide
theorem mtFiber63Row_9_ok : mtFiber63RowCheck 9 = true := by decide
theorem mtFiber63Row_10_ok : mtFiber63RowCheck 10 = true := by decide
theorem mtFiber63Row_11_ok : mtFiber63RowCheck 11 = true := by decide
theorem mtFiber63Row_12_ok : mtFiber63RowCheck 12 = true := by decide
theorem mtFiber63Row_13_ok : mtFiber63RowCheck 13 = true := by decide
theorem mtFiber63Row_14_ok : mtFiber63RowCheck 14 = true := by decide
theorem mtFiber63Row_15_ok : mtFiber63RowCheck 15 = true := by decide

def mtFiber63ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber63Rows mtMaxParentDepth (listGetD mtFiber63Expected i 0) == 416

theorem mtFiber63Parent_0_ok : mtFiber63ParentCheck 0 = true := by decide
theorem mtFiber63Parent_1_ok : mtFiber63ParentCheck 1 = true := by decide
theorem mtFiber63Parent_2_ok : mtFiber63ParentCheck 2 = true := by decide
theorem mtFiber63Parent_3_ok : mtFiber63ParentCheck 3 = true := by decide
theorem mtFiber63Parent_4_ok : mtFiber63ParentCheck 4 = true := by decide
theorem mtFiber63Parent_5_ok : mtFiber63ParentCheck 5 = true := by decide
theorem mtFiber63Parent_6_ok : mtFiber63ParentCheck 6 = true := by decide
theorem mtFiber63Parent_7_ok : mtFiber63ParentCheck 7 = true := by decide
theorem mtFiber63Parent_8_ok : mtFiber63ParentCheck 8 = true := by decide
theorem mtFiber63Parent_9_ok : mtFiber63ParentCheck 9 = true := by decide
theorem mtFiber63Parent_10_ok : mtFiber63ParentCheck 10 = true := by decide
theorem mtFiber63Parent_11_ok : mtFiber63ParentCheck 11 = true := by decide
theorem mtFiber63Parent_12_ok : mtFiber63ParentCheck 12 = true := by decide
theorem mtFiber63Parent_13_ok : mtFiber63ParentCheck 13 = true := by decide
theorem mtFiber63Parent_14_ok : mtFiber63ParentCheck 14 = true := by decide
theorem mtFiber63Parent_15_ok : mtFiber63ParentCheck 15 = true := by decide

def mtFiber63CertificateAudit : Bool :=
  mtFiber63SourcesCheck &&
    mtFiber63RowCheck 0 &&
    mtFiber63RowCheck 1 &&
    mtFiber63RowCheck 2 &&
    mtFiber63RowCheck 3 &&
    mtFiber63RowCheck 4 &&
    mtFiber63RowCheck 5 &&
    mtFiber63RowCheck 6 &&
    mtFiber63RowCheck 7 &&
    mtFiber63RowCheck 8 &&
    mtFiber63RowCheck 9 &&
    mtFiber63RowCheck 10 &&
    mtFiber63RowCheck 11 &&
    mtFiber63RowCheck 12 &&
    mtFiber63RowCheck 13 &&
    mtFiber63RowCheck 14 &&
    mtFiber63RowCheck 15 &&
    mtFiber63ParentCheck 0 &&
    mtFiber63ParentCheck 1 &&
    mtFiber63ParentCheck 2 &&
    mtFiber63ParentCheck 3 &&
    mtFiber63ParentCheck 4 &&
    mtFiber63ParentCheck 5 &&
    mtFiber63ParentCheck 6 &&
    mtFiber63ParentCheck 7 &&
    mtFiber63ParentCheck 8 &&
    mtFiber63ParentCheck 9 &&
    mtFiber63ParentCheck 10 &&
    mtFiber63ParentCheck 11 &&
    mtFiber63ParentCheck 12 &&
    mtFiber63ParentCheck 13 &&
    mtFiber63ParentCheck 14 &&
    mtFiber63ParentCheck 15

theorem mtFiber63CertificateAudit_ok :
    mtFiber63CertificateAudit = true := by
  simp [mtFiber63CertificateAudit,
    mtFiber63SourcesCheck_ok,
    mtFiber63Row_0_ok,
    mtFiber63Row_1_ok,
    mtFiber63Row_2_ok,
    mtFiber63Row_3_ok,
    mtFiber63Row_4_ok,
    mtFiber63Row_5_ok,
    mtFiber63Row_6_ok,
    mtFiber63Row_7_ok,
    mtFiber63Row_8_ok,
    mtFiber63Row_9_ok,
    mtFiber63Row_10_ok,
    mtFiber63Row_11_ok,
    mtFiber63Row_12_ok,
    mtFiber63Row_13_ok,
    mtFiber63Row_14_ok,
    mtFiber63Row_15_ok,
    mtFiber63Parent_0_ok,
    mtFiber63Parent_1_ok,
    mtFiber63Parent_2_ok,
    mtFiber63Parent_3_ok,
    mtFiber63Parent_4_ok,
    mtFiber63Parent_5_ok,
    mtFiber63Parent_6_ok,
    mtFiber63Parent_7_ok,
    mtFiber63Parent_8_ok,
    mtFiber63Parent_9_ok,
    mtFiber63Parent_10_ok,
    mtFiber63Parent_11_ok,
    mtFiber63Parent_12_ok,
    mtFiber63Parent_13_ok,
    mtFiber63Parent_14_ok,
    mtFiber63Parent_15_ok]

def mtFiber64Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.b]

def mtFiber64Expected : List Nat :=
  [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

def mtFiber64Rows : List DirectChainParentRow :=
  [ directRow 32 32 4 168 4 168 default
  , directRow 33 32 4 169 4 168 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 34 32 4 170 4 168 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 35 33 4 171 4 169 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 36 32 5 160 4 168 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 37 33 5 161 4 169 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 38 34 5 162 4 170 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 39 35 5 163 4 171 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 40 32 6 184 4 168 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 41 33 6 185 4 169 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 42 34 6 186 4 170 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 43 35 6 187 4 171 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 44 36 7 176 5 160 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 45 37 7 177 5 161 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 46 38 7 178 5 162 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 47 39 7 179 5 163 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber64RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber64Rows i default

def mtFiber64SourcesCheck : Bool :=
  (mtFiber64Rows.map fun row => row.source) == mtFiber64Expected

theorem mtFiber64SourcesCheck_ok :
    mtFiber64SourcesCheck = true := by
  decide

def mtFiber64RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt i)

theorem mtFiber64Row_0_ok : mtFiber64RowCheck 0 = true := by decide
theorem mtFiber64Row_1_ok : mtFiber64RowCheck 1 = true := by decide
theorem mtFiber64Row_2_ok : mtFiber64RowCheck 2 = true := by decide
theorem mtFiber64Row_3_ok : mtFiber64RowCheck 3 = true := by decide
theorem mtFiber64Row_4_ok : mtFiber64RowCheck 4 = true := by decide
theorem mtFiber64Row_5_ok : mtFiber64RowCheck 5 = true := by decide
theorem mtFiber64Row_6_ok : mtFiber64RowCheck 6 = true := by decide
theorem mtFiber64Row_7_ok : mtFiber64RowCheck 7 = true := by decide
theorem mtFiber64Row_8_ok : mtFiber64RowCheck 8 = true := by decide
theorem mtFiber64Row_9_ok : mtFiber64RowCheck 9 = true := by decide
theorem mtFiber64Row_10_ok : mtFiber64RowCheck 10 = true := by decide
theorem mtFiber64Row_11_ok : mtFiber64RowCheck 11 = true := by decide
theorem mtFiber64Row_12_ok : mtFiber64RowCheck 12 = true := by decide
theorem mtFiber64Row_13_ok : mtFiber64RowCheck 13 = true := by decide
theorem mtFiber64Row_14_ok : mtFiber64RowCheck 14 = true := by decide
theorem mtFiber64Row_15_ok : mtFiber64RowCheck 15 = true := by decide

def mtFiber64ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber64Rows mtMaxParentDepth (listGetD mtFiber64Expected i 0) == 32

theorem mtFiber64Parent_0_ok : mtFiber64ParentCheck 0 = true := by decide
theorem mtFiber64Parent_1_ok : mtFiber64ParentCheck 1 = true := by decide
theorem mtFiber64Parent_2_ok : mtFiber64ParentCheck 2 = true := by decide
theorem mtFiber64Parent_3_ok : mtFiber64ParentCheck 3 = true := by decide
theorem mtFiber64Parent_4_ok : mtFiber64ParentCheck 4 = true := by decide
theorem mtFiber64Parent_5_ok : mtFiber64ParentCheck 5 = true := by decide
theorem mtFiber64Parent_6_ok : mtFiber64ParentCheck 6 = true := by decide
theorem mtFiber64Parent_7_ok : mtFiber64ParentCheck 7 = true := by decide
theorem mtFiber64Parent_8_ok : mtFiber64ParentCheck 8 = true := by decide
theorem mtFiber64Parent_9_ok : mtFiber64ParentCheck 9 = true := by decide
theorem mtFiber64Parent_10_ok : mtFiber64ParentCheck 10 = true := by decide
theorem mtFiber64Parent_11_ok : mtFiber64ParentCheck 11 = true := by decide
theorem mtFiber64Parent_12_ok : mtFiber64ParentCheck 12 = true := by decide
theorem mtFiber64Parent_13_ok : mtFiber64ParentCheck 13 = true := by decide
theorem mtFiber64Parent_14_ok : mtFiber64ParentCheck 14 = true := by decide
theorem mtFiber64Parent_15_ok : mtFiber64ParentCheck 15 = true := by decide

def mtFiber64CertificateAudit : Bool :=
  mtFiber64SourcesCheck &&
    mtFiber64RowCheck 0 &&
    mtFiber64RowCheck 1 &&
    mtFiber64RowCheck 2 &&
    mtFiber64RowCheck 3 &&
    mtFiber64RowCheck 4 &&
    mtFiber64RowCheck 5 &&
    mtFiber64RowCheck 6 &&
    mtFiber64RowCheck 7 &&
    mtFiber64RowCheck 8 &&
    mtFiber64RowCheck 9 &&
    mtFiber64RowCheck 10 &&
    mtFiber64RowCheck 11 &&
    mtFiber64RowCheck 12 &&
    mtFiber64RowCheck 13 &&
    mtFiber64RowCheck 14 &&
    mtFiber64RowCheck 15 &&
    mtFiber64ParentCheck 0 &&
    mtFiber64ParentCheck 1 &&
    mtFiber64ParentCheck 2 &&
    mtFiber64ParentCheck 3 &&
    mtFiber64ParentCheck 4 &&
    mtFiber64ParentCheck 5 &&
    mtFiber64ParentCheck 6 &&
    mtFiber64ParentCheck 7 &&
    mtFiber64ParentCheck 8 &&
    mtFiber64ParentCheck 9 &&
    mtFiber64ParentCheck 10 &&
    mtFiber64ParentCheck 11 &&
    mtFiber64ParentCheck 12 &&
    mtFiber64ParentCheck 13 &&
    mtFiber64ParentCheck 14 &&
    mtFiber64ParentCheck 15

theorem mtFiber64CertificateAudit_ok :
    mtFiber64CertificateAudit = true := by
  simp [mtFiber64CertificateAudit,
    mtFiber64SourcesCheck_ok,
    mtFiber64Row_0_ok,
    mtFiber64Row_1_ok,
    mtFiber64Row_2_ok,
    mtFiber64Row_3_ok,
    mtFiber64Row_4_ok,
    mtFiber64Row_5_ok,
    mtFiber64Row_6_ok,
    mtFiber64Row_7_ok,
    mtFiber64Row_8_ok,
    mtFiber64Row_9_ok,
    mtFiber64Row_10_ok,
    mtFiber64Row_11_ok,
    mtFiber64Row_12_ok,
    mtFiber64Row_13_ok,
    mtFiber64Row_14_ok,
    mtFiber64Row_15_ok,
    mtFiber64Parent_0_ok,
    mtFiber64Parent_1_ok,
    mtFiber64Parent_2_ok,
    mtFiber64Parent_3_ok,
    mtFiber64Parent_4_ok,
    mtFiber64Parent_5_ok,
    mtFiber64Parent_6_ok,
    mtFiber64Parent_7_ok,
    mtFiber64Parent_8_ok,
    mtFiber64Parent_9_ok,
    mtFiber64Parent_10_ok,
    mtFiber64Parent_11_ok,
    mtFiber64Parent_12_ok,
    mtFiber64Parent_13_ok,
    mtFiber64Parent_14_ok,
    mtFiber64Parent_15_ok]

def mtFiber65Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.p]

def mtFiber65Expected : List Nat :=
  []

def mtFiber65Rows : List DirectChainParentRow :=
  []

def mtFiber65RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber65Rows i default

def mtFiber65SourcesCheck : Bool :=
  (mtFiber65Rows.map fun row => row.source) == mtFiber65Expected

theorem mtFiber65SourcesCheck_ok :
    mtFiber65SourcesCheck = true := by
  decide

def mtFiber65RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber65Key mtFiber65Expected (mtFiber65RowAt i)

def mtFiber65ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber65Rows mtMaxParentDepth (listGetD mtFiber65Expected i 0) == 0

def mtFiber65CertificateAudit : Bool :=
  mtFiber65SourcesCheck

theorem mtFiber65CertificateAudit_ok :
    mtFiber65CertificateAudit = true := by
  simp [mtFiber65CertificateAudit,
    mtFiber65SourcesCheck_ok]

def mtFiber66Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.r]

def mtFiber66Expected : List Nat :=
  []

def mtFiber66Rows : List DirectChainParentRow :=
  []

def mtFiber66RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber66Rows i default

def mtFiber66SourcesCheck : Bool :=
  (mtFiber66Rows.map fun row => row.source) == mtFiber66Expected

theorem mtFiber66SourcesCheck_ok :
    mtFiber66SourcesCheck = true := by
  decide

def mtFiber66RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber66Key mtFiber66Expected (mtFiber66RowAt i)

def mtFiber66ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber66Rows mtMaxParentDepth (listGetD mtFiber66Expected i 0) == 0

def mtFiber66CertificateAudit : Bool :=
  mtFiber66SourcesCheck

theorem mtFiber66CertificateAudit_ok :
    mtFiber66CertificateAudit = true := by
  simp [mtFiber66CertificateAudit,
    mtFiber66SourcesCheck_ok]

def mtFiber67Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.b]

def mtFiber67Expected : List Nat :=
  []

def mtFiber67Rows : List DirectChainParentRow :=
  []

def mtFiber67RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber67Rows i default

def mtFiber67SourcesCheck : Bool :=
  (mtFiber67Rows.map fun row => row.source) == mtFiber67Expected

theorem mtFiber67SourcesCheck_ok :
    mtFiber67SourcesCheck = true := by
  decide

def mtFiber67RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber67Key mtFiber67Expected (mtFiber67RowAt i)

def mtFiber67ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber67Rows mtMaxParentDepth (listGetD mtFiber67Expected i 0) == 0

def mtFiber67CertificateAudit : Bool :=
  mtFiber67SourcesCheck

theorem mtFiber67CertificateAudit_ok :
    mtFiber67CertificateAudit = true := by
  simp [mtFiber67CertificateAudit,
    mtFiber67SourcesCheck_ok]

def mtFiber68Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.p]

def mtFiber68Expected : List Nat :=
  []

def mtFiber68Rows : List DirectChainParentRow :=
  []

def mtFiber68RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber68Rows i default

def mtFiber68SourcesCheck : Bool :=
  (mtFiber68Rows.map fun row => row.source) == mtFiber68Expected

theorem mtFiber68SourcesCheck_ok :
    mtFiber68SourcesCheck = true := by
  decide

def mtFiber68RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber68Key mtFiber68Expected (mtFiber68RowAt i)

def mtFiber68ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber68Rows mtMaxParentDepth (listGetD mtFiber68Expected i 0) == 0

def mtFiber68CertificateAudit : Bool :=
  mtFiber68SourcesCheck

theorem mtFiber68CertificateAudit_ok :
    mtFiber68CertificateAudit = true := by
  simp [mtFiber68CertificateAudit,
    mtFiber68SourcesCheck_ok]

def mtFiber69Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.r]

def mtFiber69Expected : List Nat :=
  []

def mtFiber69Rows : List DirectChainParentRow :=
  []

def mtFiber69RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber69Rows i default

def mtFiber69SourcesCheck : Bool :=
  (mtFiber69Rows.map fun row => row.source) == mtFiber69Expected

theorem mtFiber69SourcesCheck_ok :
    mtFiber69SourcesCheck = true := by
  decide

def mtFiber69RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber69Key mtFiber69Expected (mtFiber69RowAt i)

def mtFiber69ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber69Rows mtMaxParentDepth (listGetD mtFiber69Expected i 0) == 0

def mtFiber69CertificateAudit : Bool :=
  mtFiber69SourcesCheck

theorem mtFiber69CertificateAudit_ok :
    mtFiber69CertificateAudit = true := by
  simp [mtFiber69CertificateAudit,
    mtFiber69SourcesCheck_ok]

def mtFiber70Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.b]

def mtFiber70Expected : List Nat :=
  [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]

def mtFiber70Rows : List DirectChainParentRow :=
  [ directRow 928 928 156 88 156 88 default
  , directRow 929 928 156 89 156 88 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 930 928 156 90 156 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 931 929 156 91 156 89 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 932 930 156 108 156 90 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 933 935 156 109 156 111 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 934 929 156 110 156 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 935 928 156 111 156 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 936 928 157 80 156 88 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 937 929 157 81 156 89 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 938 930 157 82 156 90 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 939 931 157 83 156 91 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 940 932 157 100 156 108 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 941 933 157 101 156 109 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 942 934 157 102 156 110 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 943 935 157 103 156 111 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 944 936 158 72 157 80 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 945 937 158 73 157 81 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 946 938 158 74 157 82 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 947 939 158 75 157 83 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 948 940 158 124 157 100 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 949 941 158 125 157 101 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 950 942 158 126 157 102 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 951 943 158 127 157 103 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 952 928 159 64 156 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 953 929 159 65 156 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 954 930 159 66 156 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 955 931 159 67 156 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 956 932 159 116 156 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 957 933 159 117 156 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 958 934 159 118 156 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 959 935 159 119 156 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 1024 928 172 24 156 88 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1025 929 172 25 156 89 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1026 930 172 26 156 90 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1027 931 172 27 156 91 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1028 1024 172 40 172 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1029 1025 172 41 172 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1030 934 172 42 156 110 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1031 935 172 43 156 111 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1032 936 173 16 157 80 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1033 937 173 17 157 81 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1034 938 173 18 157 82 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1035 939 173 19 157 83 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1036 1032 173 32 173 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1037 1033 173 33 173 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1038 942 173 34 157 102 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1039 943 173 35 157 103 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1040 1024 174 8 172 24 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1041 1025 174 9 172 25 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1042 1026 174 10 172 26 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1043 1027 174 11 172 27 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1044 1028 174 56 172 40 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1045 1029 174 57 172 41 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1046 1030 174 58 172 42 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1047 1031 174 59 172 43 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1048 952 175 0 159 64 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1049 953 175 1 159 65 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1050 954 175 2 159 66 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1051 955 175 3 159 67 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1052 1048 175 48 175 0 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1053 1049 175 49 175 1 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1054 958 175 50 159 118 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1055 959 175 51 159 119 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mtFiber70RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber70Rows i default

def mtFiber70SourcesCheck : Bool :=
  (mtFiber70Rows.map fun row => row.source) == mtFiber70Expected

theorem mtFiber70SourcesCheck_ok :
    mtFiber70SourcesCheck = true := by
  decide

def mtFiber70RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt i)

theorem mtFiber70Row_0_ok : mtFiber70RowCheck 0 = true := by decide
theorem mtFiber70Row_1_ok : mtFiber70RowCheck 1 = true := by decide
theorem mtFiber70Row_2_ok : mtFiber70RowCheck 2 = true := by decide
theorem mtFiber70Row_3_ok : mtFiber70RowCheck 3 = true := by decide
theorem mtFiber70Row_4_ok : mtFiber70RowCheck 4 = true := by decide
theorem mtFiber70Row_5_ok : mtFiber70RowCheck 5 = true := by decide
theorem mtFiber70Row_6_ok : mtFiber70RowCheck 6 = true := by decide
theorem mtFiber70Row_7_ok : mtFiber70RowCheck 7 = true := by decide
theorem mtFiber70Row_8_ok : mtFiber70RowCheck 8 = true := by decide
theorem mtFiber70Row_9_ok : mtFiber70RowCheck 9 = true := by decide
theorem mtFiber70Row_10_ok : mtFiber70RowCheck 10 = true := by decide
theorem mtFiber70Row_11_ok : mtFiber70RowCheck 11 = true := by decide
theorem mtFiber70Row_12_ok : mtFiber70RowCheck 12 = true := by decide
theorem mtFiber70Row_13_ok : mtFiber70RowCheck 13 = true := by decide
theorem mtFiber70Row_14_ok : mtFiber70RowCheck 14 = true := by decide
theorem mtFiber70Row_15_ok : mtFiber70RowCheck 15 = true := by decide
theorem mtFiber70Row_16_ok : mtFiber70RowCheck 16 = true := by decide
theorem mtFiber70Row_17_ok : mtFiber70RowCheck 17 = true := by decide
theorem mtFiber70Row_18_ok : mtFiber70RowCheck 18 = true := by decide
theorem mtFiber70Row_19_ok : mtFiber70RowCheck 19 = true := by decide
theorem mtFiber70Row_20_ok : mtFiber70RowCheck 20 = true := by decide
theorem mtFiber70Row_21_ok : mtFiber70RowCheck 21 = true := by decide
theorem mtFiber70Row_22_ok : mtFiber70RowCheck 22 = true := by decide
theorem mtFiber70Row_23_ok : mtFiber70RowCheck 23 = true := by decide
theorem mtFiber70Row_24_ok : mtFiber70RowCheck 24 = true := by decide
theorem mtFiber70Row_25_ok : mtFiber70RowCheck 25 = true := by decide
theorem mtFiber70Row_26_ok : mtFiber70RowCheck 26 = true := by decide
theorem mtFiber70Row_27_ok : mtFiber70RowCheck 27 = true := by decide
theorem mtFiber70Row_28_ok : mtFiber70RowCheck 28 = true := by decide
theorem mtFiber70Row_29_ok : mtFiber70RowCheck 29 = true := by decide
theorem mtFiber70Row_30_ok : mtFiber70RowCheck 30 = true := by decide
theorem mtFiber70Row_31_ok : mtFiber70RowCheck 31 = true := by decide
theorem mtFiber70Row_32_ok : mtFiber70RowCheck 32 = true := by decide
theorem mtFiber70Row_33_ok : mtFiber70RowCheck 33 = true := by decide
theorem mtFiber70Row_34_ok : mtFiber70RowCheck 34 = true := by decide
theorem mtFiber70Row_35_ok : mtFiber70RowCheck 35 = true := by decide
theorem mtFiber70Row_36_ok : mtFiber70RowCheck 36 = true := by decide
theorem mtFiber70Row_37_ok : mtFiber70RowCheck 37 = true := by decide
theorem mtFiber70Row_38_ok : mtFiber70RowCheck 38 = true := by decide
theorem mtFiber70Row_39_ok : mtFiber70RowCheck 39 = true := by decide
theorem mtFiber70Row_40_ok : mtFiber70RowCheck 40 = true := by decide
theorem mtFiber70Row_41_ok : mtFiber70RowCheck 41 = true := by decide
theorem mtFiber70Row_42_ok : mtFiber70RowCheck 42 = true := by decide
theorem mtFiber70Row_43_ok : mtFiber70RowCheck 43 = true := by decide
theorem mtFiber70Row_44_ok : mtFiber70RowCheck 44 = true := by decide
theorem mtFiber70Row_45_ok : mtFiber70RowCheck 45 = true := by decide
theorem mtFiber70Row_46_ok : mtFiber70RowCheck 46 = true := by decide
theorem mtFiber70Row_47_ok : mtFiber70RowCheck 47 = true := by decide
theorem mtFiber70Row_48_ok : mtFiber70RowCheck 48 = true := by decide
theorem mtFiber70Row_49_ok : mtFiber70RowCheck 49 = true := by decide
theorem mtFiber70Row_50_ok : mtFiber70RowCheck 50 = true := by decide
theorem mtFiber70Row_51_ok : mtFiber70RowCheck 51 = true := by decide
theorem mtFiber70Row_52_ok : mtFiber70RowCheck 52 = true := by decide
theorem mtFiber70Row_53_ok : mtFiber70RowCheck 53 = true := by decide
theorem mtFiber70Row_54_ok : mtFiber70RowCheck 54 = true := by decide
theorem mtFiber70Row_55_ok : mtFiber70RowCheck 55 = true := by decide
theorem mtFiber70Row_56_ok : mtFiber70RowCheck 56 = true := by decide
theorem mtFiber70Row_57_ok : mtFiber70RowCheck 57 = true := by decide
theorem mtFiber70Row_58_ok : mtFiber70RowCheck 58 = true := by decide
theorem mtFiber70Row_59_ok : mtFiber70RowCheck 59 = true := by decide
theorem mtFiber70Row_60_ok : mtFiber70RowCheck 60 = true := by decide
theorem mtFiber70Row_61_ok : mtFiber70RowCheck 61 = true := by decide
theorem mtFiber70Row_62_ok : mtFiber70RowCheck 62 = true := by decide
theorem mtFiber70Row_63_ok : mtFiber70RowCheck 63 = true := by decide

def mtFiber70ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber70Rows mtMaxParentDepth (listGetD mtFiber70Expected i 0) == 928

theorem mtFiber70Parent_0_ok : mtFiber70ParentCheck 0 = true := by decide
theorem mtFiber70Parent_1_ok : mtFiber70ParentCheck 1 = true := by decide
theorem mtFiber70Parent_2_ok : mtFiber70ParentCheck 2 = true := by decide
theorem mtFiber70Parent_3_ok : mtFiber70ParentCheck 3 = true := by decide
theorem mtFiber70Parent_4_ok : mtFiber70ParentCheck 4 = true := by decide
theorem mtFiber70Parent_5_ok : mtFiber70ParentCheck 5 = true := by decide
theorem mtFiber70Parent_6_ok : mtFiber70ParentCheck 6 = true := by decide
theorem mtFiber70Parent_7_ok : mtFiber70ParentCheck 7 = true := by decide
theorem mtFiber70Parent_8_ok : mtFiber70ParentCheck 8 = true := by decide
theorem mtFiber70Parent_9_ok : mtFiber70ParentCheck 9 = true := by decide
theorem mtFiber70Parent_10_ok : mtFiber70ParentCheck 10 = true := by decide
theorem mtFiber70Parent_11_ok : mtFiber70ParentCheck 11 = true := by decide
theorem mtFiber70Parent_12_ok : mtFiber70ParentCheck 12 = true := by decide
theorem mtFiber70Parent_13_ok : mtFiber70ParentCheck 13 = true := by decide
theorem mtFiber70Parent_14_ok : mtFiber70ParentCheck 14 = true := by decide
theorem mtFiber70Parent_15_ok : mtFiber70ParentCheck 15 = true := by decide
theorem mtFiber70Parent_16_ok : mtFiber70ParentCheck 16 = true := by decide
theorem mtFiber70Parent_17_ok : mtFiber70ParentCheck 17 = true := by decide
theorem mtFiber70Parent_18_ok : mtFiber70ParentCheck 18 = true := by decide
theorem mtFiber70Parent_19_ok : mtFiber70ParentCheck 19 = true := by decide
theorem mtFiber70Parent_20_ok : mtFiber70ParentCheck 20 = true := by decide
theorem mtFiber70Parent_21_ok : mtFiber70ParentCheck 21 = true := by decide
theorem mtFiber70Parent_22_ok : mtFiber70ParentCheck 22 = true := by decide
theorem mtFiber70Parent_23_ok : mtFiber70ParentCheck 23 = true := by decide
theorem mtFiber70Parent_24_ok : mtFiber70ParentCheck 24 = true := by decide
theorem mtFiber70Parent_25_ok : mtFiber70ParentCheck 25 = true := by decide
theorem mtFiber70Parent_26_ok : mtFiber70ParentCheck 26 = true := by decide
theorem mtFiber70Parent_27_ok : mtFiber70ParentCheck 27 = true := by decide
theorem mtFiber70Parent_28_ok : mtFiber70ParentCheck 28 = true := by decide
theorem mtFiber70Parent_29_ok : mtFiber70ParentCheck 29 = true := by decide
theorem mtFiber70Parent_30_ok : mtFiber70ParentCheck 30 = true := by decide
theorem mtFiber70Parent_31_ok : mtFiber70ParentCheck 31 = true := by decide
theorem mtFiber70Parent_32_ok : mtFiber70ParentCheck 32 = true := by decide
theorem mtFiber70Parent_33_ok : mtFiber70ParentCheck 33 = true := by decide
theorem mtFiber70Parent_34_ok : mtFiber70ParentCheck 34 = true := by decide
theorem mtFiber70Parent_35_ok : mtFiber70ParentCheck 35 = true := by decide
theorem mtFiber70Parent_36_ok : mtFiber70ParentCheck 36 = true := by decide
theorem mtFiber70Parent_37_ok : mtFiber70ParentCheck 37 = true := by decide
theorem mtFiber70Parent_38_ok : mtFiber70ParentCheck 38 = true := by decide
theorem mtFiber70Parent_39_ok : mtFiber70ParentCheck 39 = true := by decide
theorem mtFiber70Parent_40_ok : mtFiber70ParentCheck 40 = true := by decide
theorem mtFiber70Parent_41_ok : mtFiber70ParentCheck 41 = true := by decide
theorem mtFiber70Parent_42_ok : mtFiber70ParentCheck 42 = true := by decide
theorem mtFiber70Parent_43_ok : mtFiber70ParentCheck 43 = true := by decide
theorem mtFiber70Parent_44_ok : mtFiber70ParentCheck 44 = true := by decide
theorem mtFiber70Parent_45_ok : mtFiber70ParentCheck 45 = true := by decide
theorem mtFiber70Parent_46_ok : mtFiber70ParentCheck 46 = true := by decide
theorem mtFiber70Parent_47_ok : mtFiber70ParentCheck 47 = true := by decide
theorem mtFiber70Parent_48_ok : mtFiber70ParentCheck 48 = true := by decide
theorem mtFiber70Parent_49_ok : mtFiber70ParentCheck 49 = true := by decide
theorem mtFiber70Parent_50_ok : mtFiber70ParentCheck 50 = true := by decide
theorem mtFiber70Parent_51_ok : mtFiber70ParentCheck 51 = true := by decide
theorem mtFiber70Parent_52_ok : mtFiber70ParentCheck 52 = true := by decide
theorem mtFiber70Parent_53_ok : mtFiber70ParentCheck 53 = true := by decide
theorem mtFiber70Parent_54_ok : mtFiber70ParentCheck 54 = true := by decide
theorem mtFiber70Parent_55_ok : mtFiber70ParentCheck 55 = true := by decide
theorem mtFiber70Parent_56_ok : mtFiber70ParentCheck 56 = true := by decide
theorem mtFiber70Parent_57_ok : mtFiber70ParentCheck 57 = true := by decide
theorem mtFiber70Parent_58_ok : mtFiber70ParentCheck 58 = true := by decide
theorem mtFiber70Parent_59_ok : mtFiber70ParentCheck 59 = true := by decide
theorem mtFiber70Parent_60_ok : mtFiber70ParentCheck 60 = true := by decide
theorem mtFiber70Parent_61_ok : mtFiber70ParentCheck 61 = true := by decide
theorem mtFiber70Parent_62_ok : mtFiber70ParentCheck 62 = true := by decide
theorem mtFiber70Parent_63_ok : mtFiber70ParentCheck 63 = true := by decide

def mtFiber70CertificateAudit : Bool :=
  mtFiber70SourcesCheck &&
    mtFiber70RowCheck 0 &&
    mtFiber70RowCheck 1 &&
    mtFiber70RowCheck 2 &&
    mtFiber70RowCheck 3 &&
    mtFiber70RowCheck 4 &&
    mtFiber70RowCheck 5 &&
    mtFiber70RowCheck 6 &&
    mtFiber70RowCheck 7 &&
    mtFiber70RowCheck 8 &&
    mtFiber70RowCheck 9 &&
    mtFiber70RowCheck 10 &&
    mtFiber70RowCheck 11 &&
    mtFiber70RowCheck 12 &&
    mtFiber70RowCheck 13 &&
    mtFiber70RowCheck 14 &&
    mtFiber70RowCheck 15 &&
    mtFiber70RowCheck 16 &&
    mtFiber70RowCheck 17 &&
    mtFiber70RowCheck 18 &&
    mtFiber70RowCheck 19 &&
    mtFiber70RowCheck 20 &&
    mtFiber70RowCheck 21 &&
    mtFiber70RowCheck 22 &&
    mtFiber70RowCheck 23 &&
    mtFiber70RowCheck 24 &&
    mtFiber70RowCheck 25 &&
    mtFiber70RowCheck 26 &&
    mtFiber70RowCheck 27 &&
    mtFiber70RowCheck 28 &&
    mtFiber70RowCheck 29 &&
    mtFiber70RowCheck 30 &&
    mtFiber70RowCheck 31 &&
    mtFiber70RowCheck 32 &&
    mtFiber70RowCheck 33 &&
    mtFiber70RowCheck 34 &&
    mtFiber70RowCheck 35 &&
    mtFiber70RowCheck 36 &&
    mtFiber70RowCheck 37 &&
    mtFiber70RowCheck 38 &&
    mtFiber70RowCheck 39 &&
    mtFiber70RowCheck 40 &&
    mtFiber70RowCheck 41 &&
    mtFiber70RowCheck 42 &&
    mtFiber70RowCheck 43 &&
    mtFiber70RowCheck 44 &&
    mtFiber70RowCheck 45 &&
    mtFiber70RowCheck 46 &&
    mtFiber70RowCheck 47 &&
    mtFiber70RowCheck 48 &&
    mtFiber70RowCheck 49 &&
    mtFiber70RowCheck 50 &&
    mtFiber70RowCheck 51 &&
    mtFiber70RowCheck 52 &&
    mtFiber70RowCheck 53 &&
    mtFiber70RowCheck 54 &&
    mtFiber70RowCheck 55 &&
    mtFiber70RowCheck 56 &&
    mtFiber70RowCheck 57 &&
    mtFiber70RowCheck 58 &&
    mtFiber70RowCheck 59 &&
    mtFiber70RowCheck 60 &&
    mtFiber70RowCheck 61 &&
    mtFiber70RowCheck 62 &&
    mtFiber70RowCheck 63 &&
    mtFiber70ParentCheck 0 &&
    mtFiber70ParentCheck 1 &&
    mtFiber70ParentCheck 2 &&
    mtFiber70ParentCheck 3 &&
    mtFiber70ParentCheck 4 &&
    mtFiber70ParentCheck 5 &&
    mtFiber70ParentCheck 6 &&
    mtFiber70ParentCheck 7 &&
    mtFiber70ParentCheck 8 &&
    mtFiber70ParentCheck 9 &&
    mtFiber70ParentCheck 10 &&
    mtFiber70ParentCheck 11 &&
    mtFiber70ParentCheck 12 &&
    mtFiber70ParentCheck 13 &&
    mtFiber70ParentCheck 14 &&
    mtFiber70ParentCheck 15 &&
    mtFiber70ParentCheck 16 &&
    mtFiber70ParentCheck 17 &&
    mtFiber70ParentCheck 18 &&
    mtFiber70ParentCheck 19 &&
    mtFiber70ParentCheck 20 &&
    mtFiber70ParentCheck 21 &&
    mtFiber70ParentCheck 22 &&
    mtFiber70ParentCheck 23 &&
    mtFiber70ParentCheck 24 &&
    mtFiber70ParentCheck 25 &&
    mtFiber70ParentCheck 26 &&
    mtFiber70ParentCheck 27 &&
    mtFiber70ParentCheck 28 &&
    mtFiber70ParentCheck 29 &&
    mtFiber70ParentCheck 30 &&
    mtFiber70ParentCheck 31 &&
    mtFiber70ParentCheck 32 &&
    mtFiber70ParentCheck 33 &&
    mtFiber70ParentCheck 34 &&
    mtFiber70ParentCheck 35 &&
    mtFiber70ParentCheck 36 &&
    mtFiber70ParentCheck 37 &&
    mtFiber70ParentCheck 38 &&
    mtFiber70ParentCheck 39 &&
    mtFiber70ParentCheck 40 &&
    mtFiber70ParentCheck 41 &&
    mtFiber70ParentCheck 42 &&
    mtFiber70ParentCheck 43 &&
    mtFiber70ParentCheck 44 &&
    mtFiber70ParentCheck 45 &&
    mtFiber70ParentCheck 46 &&
    mtFiber70ParentCheck 47 &&
    mtFiber70ParentCheck 48 &&
    mtFiber70ParentCheck 49 &&
    mtFiber70ParentCheck 50 &&
    mtFiber70ParentCheck 51 &&
    mtFiber70ParentCheck 52 &&
    mtFiber70ParentCheck 53 &&
    mtFiber70ParentCheck 54 &&
    mtFiber70ParentCheck 55 &&
    mtFiber70ParentCheck 56 &&
    mtFiber70ParentCheck 57 &&
    mtFiber70ParentCheck 58 &&
    mtFiber70ParentCheck 59 &&
    mtFiber70ParentCheck 60 &&
    mtFiber70ParentCheck 61 &&
    mtFiber70ParentCheck 62 &&
    mtFiber70ParentCheck 63

theorem mtFiber70CertificateAudit_ok :
    mtFiber70CertificateAudit = true := by
  simp [mtFiber70CertificateAudit,
    mtFiber70SourcesCheck_ok,
    mtFiber70Row_0_ok,
    mtFiber70Row_1_ok,
    mtFiber70Row_2_ok,
    mtFiber70Row_3_ok,
    mtFiber70Row_4_ok,
    mtFiber70Row_5_ok,
    mtFiber70Row_6_ok,
    mtFiber70Row_7_ok,
    mtFiber70Row_8_ok,
    mtFiber70Row_9_ok,
    mtFiber70Row_10_ok,
    mtFiber70Row_11_ok,
    mtFiber70Row_12_ok,
    mtFiber70Row_13_ok,
    mtFiber70Row_14_ok,
    mtFiber70Row_15_ok,
    mtFiber70Row_16_ok,
    mtFiber70Row_17_ok,
    mtFiber70Row_18_ok,
    mtFiber70Row_19_ok,
    mtFiber70Row_20_ok,
    mtFiber70Row_21_ok,
    mtFiber70Row_22_ok,
    mtFiber70Row_23_ok,
    mtFiber70Row_24_ok,
    mtFiber70Row_25_ok,
    mtFiber70Row_26_ok,
    mtFiber70Row_27_ok,
    mtFiber70Row_28_ok,
    mtFiber70Row_29_ok,
    mtFiber70Row_30_ok,
    mtFiber70Row_31_ok,
    mtFiber70Row_32_ok,
    mtFiber70Row_33_ok,
    mtFiber70Row_34_ok,
    mtFiber70Row_35_ok,
    mtFiber70Row_36_ok,
    mtFiber70Row_37_ok,
    mtFiber70Row_38_ok,
    mtFiber70Row_39_ok,
    mtFiber70Row_40_ok,
    mtFiber70Row_41_ok,
    mtFiber70Row_42_ok,
    mtFiber70Row_43_ok,
    mtFiber70Row_44_ok,
    mtFiber70Row_45_ok,
    mtFiber70Row_46_ok,
    mtFiber70Row_47_ok,
    mtFiber70Row_48_ok,
    mtFiber70Row_49_ok,
    mtFiber70Row_50_ok,
    mtFiber70Row_51_ok,
    mtFiber70Row_52_ok,
    mtFiber70Row_53_ok,
    mtFiber70Row_54_ok,
    mtFiber70Row_55_ok,
    mtFiber70Row_56_ok,
    mtFiber70Row_57_ok,
    mtFiber70Row_58_ok,
    mtFiber70Row_59_ok,
    mtFiber70Row_60_ok,
    mtFiber70Row_61_ok,
    mtFiber70Row_62_ok,
    mtFiber70Row_63_ok,
    mtFiber70Parent_0_ok,
    mtFiber70Parent_1_ok,
    mtFiber70Parent_2_ok,
    mtFiber70Parent_3_ok,
    mtFiber70Parent_4_ok,
    mtFiber70Parent_5_ok,
    mtFiber70Parent_6_ok,
    mtFiber70Parent_7_ok,
    mtFiber70Parent_8_ok,
    mtFiber70Parent_9_ok,
    mtFiber70Parent_10_ok,
    mtFiber70Parent_11_ok,
    mtFiber70Parent_12_ok,
    mtFiber70Parent_13_ok,
    mtFiber70Parent_14_ok,
    mtFiber70Parent_15_ok,
    mtFiber70Parent_16_ok,
    mtFiber70Parent_17_ok,
    mtFiber70Parent_18_ok,
    mtFiber70Parent_19_ok,
    mtFiber70Parent_20_ok,
    mtFiber70Parent_21_ok,
    mtFiber70Parent_22_ok,
    mtFiber70Parent_23_ok,
    mtFiber70Parent_24_ok,
    mtFiber70Parent_25_ok,
    mtFiber70Parent_26_ok,
    mtFiber70Parent_27_ok,
    mtFiber70Parent_28_ok,
    mtFiber70Parent_29_ok,
    mtFiber70Parent_30_ok,
    mtFiber70Parent_31_ok,
    mtFiber70Parent_32_ok,
    mtFiber70Parent_33_ok,
    mtFiber70Parent_34_ok,
    mtFiber70Parent_35_ok,
    mtFiber70Parent_36_ok,
    mtFiber70Parent_37_ok,
    mtFiber70Parent_38_ok,
    mtFiber70Parent_39_ok,
    mtFiber70Parent_40_ok,
    mtFiber70Parent_41_ok,
    mtFiber70Parent_42_ok,
    mtFiber70Parent_43_ok,
    mtFiber70Parent_44_ok,
    mtFiber70Parent_45_ok,
    mtFiber70Parent_46_ok,
    mtFiber70Parent_47_ok,
    mtFiber70Parent_48_ok,
    mtFiber70Parent_49_ok,
    mtFiber70Parent_50_ok,
    mtFiber70Parent_51_ok,
    mtFiber70Parent_52_ok,
    mtFiber70Parent_53_ok,
    mtFiber70Parent_54_ok,
    mtFiber70Parent_55_ok,
    mtFiber70Parent_56_ok,
    mtFiber70Parent_57_ok,
    mtFiber70Parent_58_ok,
    mtFiber70Parent_59_ok,
    mtFiber70Parent_60_ok,
    mtFiber70Parent_61_ok,
    mtFiber70Parent_62_ok,
    mtFiber70Parent_63_ok]

def mtFiber71Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.p]

def mtFiber71Expected : List Nat :=
  [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]

def mtFiber71Rows : List DirectChainParentRow :=
  [ directRow 560 560 92 152 92 152 default
  , directRow 561 560 92 153 92 152 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 562 561 92 154 92 153 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 563 560 92 155 92 152 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 564 560 93 144 92 152 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 565 561 93 145 92 153 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 566 562 93 146 92 154 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 567 563 93 147 92 155 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 568 560 94 136 92 152 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 569 561 94 137 92 153 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 570 562 94 138 92 154 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 571 563 94 139 92 155 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 572 564 95 128 93 144 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 573 565 95 129 93 145 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 574 566 95 130 93 146 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 575 567 95 131 93 147 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber71RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber71Rows i default

def mtFiber71SourcesCheck : Bool :=
  (mtFiber71Rows.map fun row => row.source) == mtFiber71Expected

theorem mtFiber71SourcesCheck_ok :
    mtFiber71SourcesCheck = true := by
  decide

def mtFiber71RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt i)

theorem mtFiber71Row_0_ok : mtFiber71RowCheck 0 = true := by decide
theorem mtFiber71Row_1_ok : mtFiber71RowCheck 1 = true := by decide
theorem mtFiber71Row_2_ok : mtFiber71RowCheck 2 = true := by decide
theorem mtFiber71Row_3_ok : mtFiber71RowCheck 3 = true := by decide
theorem mtFiber71Row_4_ok : mtFiber71RowCheck 4 = true := by decide
theorem mtFiber71Row_5_ok : mtFiber71RowCheck 5 = true := by decide
theorem mtFiber71Row_6_ok : mtFiber71RowCheck 6 = true := by decide
theorem mtFiber71Row_7_ok : mtFiber71RowCheck 7 = true := by decide
theorem mtFiber71Row_8_ok : mtFiber71RowCheck 8 = true := by decide
theorem mtFiber71Row_9_ok : mtFiber71RowCheck 9 = true := by decide
theorem mtFiber71Row_10_ok : mtFiber71RowCheck 10 = true := by decide
theorem mtFiber71Row_11_ok : mtFiber71RowCheck 11 = true := by decide
theorem mtFiber71Row_12_ok : mtFiber71RowCheck 12 = true := by decide
theorem mtFiber71Row_13_ok : mtFiber71RowCheck 13 = true := by decide
theorem mtFiber71Row_14_ok : mtFiber71RowCheck 14 = true := by decide
theorem mtFiber71Row_15_ok : mtFiber71RowCheck 15 = true := by decide

def mtFiber71ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber71Rows mtMaxParentDepth (listGetD mtFiber71Expected i 0) == 560

theorem mtFiber71Parent_0_ok : mtFiber71ParentCheck 0 = true := by decide
theorem mtFiber71Parent_1_ok : mtFiber71ParentCheck 1 = true := by decide
theorem mtFiber71Parent_2_ok : mtFiber71ParentCheck 2 = true := by decide
theorem mtFiber71Parent_3_ok : mtFiber71ParentCheck 3 = true := by decide
theorem mtFiber71Parent_4_ok : mtFiber71ParentCheck 4 = true := by decide
theorem mtFiber71Parent_5_ok : mtFiber71ParentCheck 5 = true := by decide
theorem mtFiber71Parent_6_ok : mtFiber71ParentCheck 6 = true := by decide
theorem mtFiber71Parent_7_ok : mtFiber71ParentCheck 7 = true := by decide
theorem mtFiber71Parent_8_ok : mtFiber71ParentCheck 8 = true := by decide
theorem mtFiber71Parent_9_ok : mtFiber71ParentCheck 9 = true := by decide
theorem mtFiber71Parent_10_ok : mtFiber71ParentCheck 10 = true := by decide
theorem mtFiber71Parent_11_ok : mtFiber71ParentCheck 11 = true := by decide
theorem mtFiber71Parent_12_ok : mtFiber71ParentCheck 12 = true := by decide
theorem mtFiber71Parent_13_ok : mtFiber71ParentCheck 13 = true := by decide
theorem mtFiber71Parent_14_ok : mtFiber71ParentCheck 14 = true := by decide
theorem mtFiber71Parent_15_ok : mtFiber71ParentCheck 15 = true := by decide

def mtFiber71CertificateAudit : Bool :=
  mtFiber71SourcesCheck &&
    mtFiber71RowCheck 0 &&
    mtFiber71RowCheck 1 &&
    mtFiber71RowCheck 2 &&
    mtFiber71RowCheck 3 &&
    mtFiber71RowCheck 4 &&
    mtFiber71RowCheck 5 &&
    mtFiber71RowCheck 6 &&
    mtFiber71RowCheck 7 &&
    mtFiber71RowCheck 8 &&
    mtFiber71RowCheck 9 &&
    mtFiber71RowCheck 10 &&
    mtFiber71RowCheck 11 &&
    mtFiber71RowCheck 12 &&
    mtFiber71RowCheck 13 &&
    mtFiber71RowCheck 14 &&
    mtFiber71RowCheck 15 &&
    mtFiber71ParentCheck 0 &&
    mtFiber71ParentCheck 1 &&
    mtFiber71ParentCheck 2 &&
    mtFiber71ParentCheck 3 &&
    mtFiber71ParentCheck 4 &&
    mtFiber71ParentCheck 5 &&
    mtFiber71ParentCheck 6 &&
    mtFiber71ParentCheck 7 &&
    mtFiber71ParentCheck 8 &&
    mtFiber71ParentCheck 9 &&
    mtFiber71ParentCheck 10 &&
    mtFiber71ParentCheck 11 &&
    mtFiber71ParentCheck 12 &&
    mtFiber71ParentCheck 13 &&
    mtFiber71ParentCheck 14 &&
    mtFiber71ParentCheck 15

theorem mtFiber71CertificateAudit_ok :
    mtFiber71CertificateAudit = true := by
  simp [mtFiber71CertificateAudit,
    mtFiber71SourcesCheck_ok,
    mtFiber71Row_0_ok,
    mtFiber71Row_1_ok,
    mtFiber71Row_2_ok,
    mtFiber71Row_3_ok,
    mtFiber71Row_4_ok,
    mtFiber71Row_5_ok,
    mtFiber71Row_6_ok,
    mtFiber71Row_7_ok,
    mtFiber71Row_8_ok,
    mtFiber71Row_9_ok,
    mtFiber71Row_10_ok,
    mtFiber71Row_11_ok,
    mtFiber71Row_12_ok,
    mtFiber71Row_13_ok,
    mtFiber71Row_14_ok,
    mtFiber71Row_15_ok,
    mtFiber71Parent_0_ok,
    mtFiber71Parent_1_ok,
    mtFiber71Parent_2_ok,
    mtFiber71Parent_3_ok,
    mtFiber71Parent_4_ok,
    mtFiber71Parent_5_ok,
    mtFiber71Parent_6_ok,
    mtFiber71Parent_7_ok,
    mtFiber71Parent_8_ok,
    mtFiber71Parent_9_ok,
    mtFiber71Parent_10_ok,
    mtFiber71Parent_11_ok,
    mtFiber71Parent_12_ok,
    mtFiber71Parent_13_ok,
    mtFiber71Parent_14_ok,
    mtFiber71Parent_15_ok]

def mtFiber72Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.r]

def mtFiber72Expected : List Nat :=
  [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]

def mtFiber72Rows : List DirectChainParentRow :=
  [ directRow 784 784 132 88 132 88 default
  , directRow 785 784 132 89 132 88 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 786 784 132 90 132 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 787 785 132 91 132 89 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 788 786 132 108 132 90 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 789 791 132 109 132 111 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 790 785 132 110 132 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 791 784 132 111 132 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 792 784 133 80 132 88 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 793 785 133 81 132 89 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 794 786 133 82 132 90 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 795 787 133 83 132 91 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 796 788 133 100 132 108 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 797 789 133 101 132 109 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 798 790 133 102 132 110 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 799 791 133 103 132 111 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 800 792 134 72 133 80 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 801 793 134 73 133 81 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 802 794 134 74 133 82 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 803 795 134 75 133 83 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 804 796 134 124 133 100 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 805 797 134 125 133 101 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 806 798 134 126 133 102 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 807 799 134 127 133 103 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 808 784 135 64 132 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 809 785 135 65 132 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 810 786 135 66 132 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 811 787 135 67 132 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 812 788 135 116 132 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 813 789 135 117 132 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 814 790 135 118 132 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 815 791 135 119 132 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 1072 784 180 24 132 88 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1073 785 180 25 132 89 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1074 786 180 26 132 90 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1075 787 180 27 132 91 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1076 1072 180 40 180 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1077 1073 180 41 180 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1078 790 180 42 132 110 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1079 791 180 43 132 111 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1080 792 181 16 133 80 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1081 793 181 17 133 81 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1082 794 181 18 133 82 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1083 795 181 19 133 83 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1084 1080 181 32 181 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1085 1081 181 33 181 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1086 798 181 34 133 102 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1087 799 181 35 133 103 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1088 1072 182 8 180 24 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1089 1073 182 9 180 25 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1090 1074 182 10 180 26 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1091 1075 182 11 180 27 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1092 1076 182 56 180 40 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1093 1077 182 57 180 41 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1094 1078 182 58 180 42 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1095 1079 182 59 180 43 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1096 808 183 0 135 64 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1097 809 183 1 135 65 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1098 810 183 2 135 66 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1099 811 183 3 135 67 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1100 1096 183 48 183 0 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1101 1097 183 49 183 1 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1102 814 183 50 135 118 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1103 815 183 51 135 119 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mtFiber72RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber72Rows i default

def mtFiber72SourcesCheck : Bool :=
  (mtFiber72Rows.map fun row => row.source) == mtFiber72Expected

theorem mtFiber72SourcesCheck_ok :
    mtFiber72SourcesCheck = true := by
  decide

def mtFiber72RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt i)

theorem mtFiber72Row_0_ok : mtFiber72RowCheck 0 = true := by decide
theorem mtFiber72Row_1_ok : mtFiber72RowCheck 1 = true := by decide
theorem mtFiber72Row_2_ok : mtFiber72RowCheck 2 = true := by decide
theorem mtFiber72Row_3_ok : mtFiber72RowCheck 3 = true := by decide
theorem mtFiber72Row_4_ok : mtFiber72RowCheck 4 = true := by decide
theorem mtFiber72Row_5_ok : mtFiber72RowCheck 5 = true := by decide
theorem mtFiber72Row_6_ok : mtFiber72RowCheck 6 = true := by decide
theorem mtFiber72Row_7_ok : mtFiber72RowCheck 7 = true := by decide
theorem mtFiber72Row_8_ok : mtFiber72RowCheck 8 = true := by decide
theorem mtFiber72Row_9_ok : mtFiber72RowCheck 9 = true := by decide
theorem mtFiber72Row_10_ok : mtFiber72RowCheck 10 = true := by decide
theorem mtFiber72Row_11_ok : mtFiber72RowCheck 11 = true := by decide
theorem mtFiber72Row_12_ok : mtFiber72RowCheck 12 = true := by decide
theorem mtFiber72Row_13_ok : mtFiber72RowCheck 13 = true := by decide
theorem mtFiber72Row_14_ok : mtFiber72RowCheck 14 = true := by decide
theorem mtFiber72Row_15_ok : mtFiber72RowCheck 15 = true := by decide
theorem mtFiber72Row_16_ok : mtFiber72RowCheck 16 = true := by decide
theorem mtFiber72Row_17_ok : mtFiber72RowCheck 17 = true := by decide
theorem mtFiber72Row_18_ok : mtFiber72RowCheck 18 = true := by decide
theorem mtFiber72Row_19_ok : mtFiber72RowCheck 19 = true := by decide
theorem mtFiber72Row_20_ok : mtFiber72RowCheck 20 = true := by decide
theorem mtFiber72Row_21_ok : mtFiber72RowCheck 21 = true := by decide
theorem mtFiber72Row_22_ok : mtFiber72RowCheck 22 = true := by decide
theorem mtFiber72Row_23_ok : mtFiber72RowCheck 23 = true := by decide
theorem mtFiber72Row_24_ok : mtFiber72RowCheck 24 = true := by decide
theorem mtFiber72Row_25_ok : mtFiber72RowCheck 25 = true := by decide
theorem mtFiber72Row_26_ok : mtFiber72RowCheck 26 = true := by decide
theorem mtFiber72Row_27_ok : mtFiber72RowCheck 27 = true := by decide
theorem mtFiber72Row_28_ok : mtFiber72RowCheck 28 = true := by decide
theorem mtFiber72Row_29_ok : mtFiber72RowCheck 29 = true := by decide
theorem mtFiber72Row_30_ok : mtFiber72RowCheck 30 = true := by decide
theorem mtFiber72Row_31_ok : mtFiber72RowCheck 31 = true := by decide
theorem mtFiber72Row_32_ok : mtFiber72RowCheck 32 = true := by decide
theorem mtFiber72Row_33_ok : mtFiber72RowCheck 33 = true := by decide
theorem mtFiber72Row_34_ok : mtFiber72RowCheck 34 = true := by decide
theorem mtFiber72Row_35_ok : mtFiber72RowCheck 35 = true := by decide
theorem mtFiber72Row_36_ok : mtFiber72RowCheck 36 = true := by decide
theorem mtFiber72Row_37_ok : mtFiber72RowCheck 37 = true := by decide
theorem mtFiber72Row_38_ok : mtFiber72RowCheck 38 = true := by decide
theorem mtFiber72Row_39_ok : mtFiber72RowCheck 39 = true := by decide
theorem mtFiber72Row_40_ok : mtFiber72RowCheck 40 = true := by decide
theorem mtFiber72Row_41_ok : mtFiber72RowCheck 41 = true := by decide
theorem mtFiber72Row_42_ok : mtFiber72RowCheck 42 = true := by decide
theorem mtFiber72Row_43_ok : mtFiber72RowCheck 43 = true := by decide
theorem mtFiber72Row_44_ok : mtFiber72RowCheck 44 = true := by decide
theorem mtFiber72Row_45_ok : mtFiber72RowCheck 45 = true := by decide
theorem mtFiber72Row_46_ok : mtFiber72RowCheck 46 = true := by decide
theorem mtFiber72Row_47_ok : mtFiber72RowCheck 47 = true := by decide
theorem mtFiber72Row_48_ok : mtFiber72RowCheck 48 = true := by decide
theorem mtFiber72Row_49_ok : mtFiber72RowCheck 49 = true := by decide
theorem mtFiber72Row_50_ok : mtFiber72RowCheck 50 = true := by decide
theorem mtFiber72Row_51_ok : mtFiber72RowCheck 51 = true := by decide
theorem mtFiber72Row_52_ok : mtFiber72RowCheck 52 = true := by decide
theorem mtFiber72Row_53_ok : mtFiber72RowCheck 53 = true := by decide
theorem mtFiber72Row_54_ok : mtFiber72RowCheck 54 = true := by decide
theorem mtFiber72Row_55_ok : mtFiber72RowCheck 55 = true := by decide
theorem mtFiber72Row_56_ok : mtFiber72RowCheck 56 = true := by decide
theorem mtFiber72Row_57_ok : mtFiber72RowCheck 57 = true := by decide
theorem mtFiber72Row_58_ok : mtFiber72RowCheck 58 = true := by decide
theorem mtFiber72Row_59_ok : mtFiber72RowCheck 59 = true := by decide
theorem mtFiber72Row_60_ok : mtFiber72RowCheck 60 = true := by decide
theorem mtFiber72Row_61_ok : mtFiber72RowCheck 61 = true := by decide
theorem mtFiber72Row_62_ok : mtFiber72RowCheck 62 = true := by decide
theorem mtFiber72Row_63_ok : mtFiber72RowCheck 63 = true := by decide

def mtFiber72ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber72Rows mtMaxParentDepth (listGetD mtFiber72Expected i 0) == 784

theorem mtFiber72Parent_0_ok : mtFiber72ParentCheck 0 = true := by decide
theorem mtFiber72Parent_1_ok : mtFiber72ParentCheck 1 = true := by decide
theorem mtFiber72Parent_2_ok : mtFiber72ParentCheck 2 = true := by decide
theorem mtFiber72Parent_3_ok : mtFiber72ParentCheck 3 = true := by decide
theorem mtFiber72Parent_4_ok : mtFiber72ParentCheck 4 = true := by decide
theorem mtFiber72Parent_5_ok : mtFiber72ParentCheck 5 = true := by decide
theorem mtFiber72Parent_6_ok : mtFiber72ParentCheck 6 = true := by decide
theorem mtFiber72Parent_7_ok : mtFiber72ParentCheck 7 = true := by decide
theorem mtFiber72Parent_8_ok : mtFiber72ParentCheck 8 = true := by decide
theorem mtFiber72Parent_9_ok : mtFiber72ParentCheck 9 = true := by decide
theorem mtFiber72Parent_10_ok : mtFiber72ParentCheck 10 = true := by decide
theorem mtFiber72Parent_11_ok : mtFiber72ParentCheck 11 = true := by decide
theorem mtFiber72Parent_12_ok : mtFiber72ParentCheck 12 = true := by decide
theorem mtFiber72Parent_13_ok : mtFiber72ParentCheck 13 = true := by decide
theorem mtFiber72Parent_14_ok : mtFiber72ParentCheck 14 = true := by decide
theorem mtFiber72Parent_15_ok : mtFiber72ParentCheck 15 = true := by decide
theorem mtFiber72Parent_16_ok : mtFiber72ParentCheck 16 = true := by decide
theorem mtFiber72Parent_17_ok : mtFiber72ParentCheck 17 = true := by decide
theorem mtFiber72Parent_18_ok : mtFiber72ParentCheck 18 = true := by decide
theorem mtFiber72Parent_19_ok : mtFiber72ParentCheck 19 = true := by decide
theorem mtFiber72Parent_20_ok : mtFiber72ParentCheck 20 = true := by decide
theorem mtFiber72Parent_21_ok : mtFiber72ParentCheck 21 = true := by decide
theorem mtFiber72Parent_22_ok : mtFiber72ParentCheck 22 = true := by decide
theorem mtFiber72Parent_23_ok : mtFiber72ParentCheck 23 = true := by decide
theorem mtFiber72Parent_24_ok : mtFiber72ParentCheck 24 = true := by decide
theorem mtFiber72Parent_25_ok : mtFiber72ParentCheck 25 = true := by decide
theorem mtFiber72Parent_26_ok : mtFiber72ParentCheck 26 = true := by decide
theorem mtFiber72Parent_27_ok : mtFiber72ParentCheck 27 = true := by decide
theorem mtFiber72Parent_28_ok : mtFiber72ParentCheck 28 = true := by decide
theorem mtFiber72Parent_29_ok : mtFiber72ParentCheck 29 = true := by decide
theorem mtFiber72Parent_30_ok : mtFiber72ParentCheck 30 = true := by decide
theorem mtFiber72Parent_31_ok : mtFiber72ParentCheck 31 = true := by decide
theorem mtFiber72Parent_32_ok : mtFiber72ParentCheck 32 = true := by decide
theorem mtFiber72Parent_33_ok : mtFiber72ParentCheck 33 = true := by decide
theorem mtFiber72Parent_34_ok : mtFiber72ParentCheck 34 = true := by decide
theorem mtFiber72Parent_35_ok : mtFiber72ParentCheck 35 = true := by decide
theorem mtFiber72Parent_36_ok : mtFiber72ParentCheck 36 = true := by decide
theorem mtFiber72Parent_37_ok : mtFiber72ParentCheck 37 = true := by decide
theorem mtFiber72Parent_38_ok : mtFiber72ParentCheck 38 = true := by decide
theorem mtFiber72Parent_39_ok : mtFiber72ParentCheck 39 = true := by decide
theorem mtFiber72Parent_40_ok : mtFiber72ParentCheck 40 = true := by decide
theorem mtFiber72Parent_41_ok : mtFiber72ParentCheck 41 = true := by decide
theorem mtFiber72Parent_42_ok : mtFiber72ParentCheck 42 = true := by decide
theorem mtFiber72Parent_43_ok : mtFiber72ParentCheck 43 = true := by decide
theorem mtFiber72Parent_44_ok : mtFiber72ParentCheck 44 = true := by decide
theorem mtFiber72Parent_45_ok : mtFiber72ParentCheck 45 = true := by decide
theorem mtFiber72Parent_46_ok : mtFiber72ParentCheck 46 = true := by decide
theorem mtFiber72Parent_47_ok : mtFiber72ParentCheck 47 = true := by decide
theorem mtFiber72Parent_48_ok : mtFiber72ParentCheck 48 = true := by decide
theorem mtFiber72Parent_49_ok : mtFiber72ParentCheck 49 = true := by decide
theorem mtFiber72Parent_50_ok : mtFiber72ParentCheck 50 = true := by decide
theorem mtFiber72Parent_51_ok : mtFiber72ParentCheck 51 = true := by decide
theorem mtFiber72Parent_52_ok : mtFiber72ParentCheck 52 = true := by decide
theorem mtFiber72Parent_53_ok : mtFiber72ParentCheck 53 = true := by decide
theorem mtFiber72Parent_54_ok : mtFiber72ParentCheck 54 = true := by decide
theorem mtFiber72Parent_55_ok : mtFiber72ParentCheck 55 = true := by decide
theorem mtFiber72Parent_56_ok : mtFiber72ParentCheck 56 = true := by decide
theorem mtFiber72Parent_57_ok : mtFiber72ParentCheck 57 = true := by decide
theorem mtFiber72Parent_58_ok : mtFiber72ParentCheck 58 = true := by decide
theorem mtFiber72Parent_59_ok : mtFiber72ParentCheck 59 = true := by decide
theorem mtFiber72Parent_60_ok : mtFiber72ParentCheck 60 = true := by decide
theorem mtFiber72Parent_61_ok : mtFiber72ParentCheck 61 = true := by decide
theorem mtFiber72Parent_62_ok : mtFiber72ParentCheck 62 = true := by decide
theorem mtFiber72Parent_63_ok : mtFiber72ParentCheck 63 = true := by decide

def mtFiber72CertificateAudit : Bool :=
  mtFiber72SourcesCheck &&
    mtFiber72RowCheck 0 &&
    mtFiber72RowCheck 1 &&
    mtFiber72RowCheck 2 &&
    mtFiber72RowCheck 3 &&
    mtFiber72RowCheck 4 &&
    mtFiber72RowCheck 5 &&
    mtFiber72RowCheck 6 &&
    mtFiber72RowCheck 7 &&
    mtFiber72RowCheck 8 &&
    mtFiber72RowCheck 9 &&
    mtFiber72RowCheck 10 &&
    mtFiber72RowCheck 11 &&
    mtFiber72RowCheck 12 &&
    mtFiber72RowCheck 13 &&
    mtFiber72RowCheck 14 &&
    mtFiber72RowCheck 15 &&
    mtFiber72RowCheck 16 &&
    mtFiber72RowCheck 17 &&
    mtFiber72RowCheck 18 &&
    mtFiber72RowCheck 19 &&
    mtFiber72RowCheck 20 &&
    mtFiber72RowCheck 21 &&
    mtFiber72RowCheck 22 &&
    mtFiber72RowCheck 23 &&
    mtFiber72RowCheck 24 &&
    mtFiber72RowCheck 25 &&
    mtFiber72RowCheck 26 &&
    mtFiber72RowCheck 27 &&
    mtFiber72RowCheck 28 &&
    mtFiber72RowCheck 29 &&
    mtFiber72RowCheck 30 &&
    mtFiber72RowCheck 31 &&
    mtFiber72RowCheck 32 &&
    mtFiber72RowCheck 33 &&
    mtFiber72RowCheck 34 &&
    mtFiber72RowCheck 35 &&
    mtFiber72RowCheck 36 &&
    mtFiber72RowCheck 37 &&
    mtFiber72RowCheck 38 &&
    mtFiber72RowCheck 39 &&
    mtFiber72RowCheck 40 &&
    mtFiber72RowCheck 41 &&
    mtFiber72RowCheck 42 &&
    mtFiber72RowCheck 43 &&
    mtFiber72RowCheck 44 &&
    mtFiber72RowCheck 45 &&
    mtFiber72RowCheck 46 &&
    mtFiber72RowCheck 47 &&
    mtFiber72RowCheck 48 &&
    mtFiber72RowCheck 49 &&
    mtFiber72RowCheck 50 &&
    mtFiber72RowCheck 51 &&
    mtFiber72RowCheck 52 &&
    mtFiber72RowCheck 53 &&
    mtFiber72RowCheck 54 &&
    mtFiber72RowCheck 55 &&
    mtFiber72RowCheck 56 &&
    mtFiber72RowCheck 57 &&
    mtFiber72RowCheck 58 &&
    mtFiber72RowCheck 59 &&
    mtFiber72RowCheck 60 &&
    mtFiber72RowCheck 61 &&
    mtFiber72RowCheck 62 &&
    mtFiber72RowCheck 63 &&
    mtFiber72ParentCheck 0 &&
    mtFiber72ParentCheck 1 &&
    mtFiber72ParentCheck 2 &&
    mtFiber72ParentCheck 3 &&
    mtFiber72ParentCheck 4 &&
    mtFiber72ParentCheck 5 &&
    mtFiber72ParentCheck 6 &&
    mtFiber72ParentCheck 7 &&
    mtFiber72ParentCheck 8 &&
    mtFiber72ParentCheck 9 &&
    mtFiber72ParentCheck 10 &&
    mtFiber72ParentCheck 11 &&
    mtFiber72ParentCheck 12 &&
    mtFiber72ParentCheck 13 &&
    mtFiber72ParentCheck 14 &&
    mtFiber72ParentCheck 15 &&
    mtFiber72ParentCheck 16 &&
    mtFiber72ParentCheck 17 &&
    mtFiber72ParentCheck 18 &&
    mtFiber72ParentCheck 19 &&
    mtFiber72ParentCheck 20 &&
    mtFiber72ParentCheck 21 &&
    mtFiber72ParentCheck 22 &&
    mtFiber72ParentCheck 23 &&
    mtFiber72ParentCheck 24 &&
    mtFiber72ParentCheck 25 &&
    mtFiber72ParentCheck 26 &&
    mtFiber72ParentCheck 27 &&
    mtFiber72ParentCheck 28 &&
    mtFiber72ParentCheck 29 &&
    mtFiber72ParentCheck 30 &&
    mtFiber72ParentCheck 31 &&
    mtFiber72ParentCheck 32 &&
    mtFiber72ParentCheck 33 &&
    mtFiber72ParentCheck 34 &&
    mtFiber72ParentCheck 35 &&
    mtFiber72ParentCheck 36 &&
    mtFiber72ParentCheck 37 &&
    mtFiber72ParentCheck 38 &&
    mtFiber72ParentCheck 39 &&
    mtFiber72ParentCheck 40 &&
    mtFiber72ParentCheck 41 &&
    mtFiber72ParentCheck 42 &&
    mtFiber72ParentCheck 43 &&
    mtFiber72ParentCheck 44 &&
    mtFiber72ParentCheck 45 &&
    mtFiber72ParentCheck 46 &&
    mtFiber72ParentCheck 47 &&
    mtFiber72ParentCheck 48 &&
    mtFiber72ParentCheck 49 &&
    mtFiber72ParentCheck 50 &&
    mtFiber72ParentCheck 51 &&
    mtFiber72ParentCheck 52 &&
    mtFiber72ParentCheck 53 &&
    mtFiber72ParentCheck 54 &&
    mtFiber72ParentCheck 55 &&
    mtFiber72ParentCheck 56 &&
    mtFiber72ParentCheck 57 &&
    mtFiber72ParentCheck 58 &&
    mtFiber72ParentCheck 59 &&
    mtFiber72ParentCheck 60 &&
    mtFiber72ParentCheck 61 &&
    mtFiber72ParentCheck 62 &&
    mtFiber72ParentCheck 63

theorem mtFiber72CertificateAudit_ok :
    mtFiber72CertificateAudit = true := by
  simp [mtFiber72CertificateAudit,
    mtFiber72SourcesCheck_ok,
    mtFiber72Row_0_ok,
    mtFiber72Row_1_ok,
    mtFiber72Row_2_ok,
    mtFiber72Row_3_ok,
    mtFiber72Row_4_ok,
    mtFiber72Row_5_ok,
    mtFiber72Row_6_ok,
    mtFiber72Row_7_ok,
    mtFiber72Row_8_ok,
    mtFiber72Row_9_ok,
    mtFiber72Row_10_ok,
    mtFiber72Row_11_ok,
    mtFiber72Row_12_ok,
    mtFiber72Row_13_ok,
    mtFiber72Row_14_ok,
    mtFiber72Row_15_ok,
    mtFiber72Row_16_ok,
    mtFiber72Row_17_ok,
    mtFiber72Row_18_ok,
    mtFiber72Row_19_ok,
    mtFiber72Row_20_ok,
    mtFiber72Row_21_ok,
    mtFiber72Row_22_ok,
    mtFiber72Row_23_ok,
    mtFiber72Row_24_ok,
    mtFiber72Row_25_ok,
    mtFiber72Row_26_ok,
    mtFiber72Row_27_ok,
    mtFiber72Row_28_ok,
    mtFiber72Row_29_ok,
    mtFiber72Row_30_ok,
    mtFiber72Row_31_ok,
    mtFiber72Row_32_ok,
    mtFiber72Row_33_ok,
    mtFiber72Row_34_ok,
    mtFiber72Row_35_ok,
    mtFiber72Row_36_ok,
    mtFiber72Row_37_ok,
    mtFiber72Row_38_ok,
    mtFiber72Row_39_ok,
    mtFiber72Row_40_ok,
    mtFiber72Row_41_ok,
    mtFiber72Row_42_ok,
    mtFiber72Row_43_ok,
    mtFiber72Row_44_ok,
    mtFiber72Row_45_ok,
    mtFiber72Row_46_ok,
    mtFiber72Row_47_ok,
    mtFiber72Row_48_ok,
    mtFiber72Row_49_ok,
    mtFiber72Row_50_ok,
    mtFiber72Row_51_ok,
    mtFiber72Row_52_ok,
    mtFiber72Row_53_ok,
    mtFiber72Row_54_ok,
    mtFiber72Row_55_ok,
    mtFiber72Row_56_ok,
    mtFiber72Row_57_ok,
    mtFiber72Row_58_ok,
    mtFiber72Row_59_ok,
    mtFiber72Row_60_ok,
    mtFiber72Row_61_ok,
    mtFiber72Row_62_ok,
    mtFiber72Row_63_ok,
    mtFiber72Parent_0_ok,
    mtFiber72Parent_1_ok,
    mtFiber72Parent_2_ok,
    mtFiber72Parent_3_ok,
    mtFiber72Parent_4_ok,
    mtFiber72Parent_5_ok,
    mtFiber72Parent_6_ok,
    mtFiber72Parent_7_ok,
    mtFiber72Parent_8_ok,
    mtFiber72Parent_9_ok,
    mtFiber72Parent_10_ok,
    mtFiber72Parent_11_ok,
    mtFiber72Parent_12_ok,
    mtFiber72Parent_13_ok,
    mtFiber72Parent_14_ok,
    mtFiber72Parent_15_ok,
    mtFiber72Parent_16_ok,
    mtFiber72Parent_17_ok,
    mtFiber72Parent_18_ok,
    mtFiber72Parent_19_ok,
    mtFiber72Parent_20_ok,
    mtFiber72Parent_21_ok,
    mtFiber72Parent_22_ok,
    mtFiber72Parent_23_ok,
    mtFiber72Parent_24_ok,
    mtFiber72Parent_25_ok,
    mtFiber72Parent_26_ok,
    mtFiber72Parent_27_ok,
    mtFiber72Parent_28_ok,
    mtFiber72Parent_29_ok,
    mtFiber72Parent_30_ok,
    mtFiber72Parent_31_ok,
    mtFiber72Parent_32_ok,
    mtFiber72Parent_33_ok,
    mtFiber72Parent_34_ok,
    mtFiber72Parent_35_ok,
    mtFiber72Parent_36_ok,
    mtFiber72Parent_37_ok,
    mtFiber72Parent_38_ok,
    mtFiber72Parent_39_ok,
    mtFiber72Parent_40_ok,
    mtFiber72Parent_41_ok,
    mtFiber72Parent_42_ok,
    mtFiber72Parent_43_ok,
    mtFiber72Parent_44_ok,
    mtFiber72Parent_45_ok,
    mtFiber72Parent_46_ok,
    mtFiber72Parent_47_ok,
    mtFiber72Parent_48_ok,
    mtFiber72Parent_49_ok,
    mtFiber72Parent_50_ok,
    mtFiber72Parent_51_ok,
    mtFiber72Parent_52_ok,
    mtFiber72Parent_53_ok,
    mtFiber72Parent_54_ok,
    mtFiber72Parent_55_ok,
    mtFiber72Parent_56_ok,
    mtFiber72Parent_57_ok,
    mtFiber72Parent_58_ok,
    mtFiber72Parent_59_ok,
    mtFiber72Parent_60_ok,
    mtFiber72Parent_61_ok,
    mtFiber72Parent_62_ok,
    mtFiber72Parent_63_ok]

def mtFiber73Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.b]

def mtFiber73Expected : List Nat :=
  []

def mtFiber73Rows : List DirectChainParentRow :=
  []

def mtFiber73RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber73Rows i default

def mtFiber73SourcesCheck : Bool :=
  (mtFiber73Rows.map fun row => row.source) == mtFiber73Expected

theorem mtFiber73SourcesCheck_ok :
    mtFiber73SourcesCheck = true := by
  decide

def mtFiber73RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber73Key mtFiber73Expected (mtFiber73RowAt i)

def mtFiber73ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber73Rows mtMaxParentDepth (listGetD mtFiber73Expected i 0) == 0

def mtFiber73CertificateAudit : Bool :=
  mtFiber73SourcesCheck

theorem mtFiber73CertificateAudit_ok :
    mtFiber73CertificateAudit = true := by
  simp [mtFiber73CertificateAudit,
    mtFiber73SourcesCheck_ok]

def mtFiber74Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.p]

def mtFiber74Expected : List Nat :=
  [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]

def mtFiber74Rows : List DirectChainParentRow :=
  [ directRow 128 128 20 168 20 168 default
  , directRow 129 128 20 169 20 168 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 130 128 20 170 20 168 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 131 129 20 171 20 169 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 132 128 21 160 20 168 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 133 129 21 161 20 169 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 134 130 21 162 20 170 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 135 131 21 163 20 171 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 136 128 22 184 20 168 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 137 129 22 185 20 169 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 138 130 22 186 20 170 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 139 131 22 187 20 171 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 140 132 23 176 21 160 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 141 133 23 177 21 161 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 142 134 23 178 21 162 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 143 135 23 179 21 163 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber74RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber74Rows i default

def mtFiber74SourcesCheck : Bool :=
  (mtFiber74Rows.map fun row => row.source) == mtFiber74Expected

theorem mtFiber74SourcesCheck_ok :
    mtFiber74SourcesCheck = true := by
  decide

def mtFiber74RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt i)

theorem mtFiber74Row_0_ok : mtFiber74RowCheck 0 = true := by decide
theorem mtFiber74Row_1_ok : mtFiber74RowCheck 1 = true := by decide
theorem mtFiber74Row_2_ok : mtFiber74RowCheck 2 = true := by decide
theorem mtFiber74Row_3_ok : mtFiber74RowCheck 3 = true := by decide
theorem mtFiber74Row_4_ok : mtFiber74RowCheck 4 = true := by decide
theorem mtFiber74Row_5_ok : mtFiber74RowCheck 5 = true := by decide
theorem mtFiber74Row_6_ok : mtFiber74RowCheck 6 = true := by decide
theorem mtFiber74Row_7_ok : mtFiber74RowCheck 7 = true := by decide
theorem mtFiber74Row_8_ok : mtFiber74RowCheck 8 = true := by decide
theorem mtFiber74Row_9_ok : mtFiber74RowCheck 9 = true := by decide
theorem mtFiber74Row_10_ok : mtFiber74RowCheck 10 = true := by decide
theorem mtFiber74Row_11_ok : mtFiber74RowCheck 11 = true := by decide
theorem mtFiber74Row_12_ok : mtFiber74RowCheck 12 = true := by decide
theorem mtFiber74Row_13_ok : mtFiber74RowCheck 13 = true := by decide
theorem mtFiber74Row_14_ok : mtFiber74RowCheck 14 = true := by decide
theorem mtFiber74Row_15_ok : mtFiber74RowCheck 15 = true := by decide

def mtFiber74ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber74Rows mtMaxParentDepth (listGetD mtFiber74Expected i 0) == 128

theorem mtFiber74Parent_0_ok : mtFiber74ParentCheck 0 = true := by decide
theorem mtFiber74Parent_1_ok : mtFiber74ParentCheck 1 = true := by decide
theorem mtFiber74Parent_2_ok : mtFiber74ParentCheck 2 = true := by decide
theorem mtFiber74Parent_3_ok : mtFiber74ParentCheck 3 = true := by decide
theorem mtFiber74Parent_4_ok : mtFiber74ParentCheck 4 = true := by decide
theorem mtFiber74Parent_5_ok : mtFiber74ParentCheck 5 = true := by decide
theorem mtFiber74Parent_6_ok : mtFiber74ParentCheck 6 = true := by decide
theorem mtFiber74Parent_7_ok : mtFiber74ParentCheck 7 = true := by decide
theorem mtFiber74Parent_8_ok : mtFiber74ParentCheck 8 = true := by decide
theorem mtFiber74Parent_9_ok : mtFiber74ParentCheck 9 = true := by decide
theorem mtFiber74Parent_10_ok : mtFiber74ParentCheck 10 = true := by decide
theorem mtFiber74Parent_11_ok : mtFiber74ParentCheck 11 = true := by decide
theorem mtFiber74Parent_12_ok : mtFiber74ParentCheck 12 = true := by decide
theorem mtFiber74Parent_13_ok : mtFiber74ParentCheck 13 = true := by decide
theorem mtFiber74Parent_14_ok : mtFiber74ParentCheck 14 = true := by decide
theorem mtFiber74Parent_15_ok : mtFiber74ParentCheck 15 = true := by decide

def mtFiber74CertificateAudit : Bool :=
  mtFiber74SourcesCheck &&
    mtFiber74RowCheck 0 &&
    mtFiber74RowCheck 1 &&
    mtFiber74RowCheck 2 &&
    mtFiber74RowCheck 3 &&
    mtFiber74RowCheck 4 &&
    mtFiber74RowCheck 5 &&
    mtFiber74RowCheck 6 &&
    mtFiber74RowCheck 7 &&
    mtFiber74RowCheck 8 &&
    mtFiber74RowCheck 9 &&
    mtFiber74RowCheck 10 &&
    mtFiber74RowCheck 11 &&
    mtFiber74RowCheck 12 &&
    mtFiber74RowCheck 13 &&
    mtFiber74RowCheck 14 &&
    mtFiber74RowCheck 15 &&
    mtFiber74ParentCheck 0 &&
    mtFiber74ParentCheck 1 &&
    mtFiber74ParentCheck 2 &&
    mtFiber74ParentCheck 3 &&
    mtFiber74ParentCheck 4 &&
    mtFiber74ParentCheck 5 &&
    mtFiber74ParentCheck 6 &&
    mtFiber74ParentCheck 7 &&
    mtFiber74ParentCheck 8 &&
    mtFiber74ParentCheck 9 &&
    mtFiber74ParentCheck 10 &&
    mtFiber74ParentCheck 11 &&
    mtFiber74ParentCheck 12 &&
    mtFiber74ParentCheck 13 &&
    mtFiber74ParentCheck 14 &&
    mtFiber74ParentCheck 15

theorem mtFiber74CertificateAudit_ok :
    mtFiber74CertificateAudit = true := by
  simp [mtFiber74CertificateAudit,
    mtFiber74SourcesCheck_ok,
    mtFiber74Row_0_ok,
    mtFiber74Row_1_ok,
    mtFiber74Row_2_ok,
    mtFiber74Row_3_ok,
    mtFiber74Row_4_ok,
    mtFiber74Row_5_ok,
    mtFiber74Row_6_ok,
    mtFiber74Row_7_ok,
    mtFiber74Row_8_ok,
    mtFiber74Row_9_ok,
    mtFiber74Row_10_ok,
    mtFiber74Row_11_ok,
    mtFiber74Row_12_ok,
    mtFiber74Row_13_ok,
    mtFiber74Row_14_ok,
    mtFiber74Row_15_ok,
    mtFiber74Parent_0_ok,
    mtFiber74Parent_1_ok,
    mtFiber74Parent_2_ok,
    mtFiber74Parent_3_ok,
    mtFiber74Parent_4_ok,
    mtFiber74Parent_5_ok,
    mtFiber74Parent_6_ok,
    mtFiber74Parent_7_ok,
    mtFiber74Parent_8_ok,
    mtFiber74Parent_9_ok,
    mtFiber74Parent_10_ok,
    mtFiber74Parent_11_ok,
    mtFiber74Parent_12_ok,
    mtFiber74Parent_13_ok,
    mtFiber74Parent_14_ok,
    mtFiber74Parent_15_ok]

def mtFiber75Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.r]

def mtFiber75Expected : List Nat :=
  []

def mtFiber75Rows : List DirectChainParentRow :=
  []

def mtFiber75RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber75Rows i default

def mtFiber75SourcesCheck : Bool :=
  (mtFiber75Rows.map fun row => row.source) == mtFiber75Expected

theorem mtFiber75SourcesCheck_ok :
    mtFiber75SourcesCheck = true := by
  decide

def mtFiber75RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber75Key mtFiber75Expected (mtFiber75RowAt i)

def mtFiber75ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber75Rows mtMaxParentDepth (listGetD mtFiber75Expected i 0) == 0

def mtFiber75CertificateAudit : Bool :=
  mtFiber75SourcesCheck

theorem mtFiber75CertificateAudit_ok :
    mtFiber75CertificateAudit = true := by
  simp [mtFiber75CertificateAudit,
    mtFiber75SourcesCheck_ok]

def mtFiber76Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.b]

def mtFiber76Expected : List Nat :=
  [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]

def mtFiber76Rows : List DirectChainParentRow :=
  [ directRow 880 880 148 88 148 88 default
  , directRow 881 880 148 89 148 88 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 882 880 148 90 148 88 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 883 881 148 91 148 89 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 884 882 148 108 148 90 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 885 887 148 109 148 111 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 886 881 148 110 148 89 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 887 880 148 111 148 88 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 888 880 149 80 148 88 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 889 881 149 81 148 89 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 890 882 149 82 148 90 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 891 883 149 83 148 91 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 892 884 149 100 148 108 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 893 885 149 101 148 109 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 894 886 149 102 148 110 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 895 887 149 103 148 111 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 896 888 150 72 149 80 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 897 889 150 73 149 81 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 898 890 150 74 149 82 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 899 891 150 75 149 83 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 900 892 150 124 149 100 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 901 893 150 125 149 101 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 902 894 150 126 149 102 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 903 895 150 127 149 103 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 904 880 151 64 148 88 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 905 881 151 65 148 89 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 906 882 151 66 148 90 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 907 883 151 67 148 91 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 908 884 151 116 148 108 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 909 885 151 117 148 109 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 910 886 151 118 148 110 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 911 887 151 119 148 111 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 976 880 164 24 148 88 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 977 881 164 25 148 89 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 978 882 164 26 148 90 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 979 883 164 27 148 91 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 980 976 164 40 164 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 981 977 164 41 164 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 982 886 164 42 148 110 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 983 887 164 43 148 111 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 984 888 165 16 149 80 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 985 889 165 17 149 81 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 986 890 165 18 149 82 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 987 891 165 19 149 83 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 988 984 165 32 165 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 989 985 165 33 165 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 990 894 165 34 149 102 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 991 895 165 35 149 103 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 992 976 166 8 164 24 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 993 977 166 9 164 25 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 994 978 166 10 164 26 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 995 979 166 11 164 27 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 996 980 166 56 164 40 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 997 981 166 57 164 41 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 998 982 166 58 164 42 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 999 983 166 59 164 43 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 1000 904 167 0 151 64 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1001 905 167 1 151 65 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1002 906 167 2 151 66 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1003 907 167 3 151 67 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1004 1000 167 48 167 0 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1005 1001 167 49 167 1 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 1006 910 167 50 151 118 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 1007 911 167 51 151 119 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mtFiber76RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber76Rows i default

def mtFiber76SourcesCheck : Bool :=
  (mtFiber76Rows.map fun row => row.source) == mtFiber76Expected

theorem mtFiber76SourcesCheck_ok :
    mtFiber76SourcesCheck = true := by
  decide

def mtFiber76RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt i)

theorem mtFiber76Row_0_ok : mtFiber76RowCheck 0 = true := by decide
theorem mtFiber76Row_1_ok : mtFiber76RowCheck 1 = true := by decide
theorem mtFiber76Row_2_ok : mtFiber76RowCheck 2 = true := by decide
theorem mtFiber76Row_3_ok : mtFiber76RowCheck 3 = true := by decide
theorem mtFiber76Row_4_ok : mtFiber76RowCheck 4 = true := by decide
theorem mtFiber76Row_5_ok : mtFiber76RowCheck 5 = true := by decide
theorem mtFiber76Row_6_ok : mtFiber76RowCheck 6 = true := by decide
theorem mtFiber76Row_7_ok : mtFiber76RowCheck 7 = true := by decide
theorem mtFiber76Row_8_ok : mtFiber76RowCheck 8 = true := by decide
theorem mtFiber76Row_9_ok : mtFiber76RowCheck 9 = true := by decide
theorem mtFiber76Row_10_ok : mtFiber76RowCheck 10 = true := by decide
theorem mtFiber76Row_11_ok : mtFiber76RowCheck 11 = true := by decide
theorem mtFiber76Row_12_ok : mtFiber76RowCheck 12 = true := by decide
theorem mtFiber76Row_13_ok : mtFiber76RowCheck 13 = true := by decide
theorem mtFiber76Row_14_ok : mtFiber76RowCheck 14 = true := by decide
theorem mtFiber76Row_15_ok : mtFiber76RowCheck 15 = true := by decide
theorem mtFiber76Row_16_ok : mtFiber76RowCheck 16 = true := by decide
theorem mtFiber76Row_17_ok : mtFiber76RowCheck 17 = true := by decide
theorem mtFiber76Row_18_ok : mtFiber76RowCheck 18 = true := by decide
theorem mtFiber76Row_19_ok : mtFiber76RowCheck 19 = true := by decide
theorem mtFiber76Row_20_ok : mtFiber76RowCheck 20 = true := by decide
theorem mtFiber76Row_21_ok : mtFiber76RowCheck 21 = true := by decide
theorem mtFiber76Row_22_ok : mtFiber76RowCheck 22 = true := by decide
theorem mtFiber76Row_23_ok : mtFiber76RowCheck 23 = true := by decide
theorem mtFiber76Row_24_ok : mtFiber76RowCheck 24 = true := by decide
theorem mtFiber76Row_25_ok : mtFiber76RowCheck 25 = true := by decide
theorem mtFiber76Row_26_ok : mtFiber76RowCheck 26 = true := by decide
theorem mtFiber76Row_27_ok : mtFiber76RowCheck 27 = true := by decide
theorem mtFiber76Row_28_ok : mtFiber76RowCheck 28 = true := by decide
theorem mtFiber76Row_29_ok : mtFiber76RowCheck 29 = true := by decide
theorem mtFiber76Row_30_ok : mtFiber76RowCheck 30 = true := by decide
theorem mtFiber76Row_31_ok : mtFiber76RowCheck 31 = true := by decide
theorem mtFiber76Row_32_ok : mtFiber76RowCheck 32 = true := by decide
theorem mtFiber76Row_33_ok : mtFiber76RowCheck 33 = true := by decide
theorem mtFiber76Row_34_ok : mtFiber76RowCheck 34 = true := by decide
theorem mtFiber76Row_35_ok : mtFiber76RowCheck 35 = true := by decide
theorem mtFiber76Row_36_ok : mtFiber76RowCheck 36 = true := by decide
theorem mtFiber76Row_37_ok : mtFiber76RowCheck 37 = true := by decide
theorem mtFiber76Row_38_ok : mtFiber76RowCheck 38 = true := by decide
theorem mtFiber76Row_39_ok : mtFiber76RowCheck 39 = true := by decide
theorem mtFiber76Row_40_ok : mtFiber76RowCheck 40 = true := by decide
theorem mtFiber76Row_41_ok : mtFiber76RowCheck 41 = true := by decide
theorem mtFiber76Row_42_ok : mtFiber76RowCheck 42 = true := by decide
theorem mtFiber76Row_43_ok : mtFiber76RowCheck 43 = true := by decide
theorem mtFiber76Row_44_ok : mtFiber76RowCheck 44 = true := by decide
theorem mtFiber76Row_45_ok : mtFiber76RowCheck 45 = true := by decide
theorem mtFiber76Row_46_ok : mtFiber76RowCheck 46 = true := by decide
theorem mtFiber76Row_47_ok : mtFiber76RowCheck 47 = true := by decide
theorem mtFiber76Row_48_ok : mtFiber76RowCheck 48 = true := by decide
theorem mtFiber76Row_49_ok : mtFiber76RowCheck 49 = true := by decide
theorem mtFiber76Row_50_ok : mtFiber76RowCheck 50 = true := by decide
theorem mtFiber76Row_51_ok : mtFiber76RowCheck 51 = true := by decide
theorem mtFiber76Row_52_ok : mtFiber76RowCheck 52 = true := by decide
theorem mtFiber76Row_53_ok : mtFiber76RowCheck 53 = true := by decide
theorem mtFiber76Row_54_ok : mtFiber76RowCheck 54 = true := by decide
theorem mtFiber76Row_55_ok : mtFiber76RowCheck 55 = true := by decide
theorem mtFiber76Row_56_ok : mtFiber76RowCheck 56 = true := by decide
theorem mtFiber76Row_57_ok : mtFiber76RowCheck 57 = true := by decide
theorem mtFiber76Row_58_ok : mtFiber76RowCheck 58 = true := by decide
theorem mtFiber76Row_59_ok : mtFiber76RowCheck 59 = true := by decide
theorem mtFiber76Row_60_ok : mtFiber76RowCheck 60 = true := by decide
theorem mtFiber76Row_61_ok : mtFiber76RowCheck 61 = true := by decide
theorem mtFiber76Row_62_ok : mtFiber76RowCheck 62 = true := by decide
theorem mtFiber76Row_63_ok : mtFiber76RowCheck 63 = true := by decide

def mtFiber76ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber76Rows mtMaxParentDepth (listGetD mtFiber76Expected i 0) == 880

theorem mtFiber76Parent_0_ok : mtFiber76ParentCheck 0 = true := by decide
theorem mtFiber76Parent_1_ok : mtFiber76ParentCheck 1 = true := by decide
theorem mtFiber76Parent_2_ok : mtFiber76ParentCheck 2 = true := by decide
theorem mtFiber76Parent_3_ok : mtFiber76ParentCheck 3 = true := by decide
theorem mtFiber76Parent_4_ok : mtFiber76ParentCheck 4 = true := by decide
theorem mtFiber76Parent_5_ok : mtFiber76ParentCheck 5 = true := by decide
theorem mtFiber76Parent_6_ok : mtFiber76ParentCheck 6 = true := by decide
theorem mtFiber76Parent_7_ok : mtFiber76ParentCheck 7 = true := by decide
theorem mtFiber76Parent_8_ok : mtFiber76ParentCheck 8 = true := by decide
theorem mtFiber76Parent_9_ok : mtFiber76ParentCheck 9 = true := by decide
theorem mtFiber76Parent_10_ok : mtFiber76ParentCheck 10 = true := by decide
theorem mtFiber76Parent_11_ok : mtFiber76ParentCheck 11 = true := by decide
theorem mtFiber76Parent_12_ok : mtFiber76ParentCheck 12 = true := by decide
theorem mtFiber76Parent_13_ok : mtFiber76ParentCheck 13 = true := by decide
theorem mtFiber76Parent_14_ok : mtFiber76ParentCheck 14 = true := by decide
theorem mtFiber76Parent_15_ok : mtFiber76ParentCheck 15 = true := by decide
theorem mtFiber76Parent_16_ok : mtFiber76ParentCheck 16 = true := by decide
theorem mtFiber76Parent_17_ok : mtFiber76ParentCheck 17 = true := by decide
theorem mtFiber76Parent_18_ok : mtFiber76ParentCheck 18 = true := by decide
theorem mtFiber76Parent_19_ok : mtFiber76ParentCheck 19 = true := by decide
theorem mtFiber76Parent_20_ok : mtFiber76ParentCheck 20 = true := by decide
theorem mtFiber76Parent_21_ok : mtFiber76ParentCheck 21 = true := by decide
theorem mtFiber76Parent_22_ok : mtFiber76ParentCheck 22 = true := by decide
theorem mtFiber76Parent_23_ok : mtFiber76ParentCheck 23 = true := by decide
theorem mtFiber76Parent_24_ok : mtFiber76ParentCheck 24 = true := by decide
theorem mtFiber76Parent_25_ok : mtFiber76ParentCheck 25 = true := by decide
theorem mtFiber76Parent_26_ok : mtFiber76ParentCheck 26 = true := by decide
theorem mtFiber76Parent_27_ok : mtFiber76ParentCheck 27 = true := by decide
theorem mtFiber76Parent_28_ok : mtFiber76ParentCheck 28 = true := by decide
theorem mtFiber76Parent_29_ok : mtFiber76ParentCheck 29 = true := by decide
theorem mtFiber76Parent_30_ok : mtFiber76ParentCheck 30 = true := by decide
theorem mtFiber76Parent_31_ok : mtFiber76ParentCheck 31 = true := by decide
theorem mtFiber76Parent_32_ok : mtFiber76ParentCheck 32 = true := by decide
theorem mtFiber76Parent_33_ok : mtFiber76ParentCheck 33 = true := by decide
theorem mtFiber76Parent_34_ok : mtFiber76ParentCheck 34 = true := by decide
theorem mtFiber76Parent_35_ok : mtFiber76ParentCheck 35 = true := by decide
theorem mtFiber76Parent_36_ok : mtFiber76ParentCheck 36 = true := by decide
theorem mtFiber76Parent_37_ok : mtFiber76ParentCheck 37 = true := by decide
theorem mtFiber76Parent_38_ok : mtFiber76ParentCheck 38 = true := by decide
theorem mtFiber76Parent_39_ok : mtFiber76ParentCheck 39 = true := by decide
theorem mtFiber76Parent_40_ok : mtFiber76ParentCheck 40 = true := by decide
theorem mtFiber76Parent_41_ok : mtFiber76ParentCheck 41 = true := by decide
theorem mtFiber76Parent_42_ok : mtFiber76ParentCheck 42 = true := by decide
theorem mtFiber76Parent_43_ok : mtFiber76ParentCheck 43 = true := by decide
theorem mtFiber76Parent_44_ok : mtFiber76ParentCheck 44 = true := by decide
theorem mtFiber76Parent_45_ok : mtFiber76ParentCheck 45 = true := by decide
theorem mtFiber76Parent_46_ok : mtFiber76ParentCheck 46 = true := by decide
theorem mtFiber76Parent_47_ok : mtFiber76ParentCheck 47 = true := by decide
theorem mtFiber76Parent_48_ok : mtFiber76ParentCheck 48 = true := by decide
theorem mtFiber76Parent_49_ok : mtFiber76ParentCheck 49 = true := by decide
theorem mtFiber76Parent_50_ok : mtFiber76ParentCheck 50 = true := by decide
theorem mtFiber76Parent_51_ok : mtFiber76ParentCheck 51 = true := by decide
theorem mtFiber76Parent_52_ok : mtFiber76ParentCheck 52 = true := by decide
theorem mtFiber76Parent_53_ok : mtFiber76ParentCheck 53 = true := by decide
theorem mtFiber76Parent_54_ok : mtFiber76ParentCheck 54 = true := by decide
theorem mtFiber76Parent_55_ok : mtFiber76ParentCheck 55 = true := by decide
theorem mtFiber76Parent_56_ok : mtFiber76ParentCheck 56 = true := by decide
theorem mtFiber76Parent_57_ok : mtFiber76ParentCheck 57 = true := by decide
theorem mtFiber76Parent_58_ok : mtFiber76ParentCheck 58 = true := by decide
theorem mtFiber76Parent_59_ok : mtFiber76ParentCheck 59 = true := by decide
theorem mtFiber76Parent_60_ok : mtFiber76ParentCheck 60 = true := by decide
theorem mtFiber76Parent_61_ok : mtFiber76ParentCheck 61 = true := by decide
theorem mtFiber76Parent_62_ok : mtFiber76ParentCheck 62 = true := by decide
theorem mtFiber76Parent_63_ok : mtFiber76ParentCheck 63 = true := by decide

def mtFiber76CertificateAudit : Bool :=
  mtFiber76SourcesCheck &&
    mtFiber76RowCheck 0 &&
    mtFiber76RowCheck 1 &&
    mtFiber76RowCheck 2 &&
    mtFiber76RowCheck 3 &&
    mtFiber76RowCheck 4 &&
    mtFiber76RowCheck 5 &&
    mtFiber76RowCheck 6 &&
    mtFiber76RowCheck 7 &&
    mtFiber76RowCheck 8 &&
    mtFiber76RowCheck 9 &&
    mtFiber76RowCheck 10 &&
    mtFiber76RowCheck 11 &&
    mtFiber76RowCheck 12 &&
    mtFiber76RowCheck 13 &&
    mtFiber76RowCheck 14 &&
    mtFiber76RowCheck 15 &&
    mtFiber76RowCheck 16 &&
    mtFiber76RowCheck 17 &&
    mtFiber76RowCheck 18 &&
    mtFiber76RowCheck 19 &&
    mtFiber76RowCheck 20 &&
    mtFiber76RowCheck 21 &&
    mtFiber76RowCheck 22 &&
    mtFiber76RowCheck 23 &&
    mtFiber76RowCheck 24 &&
    mtFiber76RowCheck 25 &&
    mtFiber76RowCheck 26 &&
    mtFiber76RowCheck 27 &&
    mtFiber76RowCheck 28 &&
    mtFiber76RowCheck 29 &&
    mtFiber76RowCheck 30 &&
    mtFiber76RowCheck 31 &&
    mtFiber76RowCheck 32 &&
    mtFiber76RowCheck 33 &&
    mtFiber76RowCheck 34 &&
    mtFiber76RowCheck 35 &&
    mtFiber76RowCheck 36 &&
    mtFiber76RowCheck 37 &&
    mtFiber76RowCheck 38 &&
    mtFiber76RowCheck 39 &&
    mtFiber76RowCheck 40 &&
    mtFiber76RowCheck 41 &&
    mtFiber76RowCheck 42 &&
    mtFiber76RowCheck 43 &&
    mtFiber76RowCheck 44 &&
    mtFiber76RowCheck 45 &&
    mtFiber76RowCheck 46 &&
    mtFiber76RowCheck 47 &&
    mtFiber76RowCheck 48 &&
    mtFiber76RowCheck 49 &&
    mtFiber76RowCheck 50 &&
    mtFiber76RowCheck 51 &&
    mtFiber76RowCheck 52 &&
    mtFiber76RowCheck 53 &&
    mtFiber76RowCheck 54 &&
    mtFiber76RowCheck 55 &&
    mtFiber76RowCheck 56 &&
    mtFiber76RowCheck 57 &&
    mtFiber76RowCheck 58 &&
    mtFiber76RowCheck 59 &&
    mtFiber76RowCheck 60 &&
    mtFiber76RowCheck 61 &&
    mtFiber76RowCheck 62 &&
    mtFiber76RowCheck 63 &&
    mtFiber76ParentCheck 0 &&
    mtFiber76ParentCheck 1 &&
    mtFiber76ParentCheck 2 &&
    mtFiber76ParentCheck 3 &&
    mtFiber76ParentCheck 4 &&
    mtFiber76ParentCheck 5 &&
    mtFiber76ParentCheck 6 &&
    mtFiber76ParentCheck 7 &&
    mtFiber76ParentCheck 8 &&
    mtFiber76ParentCheck 9 &&
    mtFiber76ParentCheck 10 &&
    mtFiber76ParentCheck 11 &&
    mtFiber76ParentCheck 12 &&
    mtFiber76ParentCheck 13 &&
    mtFiber76ParentCheck 14 &&
    mtFiber76ParentCheck 15 &&
    mtFiber76ParentCheck 16 &&
    mtFiber76ParentCheck 17 &&
    mtFiber76ParentCheck 18 &&
    mtFiber76ParentCheck 19 &&
    mtFiber76ParentCheck 20 &&
    mtFiber76ParentCheck 21 &&
    mtFiber76ParentCheck 22 &&
    mtFiber76ParentCheck 23 &&
    mtFiber76ParentCheck 24 &&
    mtFiber76ParentCheck 25 &&
    mtFiber76ParentCheck 26 &&
    mtFiber76ParentCheck 27 &&
    mtFiber76ParentCheck 28 &&
    mtFiber76ParentCheck 29 &&
    mtFiber76ParentCheck 30 &&
    mtFiber76ParentCheck 31 &&
    mtFiber76ParentCheck 32 &&
    mtFiber76ParentCheck 33 &&
    mtFiber76ParentCheck 34 &&
    mtFiber76ParentCheck 35 &&
    mtFiber76ParentCheck 36 &&
    mtFiber76ParentCheck 37 &&
    mtFiber76ParentCheck 38 &&
    mtFiber76ParentCheck 39 &&
    mtFiber76ParentCheck 40 &&
    mtFiber76ParentCheck 41 &&
    mtFiber76ParentCheck 42 &&
    mtFiber76ParentCheck 43 &&
    mtFiber76ParentCheck 44 &&
    mtFiber76ParentCheck 45 &&
    mtFiber76ParentCheck 46 &&
    mtFiber76ParentCheck 47 &&
    mtFiber76ParentCheck 48 &&
    mtFiber76ParentCheck 49 &&
    mtFiber76ParentCheck 50 &&
    mtFiber76ParentCheck 51 &&
    mtFiber76ParentCheck 52 &&
    mtFiber76ParentCheck 53 &&
    mtFiber76ParentCheck 54 &&
    mtFiber76ParentCheck 55 &&
    mtFiber76ParentCheck 56 &&
    mtFiber76ParentCheck 57 &&
    mtFiber76ParentCheck 58 &&
    mtFiber76ParentCheck 59 &&
    mtFiber76ParentCheck 60 &&
    mtFiber76ParentCheck 61 &&
    mtFiber76ParentCheck 62 &&
    mtFiber76ParentCheck 63

theorem mtFiber76CertificateAudit_ok :
    mtFiber76CertificateAudit = true := by
  simp [mtFiber76CertificateAudit,
    mtFiber76SourcesCheck_ok,
    mtFiber76Row_0_ok,
    mtFiber76Row_1_ok,
    mtFiber76Row_2_ok,
    mtFiber76Row_3_ok,
    mtFiber76Row_4_ok,
    mtFiber76Row_5_ok,
    mtFiber76Row_6_ok,
    mtFiber76Row_7_ok,
    mtFiber76Row_8_ok,
    mtFiber76Row_9_ok,
    mtFiber76Row_10_ok,
    mtFiber76Row_11_ok,
    mtFiber76Row_12_ok,
    mtFiber76Row_13_ok,
    mtFiber76Row_14_ok,
    mtFiber76Row_15_ok,
    mtFiber76Row_16_ok,
    mtFiber76Row_17_ok,
    mtFiber76Row_18_ok,
    mtFiber76Row_19_ok,
    mtFiber76Row_20_ok,
    mtFiber76Row_21_ok,
    mtFiber76Row_22_ok,
    mtFiber76Row_23_ok,
    mtFiber76Row_24_ok,
    mtFiber76Row_25_ok,
    mtFiber76Row_26_ok,
    mtFiber76Row_27_ok,
    mtFiber76Row_28_ok,
    mtFiber76Row_29_ok,
    mtFiber76Row_30_ok,
    mtFiber76Row_31_ok,
    mtFiber76Row_32_ok,
    mtFiber76Row_33_ok,
    mtFiber76Row_34_ok,
    mtFiber76Row_35_ok,
    mtFiber76Row_36_ok,
    mtFiber76Row_37_ok,
    mtFiber76Row_38_ok,
    mtFiber76Row_39_ok,
    mtFiber76Row_40_ok,
    mtFiber76Row_41_ok,
    mtFiber76Row_42_ok,
    mtFiber76Row_43_ok,
    mtFiber76Row_44_ok,
    mtFiber76Row_45_ok,
    mtFiber76Row_46_ok,
    mtFiber76Row_47_ok,
    mtFiber76Row_48_ok,
    mtFiber76Row_49_ok,
    mtFiber76Row_50_ok,
    mtFiber76Row_51_ok,
    mtFiber76Row_52_ok,
    mtFiber76Row_53_ok,
    mtFiber76Row_54_ok,
    mtFiber76Row_55_ok,
    mtFiber76Row_56_ok,
    mtFiber76Row_57_ok,
    mtFiber76Row_58_ok,
    mtFiber76Row_59_ok,
    mtFiber76Row_60_ok,
    mtFiber76Row_61_ok,
    mtFiber76Row_62_ok,
    mtFiber76Row_63_ok,
    mtFiber76Parent_0_ok,
    mtFiber76Parent_1_ok,
    mtFiber76Parent_2_ok,
    mtFiber76Parent_3_ok,
    mtFiber76Parent_4_ok,
    mtFiber76Parent_5_ok,
    mtFiber76Parent_6_ok,
    mtFiber76Parent_7_ok,
    mtFiber76Parent_8_ok,
    mtFiber76Parent_9_ok,
    mtFiber76Parent_10_ok,
    mtFiber76Parent_11_ok,
    mtFiber76Parent_12_ok,
    mtFiber76Parent_13_ok,
    mtFiber76Parent_14_ok,
    mtFiber76Parent_15_ok,
    mtFiber76Parent_16_ok,
    mtFiber76Parent_17_ok,
    mtFiber76Parent_18_ok,
    mtFiber76Parent_19_ok,
    mtFiber76Parent_20_ok,
    mtFiber76Parent_21_ok,
    mtFiber76Parent_22_ok,
    mtFiber76Parent_23_ok,
    mtFiber76Parent_24_ok,
    mtFiber76Parent_25_ok,
    mtFiber76Parent_26_ok,
    mtFiber76Parent_27_ok,
    mtFiber76Parent_28_ok,
    mtFiber76Parent_29_ok,
    mtFiber76Parent_30_ok,
    mtFiber76Parent_31_ok,
    mtFiber76Parent_32_ok,
    mtFiber76Parent_33_ok,
    mtFiber76Parent_34_ok,
    mtFiber76Parent_35_ok,
    mtFiber76Parent_36_ok,
    mtFiber76Parent_37_ok,
    mtFiber76Parent_38_ok,
    mtFiber76Parent_39_ok,
    mtFiber76Parent_40_ok,
    mtFiber76Parent_41_ok,
    mtFiber76Parent_42_ok,
    mtFiber76Parent_43_ok,
    mtFiber76Parent_44_ok,
    mtFiber76Parent_45_ok,
    mtFiber76Parent_46_ok,
    mtFiber76Parent_47_ok,
    mtFiber76Parent_48_ok,
    mtFiber76Parent_49_ok,
    mtFiber76Parent_50_ok,
    mtFiber76Parent_51_ok,
    mtFiber76Parent_52_ok,
    mtFiber76Parent_53_ok,
    mtFiber76Parent_54_ok,
    mtFiber76Parent_55_ok,
    mtFiber76Parent_56_ok,
    mtFiber76Parent_57_ok,
    mtFiber76Parent_58_ok,
    mtFiber76Parent_59_ok,
    mtFiber76Parent_60_ok,
    mtFiber76Parent_61_ok,
    mtFiber76Parent_62_ok,
    mtFiber76Parent_63_ok]

def mtFiber77Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.p]

def mtFiber77Expected : List Nat :=
  [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]

def mtFiber77Rows : List DirectChainParentRow :=
  [ directRow 512 512 84 152 84 152 default
  , directRow 513 512 84 153 84 152 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 514 513 84 154 84 153 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 515 512 84 155 84 152 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 516 512 85 144 84 152 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 517 513 85 145 84 153 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 518 514 85 146 84 154 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 519 515 85 147 84 155 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 520 512 86 136 84 152 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 521 513 86 137 84 153 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 522 514 86 138 84 154 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 523 515 86 139 84 155 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 524 516 87 128 85 144 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 525 517 87 129 85 145 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 526 518 87 130 85 146 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 527 519 87 131 85 147 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  ]

def mtFiber77RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber77Rows i default

def mtFiber77SourcesCheck : Bool :=
  (mtFiber77Rows.map fun row => row.source) == mtFiber77Expected

theorem mtFiber77SourcesCheck_ok :
    mtFiber77SourcesCheck = true := by
  decide

def mtFiber77RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt i)

theorem mtFiber77Row_0_ok : mtFiber77RowCheck 0 = true := by decide
theorem mtFiber77Row_1_ok : mtFiber77RowCheck 1 = true := by decide
theorem mtFiber77Row_2_ok : mtFiber77RowCheck 2 = true := by decide
theorem mtFiber77Row_3_ok : mtFiber77RowCheck 3 = true := by decide
theorem mtFiber77Row_4_ok : mtFiber77RowCheck 4 = true := by decide
theorem mtFiber77Row_5_ok : mtFiber77RowCheck 5 = true := by decide
theorem mtFiber77Row_6_ok : mtFiber77RowCheck 6 = true := by decide
theorem mtFiber77Row_7_ok : mtFiber77RowCheck 7 = true := by decide
theorem mtFiber77Row_8_ok : mtFiber77RowCheck 8 = true := by decide
theorem mtFiber77Row_9_ok : mtFiber77RowCheck 9 = true := by decide
theorem mtFiber77Row_10_ok : mtFiber77RowCheck 10 = true := by decide
theorem mtFiber77Row_11_ok : mtFiber77RowCheck 11 = true := by decide
theorem mtFiber77Row_12_ok : mtFiber77RowCheck 12 = true := by decide
theorem mtFiber77Row_13_ok : mtFiber77RowCheck 13 = true := by decide
theorem mtFiber77Row_14_ok : mtFiber77RowCheck 14 = true := by decide
theorem mtFiber77Row_15_ok : mtFiber77RowCheck 15 = true := by decide

def mtFiber77ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber77Rows mtMaxParentDepth (listGetD mtFiber77Expected i 0) == 512

theorem mtFiber77Parent_0_ok : mtFiber77ParentCheck 0 = true := by decide
theorem mtFiber77Parent_1_ok : mtFiber77ParentCheck 1 = true := by decide
theorem mtFiber77Parent_2_ok : mtFiber77ParentCheck 2 = true := by decide
theorem mtFiber77Parent_3_ok : mtFiber77ParentCheck 3 = true := by decide
theorem mtFiber77Parent_4_ok : mtFiber77ParentCheck 4 = true := by decide
theorem mtFiber77Parent_5_ok : mtFiber77ParentCheck 5 = true := by decide
theorem mtFiber77Parent_6_ok : mtFiber77ParentCheck 6 = true := by decide
theorem mtFiber77Parent_7_ok : mtFiber77ParentCheck 7 = true := by decide
theorem mtFiber77Parent_8_ok : mtFiber77ParentCheck 8 = true := by decide
theorem mtFiber77Parent_9_ok : mtFiber77ParentCheck 9 = true := by decide
theorem mtFiber77Parent_10_ok : mtFiber77ParentCheck 10 = true := by decide
theorem mtFiber77Parent_11_ok : mtFiber77ParentCheck 11 = true := by decide
theorem mtFiber77Parent_12_ok : mtFiber77ParentCheck 12 = true := by decide
theorem mtFiber77Parent_13_ok : mtFiber77ParentCheck 13 = true := by decide
theorem mtFiber77Parent_14_ok : mtFiber77ParentCheck 14 = true := by decide
theorem mtFiber77Parent_15_ok : mtFiber77ParentCheck 15 = true := by decide

def mtFiber77CertificateAudit : Bool :=
  mtFiber77SourcesCheck &&
    mtFiber77RowCheck 0 &&
    mtFiber77RowCheck 1 &&
    mtFiber77RowCheck 2 &&
    mtFiber77RowCheck 3 &&
    mtFiber77RowCheck 4 &&
    mtFiber77RowCheck 5 &&
    mtFiber77RowCheck 6 &&
    mtFiber77RowCheck 7 &&
    mtFiber77RowCheck 8 &&
    mtFiber77RowCheck 9 &&
    mtFiber77RowCheck 10 &&
    mtFiber77RowCheck 11 &&
    mtFiber77RowCheck 12 &&
    mtFiber77RowCheck 13 &&
    mtFiber77RowCheck 14 &&
    mtFiber77RowCheck 15 &&
    mtFiber77ParentCheck 0 &&
    mtFiber77ParentCheck 1 &&
    mtFiber77ParentCheck 2 &&
    mtFiber77ParentCheck 3 &&
    mtFiber77ParentCheck 4 &&
    mtFiber77ParentCheck 5 &&
    mtFiber77ParentCheck 6 &&
    mtFiber77ParentCheck 7 &&
    mtFiber77ParentCheck 8 &&
    mtFiber77ParentCheck 9 &&
    mtFiber77ParentCheck 10 &&
    mtFiber77ParentCheck 11 &&
    mtFiber77ParentCheck 12 &&
    mtFiber77ParentCheck 13 &&
    mtFiber77ParentCheck 14 &&
    mtFiber77ParentCheck 15

theorem mtFiber77CertificateAudit_ok :
    mtFiber77CertificateAudit = true := by
  simp [mtFiber77CertificateAudit,
    mtFiber77SourcesCheck_ok,
    mtFiber77Row_0_ok,
    mtFiber77Row_1_ok,
    mtFiber77Row_2_ok,
    mtFiber77Row_3_ok,
    mtFiber77Row_4_ok,
    mtFiber77Row_5_ok,
    mtFiber77Row_6_ok,
    mtFiber77Row_7_ok,
    mtFiber77Row_8_ok,
    mtFiber77Row_9_ok,
    mtFiber77Row_10_ok,
    mtFiber77Row_11_ok,
    mtFiber77Row_12_ok,
    mtFiber77Row_13_ok,
    mtFiber77Row_14_ok,
    mtFiber77Row_15_ok,
    mtFiber77Parent_0_ok,
    mtFiber77Parent_1_ok,
    mtFiber77Parent_2_ok,
    mtFiber77Parent_3_ok,
    mtFiber77Parent_4_ok,
    mtFiber77Parent_5_ok,
    mtFiber77Parent_6_ok,
    mtFiber77Parent_7_ok,
    mtFiber77Parent_8_ok,
    mtFiber77Parent_9_ok,
    mtFiber77Parent_10_ok,
    mtFiber77Parent_11_ok,
    mtFiber77Parent_12_ok,
    mtFiber77Parent_13_ok,
    mtFiber77Parent_14_ok,
    mtFiber77Parent_15_ok]

def mtFiber78Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.r]

def mtFiber78Expected : List Nat :=
  []

def mtFiber78Rows : List DirectChainParentRow :=
  []

def mtFiber78RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber78Rows i default

def mtFiber78SourcesCheck : Bool :=
  (mtFiber78Rows.map fun row => row.source) == mtFiber78Expected

theorem mtFiber78SourcesCheck_ok :
    mtFiber78SourcesCheck = true := by
  decide

def mtFiber78RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber78Key mtFiber78Expected (mtFiber78RowAt i)

def mtFiber78ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber78Rows mtMaxParentDepth (listGetD mtFiber78Expected i 0) == 0

def mtFiber78CertificateAudit : Bool :=
  mtFiber78SourcesCheck

theorem mtFiber78CertificateAudit_ok :
    mtFiber78CertificateAudit = true := by
  simp [mtFiber78CertificateAudit,
    mtFiber78SourcesCheck_ok]

def mtFiber79Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.b]

def mtFiber79Expected : List Nat :=
  []

def mtFiber79Rows : List DirectChainParentRow :=
  []

def mtFiber79RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber79Rows i default

def mtFiber79SourcesCheck : Bool :=
  (mtFiber79Rows.map fun row => row.source) == mtFiber79Expected

theorem mtFiber79SourcesCheck_ok :
    mtFiber79SourcesCheck = true := by
  decide

def mtFiber79RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber79Key mtFiber79Expected (mtFiber79RowAt i)

def mtFiber79ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber79Rows mtMaxParentDepth (listGetD mtFiber79Expected i 0) == 0

def mtFiber79CertificateAudit : Bool :=
  mtFiber79SourcesCheck

theorem mtFiber79CertificateAudit_ok :
    mtFiber79CertificateAudit = true := by
  simp [mtFiber79CertificateAudit,
    mtFiber79SourcesCheck_ok]

def mtFiber80Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.p]

def mtFiber80Expected : List Nat :=
  []

def mtFiber80Rows : List DirectChainParentRow :=
  []

def mtFiber80RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mtFiber80Rows i default

def mtFiber80SourcesCheck : Bool :=
  (mtFiber80Rows.map fun row => row.source) == mtFiber80Expected

theorem mtFiber80SourcesCheck_ok :
    mtFiber80SourcesCheck = true := by
  decide

def mtFiber80RowCheck (i : Nat) : Bool :=
  mtRowValid mtFiber80Key mtFiber80Expected (mtFiber80RowAt i)

def mtFiber80ParentCheck (i : Nat) : Bool :=
  directParentIter mtFiber80Rows mtMaxParentDepth (listGetD mtFiber80Expected i 0) == 0

def mtFiber80CertificateAudit : Bool :=
  mtFiber80SourcesCheck

theorem mtFiber80CertificateAudit_ok :
    mtFiber80CertificateAudit = true := by
  simp [mtFiber80CertificateAudit,
    mtFiber80SourcesCheck_ok]

def mtAllFiberCertificateAudit : Bool :=
  mtFiber0CertificateAudit &&
    mtFiber1CertificateAudit &&
    mtFiber2CertificateAudit &&
    mtFiber3CertificateAudit &&
    mtFiber4CertificateAudit &&
    mtFiber5CertificateAudit &&
    mtFiber6CertificateAudit &&
    mtFiber7CertificateAudit &&
    mtFiber8CertificateAudit &&
    mtFiber9CertificateAudit &&
    mtFiber10CertificateAudit &&
    mtFiber11CertificateAudit &&
    mtFiber12CertificateAudit &&
    mtFiber13CertificateAudit &&
    mtFiber14CertificateAudit &&
    mtFiber15CertificateAudit &&
    mtFiber16CertificateAudit &&
    mtFiber17CertificateAudit &&
    mtFiber18CertificateAudit &&
    mtFiber19CertificateAudit &&
    mtFiber20CertificateAudit &&
    mtFiber21CertificateAudit &&
    mtFiber22CertificateAudit &&
    mtFiber23CertificateAudit &&
    mtFiber24CertificateAudit &&
    mtFiber25CertificateAudit &&
    mtFiber26CertificateAudit &&
    mtFiber27CertificateAudit &&
    mtFiber28CertificateAudit &&
    mtFiber29CertificateAudit &&
    mtFiber30CertificateAudit &&
    mtFiber31CertificateAudit &&
    mtFiber32CertificateAudit &&
    mtFiber33CertificateAudit &&
    mtFiber34CertificateAudit &&
    mtFiber35CertificateAudit &&
    mtFiber36CertificateAudit &&
    mtFiber37CertificateAudit &&
    mtFiber38CertificateAudit &&
    mtFiber39CertificateAudit &&
    mtFiber40CertificateAudit &&
    mtFiber41CertificateAudit &&
    mtFiber42CertificateAudit &&
    mtFiber43CertificateAudit &&
    mtFiber44CertificateAudit &&
    mtFiber45CertificateAudit &&
    mtFiber46CertificateAudit &&
    mtFiber47CertificateAudit &&
    mtFiber48CertificateAudit &&
    mtFiber49CertificateAudit &&
    mtFiber50CertificateAudit &&
    mtFiber51CertificateAudit &&
    mtFiber52CertificateAudit &&
    mtFiber53CertificateAudit &&
    mtFiber54CertificateAudit &&
    mtFiber55CertificateAudit &&
    mtFiber56CertificateAudit &&
    mtFiber57CertificateAudit &&
    mtFiber58CertificateAudit &&
    mtFiber59CertificateAudit &&
    mtFiber60CertificateAudit &&
    mtFiber61CertificateAudit &&
    mtFiber62CertificateAudit &&
    mtFiber63CertificateAudit &&
    mtFiber64CertificateAudit &&
    mtFiber65CertificateAudit &&
    mtFiber66CertificateAudit &&
    mtFiber67CertificateAudit &&
    mtFiber68CertificateAudit &&
    mtFiber69CertificateAudit &&
    mtFiber70CertificateAudit &&
    mtFiber71CertificateAudit &&
    mtFiber72CertificateAudit &&
    mtFiber73CertificateAudit &&
    mtFiber74CertificateAudit &&
    mtFiber75CertificateAudit &&
    mtFiber76CertificateAudit &&
    mtFiber77CertificateAudit &&
    mtFiber78CertificateAudit &&
    mtFiber79CertificateAudit &&
    mtFiber80CertificateAudit

theorem mtAllFiberCertificateAudit_ok :
    mtAllFiberCertificateAudit = true := by
  simp [mtAllFiberCertificateAudit,
    mtFiber0CertificateAudit_ok,
    mtFiber1CertificateAudit_ok,
    mtFiber2CertificateAudit_ok,
    mtFiber3CertificateAudit_ok,
    mtFiber4CertificateAudit_ok,
    mtFiber5CertificateAudit_ok,
    mtFiber6CertificateAudit_ok,
    mtFiber7CertificateAudit_ok,
    mtFiber8CertificateAudit_ok,
    mtFiber9CertificateAudit_ok,
    mtFiber10CertificateAudit_ok,
    mtFiber11CertificateAudit_ok,
    mtFiber12CertificateAudit_ok,
    mtFiber13CertificateAudit_ok,
    mtFiber14CertificateAudit_ok,
    mtFiber15CertificateAudit_ok,
    mtFiber16CertificateAudit_ok,
    mtFiber17CertificateAudit_ok,
    mtFiber18CertificateAudit_ok,
    mtFiber19CertificateAudit_ok,
    mtFiber20CertificateAudit_ok,
    mtFiber21CertificateAudit_ok,
    mtFiber22CertificateAudit_ok,
    mtFiber23CertificateAudit_ok,
    mtFiber24CertificateAudit_ok,
    mtFiber25CertificateAudit_ok,
    mtFiber26CertificateAudit_ok,
    mtFiber27CertificateAudit_ok,
    mtFiber28CertificateAudit_ok,
    mtFiber29CertificateAudit_ok,
    mtFiber30CertificateAudit_ok,
    mtFiber31CertificateAudit_ok,
    mtFiber32CertificateAudit_ok,
    mtFiber33CertificateAudit_ok,
    mtFiber34CertificateAudit_ok,
    mtFiber35CertificateAudit_ok,
    mtFiber36CertificateAudit_ok,
    mtFiber37CertificateAudit_ok,
    mtFiber38CertificateAudit_ok,
    mtFiber39CertificateAudit_ok,
    mtFiber40CertificateAudit_ok,
    mtFiber41CertificateAudit_ok,
    mtFiber42CertificateAudit_ok,
    mtFiber43CertificateAudit_ok,
    mtFiber44CertificateAudit_ok,
    mtFiber45CertificateAudit_ok,
    mtFiber46CertificateAudit_ok,
    mtFiber47CertificateAudit_ok,
    mtFiber48CertificateAudit_ok,
    mtFiber49CertificateAudit_ok,
    mtFiber50CertificateAudit_ok,
    mtFiber51CertificateAudit_ok,
    mtFiber52CertificateAudit_ok,
    mtFiber53CertificateAudit_ok,
    mtFiber54CertificateAudit_ok,
    mtFiber55CertificateAudit_ok,
    mtFiber56CertificateAudit_ok,
    mtFiber57CertificateAudit_ok,
    mtFiber58CertificateAudit_ok,
    mtFiber59CertificateAudit_ok,
    mtFiber60CertificateAudit_ok,
    mtFiber61CertificateAudit_ok,
    mtFiber62CertificateAudit_ok,
    mtFiber63CertificateAudit_ok,
    mtFiber64CertificateAudit_ok,
    mtFiber65CertificateAudit_ok,
    mtFiber66CertificateAudit_ok,
    mtFiber67CertificateAudit_ok,
    mtFiber68CertificateAudit_ok,
    mtFiber69CertificateAudit_ok,
    mtFiber70CertificateAudit_ok,
    mtFiber71CertificateAudit_ok,
    mtFiber72CertificateAudit_ok,
    mtFiber73CertificateAudit_ok,
    mtFiber74CertificateAudit_ok,
    mtFiber75CertificateAudit_ok,
    mtFiber76CertificateAudit_ok,
    mtFiber77CertificateAudit_ok,
    mtFiber78CertificateAudit_ok,
    mtFiber79CertificateAudit_ok,
    mtFiber80CertificateAudit_ok]

end GoertzelLemma818MirrorTauCertificate

end Mettapedia.GraphTheory.FourColor
