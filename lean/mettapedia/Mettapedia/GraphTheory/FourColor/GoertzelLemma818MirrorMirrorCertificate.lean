import Mettapedia.GraphTheory.FourColor.GoertzelLemma818CompositeCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: generated `mirror-mirror` length-2 certificate

This file checks the generated direct parent/path table for all 81
fixed-input keys of the `mirror-mirror` composite.  The checks are row-split;
the all-chain frontier/DFA lift is a separate theorem.
-/

namespace GoertzelLemma818MirrorMirrorCertificate

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def mmWord : List TauOrient :=
  [TauOrient.mirror, TauOrient.mirror]

def mmNonemptyFiberCount : Nat := 36
def mmCompositeStateCount : Nat := 960
def mmMaxParentDepth : Nat := 4

def mmRowValid (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) : Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := directStates row.sourceLeft row.sourceRight
    let t := directStates row.parentLeft row.parentRight
    compatibleChainStates mmWord s && compatibleChainStates mmWord t &&
      chainInputKey mmWord s == key && chainInputKey mmWord t == key &&
        (row.source == row.parent || chainSpecifiedKempeStep mmWord s t row.move)

def mmFiber0Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.r]

def mmFiber0Expected : List Nat :=
  []

def mmFiber0Rows : List DirectChainParentRow :=
  []

def mmFiber0RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber0Rows i default

def mmFiber0SourcesCheck : Bool :=
  (mmFiber0Rows.map fun row => row.source) == mmFiber0Expected

theorem mmFiber0SourcesCheck_ok :
    mmFiber0SourcesCheck = true := by
  decide

def mmFiber0RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber0Key mmFiber0Expected (mmFiber0RowAt i)

def mmFiber0ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber0Rows mmMaxParentDepth (listGetD mmFiber0Expected i 0) == 0

def mmFiber0CertificateAudit : Bool :=
  mmFiber0SourcesCheck

theorem mmFiber0CertificateAudit_ok :
    mmFiber0CertificateAudit = true := by
  simp [mmFiber0CertificateAudit,
    mmFiber0SourcesCheck_ok]

def mmFiber1Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.b]

def mmFiber1Expected : List Nat :=
  []

def mmFiber1Rows : List DirectChainParentRow :=
  []

def mmFiber1RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber1Rows i default

def mmFiber1SourcesCheck : Bool :=
  (mmFiber1Rows.map fun row => row.source) == mmFiber1Expected

theorem mmFiber1SourcesCheck_ok :
    mmFiber1SourcesCheck = true := by
  decide

def mmFiber1RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber1Key mmFiber1Expected (mmFiber1RowAt i)

def mmFiber1ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber1Rows mmMaxParentDepth (listGetD mmFiber1Expected i 0) == 0

def mmFiber1CertificateAudit : Bool :=
  mmFiber1SourcesCheck

theorem mmFiber1CertificateAudit_ok :
    mmFiber1CertificateAudit = true := by
  simp [mmFiber1CertificateAudit,
    mmFiber1SourcesCheck_ok]

def mmFiber2Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.p]

def mmFiber2Expected : List Nat :=
  []

def mmFiber2Rows : List DirectChainParentRow :=
  []

def mmFiber2RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber2Rows i default

def mmFiber2SourcesCheck : Bool :=
  (mmFiber2Rows.map fun row => row.source) == mmFiber2Expected

theorem mmFiber2SourcesCheck_ok :
    mmFiber2SourcesCheck = true := by
  decide

def mmFiber2RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber2Key mmFiber2Expected (mmFiber2RowAt i)

def mmFiber2ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber2Rows mmMaxParentDepth (listGetD mmFiber2Expected i 0) == 0

def mmFiber2CertificateAudit : Bool :=
  mmFiber2SourcesCheck

theorem mmFiber2CertificateAudit_ok :
    mmFiber2CertificateAudit = true := by
  simp [mmFiber2CertificateAudit,
    mmFiber2SourcesCheck_ok]

def mmFiber3Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.r]

def mmFiber3Expected : List Nat :=
  [600, 601, 602, 603, 604, 605, 606, 607]

def mmFiber3Rows : List DirectChainParentRow :=
  [ directRow 600 600 122 52 122 52 default
  , directRow 601 600 122 53 122 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 602 601 122 54 122 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 603 600 122 55 122 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 604 600 123 60 122 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 605 601 123 61 122 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 606 602 123 62 122 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 607 603 123 63 122 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber3RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber3Rows i default

def mmFiber3SourcesCheck : Bool :=
  (mmFiber3Rows.map fun row => row.source) == mmFiber3Expected

theorem mmFiber3SourcesCheck_ok :
    mmFiber3SourcesCheck = true := by
  decide

def mmFiber3RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt i)

theorem mmFiber3Row_0_ok : mmFiber3RowCheck 0 = true := by decide
theorem mmFiber3Row_1_ok : mmFiber3RowCheck 1 = true := by decide
theorem mmFiber3Row_2_ok : mmFiber3RowCheck 2 = true := by decide
theorem mmFiber3Row_3_ok : mmFiber3RowCheck 3 = true := by decide
theorem mmFiber3Row_4_ok : mmFiber3RowCheck 4 = true := by decide
theorem mmFiber3Row_5_ok : mmFiber3RowCheck 5 = true := by decide
theorem mmFiber3Row_6_ok : mmFiber3RowCheck 6 = true := by decide
theorem mmFiber3Row_7_ok : mmFiber3RowCheck 7 = true := by decide

def mmFiber3ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber3Rows mmMaxParentDepth (listGetD mmFiber3Expected i 0) == 600

theorem mmFiber3Parent_0_ok : mmFiber3ParentCheck 0 = true := by decide
theorem mmFiber3Parent_1_ok : mmFiber3ParentCheck 1 = true := by decide
theorem mmFiber3Parent_2_ok : mmFiber3ParentCheck 2 = true := by decide
theorem mmFiber3Parent_3_ok : mmFiber3ParentCheck 3 = true := by decide
theorem mmFiber3Parent_4_ok : mmFiber3ParentCheck 4 = true := by decide
theorem mmFiber3Parent_5_ok : mmFiber3ParentCheck 5 = true := by decide
theorem mmFiber3Parent_6_ok : mmFiber3ParentCheck 6 = true := by decide
theorem mmFiber3Parent_7_ok : mmFiber3ParentCheck 7 = true := by decide

def mmFiber3CertificateAudit : Bool :=
  mmFiber3SourcesCheck &&
    mmFiber3RowCheck 0 &&
    mmFiber3RowCheck 1 &&
    mmFiber3RowCheck 2 &&
    mmFiber3RowCheck 3 &&
    mmFiber3RowCheck 4 &&
    mmFiber3RowCheck 5 &&
    mmFiber3RowCheck 6 &&
    mmFiber3RowCheck 7 &&
    mmFiber3ParentCheck 0 &&
    mmFiber3ParentCheck 1 &&
    mmFiber3ParentCheck 2 &&
    mmFiber3ParentCheck 3 &&
    mmFiber3ParentCheck 4 &&
    mmFiber3ParentCheck 5 &&
    mmFiber3ParentCheck 6 &&
    mmFiber3ParentCheck 7

theorem mmFiber3CertificateAudit_ok :
    mmFiber3CertificateAudit = true := by
  simp [mmFiber3CertificateAudit,
    mmFiber3SourcesCheck_ok,
    mmFiber3Row_0_ok,
    mmFiber3Row_1_ok,
    mmFiber3Row_2_ok,
    mmFiber3Row_3_ok,
    mmFiber3Row_4_ok,
    mmFiber3Row_5_ok,
    mmFiber3Row_6_ok,
    mmFiber3Row_7_ok,
    mmFiber3Parent_0_ok,
    mmFiber3Parent_1_ok,
    mmFiber3Parent_2_ok,
    mmFiber3Parent_3_ok,
    mmFiber3Parent_4_ok,
    mmFiber3Parent_5_ok,
    mmFiber3Parent_6_ok,
    mmFiber3Parent_7_ok]

def mmFiber4Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.b]

def mmFiber4Expected : List Nat :=
  [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311]

def mmFiber4Rows : List DirectChainParentRow :=
  [ directRow 40 40 8 80 8 80 default
  , directRow 41 40 8 81 8 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 42 40 8 82 8 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 43 41 8 83 8 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 44 42 8 100 8 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 45 47 8 101 8 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 46 41 8 102 8 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 47 40 8 103 8 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 48 40 9 88 8 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 49 41 9 89 8 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 50 42 9 90 8 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 51 43 9 91 8 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 52 44 9 108 8 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 53 45 9 109 8 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 54 46 9 110 8 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 55 47 9 111 8 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 56 40 10 16 8 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 57 41 10 17 8 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 58 42 10 18 8 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 59 43 10 19 8 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 60 56 10 32 10 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 61 57 10 33 10 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 62 46 10 34 8 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 63 47 10 35 8 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 64 48 11 24 9 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 65 49 11 25 9 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 66 50 11 26 9 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 67 51 11 27 9 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 68 64 11 40 11 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 69 65 11 41 11 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 70 54 11 42 9 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 71 55 11 43 9 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 280 40 56 148 8 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 281 41 56 149 8 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 282 42 56 150 8 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 283 280 56 151 56 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 284 280 56 164 56 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 285 281 56 165 56 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 286 46 56 166 8 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 287 47 56 167 8 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 288 48 57 156 9 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 289 49 57 157 9 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 290 50 57 158 9 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 291 288 57 159 57 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 292 288 57 172 57 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 293 289 57 173 57 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 294 54 57 174 9 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 295 55 57 175 9 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 296 56 58 0 10 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 297 57 58 1 10 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 298 58 58 2 10 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 299 59 58 3 10 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 300 288 58 48 57 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 301 289 58 49 57 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 302 62 58 50 10 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 303 63 58 51 10 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 304 287 59 8 56 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 305 286 59 9 56 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 306 284 59 10 56 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 307 285 59 11 56 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 308 280 59 56 56 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 309 281 59 57 56 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 310 282 59 58 56 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 311 283 59 59 56 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mmFiber4RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber4Rows i default

def mmFiber4SourcesCheck : Bool :=
  (mmFiber4Rows.map fun row => row.source) == mmFiber4Expected

theorem mmFiber4SourcesCheck_ok :
    mmFiber4SourcesCheck = true := by
  decide

def mmFiber4RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt i)

theorem mmFiber4Row_0_ok : mmFiber4RowCheck 0 = true := by decide
theorem mmFiber4Row_1_ok : mmFiber4RowCheck 1 = true := by decide
theorem mmFiber4Row_2_ok : mmFiber4RowCheck 2 = true := by decide
theorem mmFiber4Row_3_ok : mmFiber4RowCheck 3 = true := by decide
theorem mmFiber4Row_4_ok : mmFiber4RowCheck 4 = true := by decide
theorem mmFiber4Row_5_ok : mmFiber4RowCheck 5 = true := by decide
theorem mmFiber4Row_6_ok : mmFiber4RowCheck 6 = true := by decide
theorem mmFiber4Row_7_ok : mmFiber4RowCheck 7 = true := by decide
theorem mmFiber4Row_8_ok : mmFiber4RowCheck 8 = true := by decide
theorem mmFiber4Row_9_ok : mmFiber4RowCheck 9 = true := by decide
theorem mmFiber4Row_10_ok : mmFiber4RowCheck 10 = true := by decide
theorem mmFiber4Row_11_ok : mmFiber4RowCheck 11 = true := by decide
theorem mmFiber4Row_12_ok : mmFiber4RowCheck 12 = true := by decide
theorem mmFiber4Row_13_ok : mmFiber4RowCheck 13 = true := by decide
theorem mmFiber4Row_14_ok : mmFiber4RowCheck 14 = true := by decide
theorem mmFiber4Row_15_ok : mmFiber4RowCheck 15 = true := by decide
theorem mmFiber4Row_16_ok : mmFiber4RowCheck 16 = true := by decide
theorem mmFiber4Row_17_ok : mmFiber4RowCheck 17 = true := by decide
theorem mmFiber4Row_18_ok : mmFiber4RowCheck 18 = true := by decide
theorem mmFiber4Row_19_ok : mmFiber4RowCheck 19 = true := by decide
theorem mmFiber4Row_20_ok : mmFiber4RowCheck 20 = true := by decide
theorem mmFiber4Row_21_ok : mmFiber4RowCheck 21 = true := by decide
theorem mmFiber4Row_22_ok : mmFiber4RowCheck 22 = true := by decide
theorem mmFiber4Row_23_ok : mmFiber4RowCheck 23 = true := by decide
theorem mmFiber4Row_24_ok : mmFiber4RowCheck 24 = true := by decide
theorem mmFiber4Row_25_ok : mmFiber4RowCheck 25 = true := by decide
theorem mmFiber4Row_26_ok : mmFiber4RowCheck 26 = true := by decide
theorem mmFiber4Row_27_ok : mmFiber4RowCheck 27 = true := by decide
theorem mmFiber4Row_28_ok : mmFiber4RowCheck 28 = true := by decide
theorem mmFiber4Row_29_ok : mmFiber4RowCheck 29 = true := by decide
theorem mmFiber4Row_30_ok : mmFiber4RowCheck 30 = true := by decide
theorem mmFiber4Row_31_ok : mmFiber4RowCheck 31 = true := by decide
theorem mmFiber4Row_32_ok : mmFiber4RowCheck 32 = true := by decide
theorem mmFiber4Row_33_ok : mmFiber4RowCheck 33 = true := by decide
theorem mmFiber4Row_34_ok : mmFiber4RowCheck 34 = true := by decide
theorem mmFiber4Row_35_ok : mmFiber4RowCheck 35 = true := by decide
theorem mmFiber4Row_36_ok : mmFiber4RowCheck 36 = true := by decide
theorem mmFiber4Row_37_ok : mmFiber4RowCheck 37 = true := by decide
theorem mmFiber4Row_38_ok : mmFiber4RowCheck 38 = true := by decide
theorem mmFiber4Row_39_ok : mmFiber4RowCheck 39 = true := by decide
theorem mmFiber4Row_40_ok : mmFiber4RowCheck 40 = true := by decide
theorem mmFiber4Row_41_ok : mmFiber4RowCheck 41 = true := by decide
theorem mmFiber4Row_42_ok : mmFiber4RowCheck 42 = true := by decide
theorem mmFiber4Row_43_ok : mmFiber4RowCheck 43 = true := by decide
theorem mmFiber4Row_44_ok : mmFiber4RowCheck 44 = true := by decide
theorem mmFiber4Row_45_ok : mmFiber4RowCheck 45 = true := by decide
theorem mmFiber4Row_46_ok : mmFiber4RowCheck 46 = true := by decide
theorem mmFiber4Row_47_ok : mmFiber4RowCheck 47 = true := by decide
theorem mmFiber4Row_48_ok : mmFiber4RowCheck 48 = true := by decide
theorem mmFiber4Row_49_ok : mmFiber4RowCheck 49 = true := by decide
theorem mmFiber4Row_50_ok : mmFiber4RowCheck 50 = true := by decide
theorem mmFiber4Row_51_ok : mmFiber4RowCheck 51 = true := by decide
theorem mmFiber4Row_52_ok : mmFiber4RowCheck 52 = true := by decide
theorem mmFiber4Row_53_ok : mmFiber4RowCheck 53 = true := by decide
theorem mmFiber4Row_54_ok : mmFiber4RowCheck 54 = true := by decide
theorem mmFiber4Row_55_ok : mmFiber4RowCheck 55 = true := by decide
theorem mmFiber4Row_56_ok : mmFiber4RowCheck 56 = true := by decide
theorem mmFiber4Row_57_ok : mmFiber4RowCheck 57 = true := by decide
theorem mmFiber4Row_58_ok : mmFiber4RowCheck 58 = true := by decide
theorem mmFiber4Row_59_ok : mmFiber4RowCheck 59 = true := by decide
theorem mmFiber4Row_60_ok : mmFiber4RowCheck 60 = true := by decide
theorem mmFiber4Row_61_ok : mmFiber4RowCheck 61 = true := by decide
theorem mmFiber4Row_62_ok : mmFiber4RowCheck 62 = true := by decide
theorem mmFiber4Row_63_ok : mmFiber4RowCheck 63 = true := by decide

def mmFiber4ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber4Rows mmMaxParentDepth (listGetD mmFiber4Expected i 0) == 40

theorem mmFiber4Parent_0_ok : mmFiber4ParentCheck 0 = true := by decide
theorem mmFiber4Parent_1_ok : mmFiber4ParentCheck 1 = true := by decide
theorem mmFiber4Parent_2_ok : mmFiber4ParentCheck 2 = true := by decide
theorem mmFiber4Parent_3_ok : mmFiber4ParentCheck 3 = true := by decide
theorem mmFiber4Parent_4_ok : mmFiber4ParentCheck 4 = true := by decide
theorem mmFiber4Parent_5_ok : mmFiber4ParentCheck 5 = true := by decide
theorem mmFiber4Parent_6_ok : mmFiber4ParentCheck 6 = true := by decide
theorem mmFiber4Parent_7_ok : mmFiber4ParentCheck 7 = true := by decide
theorem mmFiber4Parent_8_ok : mmFiber4ParentCheck 8 = true := by decide
theorem mmFiber4Parent_9_ok : mmFiber4ParentCheck 9 = true := by decide
theorem mmFiber4Parent_10_ok : mmFiber4ParentCheck 10 = true := by decide
theorem mmFiber4Parent_11_ok : mmFiber4ParentCheck 11 = true := by decide
theorem mmFiber4Parent_12_ok : mmFiber4ParentCheck 12 = true := by decide
theorem mmFiber4Parent_13_ok : mmFiber4ParentCheck 13 = true := by decide
theorem mmFiber4Parent_14_ok : mmFiber4ParentCheck 14 = true := by decide
theorem mmFiber4Parent_15_ok : mmFiber4ParentCheck 15 = true := by decide
theorem mmFiber4Parent_16_ok : mmFiber4ParentCheck 16 = true := by decide
theorem mmFiber4Parent_17_ok : mmFiber4ParentCheck 17 = true := by decide
theorem mmFiber4Parent_18_ok : mmFiber4ParentCheck 18 = true := by decide
theorem mmFiber4Parent_19_ok : mmFiber4ParentCheck 19 = true := by decide
theorem mmFiber4Parent_20_ok : mmFiber4ParentCheck 20 = true := by decide
theorem mmFiber4Parent_21_ok : mmFiber4ParentCheck 21 = true := by decide
theorem mmFiber4Parent_22_ok : mmFiber4ParentCheck 22 = true := by decide
theorem mmFiber4Parent_23_ok : mmFiber4ParentCheck 23 = true := by decide
theorem mmFiber4Parent_24_ok : mmFiber4ParentCheck 24 = true := by decide
theorem mmFiber4Parent_25_ok : mmFiber4ParentCheck 25 = true := by decide
theorem mmFiber4Parent_26_ok : mmFiber4ParentCheck 26 = true := by decide
theorem mmFiber4Parent_27_ok : mmFiber4ParentCheck 27 = true := by decide
theorem mmFiber4Parent_28_ok : mmFiber4ParentCheck 28 = true := by decide
theorem mmFiber4Parent_29_ok : mmFiber4ParentCheck 29 = true := by decide
theorem mmFiber4Parent_30_ok : mmFiber4ParentCheck 30 = true := by decide
theorem mmFiber4Parent_31_ok : mmFiber4ParentCheck 31 = true := by decide
theorem mmFiber4Parent_32_ok : mmFiber4ParentCheck 32 = true := by decide
theorem mmFiber4Parent_33_ok : mmFiber4ParentCheck 33 = true := by decide
theorem mmFiber4Parent_34_ok : mmFiber4ParentCheck 34 = true := by decide
theorem mmFiber4Parent_35_ok : mmFiber4ParentCheck 35 = true := by decide
theorem mmFiber4Parent_36_ok : mmFiber4ParentCheck 36 = true := by decide
theorem mmFiber4Parent_37_ok : mmFiber4ParentCheck 37 = true := by decide
theorem mmFiber4Parent_38_ok : mmFiber4ParentCheck 38 = true := by decide
theorem mmFiber4Parent_39_ok : mmFiber4ParentCheck 39 = true := by decide
theorem mmFiber4Parent_40_ok : mmFiber4ParentCheck 40 = true := by decide
theorem mmFiber4Parent_41_ok : mmFiber4ParentCheck 41 = true := by decide
theorem mmFiber4Parent_42_ok : mmFiber4ParentCheck 42 = true := by decide
theorem mmFiber4Parent_43_ok : mmFiber4ParentCheck 43 = true := by decide
theorem mmFiber4Parent_44_ok : mmFiber4ParentCheck 44 = true := by decide
theorem mmFiber4Parent_45_ok : mmFiber4ParentCheck 45 = true := by decide
theorem mmFiber4Parent_46_ok : mmFiber4ParentCheck 46 = true := by decide
theorem mmFiber4Parent_47_ok : mmFiber4ParentCheck 47 = true := by decide
theorem mmFiber4Parent_48_ok : mmFiber4ParentCheck 48 = true := by decide
theorem mmFiber4Parent_49_ok : mmFiber4ParentCheck 49 = true := by decide
theorem mmFiber4Parent_50_ok : mmFiber4ParentCheck 50 = true := by decide
theorem mmFiber4Parent_51_ok : mmFiber4ParentCheck 51 = true := by decide
theorem mmFiber4Parent_52_ok : mmFiber4ParentCheck 52 = true := by decide
theorem mmFiber4Parent_53_ok : mmFiber4ParentCheck 53 = true := by decide
theorem mmFiber4Parent_54_ok : mmFiber4ParentCheck 54 = true := by decide
theorem mmFiber4Parent_55_ok : mmFiber4ParentCheck 55 = true := by decide
theorem mmFiber4Parent_56_ok : mmFiber4ParentCheck 56 = true := by decide
theorem mmFiber4Parent_57_ok : mmFiber4ParentCheck 57 = true := by decide
theorem mmFiber4Parent_58_ok : mmFiber4ParentCheck 58 = true := by decide
theorem mmFiber4Parent_59_ok : mmFiber4ParentCheck 59 = true := by decide
theorem mmFiber4Parent_60_ok : mmFiber4ParentCheck 60 = true := by decide
theorem mmFiber4Parent_61_ok : mmFiber4ParentCheck 61 = true := by decide
theorem mmFiber4Parent_62_ok : mmFiber4ParentCheck 62 = true := by decide
theorem mmFiber4Parent_63_ok : mmFiber4ParentCheck 63 = true := by decide

def mmFiber4CertificateAudit : Bool :=
  mmFiber4SourcesCheck &&
    mmFiber4RowCheck 0 &&
    mmFiber4RowCheck 1 &&
    mmFiber4RowCheck 2 &&
    mmFiber4RowCheck 3 &&
    mmFiber4RowCheck 4 &&
    mmFiber4RowCheck 5 &&
    mmFiber4RowCheck 6 &&
    mmFiber4RowCheck 7 &&
    mmFiber4RowCheck 8 &&
    mmFiber4RowCheck 9 &&
    mmFiber4RowCheck 10 &&
    mmFiber4RowCheck 11 &&
    mmFiber4RowCheck 12 &&
    mmFiber4RowCheck 13 &&
    mmFiber4RowCheck 14 &&
    mmFiber4RowCheck 15 &&
    mmFiber4RowCheck 16 &&
    mmFiber4RowCheck 17 &&
    mmFiber4RowCheck 18 &&
    mmFiber4RowCheck 19 &&
    mmFiber4RowCheck 20 &&
    mmFiber4RowCheck 21 &&
    mmFiber4RowCheck 22 &&
    mmFiber4RowCheck 23 &&
    mmFiber4RowCheck 24 &&
    mmFiber4RowCheck 25 &&
    mmFiber4RowCheck 26 &&
    mmFiber4RowCheck 27 &&
    mmFiber4RowCheck 28 &&
    mmFiber4RowCheck 29 &&
    mmFiber4RowCheck 30 &&
    mmFiber4RowCheck 31 &&
    mmFiber4RowCheck 32 &&
    mmFiber4RowCheck 33 &&
    mmFiber4RowCheck 34 &&
    mmFiber4RowCheck 35 &&
    mmFiber4RowCheck 36 &&
    mmFiber4RowCheck 37 &&
    mmFiber4RowCheck 38 &&
    mmFiber4RowCheck 39 &&
    mmFiber4RowCheck 40 &&
    mmFiber4RowCheck 41 &&
    mmFiber4RowCheck 42 &&
    mmFiber4RowCheck 43 &&
    mmFiber4RowCheck 44 &&
    mmFiber4RowCheck 45 &&
    mmFiber4RowCheck 46 &&
    mmFiber4RowCheck 47 &&
    mmFiber4RowCheck 48 &&
    mmFiber4RowCheck 49 &&
    mmFiber4RowCheck 50 &&
    mmFiber4RowCheck 51 &&
    mmFiber4RowCheck 52 &&
    mmFiber4RowCheck 53 &&
    mmFiber4RowCheck 54 &&
    mmFiber4RowCheck 55 &&
    mmFiber4RowCheck 56 &&
    mmFiber4RowCheck 57 &&
    mmFiber4RowCheck 58 &&
    mmFiber4RowCheck 59 &&
    mmFiber4RowCheck 60 &&
    mmFiber4RowCheck 61 &&
    mmFiber4RowCheck 62 &&
    mmFiber4RowCheck 63 &&
    mmFiber4ParentCheck 0 &&
    mmFiber4ParentCheck 1 &&
    mmFiber4ParentCheck 2 &&
    mmFiber4ParentCheck 3 &&
    mmFiber4ParentCheck 4 &&
    mmFiber4ParentCheck 5 &&
    mmFiber4ParentCheck 6 &&
    mmFiber4ParentCheck 7 &&
    mmFiber4ParentCheck 8 &&
    mmFiber4ParentCheck 9 &&
    mmFiber4ParentCheck 10 &&
    mmFiber4ParentCheck 11 &&
    mmFiber4ParentCheck 12 &&
    mmFiber4ParentCheck 13 &&
    mmFiber4ParentCheck 14 &&
    mmFiber4ParentCheck 15 &&
    mmFiber4ParentCheck 16 &&
    mmFiber4ParentCheck 17 &&
    mmFiber4ParentCheck 18 &&
    mmFiber4ParentCheck 19 &&
    mmFiber4ParentCheck 20 &&
    mmFiber4ParentCheck 21 &&
    mmFiber4ParentCheck 22 &&
    mmFiber4ParentCheck 23 &&
    mmFiber4ParentCheck 24 &&
    mmFiber4ParentCheck 25 &&
    mmFiber4ParentCheck 26 &&
    mmFiber4ParentCheck 27 &&
    mmFiber4ParentCheck 28 &&
    mmFiber4ParentCheck 29 &&
    mmFiber4ParentCheck 30 &&
    mmFiber4ParentCheck 31 &&
    mmFiber4ParentCheck 32 &&
    mmFiber4ParentCheck 33 &&
    mmFiber4ParentCheck 34 &&
    mmFiber4ParentCheck 35 &&
    mmFiber4ParentCheck 36 &&
    mmFiber4ParentCheck 37 &&
    mmFiber4ParentCheck 38 &&
    mmFiber4ParentCheck 39 &&
    mmFiber4ParentCheck 40 &&
    mmFiber4ParentCheck 41 &&
    mmFiber4ParentCheck 42 &&
    mmFiber4ParentCheck 43 &&
    mmFiber4ParentCheck 44 &&
    mmFiber4ParentCheck 45 &&
    mmFiber4ParentCheck 46 &&
    mmFiber4ParentCheck 47 &&
    mmFiber4ParentCheck 48 &&
    mmFiber4ParentCheck 49 &&
    mmFiber4ParentCheck 50 &&
    mmFiber4ParentCheck 51 &&
    mmFiber4ParentCheck 52 &&
    mmFiber4ParentCheck 53 &&
    mmFiber4ParentCheck 54 &&
    mmFiber4ParentCheck 55 &&
    mmFiber4ParentCheck 56 &&
    mmFiber4ParentCheck 57 &&
    mmFiber4ParentCheck 58 &&
    mmFiber4ParentCheck 59 &&
    mmFiber4ParentCheck 60 &&
    mmFiber4ParentCheck 61 &&
    mmFiber4ParentCheck 62 &&
    mmFiber4ParentCheck 63

theorem mmFiber4CertificateAudit_ok :
    mmFiber4CertificateAudit = true := by
  simp [mmFiber4CertificateAudit,
    mmFiber4SourcesCheck_ok,
    mmFiber4Row_0_ok,
    mmFiber4Row_1_ok,
    mmFiber4Row_2_ok,
    mmFiber4Row_3_ok,
    mmFiber4Row_4_ok,
    mmFiber4Row_5_ok,
    mmFiber4Row_6_ok,
    mmFiber4Row_7_ok,
    mmFiber4Row_8_ok,
    mmFiber4Row_9_ok,
    mmFiber4Row_10_ok,
    mmFiber4Row_11_ok,
    mmFiber4Row_12_ok,
    mmFiber4Row_13_ok,
    mmFiber4Row_14_ok,
    mmFiber4Row_15_ok,
    mmFiber4Row_16_ok,
    mmFiber4Row_17_ok,
    mmFiber4Row_18_ok,
    mmFiber4Row_19_ok,
    mmFiber4Row_20_ok,
    mmFiber4Row_21_ok,
    mmFiber4Row_22_ok,
    mmFiber4Row_23_ok,
    mmFiber4Row_24_ok,
    mmFiber4Row_25_ok,
    mmFiber4Row_26_ok,
    mmFiber4Row_27_ok,
    mmFiber4Row_28_ok,
    mmFiber4Row_29_ok,
    mmFiber4Row_30_ok,
    mmFiber4Row_31_ok,
    mmFiber4Row_32_ok,
    mmFiber4Row_33_ok,
    mmFiber4Row_34_ok,
    mmFiber4Row_35_ok,
    mmFiber4Row_36_ok,
    mmFiber4Row_37_ok,
    mmFiber4Row_38_ok,
    mmFiber4Row_39_ok,
    mmFiber4Row_40_ok,
    mmFiber4Row_41_ok,
    mmFiber4Row_42_ok,
    mmFiber4Row_43_ok,
    mmFiber4Row_44_ok,
    mmFiber4Row_45_ok,
    mmFiber4Row_46_ok,
    mmFiber4Row_47_ok,
    mmFiber4Row_48_ok,
    mmFiber4Row_49_ok,
    mmFiber4Row_50_ok,
    mmFiber4Row_51_ok,
    mmFiber4Row_52_ok,
    mmFiber4Row_53_ok,
    mmFiber4Row_54_ok,
    mmFiber4Row_55_ok,
    mmFiber4Row_56_ok,
    mmFiber4Row_57_ok,
    mmFiber4Row_58_ok,
    mmFiber4Row_59_ok,
    mmFiber4Row_60_ok,
    mmFiber4Row_61_ok,
    mmFiber4Row_62_ok,
    mmFiber4Row_63_ok,
    mmFiber4Parent_0_ok,
    mmFiber4Parent_1_ok,
    mmFiber4Parent_2_ok,
    mmFiber4Parent_3_ok,
    mmFiber4Parent_4_ok,
    mmFiber4Parent_5_ok,
    mmFiber4Parent_6_ok,
    mmFiber4Parent_7_ok,
    mmFiber4Parent_8_ok,
    mmFiber4Parent_9_ok,
    mmFiber4Parent_10_ok,
    mmFiber4Parent_11_ok,
    mmFiber4Parent_12_ok,
    mmFiber4Parent_13_ok,
    mmFiber4Parent_14_ok,
    mmFiber4Parent_15_ok,
    mmFiber4Parent_16_ok,
    mmFiber4Parent_17_ok,
    mmFiber4Parent_18_ok,
    mmFiber4Parent_19_ok,
    mmFiber4Parent_20_ok,
    mmFiber4Parent_21_ok,
    mmFiber4Parent_22_ok,
    mmFiber4Parent_23_ok,
    mmFiber4Parent_24_ok,
    mmFiber4Parent_25_ok,
    mmFiber4Parent_26_ok,
    mmFiber4Parent_27_ok,
    mmFiber4Parent_28_ok,
    mmFiber4Parent_29_ok,
    mmFiber4Parent_30_ok,
    mmFiber4Parent_31_ok,
    mmFiber4Parent_32_ok,
    mmFiber4Parent_33_ok,
    mmFiber4Parent_34_ok,
    mmFiber4Parent_35_ok,
    mmFiber4Parent_36_ok,
    mmFiber4Parent_37_ok,
    mmFiber4Parent_38_ok,
    mmFiber4Parent_39_ok,
    mmFiber4Parent_40_ok,
    mmFiber4Parent_41_ok,
    mmFiber4Parent_42_ok,
    mmFiber4Parent_43_ok,
    mmFiber4Parent_44_ok,
    mmFiber4Parent_45_ok,
    mmFiber4Parent_46_ok,
    mmFiber4Parent_47_ok,
    mmFiber4Parent_48_ok,
    mmFiber4Parent_49_ok,
    mmFiber4Parent_50_ok,
    mmFiber4Parent_51_ok,
    mmFiber4Parent_52_ok,
    mmFiber4Parent_53_ok,
    mmFiber4Parent_54_ok,
    mmFiber4Parent_55_ok,
    mmFiber4Parent_56_ok,
    mmFiber4Parent_57_ok,
    mmFiber4Parent_58_ok,
    mmFiber4Parent_59_ok,
    mmFiber4Parent_60_ok,
    mmFiber4Parent_61_ok,
    mmFiber4Parent_62_ok,
    mmFiber4Parent_63_ok]

def mmFiber5Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.p]

def mmFiber5Expected : List Nat :=
  []

def mmFiber5Rows : List DirectChainParentRow :=
  []

def mmFiber5RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber5Rows i default

def mmFiber5SourcesCheck : Bool :=
  (mmFiber5Rows.map fun row => row.source) == mmFiber5Expected

theorem mmFiber5SourcesCheck_ok :
    mmFiber5SourcesCheck = true := by
  decide

def mmFiber5RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber5Key mmFiber5Expected (mmFiber5RowAt i)

def mmFiber5ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber5Rows mmMaxParentDepth (listGetD mmFiber5Expected i 0) == 0

def mmFiber5CertificateAudit : Bool :=
  mmFiber5SourcesCheck

theorem mmFiber5CertificateAudit_ok :
    mmFiber5CertificateAudit = true := by
  simp [mmFiber5CertificateAudit,
    mmFiber5SourcesCheck_ok]

def mmFiber6Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.r]

def mmFiber6Expected : List Nat :=
  [920, 921, 922, 923, 924, 925, 926, 927]

def mmFiber6Rows : List DirectChainParentRow :=
  [ directRow 920 920 184 20 184 20 default
  , directRow 921 920 184 21 184 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 922 920 184 22 184 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 923 921 184 23 184 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 924 920 185 28 184 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 925 921 185 29 184 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 926 922 185 30 184 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 927 923 185 31 184 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber6RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber6Rows i default

def mmFiber6SourcesCheck : Bool :=
  (mmFiber6Rows.map fun row => row.source) == mmFiber6Expected

theorem mmFiber6SourcesCheck_ok :
    mmFiber6SourcesCheck = true := by
  decide

def mmFiber6RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt i)

theorem mmFiber6Row_0_ok : mmFiber6RowCheck 0 = true := by decide
theorem mmFiber6Row_1_ok : mmFiber6RowCheck 1 = true := by decide
theorem mmFiber6Row_2_ok : mmFiber6RowCheck 2 = true := by decide
theorem mmFiber6Row_3_ok : mmFiber6RowCheck 3 = true := by decide
theorem mmFiber6Row_4_ok : mmFiber6RowCheck 4 = true := by decide
theorem mmFiber6Row_5_ok : mmFiber6RowCheck 5 = true := by decide
theorem mmFiber6Row_6_ok : mmFiber6RowCheck 6 = true := by decide
theorem mmFiber6Row_7_ok : mmFiber6RowCheck 7 = true := by decide

def mmFiber6ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber6Rows mmMaxParentDepth (listGetD mmFiber6Expected i 0) == 920

theorem mmFiber6Parent_0_ok : mmFiber6ParentCheck 0 = true := by decide
theorem mmFiber6Parent_1_ok : mmFiber6ParentCheck 1 = true := by decide
theorem mmFiber6Parent_2_ok : mmFiber6ParentCheck 2 = true := by decide
theorem mmFiber6Parent_3_ok : mmFiber6ParentCheck 3 = true := by decide
theorem mmFiber6Parent_4_ok : mmFiber6ParentCheck 4 = true := by decide
theorem mmFiber6Parent_5_ok : mmFiber6ParentCheck 5 = true := by decide
theorem mmFiber6Parent_6_ok : mmFiber6ParentCheck 6 = true := by decide
theorem mmFiber6Parent_7_ok : mmFiber6ParentCheck 7 = true := by decide

def mmFiber6CertificateAudit : Bool :=
  mmFiber6SourcesCheck &&
    mmFiber6RowCheck 0 &&
    mmFiber6RowCheck 1 &&
    mmFiber6RowCheck 2 &&
    mmFiber6RowCheck 3 &&
    mmFiber6RowCheck 4 &&
    mmFiber6RowCheck 5 &&
    mmFiber6RowCheck 6 &&
    mmFiber6RowCheck 7 &&
    mmFiber6ParentCheck 0 &&
    mmFiber6ParentCheck 1 &&
    mmFiber6ParentCheck 2 &&
    mmFiber6ParentCheck 3 &&
    mmFiber6ParentCheck 4 &&
    mmFiber6ParentCheck 5 &&
    mmFiber6ParentCheck 6 &&
    mmFiber6ParentCheck 7

theorem mmFiber6CertificateAudit_ok :
    mmFiber6CertificateAudit = true := by
  simp [mmFiber6CertificateAudit,
    mmFiber6SourcesCheck_ok,
    mmFiber6Row_0_ok,
    mmFiber6Row_1_ok,
    mmFiber6Row_2_ok,
    mmFiber6Row_3_ok,
    mmFiber6Row_4_ok,
    mmFiber6Row_5_ok,
    mmFiber6Row_6_ok,
    mmFiber6Row_7_ok,
    mmFiber6Parent_0_ok,
    mmFiber6Parent_1_ok,
    mmFiber6Parent_2_ok,
    mmFiber6Parent_3_ok,
    mmFiber6Parent_4_ok,
    mmFiber6Parent_5_ok,
    mmFiber6Parent_6_ok,
    mmFiber6Parent_7_ok]

def mmFiber7Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.b]

def mmFiber7Expected : List Nat :=
  []

def mmFiber7Rows : List DirectChainParentRow :=
  []

def mmFiber7RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber7Rows i default

def mmFiber7SourcesCheck : Bool :=
  (mmFiber7Rows.map fun row => row.source) == mmFiber7Expected

theorem mmFiber7SourcesCheck_ok :
    mmFiber7SourcesCheck = true := by
  decide

def mmFiber7RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber7Key mmFiber7Expected (mmFiber7RowAt i)

def mmFiber7ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber7Rows mmMaxParentDepth (listGetD mmFiber7Expected i 0) == 0

def mmFiber7CertificateAudit : Bool :=
  mmFiber7SourcesCheck

theorem mmFiber7CertificateAudit_ok :
    mmFiber7CertificateAudit = true := by
  simp [mmFiber7CertificateAudit,
    mmFiber7SourcesCheck_ok]

def mmFiber8Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.p]

def mmFiber8Expected : List Nat :=
  [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231]

def mmFiber8Rows : List DirectChainParentRow :=
  [ directRow 120 120 24 80 24 80 default
  , directRow 121 120 24 81 24 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 122 120 24 82 24 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 123 121 24 83 24 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 124 122 24 100 24 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 125 127 24 101 24 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 126 121 24 102 24 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 127 120 24 103 24 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 128 120 25 88 24 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 129 121 25 89 24 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 130 122 25 90 24 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 131 123 25 91 24 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 132 124 25 108 24 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 133 125 25 109 24 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 134 126 25 110 24 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 135 127 25 111 24 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 136 120 26 16 24 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 137 121 26 17 24 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 138 122 26 18 24 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 139 123 26 19 24 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 140 136 26 32 26 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 141 137 26 33 26 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 142 126 26 34 24 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 143 127 26 35 24 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 144 128 27 24 25 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 145 129 27 25 25 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 146 130 27 26 25 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 147 131 27 27 25 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 148 144 27 40 27 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 149 145 27 41 27 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 150 134 27 42 25 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 151 135 27 43 25 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 200 120 40 148 24 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 201 121 40 149 24 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 202 122 40 150 24 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 203 200 40 151 40 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 204 200 40 164 40 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 205 201 40 165 40 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 206 126 40 166 24 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 207 127 40 167 24 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 208 128 41 156 25 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 209 129 41 157 25 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 210 130 41 158 25 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 211 208 41 159 41 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 212 208 41 172 41 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 213 209 41 173 41 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 214 134 41 174 25 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 215 135 41 175 25 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 216 136 42 0 26 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 217 137 42 1 26 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 218 138 42 2 26 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 219 139 42 3 26 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 220 208 42 48 41 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 221 209 42 49 41 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 222 142 42 50 26 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 223 143 42 51 26 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 224 207 43 8 40 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 225 206 43 9 40 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 226 204 43 10 40 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 227 205 43 11 40 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 228 200 43 56 40 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 229 201 43 57 40 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 230 202 43 58 40 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 231 203 43 59 40 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mmFiber8RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber8Rows i default

def mmFiber8SourcesCheck : Bool :=
  (mmFiber8Rows.map fun row => row.source) == mmFiber8Expected

theorem mmFiber8SourcesCheck_ok :
    mmFiber8SourcesCheck = true := by
  decide

def mmFiber8RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber8Key mmFiber8Expected (mmFiber8RowAt i)

theorem mmFiber8Row_0_ok : mmFiber8RowCheck 0 = true := by decide
theorem mmFiber8Row_1_ok : mmFiber8RowCheck 1 = true := by decide
theorem mmFiber8Row_2_ok : mmFiber8RowCheck 2 = true := by decide
theorem mmFiber8Row_3_ok : mmFiber8RowCheck 3 = true := by decide
theorem mmFiber8Row_4_ok : mmFiber8RowCheck 4 = true := by decide
theorem mmFiber8Row_5_ok : mmFiber8RowCheck 5 = true := by decide
theorem mmFiber8Row_6_ok : mmFiber8RowCheck 6 = true := by decide
theorem mmFiber8Row_7_ok : mmFiber8RowCheck 7 = true := by decide
theorem mmFiber8Row_8_ok : mmFiber8RowCheck 8 = true := by decide
theorem mmFiber8Row_9_ok : mmFiber8RowCheck 9 = true := by decide
theorem mmFiber8Row_10_ok : mmFiber8RowCheck 10 = true := by decide
theorem mmFiber8Row_11_ok : mmFiber8RowCheck 11 = true := by decide
theorem mmFiber8Row_12_ok : mmFiber8RowCheck 12 = true := by decide
theorem mmFiber8Row_13_ok : mmFiber8RowCheck 13 = true := by decide
theorem mmFiber8Row_14_ok : mmFiber8RowCheck 14 = true := by decide
theorem mmFiber8Row_15_ok : mmFiber8RowCheck 15 = true := by decide
theorem mmFiber8Row_16_ok : mmFiber8RowCheck 16 = true := by decide
theorem mmFiber8Row_17_ok : mmFiber8RowCheck 17 = true := by decide
theorem mmFiber8Row_18_ok : mmFiber8RowCheck 18 = true := by decide
theorem mmFiber8Row_19_ok : mmFiber8RowCheck 19 = true := by decide
theorem mmFiber8Row_20_ok : mmFiber8RowCheck 20 = true := by decide
theorem mmFiber8Row_21_ok : mmFiber8RowCheck 21 = true := by decide
theorem mmFiber8Row_22_ok : mmFiber8RowCheck 22 = true := by decide
theorem mmFiber8Row_23_ok : mmFiber8RowCheck 23 = true := by decide
theorem mmFiber8Row_24_ok : mmFiber8RowCheck 24 = true := by decide
theorem mmFiber8Row_25_ok : mmFiber8RowCheck 25 = true := by decide
theorem mmFiber8Row_26_ok : mmFiber8RowCheck 26 = true := by decide
theorem mmFiber8Row_27_ok : mmFiber8RowCheck 27 = true := by decide
theorem mmFiber8Row_28_ok : mmFiber8RowCheck 28 = true := by decide
theorem mmFiber8Row_29_ok : mmFiber8RowCheck 29 = true := by decide
theorem mmFiber8Row_30_ok : mmFiber8RowCheck 30 = true := by decide
theorem mmFiber8Row_31_ok : mmFiber8RowCheck 31 = true := by decide
theorem mmFiber8Row_32_ok : mmFiber8RowCheck 32 = true := by decide
theorem mmFiber8Row_33_ok : mmFiber8RowCheck 33 = true := by decide
theorem mmFiber8Row_34_ok : mmFiber8RowCheck 34 = true := by decide
theorem mmFiber8Row_35_ok : mmFiber8RowCheck 35 = true := by decide
theorem mmFiber8Row_36_ok : mmFiber8RowCheck 36 = true := by decide
theorem mmFiber8Row_37_ok : mmFiber8RowCheck 37 = true := by decide
theorem mmFiber8Row_38_ok : mmFiber8RowCheck 38 = true := by decide
theorem mmFiber8Row_39_ok : mmFiber8RowCheck 39 = true := by decide
theorem mmFiber8Row_40_ok : mmFiber8RowCheck 40 = true := by decide
theorem mmFiber8Row_41_ok : mmFiber8RowCheck 41 = true := by decide
theorem mmFiber8Row_42_ok : mmFiber8RowCheck 42 = true := by decide
theorem mmFiber8Row_43_ok : mmFiber8RowCheck 43 = true := by decide
theorem mmFiber8Row_44_ok : mmFiber8RowCheck 44 = true := by decide
theorem mmFiber8Row_45_ok : mmFiber8RowCheck 45 = true := by decide
theorem mmFiber8Row_46_ok : mmFiber8RowCheck 46 = true := by decide
theorem mmFiber8Row_47_ok : mmFiber8RowCheck 47 = true := by decide
theorem mmFiber8Row_48_ok : mmFiber8RowCheck 48 = true := by decide
theorem mmFiber8Row_49_ok : mmFiber8RowCheck 49 = true := by decide
theorem mmFiber8Row_50_ok : mmFiber8RowCheck 50 = true := by decide
theorem mmFiber8Row_51_ok : mmFiber8RowCheck 51 = true := by decide
theorem mmFiber8Row_52_ok : mmFiber8RowCheck 52 = true := by decide
theorem mmFiber8Row_53_ok : mmFiber8RowCheck 53 = true := by decide
theorem mmFiber8Row_54_ok : mmFiber8RowCheck 54 = true := by decide
theorem mmFiber8Row_55_ok : mmFiber8RowCheck 55 = true := by decide
theorem mmFiber8Row_56_ok : mmFiber8RowCheck 56 = true := by decide
theorem mmFiber8Row_57_ok : mmFiber8RowCheck 57 = true := by decide
theorem mmFiber8Row_58_ok : mmFiber8RowCheck 58 = true := by decide
theorem mmFiber8Row_59_ok : mmFiber8RowCheck 59 = true := by decide
theorem mmFiber8Row_60_ok : mmFiber8RowCheck 60 = true := by decide
theorem mmFiber8Row_61_ok : mmFiber8RowCheck 61 = true := by decide
theorem mmFiber8Row_62_ok : mmFiber8RowCheck 62 = true := by decide
theorem mmFiber8Row_63_ok : mmFiber8RowCheck 63 = true := by decide

def mmFiber8ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber8Rows mmMaxParentDepth (listGetD mmFiber8Expected i 0) == 120

theorem mmFiber8Parent_0_ok : mmFiber8ParentCheck 0 = true := by decide
theorem mmFiber8Parent_1_ok : mmFiber8ParentCheck 1 = true := by decide
theorem mmFiber8Parent_2_ok : mmFiber8ParentCheck 2 = true := by decide
theorem mmFiber8Parent_3_ok : mmFiber8ParentCheck 3 = true := by decide
theorem mmFiber8Parent_4_ok : mmFiber8ParentCheck 4 = true := by decide
theorem mmFiber8Parent_5_ok : mmFiber8ParentCheck 5 = true := by decide
theorem mmFiber8Parent_6_ok : mmFiber8ParentCheck 6 = true := by decide
theorem mmFiber8Parent_7_ok : mmFiber8ParentCheck 7 = true := by decide
theorem mmFiber8Parent_8_ok : mmFiber8ParentCheck 8 = true := by decide
theorem mmFiber8Parent_9_ok : mmFiber8ParentCheck 9 = true := by decide
theorem mmFiber8Parent_10_ok : mmFiber8ParentCheck 10 = true := by decide
theorem mmFiber8Parent_11_ok : mmFiber8ParentCheck 11 = true := by decide
theorem mmFiber8Parent_12_ok : mmFiber8ParentCheck 12 = true := by decide
theorem mmFiber8Parent_13_ok : mmFiber8ParentCheck 13 = true := by decide
theorem mmFiber8Parent_14_ok : mmFiber8ParentCheck 14 = true := by decide
theorem mmFiber8Parent_15_ok : mmFiber8ParentCheck 15 = true := by decide
theorem mmFiber8Parent_16_ok : mmFiber8ParentCheck 16 = true := by decide
theorem mmFiber8Parent_17_ok : mmFiber8ParentCheck 17 = true := by decide
theorem mmFiber8Parent_18_ok : mmFiber8ParentCheck 18 = true := by decide
theorem mmFiber8Parent_19_ok : mmFiber8ParentCheck 19 = true := by decide
theorem mmFiber8Parent_20_ok : mmFiber8ParentCheck 20 = true := by decide
theorem mmFiber8Parent_21_ok : mmFiber8ParentCheck 21 = true := by decide
theorem mmFiber8Parent_22_ok : mmFiber8ParentCheck 22 = true := by decide
theorem mmFiber8Parent_23_ok : mmFiber8ParentCheck 23 = true := by decide
theorem mmFiber8Parent_24_ok : mmFiber8ParentCheck 24 = true := by decide
theorem mmFiber8Parent_25_ok : mmFiber8ParentCheck 25 = true := by decide
theorem mmFiber8Parent_26_ok : mmFiber8ParentCheck 26 = true := by decide
theorem mmFiber8Parent_27_ok : mmFiber8ParentCheck 27 = true := by decide
theorem mmFiber8Parent_28_ok : mmFiber8ParentCheck 28 = true := by decide
theorem mmFiber8Parent_29_ok : mmFiber8ParentCheck 29 = true := by decide
theorem mmFiber8Parent_30_ok : mmFiber8ParentCheck 30 = true := by decide
theorem mmFiber8Parent_31_ok : mmFiber8ParentCheck 31 = true := by decide
theorem mmFiber8Parent_32_ok : mmFiber8ParentCheck 32 = true := by decide
theorem mmFiber8Parent_33_ok : mmFiber8ParentCheck 33 = true := by decide
theorem mmFiber8Parent_34_ok : mmFiber8ParentCheck 34 = true := by decide
theorem mmFiber8Parent_35_ok : mmFiber8ParentCheck 35 = true := by decide
theorem mmFiber8Parent_36_ok : mmFiber8ParentCheck 36 = true := by decide
theorem mmFiber8Parent_37_ok : mmFiber8ParentCheck 37 = true := by decide
theorem mmFiber8Parent_38_ok : mmFiber8ParentCheck 38 = true := by decide
theorem mmFiber8Parent_39_ok : mmFiber8ParentCheck 39 = true := by decide
theorem mmFiber8Parent_40_ok : mmFiber8ParentCheck 40 = true := by decide
theorem mmFiber8Parent_41_ok : mmFiber8ParentCheck 41 = true := by decide
theorem mmFiber8Parent_42_ok : mmFiber8ParentCheck 42 = true := by decide
theorem mmFiber8Parent_43_ok : mmFiber8ParentCheck 43 = true := by decide
theorem mmFiber8Parent_44_ok : mmFiber8ParentCheck 44 = true := by decide
theorem mmFiber8Parent_45_ok : mmFiber8ParentCheck 45 = true := by decide
theorem mmFiber8Parent_46_ok : mmFiber8ParentCheck 46 = true := by decide
theorem mmFiber8Parent_47_ok : mmFiber8ParentCheck 47 = true := by decide
theorem mmFiber8Parent_48_ok : mmFiber8ParentCheck 48 = true := by decide
theorem mmFiber8Parent_49_ok : mmFiber8ParentCheck 49 = true := by decide
theorem mmFiber8Parent_50_ok : mmFiber8ParentCheck 50 = true := by decide
theorem mmFiber8Parent_51_ok : mmFiber8ParentCheck 51 = true := by decide
theorem mmFiber8Parent_52_ok : mmFiber8ParentCheck 52 = true := by decide
theorem mmFiber8Parent_53_ok : mmFiber8ParentCheck 53 = true := by decide
theorem mmFiber8Parent_54_ok : mmFiber8ParentCheck 54 = true := by decide
theorem mmFiber8Parent_55_ok : mmFiber8ParentCheck 55 = true := by decide
theorem mmFiber8Parent_56_ok : mmFiber8ParentCheck 56 = true := by decide
theorem mmFiber8Parent_57_ok : mmFiber8ParentCheck 57 = true := by decide
theorem mmFiber8Parent_58_ok : mmFiber8ParentCheck 58 = true := by decide
theorem mmFiber8Parent_59_ok : mmFiber8ParentCheck 59 = true := by decide
theorem mmFiber8Parent_60_ok : mmFiber8ParentCheck 60 = true := by decide
theorem mmFiber8Parent_61_ok : mmFiber8ParentCheck 61 = true := by decide
theorem mmFiber8Parent_62_ok : mmFiber8ParentCheck 62 = true := by decide
theorem mmFiber8Parent_63_ok : mmFiber8ParentCheck 63 = true := by decide

def mmFiber8CertificateAudit : Bool :=
  mmFiber8SourcesCheck &&
    mmFiber8RowCheck 0 &&
    mmFiber8RowCheck 1 &&
    mmFiber8RowCheck 2 &&
    mmFiber8RowCheck 3 &&
    mmFiber8RowCheck 4 &&
    mmFiber8RowCheck 5 &&
    mmFiber8RowCheck 6 &&
    mmFiber8RowCheck 7 &&
    mmFiber8RowCheck 8 &&
    mmFiber8RowCheck 9 &&
    mmFiber8RowCheck 10 &&
    mmFiber8RowCheck 11 &&
    mmFiber8RowCheck 12 &&
    mmFiber8RowCheck 13 &&
    mmFiber8RowCheck 14 &&
    mmFiber8RowCheck 15 &&
    mmFiber8RowCheck 16 &&
    mmFiber8RowCheck 17 &&
    mmFiber8RowCheck 18 &&
    mmFiber8RowCheck 19 &&
    mmFiber8RowCheck 20 &&
    mmFiber8RowCheck 21 &&
    mmFiber8RowCheck 22 &&
    mmFiber8RowCheck 23 &&
    mmFiber8RowCheck 24 &&
    mmFiber8RowCheck 25 &&
    mmFiber8RowCheck 26 &&
    mmFiber8RowCheck 27 &&
    mmFiber8RowCheck 28 &&
    mmFiber8RowCheck 29 &&
    mmFiber8RowCheck 30 &&
    mmFiber8RowCheck 31 &&
    mmFiber8RowCheck 32 &&
    mmFiber8RowCheck 33 &&
    mmFiber8RowCheck 34 &&
    mmFiber8RowCheck 35 &&
    mmFiber8RowCheck 36 &&
    mmFiber8RowCheck 37 &&
    mmFiber8RowCheck 38 &&
    mmFiber8RowCheck 39 &&
    mmFiber8RowCheck 40 &&
    mmFiber8RowCheck 41 &&
    mmFiber8RowCheck 42 &&
    mmFiber8RowCheck 43 &&
    mmFiber8RowCheck 44 &&
    mmFiber8RowCheck 45 &&
    mmFiber8RowCheck 46 &&
    mmFiber8RowCheck 47 &&
    mmFiber8RowCheck 48 &&
    mmFiber8RowCheck 49 &&
    mmFiber8RowCheck 50 &&
    mmFiber8RowCheck 51 &&
    mmFiber8RowCheck 52 &&
    mmFiber8RowCheck 53 &&
    mmFiber8RowCheck 54 &&
    mmFiber8RowCheck 55 &&
    mmFiber8RowCheck 56 &&
    mmFiber8RowCheck 57 &&
    mmFiber8RowCheck 58 &&
    mmFiber8RowCheck 59 &&
    mmFiber8RowCheck 60 &&
    mmFiber8RowCheck 61 &&
    mmFiber8RowCheck 62 &&
    mmFiber8RowCheck 63 &&
    mmFiber8ParentCheck 0 &&
    mmFiber8ParentCheck 1 &&
    mmFiber8ParentCheck 2 &&
    mmFiber8ParentCheck 3 &&
    mmFiber8ParentCheck 4 &&
    mmFiber8ParentCheck 5 &&
    mmFiber8ParentCheck 6 &&
    mmFiber8ParentCheck 7 &&
    mmFiber8ParentCheck 8 &&
    mmFiber8ParentCheck 9 &&
    mmFiber8ParentCheck 10 &&
    mmFiber8ParentCheck 11 &&
    mmFiber8ParentCheck 12 &&
    mmFiber8ParentCheck 13 &&
    mmFiber8ParentCheck 14 &&
    mmFiber8ParentCheck 15 &&
    mmFiber8ParentCheck 16 &&
    mmFiber8ParentCheck 17 &&
    mmFiber8ParentCheck 18 &&
    mmFiber8ParentCheck 19 &&
    mmFiber8ParentCheck 20 &&
    mmFiber8ParentCheck 21 &&
    mmFiber8ParentCheck 22 &&
    mmFiber8ParentCheck 23 &&
    mmFiber8ParentCheck 24 &&
    mmFiber8ParentCheck 25 &&
    mmFiber8ParentCheck 26 &&
    mmFiber8ParentCheck 27 &&
    mmFiber8ParentCheck 28 &&
    mmFiber8ParentCheck 29 &&
    mmFiber8ParentCheck 30 &&
    mmFiber8ParentCheck 31 &&
    mmFiber8ParentCheck 32 &&
    mmFiber8ParentCheck 33 &&
    mmFiber8ParentCheck 34 &&
    mmFiber8ParentCheck 35 &&
    mmFiber8ParentCheck 36 &&
    mmFiber8ParentCheck 37 &&
    mmFiber8ParentCheck 38 &&
    mmFiber8ParentCheck 39 &&
    mmFiber8ParentCheck 40 &&
    mmFiber8ParentCheck 41 &&
    mmFiber8ParentCheck 42 &&
    mmFiber8ParentCheck 43 &&
    mmFiber8ParentCheck 44 &&
    mmFiber8ParentCheck 45 &&
    mmFiber8ParentCheck 46 &&
    mmFiber8ParentCheck 47 &&
    mmFiber8ParentCheck 48 &&
    mmFiber8ParentCheck 49 &&
    mmFiber8ParentCheck 50 &&
    mmFiber8ParentCheck 51 &&
    mmFiber8ParentCheck 52 &&
    mmFiber8ParentCheck 53 &&
    mmFiber8ParentCheck 54 &&
    mmFiber8ParentCheck 55 &&
    mmFiber8ParentCheck 56 &&
    mmFiber8ParentCheck 57 &&
    mmFiber8ParentCheck 58 &&
    mmFiber8ParentCheck 59 &&
    mmFiber8ParentCheck 60 &&
    mmFiber8ParentCheck 61 &&
    mmFiber8ParentCheck 62 &&
    mmFiber8ParentCheck 63

theorem mmFiber8CertificateAudit_ok :
    mmFiber8CertificateAudit = true := by
  simp [mmFiber8CertificateAudit,
    mmFiber8SourcesCheck_ok,
    mmFiber8Row_0_ok,
    mmFiber8Row_1_ok,
    mmFiber8Row_2_ok,
    mmFiber8Row_3_ok,
    mmFiber8Row_4_ok,
    mmFiber8Row_5_ok,
    mmFiber8Row_6_ok,
    mmFiber8Row_7_ok,
    mmFiber8Row_8_ok,
    mmFiber8Row_9_ok,
    mmFiber8Row_10_ok,
    mmFiber8Row_11_ok,
    mmFiber8Row_12_ok,
    mmFiber8Row_13_ok,
    mmFiber8Row_14_ok,
    mmFiber8Row_15_ok,
    mmFiber8Row_16_ok,
    mmFiber8Row_17_ok,
    mmFiber8Row_18_ok,
    mmFiber8Row_19_ok,
    mmFiber8Row_20_ok,
    mmFiber8Row_21_ok,
    mmFiber8Row_22_ok,
    mmFiber8Row_23_ok,
    mmFiber8Row_24_ok,
    mmFiber8Row_25_ok,
    mmFiber8Row_26_ok,
    mmFiber8Row_27_ok,
    mmFiber8Row_28_ok,
    mmFiber8Row_29_ok,
    mmFiber8Row_30_ok,
    mmFiber8Row_31_ok,
    mmFiber8Row_32_ok,
    mmFiber8Row_33_ok,
    mmFiber8Row_34_ok,
    mmFiber8Row_35_ok,
    mmFiber8Row_36_ok,
    mmFiber8Row_37_ok,
    mmFiber8Row_38_ok,
    mmFiber8Row_39_ok,
    mmFiber8Row_40_ok,
    mmFiber8Row_41_ok,
    mmFiber8Row_42_ok,
    mmFiber8Row_43_ok,
    mmFiber8Row_44_ok,
    mmFiber8Row_45_ok,
    mmFiber8Row_46_ok,
    mmFiber8Row_47_ok,
    mmFiber8Row_48_ok,
    mmFiber8Row_49_ok,
    mmFiber8Row_50_ok,
    mmFiber8Row_51_ok,
    mmFiber8Row_52_ok,
    mmFiber8Row_53_ok,
    mmFiber8Row_54_ok,
    mmFiber8Row_55_ok,
    mmFiber8Row_56_ok,
    mmFiber8Row_57_ok,
    mmFiber8Row_58_ok,
    mmFiber8Row_59_ok,
    mmFiber8Row_60_ok,
    mmFiber8Row_61_ok,
    mmFiber8Row_62_ok,
    mmFiber8Row_63_ok,
    mmFiber8Parent_0_ok,
    mmFiber8Parent_1_ok,
    mmFiber8Parent_2_ok,
    mmFiber8Parent_3_ok,
    mmFiber8Parent_4_ok,
    mmFiber8Parent_5_ok,
    mmFiber8Parent_6_ok,
    mmFiber8Parent_7_ok,
    mmFiber8Parent_8_ok,
    mmFiber8Parent_9_ok,
    mmFiber8Parent_10_ok,
    mmFiber8Parent_11_ok,
    mmFiber8Parent_12_ok,
    mmFiber8Parent_13_ok,
    mmFiber8Parent_14_ok,
    mmFiber8Parent_15_ok,
    mmFiber8Parent_16_ok,
    mmFiber8Parent_17_ok,
    mmFiber8Parent_18_ok,
    mmFiber8Parent_19_ok,
    mmFiber8Parent_20_ok,
    mmFiber8Parent_21_ok,
    mmFiber8Parent_22_ok,
    mmFiber8Parent_23_ok,
    mmFiber8Parent_24_ok,
    mmFiber8Parent_25_ok,
    mmFiber8Parent_26_ok,
    mmFiber8Parent_27_ok,
    mmFiber8Parent_28_ok,
    mmFiber8Parent_29_ok,
    mmFiber8Parent_30_ok,
    mmFiber8Parent_31_ok,
    mmFiber8Parent_32_ok,
    mmFiber8Parent_33_ok,
    mmFiber8Parent_34_ok,
    mmFiber8Parent_35_ok,
    mmFiber8Parent_36_ok,
    mmFiber8Parent_37_ok,
    mmFiber8Parent_38_ok,
    mmFiber8Parent_39_ok,
    mmFiber8Parent_40_ok,
    mmFiber8Parent_41_ok,
    mmFiber8Parent_42_ok,
    mmFiber8Parent_43_ok,
    mmFiber8Parent_44_ok,
    mmFiber8Parent_45_ok,
    mmFiber8Parent_46_ok,
    mmFiber8Parent_47_ok,
    mmFiber8Parent_48_ok,
    mmFiber8Parent_49_ok,
    mmFiber8Parent_50_ok,
    mmFiber8Parent_51_ok,
    mmFiber8Parent_52_ok,
    mmFiber8Parent_53_ok,
    mmFiber8Parent_54_ok,
    mmFiber8Parent_55_ok,
    mmFiber8Parent_56_ok,
    mmFiber8Parent_57_ok,
    mmFiber8Parent_58_ok,
    mmFiber8Parent_59_ok,
    mmFiber8Parent_60_ok,
    mmFiber8Parent_61_ok,
    mmFiber8Parent_62_ok,
    mmFiber8Parent_63_ok]

def mmFiber9Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.r]

def mmFiber9Expected : List Nat :=
  [560, 561, 562, 563, 564, 565, 566, 567]

def mmFiber9Rows : List DirectChainParentRow :=
  [ directRow 560 560 114 52 114 52 default
  , directRow 561 560 114 53 114 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 562 561 114 54 114 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 563 560 114 55 114 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 564 560 115 60 114 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 565 561 115 61 114 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 566 562 115 62 114 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 567 563 115 63 114 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber9RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber9Rows i default

def mmFiber9SourcesCheck : Bool :=
  (mmFiber9Rows.map fun row => row.source) == mmFiber9Expected

theorem mmFiber9SourcesCheck_ok :
    mmFiber9SourcesCheck = true := by
  decide

def mmFiber9RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt i)

theorem mmFiber9Row_0_ok : mmFiber9RowCheck 0 = true := by decide
theorem mmFiber9Row_1_ok : mmFiber9RowCheck 1 = true := by decide
theorem mmFiber9Row_2_ok : mmFiber9RowCheck 2 = true := by decide
theorem mmFiber9Row_3_ok : mmFiber9RowCheck 3 = true := by decide
theorem mmFiber9Row_4_ok : mmFiber9RowCheck 4 = true := by decide
theorem mmFiber9Row_5_ok : mmFiber9RowCheck 5 = true := by decide
theorem mmFiber9Row_6_ok : mmFiber9RowCheck 6 = true := by decide
theorem mmFiber9Row_7_ok : mmFiber9RowCheck 7 = true := by decide

def mmFiber9ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber9Rows mmMaxParentDepth (listGetD mmFiber9Expected i 0) == 560

theorem mmFiber9Parent_0_ok : mmFiber9ParentCheck 0 = true := by decide
theorem mmFiber9Parent_1_ok : mmFiber9ParentCheck 1 = true := by decide
theorem mmFiber9Parent_2_ok : mmFiber9ParentCheck 2 = true := by decide
theorem mmFiber9Parent_3_ok : mmFiber9ParentCheck 3 = true := by decide
theorem mmFiber9Parent_4_ok : mmFiber9ParentCheck 4 = true := by decide
theorem mmFiber9Parent_5_ok : mmFiber9ParentCheck 5 = true := by decide
theorem mmFiber9Parent_6_ok : mmFiber9ParentCheck 6 = true := by decide
theorem mmFiber9Parent_7_ok : mmFiber9ParentCheck 7 = true := by decide

def mmFiber9CertificateAudit : Bool :=
  mmFiber9SourcesCheck &&
    mmFiber9RowCheck 0 &&
    mmFiber9RowCheck 1 &&
    mmFiber9RowCheck 2 &&
    mmFiber9RowCheck 3 &&
    mmFiber9RowCheck 4 &&
    mmFiber9RowCheck 5 &&
    mmFiber9RowCheck 6 &&
    mmFiber9RowCheck 7 &&
    mmFiber9ParentCheck 0 &&
    mmFiber9ParentCheck 1 &&
    mmFiber9ParentCheck 2 &&
    mmFiber9ParentCheck 3 &&
    mmFiber9ParentCheck 4 &&
    mmFiber9ParentCheck 5 &&
    mmFiber9ParentCheck 6 &&
    mmFiber9ParentCheck 7

theorem mmFiber9CertificateAudit_ok :
    mmFiber9CertificateAudit = true := by
  simp [mmFiber9CertificateAudit,
    mmFiber9SourcesCheck_ok,
    mmFiber9Row_0_ok,
    mmFiber9Row_1_ok,
    mmFiber9Row_2_ok,
    mmFiber9Row_3_ok,
    mmFiber9Row_4_ok,
    mmFiber9Row_5_ok,
    mmFiber9Row_6_ok,
    mmFiber9Row_7_ok,
    mmFiber9Parent_0_ok,
    mmFiber9Parent_1_ok,
    mmFiber9Parent_2_ok,
    mmFiber9Parent_3_ok,
    mmFiber9Parent_4_ok,
    mmFiber9Parent_5_ok,
    mmFiber9Parent_6_ok,
    mmFiber9Parent_7_ok]

def mmFiber10Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.b]

def mmFiber10Expected : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]

def mmFiber10Rows : List DirectChainParentRow :=
  [ directRow 0 0 0 80 0 80 default
  , directRow 1 0 0 81 0 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 2 0 0 82 0 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 3 1 0 83 0 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 4 2 0 100 0 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 5 7 0 101 0 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 6 1 0 102 0 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 7 0 0 103 0 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 8 0 1 88 0 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 9 1 1 89 0 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 10 2 1 90 0 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 11 3 1 91 0 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 12 4 1 108 0 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 13 5 1 109 0 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 14 6 1 110 0 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 15 7 1 111 0 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 16 0 2 16 0 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 17 1 2 17 0 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 18 2 2 18 0 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 19 3 2 19 0 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 20 16 2 32 2 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 21 17 2 33 2 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 22 6 2 34 0 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 23 7 2 35 0 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 24 8 3 24 1 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 25 9 3 25 1 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 26 10 3 26 1 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 27 11 3 27 1 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 28 24 3 40 3 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 29 25 3 41 3 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 30 14 3 42 1 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 31 15 3 43 1 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 240 0 48 148 0 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 241 1 48 149 0 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 242 2 48 150 0 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 243 240 48 151 48 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 244 240 48 164 48 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 245 241 48 165 48 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 246 6 48 166 0 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 247 7 48 167 0 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 248 8 49 156 1 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 249 9 49 157 1 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 250 10 49 158 1 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 251 248 49 159 49 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 252 248 49 172 49 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 253 249 49 173 49 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 254 14 49 174 1 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 255 15 49 175 1 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 256 16 50 0 2 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 257 17 50 1 2 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 258 18 50 2 2 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 259 19 50 3 2 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 260 248 50 48 49 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 261 249 50 49 49 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 262 22 50 50 2 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 263 23 50 51 2 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 264 247 51 8 48 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 265 246 51 9 48 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 266 244 51 10 48 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 267 245 51 11 48 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 268 240 51 56 48 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 269 241 51 57 48 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 270 242 51 58 48 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 271 243 51 59 48 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mmFiber10RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber10Rows i default

def mmFiber10SourcesCheck : Bool :=
  (mmFiber10Rows.map fun row => row.source) == mmFiber10Expected

theorem mmFiber10SourcesCheck_ok :
    mmFiber10SourcesCheck = true := by
  decide

def mmFiber10RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt i)

theorem mmFiber10Row_0_ok : mmFiber10RowCheck 0 = true := by decide
theorem mmFiber10Row_1_ok : mmFiber10RowCheck 1 = true := by decide
theorem mmFiber10Row_2_ok : mmFiber10RowCheck 2 = true := by decide
theorem mmFiber10Row_3_ok : mmFiber10RowCheck 3 = true := by decide
theorem mmFiber10Row_4_ok : mmFiber10RowCheck 4 = true := by decide
theorem mmFiber10Row_5_ok : mmFiber10RowCheck 5 = true := by decide
theorem mmFiber10Row_6_ok : mmFiber10RowCheck 6 = true := by decide
theorem mmFiber10Row_7_ok : mmFiber10RowCheck 7 = true := by decide
theorem mmFiber10Row_8_ok : mmFiber10RowCheck 8 = true := by decide
theorem mmFiber10Row_9_ok : mmFiber10RowCheck 9 = true := by decide
theorem mmFiber10Row_10_ok : mmFiber10RowCheck 10 = true := by decide
theorem mmFiber10Row_11_ok : mmFiber10RowCheck 11 = true := by decide
theorem mmFiber10Row_12_ok : mmFiber10RowCheck 12 = true := by decide
theorem mmFiber10Row_13_ok : mmFiber10RowCheck 13 = true := by decide
theorem mmFiber10Row_14_ok : mmFiber10RowCheck 14 = true := by decide
theorem mmFiber10Row_15_ok : mmFiber10RowCheck 15 = true := by decide
theorem mmFiber10Row_16_ok : mmFiber10RowCheck 16 = true := by decide
theorem mmFiber10Row_17_ok : mmFiber10RowCheck 17 = true := by decide
theorem mmFiber10Row_18_ok : mmFiber10RowCheck 18 = true := by decide
theorem mmFiber10Row_19_ok : mmFiber10RowCheck 19 = true := by decide
theorem mmFiber10Row_20_ok : mmFiber10RowCheck 20 = true := by decide
theorem mmFiber10Row_21_ok : mmFiber10RowCheck 21 = true := by decide
theorem mmFiber10Row_22_ok : mmFiber10RowCheck 22 = true := by decide
theorem mmFiber10Row_23_ok : mmFiber10RowCheck 23 = true := by decide
theorem mmFiber10Row_24_ok : mmFiber10RowCheck 24 = true := by decide
theorem mmFiber10Row_25_ok : mmFiber10RowCheck 25 = true := by decide
theorem mmFiber10Row_26_ok : mmFiber10RowCheck 26 = true := by decide
theorem mmFiber10Row_27_ok : mmFiber10RowCheck 27 = true := by decide
theorem mmFiber10Row_28_ok : mmFiber10RowCheck 28 = true := by decide
theorem mmFiber10Row_29_ok : mmFiber10RowCheck 29 = true := by decide
theorem mmFiber10Row_30_ok : mmFiber10RowCheck 30 = true := by decide
theorem mmFiber10Row_31_ok : mmFiber10RowCheck 31 = true := by decide
theorem mmFiber10Row_32_ok : mmFiber10RowCheck 32 = true := by decide
theorem mmFiber10Row_33_ok : mmFiber10RowCheck 33 = true := by decide
theorem mmFiber10Row_34_ok : mmFiber10RowCheck 34 = true := by decide
theorem mmFiber10Row_35_ok : mmFiber10RowCheck 35 = true := by decide
theorem mmFiber10Row_36_ok : mmFiber10RowCheck 36 = true := by decide
theorem mmFiber10Row_37_ok : mmFiber10RowCheck 37 = true := by decide
theorem mmFiber10Row_38_ok : mmFiber10RowCheck 38 = true := by decide
theorem mmFiber10Row_39_ok : mmFiber10RowCheck 39 = true := by decide
theorem mmFiber10Row_40_ok : mmFiber10RowCheck 40 = true := by decide
theorem mmFiber10Row_41_ok : mmFiber10RowCheck 41 = true := by decide
theorem mmFiber10Row_42_ok : mmFiber10RowCheck 42 = true := by decide
theorem mmFiber10Row_43_ok : mmFiber10RowCheck 43 = true := by decide
theorem mmFiber10Row_44_ok : mmFiber10RowCheck 44 = true := by decide
theorem mmFiber10Row_45_ok : mmFiber10RowCheck 45 = true := by decide
theorem mmFiber10Row_46_ok : mmFiber10RowCheck 46 = true := by decide
theorem mmFiber10Row_47_ok : mmFiber10RowCheck 47 = true := by decide
theorem mmFiber10Row_48_ok : mmFiber10RowCheck 48 = true := by decide
theorem mmFiber10Row_49_ok : mmFiber10RowCheck 49 = true := by decide
theorem mmFiber10Row_50_ok : mmFiber10RowCheck 50 = true := by decide
theorem mmFiber10Row_51_ok : mmFiber10RowCheck 51 = true := by decide
theorem mmFiber10Row_52_ok : mmFiber10RowCheck 52 = true := by decide
theorem mmFiber10Row_53_ok : mmFiber10RowCheck 53 = true := by decide
theorem mmFiber10Row_54_ok : mmFiber10RowCheck 54 = true := by decide
theorem mmFiber10Row_55_ok : mmFiber10RowCheck 55 = true := by decide
theorem mmFiber10Row_56_ok : mmFiber10RowCheck 56 = true := by decide
theorem mmFiber10Row_57_ok : mmFiber10RowCheck 57 = true := by decide
theorem mmFiber10Row_58_ok : mmFiber10RowCheck 58 = true := by decide
theorem mmFiber10Row_59_ok : mmFiber10RowCheck 59 = true := by decide
theorem mmFiber10Row_60_ok : mmFiber10RowCheck 60 = true := by decide
theorem mmFiber10Row_61_ok : mmFiber10RowCheck 61 = true := by decide
theorem mmFiber10Row_62_ok : mmFiber10RowCheck 62 = true := by decide
theorem mmFiber10Row_63_ok : mmFiber10RowCheck 63 = true := by decide

def mmFiber10ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber10Rows mmMaxParentDepth (listGetD mmFiber10Expected i 0) == 0

theorem mmFiber10Parent_0_ok : mmFiber10ParentCheck 0 = true := by decide
theorem mmFiber10Parent_1_ok : mmFiber10ParentCheck 1 = true := by decide
theorem mmFiber10Parent_2_ok : mmFiber10ParentCheck 2 = true := by decide
theorem mmFiber10Parent_3_ok : mmFiber10ParentCheck 3 = true := by decide
theorem mmFiber10Parent_4_ok : mmFiber10ParentCheck 4 = true := by decide
theorem mmFiber10Parent_5_ok : mmFiber10ParentCheck 5 = true := by decide
theorem mmFiber10Parent_6_ok : mmFiber10ParentCheck 6 = true := by decide
theorem mmFiber10Parent_7_ok : mmFiber10ParentCheck 7 = true := by decide
theorem mmFiber10Parent_8_ok : mmFiber10ParentCheck 8 = true := by decide
theorem mmFiber10Parent_9_ok : mmFiber10ParentCheck 9 = true := by decide
theorem mmFiber10Parent_10_ok : mmFiber10ParentCheck 10 = true := by decide
theorem mmFiber10Parent_11_ok : mmFiber10ParentCheck 11 = true := by decide
theorem mmFiber10Parent_12_ok : mmFiber10ParentCheck 12 = true := by decide
theorem mmFiber10Parent_13_ok : mmFiber10ParentCheck 13 = true := by decide
theorem mmFiber10Parent_14_ok : mmFiber10ParentCheck 14 = true := by decide
theorem mmFiber10Parent_15_ok : mmFiber10ParentCheck 15 = true := by decide
theorem mmFiber10Parent_16_ok : mmFiber10ParentCheck 16 = true := by decide
theorem mmFiber10Parent_17_ok : mmFiber10ParentCheck 17 = true := by decide
theorem mmFiber10Parent_18_ok : mmFiber10ParentCheck 18 = true := by decide
theorem mmFiber10Parent_19_ok : mmFiber10ParentCheck 19 = true := by decide
theorem mmFiber10Parent_20_ok : mmFiber10ParentCheck 20 = true := by decide
theorem mmFiber10Parent_21_ok : mmFiber10ParentCheck 21 = true := by decide
theorem mmFiber10Parent_22_ok : mmFiber10ParentCheck 22 = true := by decide
theorem mmFiber10Parent_23_ok : mmFiber10ParentCheck 23 = true := by decide
theorem mmFiber10Parent_24_ok : mmFiber10ParentCheck 24 = true := by decide
theorem mmFiber10Parent_25_ok : mmFiber10ParentCheck 25 = true := by decide
theorem mmFiber10Parent_26_ok : mmFiber10ParentCheck 26 = true := by decide
theorem mmFiber10Parent_27_ok : mmFiber10ParentCheck 27 = true := by decide
theorem mmFiber10Parent_28_ok : mmFiber10ParentCheck 28 = true := by decide
theorem mmFiber10Parent_29_ok : mmFiber10ParentCheck 29 = true := by decide
theorem mmFiber10Parent_30_ok : mmFiber10ParentCheck 30 = true := by decide
theorem mmFiber10Parent_31_ok : mmFiber10ParentCheck 31 = true := by decide
theorem mmFiber10Parent_32_ok : mmFiber10ParentCheck 32 = true := by decide
theorem mmFiber10Parent_33_ok : mmFiber10ParentCheck 33 = true := by decide
theorem mmFiber10Parent_34_ok : mmFiber10ParentCheck 34 = true := by decide
theorem mmFiber10Parent_35_ok : mmFiber10ParentCheck 35 = true := by decide
theorem mmFiber10Parent_36_ok : mmFiber10ParentCheck 36 = true := by decide
theorem mmFiber10Parent_37_ok : mmFiber10ParentCheck 37 = true := by decide
theorem mmFiber10Parent_38_ok : mmFiber10ParentCheck 38 = true := by decide
theorem mmFiber10Parent_39_ok : mmFiber10ParentCheck 39 = true := by decide
theorem mmFiber10Parent_40_ok : mmFiber10ParentCheck 40 = true := by decide
theorem mmFiber10Parent_41_ok : mmFiber10ParentCheck 41 = true := by decide
theorem mmFiber10Parent_42_ok : mmFiber10ParentCheck 42 = true := by decide
theorem mmFiber10Parent_43_ok : mmFiber10ParentCheck 43 = true := by decide
theorem mmFiber10Parent_44_ok : mmFiber10ParentCheck 44 = true := by decide
theorem mmFiber10Parent_45_ok : mmFiber10ParentCheck 45 = true := by decide
theorem mmFiber10Parent_46_ok : mmFiber10ParentCheck 46 = true := by decide
theorem mmFiber10Parent_47_ok : mmFiber10ParentCheck 47 = true := by decide
theorem mmFiber10Parent_48_ok : mmFiber10ParentCheck 48 = true := by decide
theorem mmFiber10Parent_49_ok : mmFiber10ParentCheck 49 = true := by decide
theorem mmFiber10Parent_50_ok : mmFiber10ParentCheck 50 = true := by decide
theorem mmFiber10Parent_51_ok : mmFiber10ParentCheck 51 = true := by decide
theorem mmFiber10Parent_52_ok : mmFiber10ParentCheck 52 = true := by decide
theorem mmFiber10Parent_53_ok : mmFiber10ParentCheck 53 = true := by decide
theorem mmFiber10Parent_54_ok : mmFiber10ParentCheck 54 = true := by decide
theorem mmFiber10Parent_55_ok : mmFiber10ParentCheck 55 = true := by decide
theorem mmFiber10Parent_56_ok : mmFiber10ParentCheck 56 = true := by decide
theorem mmFiber10Parent_57_ok : mmFiber10ParentCheck 57 = true := by decide
theorem mmFiber10Parent_58_ok : mmFiber10ParentCheck 58 = true := by decide
theorem mmFiber10Parent_59_ok : mmFiber10ParentCheck 59 = true := by decide
theorem mmFiber10Parent_60_ok : mmFiber10ParentCheck 60 = true := by decide
theorem mmFiber10Parent_61_ok : mmFiber10ParentCheck 61 = true := by decide
theorem mmFiber10Parent_62_ok : mmFiber10ParentCheck 62 = true := by decide
theorem mmFiber10Parent_63_ok : mmFiber10ParentCheck 63 = true := by decide

def mmFiber10CertificateAudit : Bool :=
  mmFiber10SourcesCheck &&
    mmFiber10RowCheck 0 &&
    mmFiber10RowCheck 1 &&
    mmFiber10RowCheck 2 &&
    mmFiber10RowCheck 3 &&
    mmFiber10RowCheck 4 &&
    mmFiber10RowCheck 5 &&
    mmFiber10RowCheck 6 &&
    mmFiber10RowCheck 7 &&
    mmFiber10RowCheck 8 &&
    mmFiber10RowCheck 9 &&
    mmFiber10RowCheck 10 &&
    mmFiber10RowCheck 11 &&
    mmFiber10RowCheck 12 &&
    mmFiber10RowCheck 13 &&
    mmFiber10RowCheck 14 &&
    mmFiber10RowCheck 15 &&
    mmFiber10RowCheck 16 &&
    mmFiber10RowCheck 17 &&
    mmFiber10RowCheck 18 &&
    mmFiber10RowCheck 19 &&
    mmFiber10RowCheck 20 &&
    mmFiber10RowCheck 21 &&
    mmFiber10RowCheck 22 &&
    mmFiber10RowCheck 23 &&
    mmFiber10RowCheck 24 &&
    mmFiber10RowCheck 25 &&
    mmFiber10RowCheck 26 &&
    mmFiber10RowCheck 27 &&
    mmFiber10RowCheck 28 &&
    mmFiber10RowCheck 29 &&
    mmFiber10RowCheck 30 &&
    mmFiber10RowCheck 31 &&
    mmFiber10RowCheck 32 &&
    mmFiber10RowCheck 33 &&
    mmFiber10RowCheck 34 &&
    mmFiber10RowCheck 35 &&
    mmFiber10RowCheck 36 &&
    mmFiber10RowCheck 37 &&
    mmFiber10RowCheck 38 &&
    mmFiber10RowCheck 39 &&
    mmFiber10RowCheck 40 &&
    mmFiber10RowCheck 41 &&
    mmFiber10RowCheck 42 &&
    mmFiber10RowCheck 43 &&
    mmFiber10RowCheck 44 &&
    mmFiber10RowCheck 45 &&
    mmFiber10RowCheck 46 &&
    mmFiber10RowCheck 47 &&
    mmFiber10RowCheck 48 &&
    mmFiber10RowCheck 49 &&
    mmFiber10RowCheck 50 &&
    mmFiber10RowCheck 51 &&
    mmFiber10RowCheck 52 &&
    mmFiber10RowCheck 53 &&
    mmFiber10RowCheck 54 &&
    mmFiber10RowCheck 55 &&
    mmFiber10RowCheck 56 &&
    mmFiber10RowCheck 57 &&
    mmFiber10RowCheck 58 &&
    mmFiber10RowCheck 59 &&
    mmFiber10RowCheck 60 &&
    mmFiber10RowCheck 61 &&
    mmFiber10RowCheck 62 &&
    mmFiber10RowCheck 63 &&
    mmFiber10ParentCheck 0 &&
    mmFiber10ParentCheck 1 &&
    mmFiber10ParentCheck 2 &&
    mmFiber10ParentCheck 3 &&
    mmFiber10ParentCheck 4 &&
    mmFiber10ParentCheck 5 &&
    mmFiber10ParentCheck 6 &&
    mmFiber10ParentCheck 7 &&
    mmFiber10ParentCheck 8 &&
    mmFiber10ParentCheck 9 &&
    mmFiber10ParentCheck 10 &&
    mmFiber10ParentCheck 11 &&
    mmFiber10ParentCheck 12 &&
    mmFiber10ParentCheck 13 &&
    mmFiber10ParentCheck 14 &&
    mmFiber10ParentCheck 15 &&
    mmFiber10ParentCheck 16 &&
    mmFiber10ParentCheck 17 &&
    mmFiber10ParentCheck 18 &&
    mmFiber10ParentCheck 19 &&
    mmFiber10ParentCheck 20 &&
    mmFiber10ParentCheck 21 &&
    mmFiber10ParentCheck 22 &&
    mmFiber10ParentCheck 23 &&
    mmFiber10ParentCheck 24 &&
    mmFiber10ParentCheck 25 &&
    mmFiber10ParentCheck 26 &&
    mmFiber10ParentCheck 27 &&
    mmFiber10ParentCheck 28 &&
    mmFiber10ParentCheck 29 &&
    mmFiber10ParentCheck 30 &&
    mmFiber10ParentCheck 31 &&
    mmFiber10ParentCheck 32 &&
    mmFiber10ParentCheck 33 &&
    mmFiber10ParentCheck 34 &&
    mmFiber10ParentCheck 35 &&
    mmFiber10ParentCheck 36 &&
    mmFiber10ParentCheck 37 &&
    mmFiber10ParentCheck 38 &&
    mmFiber10ParentCheck 39 &&
    mmFiber10ParentCheck 40 &&
    mmFiber10ParentCheck 41 &&
    mmFiber10ParentCheck 42 &&
    mmFiber10ParentCheck 43 &&
    mmFiber10ParentCheck 44 &&
    mmFiber10ParentCheck 45 &&
    mmFiber10ParentCheck 46 &&
    mmFiber10ParentCheck 47 &&
    mmFiber10ParentCheck 48 &&
    mmFiber10ParentCheck 49 &&
    mmFiber10ParentCheck 50 &&
    mmFiber10ParentCheck 51 &&
    mmFiber10ParentCheck 52 &&
    mmFiber10ParentCheck 53 &&
    mmFiber10ParentCheck 54 &&
    mmFiber10ParentCheck 55 &&
    mmFiber10ParentCheck 56 &&
    mmFiber10ParentCheck 57 &&
    mmFiber10ParentCheck 58 &&
    mmFiber10ParentCheck 59 &&
    mmFiber10ParentCheck 60 &&
    mmFiber10ParentCheck 61 &&
    mmFiber10ParentCheck 62 &&
    mmFiber10ParentCheck 63

theorem mmFiber10CertificateAudit_ok :
    mmFiber10CertificateAudit = true := by
  simp [mmFiber10CertificateAudit,
    mmFiber10SourcesCheck_ok,
    mmFiber10Row_0_ok,
    mmFiber10Row_1_ok,
    mmFiber10Row_2_ok,
    mmFiber10Row_3_ok,
    mmFiber10Row_4_ok,
    mmFiber10Row_5_ok,
    mmFiber10Row_6_ok,
    mmFiber10Row_7_ok,
    mmFiber10Row_8_ok,
    mmFiber10Row_9_ok,
    mmFiber10Row_10_ok,
    mmFiber10Row_11_ok,
    mmFiber10Row_12_ok,
    mmFiber10Row_13_ok,
    mmFiber10Row_14_ok,
    mmFiber10Row_15_ok,
    mmFiber10Row_16_ok,
    mmFiber10Row_17_ok,
    mmFiber10Row_18_ok,
    mmFiber10Row_19_ok,
    mmFiber10Row_20_ok,
    mmFiber10Row_21_ok,
    mmFiber10Row_22_ok,
    mmFiber10Row_23_ok,
    mmFiber10Row_24_ok,
    mmFiber10Row_25_ok,
    mmFiber10Row_26_ok,
    mmFiber10Row_27_ok,
    mmFiber10Row_28_ok,
    mmFiber10Row_29_ok,
    mmFiber10Row_30_ok,
    mmFiber10Row_31_ok,
    mmFiber10Row_32_ok,
    mmFiber10Row_33_ok,
    mmFiber10Row_34_ok,
    mmFiber10Row_35_ok,
    mmFiber10Row_36_ok,
    mmFiber10Row_37_ok,
    mmFiber10Row_38_ok,
    mmFiber10Row_39_ok,
    mmFiber10Row_40_ok,
    mmFiber10Row_41_ok,
    mmFiber10Row_42_ok,
    mmFiber10Row_43_ok,
    mmFiber10Row_44_ok,
    mmFiber10Row_45_ok,
    mmFiber10Row_46_ok,
    mmFiber10Row_47_ok,
    mmFiber10Row_48_ok,
    mmFiber10Row_49_ok,
    mmFiber10Row_50_ok,
    mmFiber10Row_51_ok,
    mmFiber10Row_52_ok,
    mmFiber10Row_53_ok,
    mmFiber10Row_54_ok,
    mmFiber10Row_55_ok,
    mmFiber10Row_56_ok,
    mmFiber10Row_57_ok,
    mmFiber10Row_58_ok,
    mmFiber10Row_59_ok,
    mmFiber10Row_60_ok,
    mmFiber10Row_61_ok,
    mmFiber10Row_62_ok,
    mmFiber10Row_63_ok,
    mmFiber10Parent_0_ok,
    mmFiber10Parent_1_ok,
    mmFiber10Parent_2_ok,
    mmFiber10Parent_3_ok,
    mmFiber10Parent_4_ok,
    mmFiber10Parent_5_ok,
    mmFiber10Parent_6_ok,
    mmFiber10Parent_7_ok,
    mmFiber10Parent_8_ok,
    mmFiber10Parent_9_ok,
    mmFiber10Parent_10_ok,
    mmFiber10Parent_11_ok,
    mmFiber10Parent_12_ok,
    mmFiber10Parent_13_ok,
    mmFiber10Parent_14_ok,
    mmFiber10Parent_15_ok,
    mmFiber10Parent_16_ok,
    mmFiber10Parent_17_ok,
    mmFiber10Parent_18_ok,
    mmFiber10Parent_19_ok,
    mmFiber10Parent_20_ok,
    mmFiber10Parent_21_ok,
    mmFiber10Parent_22_ok,
    mmFiber10Parent_23_ok,
    mmFiber10Parent_24_ok,
    mmFiber10Parent_25_ok,
    mmFiber10Parent_26_ok,
    mmFiber10Parent_27_ok,
    mmFiber10Parent_28_ok,
    mmFiber10Parent_29_ok,
    mmFiber10Parent_30_ok,
    mmFiber10Parent_31_ok,
    mmFiber10Parent_32_ok,
    mmFiber10Parent_33_ok,
    mmFiber10Parent_34_ok,
    mmFiber10Parent_35_ok,
    mmFiber10Parent_36_ok,
    mmFiber10Parent_37_ok,
    mmFiber10Parent_38_ok,
    mmFiber10Parent_39_ok,
    mmFiber10Parent_40_ok,
    mmFiber10Parent_41_ok,
    mmFiber10Parent_42_ok,
    mmFiber10Parent_43_ok,
    mmFiber10Parent_44_ok,
    mmFiber10Parent_45_ok,
    mmFiber10Parent_46_ok,
    mmFiber10Parent_47_ok,
    mmFiber10Parent_48_ok,
    mmFiber10Parent_49_ok,
    mmFiber10Parent_50_ok,
    mmFiber10Parent_51_ok,
    mmFiber10Parent_52_ok,
    mmFiber10Parent_53_ok,
    mmFiber10Parent_54_ok,
    mmFiber10Parent_55_ok,
    mmFiber10Parent_56_ok,
    mmFiber10Parent_57_ok,
    mmFiber10Parent_58_ok,
    mmFiber10Parent_59_ok,
    mmFiber10Parent_60_ok,
    mmFiber10Parent_61_ok,
    mmFiber10Parent_62_ok,
    mmFiber10Parent_63_ok]

def mmFiber11Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.p]

def mmFiber11Expected : List Nat :=
  []

def mmFiber11Rows : List DirectChainParentRow :=
  []

def mmFiber11RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber11Rows i default

def mmFiber11SourcesCheck : Bool :=
  (mmFiber11Rows.map fun row => row.source) == mmFiber11Expected

theorem mmFiber11SourcesCheck_ok :
    mmFiber11SourcesCheck = true := by
  decide

def mmFiber11RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber11Key mmFiber11Expected (mmFiber11RowAt i)

def mmFiber11ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber11Rows mmMaxParentDepth (listGetD mmFiber11Expected i 0) == 0

def mmFiber11CertificateAudit : Bool :=
  mmFiber11SourcesCheck

theorem mmFiber11CertificateAudit_ok :
    mmFiber11CertificateAudit = true := by
  simp [mmFiber11CertificateAudit,
    mmFiber11SourcesCheck_ok]

def mmFiber12Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.r]

def mmFiber12Expected : List Nat :=
  []

def mmFiber12Rows : List DirectChainParentRow :=
  []

def mmFiber12RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber12Rows i default

def mmFiber12SourcesCheck : Bool :=
  (mmFiber12Rows.map fun row => row.source) == mmFiber12Expected

theorem mmFiber12SourcesCheck_ok :
    mmFiber12SourcesCheck = true := by
  decide

def mmFiber12RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber12Key mmFiber12Expected (mmFiber12RowAt i)

def mmFiber12ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber12Rows mmMaxParentDepth (listGetD mmFiber12Expected i 0) == 0

def mmFiber12CertificateAudit : Bool :=
  mmFiber12SourcesCheck

theorem mmFiber12CertificateAudit_ok :
    mmFiber12CertificateAudit = true := by
  simp [mmFiber12CertificateAudit,
    mmFiber12SourcesCheck_ok]

def mmFiber13Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.b]

def mmFiber13Expected : List Nat :=
  []

def mmFiber13Rows : List DirectChainParentRow :=
  []

def mmFiber13RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber13Rows i default

def mmFiber13SourcesCheck : Bool :=
  (mmFiber13Rows.map fun row => row.source) == mmFiber13Expected

theorem mmFiber13SourcesCheck_ok :
    mmFiber13SourcesCheck = true := by
  decide

def mmFiber13RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber13Key mmFiber13Expected (mmFiber13RowAt i)

def mmFiber13ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber13Rows mmMaxParentDepth (listGetD mmFiber13Expected i 0) == 0

def mmFiber13CertificateAudit : Bool :=
  mmFiber13SourcesCheck

theorem mmFiber13CertificateAudit_ok :
    mmFiber13CertificateAudit = true := by
  simp [mmFiber13CertificateAudit,
    mmFiber13SourcesCheck_ok]

def mmFiber14Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.p]

def mmFiber14Expected : List Nat :=
  []

def mmFiber14Rows : List DirectChainParentRow :=
  []

def mmFiber14RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber14Rows i default

def mmFiber14SourcesCheck : Bool :=
  (mmFiber14Rows.map fun row => row.source) == mmFiber14Expected

theorem mmFiber14SourcesCheck_ok :
    mmFiber14SourcesCheck = true := by
  decide

def mmFiber14RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber14Key mmFiber14Expected (mmFiber14RowAt i)

def mmFiber14ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber14Rows mmMaxParentDepth (listGetD mmFiber14Expected i 0) == 0

def mmFiber14CertificateAudit : Bool :=
  mmFiber14SourcesCheck

theorem mmFiber14CertificateAudit_ok :
    mmFiber14CertificateAudit = true := by
  simp [mmFiber14CertificateAudit,
    mmFiber14SourcesCheck_ok]

def mmFiber15Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.r]

def mmFiber15Expected : List Nat :=
  []

def mmFiber15Rows : List DirectChainParentRow :=
  []

def mmFiber15RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber15Rows i default

def mmFiber15SourcesCheck : Bool :=
  (mmFiber15Rows.map fun row => row.source) == mmFiber15Expected

theorem mmFiber15SourcesCheck_ok :
    mmFiber15SourcesCheck = true := by
  decide

def mmFiber15RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber15Key mmFiber15Expected (mmFiber15RowAt i)

def mmFiber15ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber15Rows mmMaxParentDepth (listGetD mmFiber15Expected i 0) == 0

def mmFiber15CertificateAudit : Bool :=
  mmFiber15SourcesCheck

theorem mmFiber15CertificateAudit_ok :
    mmFiber15CertificateAudit = true := by
  simp [mmFiber15CertificateAudit,
    mmFiber15SourcesCheck_ok]

def mmFiber16Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.b]

def mmFiber16Expected : List Nat :=
  [840, 841, 842, 843, 844, 845, 846, 847]

def mmFiber16Rows : List DirectChainParentRow :=
  [ directRow 840 840 168 20 168 20 default
  , directRow 841 840 168 21 168 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 842 840 168 22 168 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 843 841 168 23 168 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 844 840 169 28 168 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 845 841 169 29 168 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 846 842 169 30 168 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 847 843 169 31 168 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber16RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber16Rows i default

def mmFiber16SourcesCheck : Bool :=
  (mmFiber16Rows.map fun row => row.source) == mmFiber16Expected

theorem mmFiber16SourcesCheck_ok :
    mmFiber16SourcesCheck = true := by
  decide

def mmFiber16RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt i)

theorem mmFiber16Row_0_ok : mmFiber16RowCheck 0 = true := by decide
theorem mmFiber16Row_1_ok : mmFiber16RowCheck 1 = true := by decide
theorem mmFiber16Row_2_ok : mmFiber16RowCheck 2 = true := by decide
theorem mmFiber16Row_3_ok : mmFiber16RowCheck 3 = true := by decide
theorem mmFiber16Row_4_ok : mmFiber16RowCheck 4 = true := by decide
theorem mmFiber16Row_5_ok : mmFiber16RowCheck 5 = true := by decide
theorem mmFiber16Row_6_ok : mmFiber16RowCheck 6 = true := by decide
theorem mmFiber16Row_7_ok : mmFiber16RowCheck 7 = true := by decide

def mmFiber16ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber16Rows mmMaxParentDepth (listGetD mmFiber16Expected i 0) == 840

theorem mmFiber16Parent_0_ok : mmFiber16ParentCheck 0 = true := by decide
theorem mmFiber16Parent_1_ok : mmFiber16ParentCheck 1 = true := by decide
theorem mmFiber16Parent_2_ok : mmFiber16ParentCheck 2 = true := by decide
theorem mmFiber16Parent_3_ok : mmFiber16ParentCheck 3 = true := by decide
theorem mmFiber16Parent_4_ok : mmFiber16ParentCheck 4 = true := by decide
theorem mmFiber16Parent_5_ok : mmFiber16ParentCheck 5 = true := by decide
theorem mmFiber16Parent_6_ok : mmFiber16ParentCheck 6 = true := by decide
theorem mmFiber16Parent_7_ok : mmFiber16ParentCheck 7 = true := by decide

def mmFiber16CertificateAudit : Bool :=
  mmFiber16SourcesCheck &&
    mmFiber16RowCheck 0 &&
    mmFiber16RowCheck 1 &&
    mmFiber16RowCheck 2 &&
    mmFiber16RowCheck 3 &&
    mmFiber16RowCheck 4 &&
    mmFiber16RowCheck 5 &&
    mmFiber16RowCheck 6 &&
    mmFiber16RowCheck 7 &&
    mmFiber16ParentCheck 0 &&
    mmFiber16ParentCheck 1 &&
    mmFiber16ParentCheck 2 &&
    mmFiber16ParentCheck 3 &&
    mmFiber16ParentCheck 4 &&
    mmFiber16ParentCheck 5 &&
    mmFiber16ParentCheck 6 &&
    mmFiber16ParentCheck 7

theorem mmFiber16CertificateAudit_ok :
    mmFiber16CertificateAudit = true := by
  simp [mmFiber16CertificateAudit,
    mmFiber16SourcesCheck_ok,
    mmFiber16Row_0_ok,
    mmFiber16Row_1_ok,
    mmFiber16Row_2_ok,
    mmFiber16Row_3_ok,
    mmFiber16Row_4_ok,
    mmFiber16Row_5_ok,
    mmFiber16Row_6_ok,
    mmFiber16Row_7_ok,
    mmFiber16Parent_0_ok,
    mmFiber16Parent_1_ok,
    mmFiber16Parent_2_ok,
    mmFiber16Parent_3_ok,
    mmFiber16Parent_4_ok,
    mmFiber16Parent_5_ok,
    mmFiber16Parent_6_ok,
    mmFiber16Parent_7_ok]

def mmFiber17Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.p]

def mmFiber17Expected : List Nat :=
  [520, 521, 522, 523, 524, 525, 526, 527]

def mmFiber17Rows : List DirectChainParentRow :=
  [ directRow 520 520 106 52 106 52 default
  , directRow 521 520 106 53 106 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 522 521 106 54 106 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 523 520 106 55 106 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 524 520 107 60 106 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 525 521 107 61 106 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 526 522 107 62 106 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 527 523 107 63 106 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber17RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber17Rows i default

def mmFiber17SourcesCheck : Bool :=
  (mmFiber17Rows.map fun row => row.source) == mmFiber17Expected

theorem mmFiber17SourcesCheck_ok :
    mmFiber17SourcesCheck = true := by
  decide

def mmFiber17RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt i)

theorem mmFiber17Row_0_ok : mmFiber17RowCheck 0 = true := by decide
theorem mmFiber17Row_1_ok : mmFiber17RowCheck 1 = true := by decide
theorem mmFiber17Row_2_ok : mmFiber17RowCheck 2 = true := by decide
theorem mmFiber17Row_3_ok : mmFiber17RowCheck 3 = true := by decide
theorem mmFiber17Row_4_ok : mmFiber17RowCheck 4 = true := by decide
theorem mmFiber17Row_5_ok : mmFiber17RowCheck 5 = true := by decide
theorem mmFiber17Row_6_ok : mmFiber17RowCheck 6 = true := by decide
theorem mmFiber17Row_7_ok : mmFiber17RowCheck 7 = true := by decide

def mmFiber17ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber17Rows mmMaxParentDepth (listGetD mmFiber17Expected i 0) == 520

theorem mmFiber17Parent_0_ok : mmFiber17ParentCheck 0 = true := by decide
theorem mmFiber17Parent_1_ok : mmFiber17ParentCheck 1 = true := by decide
theorem mmFiber17Parent_2_ok : mmFiber17ParentCheck 2 = true := by decide
theorem mmFiber17Parent_3_ok : mmFiber17ParentCheck 3 = true := by decide
theorem mmFiber17Parent_4_ok : mmFiber17ParentCheck 4 = true := by decide
theorem mmFiber17Parent_5_ok : mmFiber17ParentCheck 5 = true := by decide
theorem mmFiber17Parent_6_ok : mmFiber17ParentCheck 6 = true := by decide
theorem mmFiber17Parent_7_ok : mmFiber17ParentCheck 7 = true := by decide

def mmFiber17CertificateAudit : Bool :=
  mmFiber17SourcesCheck &&
    mmFiber17RowCheck 0 &&
    mmFiber17RowCheck 1 &&
    mmFiber17RowCheck 2 &&
    mmFiber17RowCheck 3 &&
    mmFiber17RowCheck 4 &&
    mmFiber17RowCheck 5 &&
    mmFiber17RowCheck 6 &&
    mmFiber17RowCheck 7 &&
    mmFiber17ParentCheck 0 &&
    mmFiber17ParentCheck 1 &&
    mmFiber17ParentCheck 2 &&
    mmFiber17ParentCheck 3 &&
    mmFiber17ParentCheck 4 &&
    mmFiber17ParentCheck 5 &&
    mmFiber17ParentCheck 6 &&
    mmFiber17ParentCheck 7

theorem mmFiber17CertificateAudit_ok :
    mmFiber17CertificateAudit = true := by
  simp [mmFiber17CertificateAudit,
    mmFiber17SourcesCheck_ok,
    mmFiber17Row_0_ok,
    mmFiber17Row_1_ok,
    mmFiber17Row_2_ok,
    mmFiber17Row_3_ok,
    mmFiber17Row_4_ok,
    mmFiber17Row_5_ok,
    mmFiber17Row_6_ok,
    mmFiber17Row_7_ok,
    mmFiber17Parent_0_ok,
    mmFiber17Parent_1_ok,
    mmFiber17Parent_2_ok,
    mmFiber17Parent_3_ok,
    mmFiber17Parent_4_ok,
    mmFiber17Parent_5_ok,
    mmFiber17Parent_6_ok,
    mmFiber17Parent_7_ok]

def mmFiber18Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.r]

def mmFiber18Expected : List Nat :=
  [880, 881, 882, 883, 884, 885, 886, 887]

def mmFiber18Rows : List DirectChainParentRow :=
  [ directRow 880 880 176 20 176 20 default
  , directRow 881 880 176 21 176 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 882 880 176 22 176 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 883 881 176 23 176 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 884 880 177 28 176 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 885 881 177 29 176 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 886 882 177 30 176 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 887 883 177 31 176 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber18RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber18Rows i default

def mmFiber18SourcesCheck : Bool :=
  (mmFiber18Rows.map fun row => row.source) == mmFiber18Expected

theorem mmFiber18SourcesCheck_ok :
    mmFiber18SourcesCheck = true := by
  decide

def mmFiber18RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt i)

theorem mmFiber18Row_0_ok : mmFiber18RowCheck 0 = true := by decide
theorem mmFiber18Row_1_ok : mmFiber18RowCheck 1 = true := by decide
theorem mmFiber18Row_2_ok : mmFiber18RowCheck 2 = true := by decide
theorem mmFiber18Row_3_ok : mmFiber18RowCheck 3 = true := by decide
theorem mmFiber18Row_4_ok : mmFiber18RowCheck 4 = true := by decide
theorem mmFiber18Row_5_ok : mmFiber18RowCheck 5 = true := by decide
theorem mmFiber18Row_6_ok : mmFiber18RowCheck 6 = true := by decide
theorem mmFiber18Row_7_ok : mmFiber18RowCheck 7 = true := by decide

def mmFiber18ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber18Rows mmMaxParentDepth (listGetD mmFiber18Expected i 0) == 880

theorem mmFiber18Parent_0_ok : mmFiber18ParentCheck 0 = true := by decide
theorem mmFiber18Parent_1_ok : mmFiber18ParentCheck 1 = true := by decide
theorem mmFiber18Parent_2_ok : mmFiber18ParentCheck 2 = true := by decide
theorem mmFiber18Parent_3_ok : mmFiber18ParentCheck 3 = true := by decide
theorem mmFiber18Parent_4_ok : mmFiber18ParentCheck 4 = true := by decide
theorem mmFiber18Parent_5_ok : mmFiber18ParentCheck 5 = true := by decide
theorem mmFiber18Parent_6_ok : mmFiber18ParentCheck 6 = true := by decide
theorem mmFiber18Parent_7_ok : mmFiber18ParentCheck 7 = true := by decide

def mmFiber18CertificateAudit : Bool :=
  mmFiber18SourcesCheck &&
    mmFiber18RowCheck 0 &&
    mmFiber18RowCheck 1 &&
    mmFiber18RowCheck 2 &&
    mmFiber18RowCheck 3 &&
    mmFiber18RowCheck 4 &&
    mmFiber18RowCheck 5 &&
    mmFiber18RowCheck 6 &&
    mmFiber18RowCheck 7 &&
    mmFiber18ParentCheck 0 &&
    mmFiber18ParentCheck 1 &&
    mmFiber18ParentCheck 2 &&
    mmFiber18ParentCheck 3 &&
    mmFiber18ParentCheck 4 &&
    mmFiber18ParentCheck 5 &&
    mmFiber18ParentCheck 6 &&
    mmFiber18ParentCheck 7

theorem mmFiber18CertificateAudit_ok :
    mmFiber18CertificateAudit = true := by
  simp [mmFiber18CertificateAudit,
    mmFiber18SourcesCheck_ok,
    mmFiber18Row_0_ok,
    mmFiber18Row_1_ok,
    mmFiber18Row_2_ok,
    mmFiber18Row_3_ok,
    mmFiber18Row_4_ok,
    mmFiber18Row_5_ok,
    mmFiber18Row_6_ok,
    mmFiber18Row_7_ok,
    mmFiber18Parent_0_ok,
    mmFiber18Parent_1_ok,
    mmFiber18Parent_2_ok,
    mmFiber18Parent_3_ok,
    mmFiber18Parent_4_ok,
    mmFiber18Parent_5_ok,
    mmFiber18Parent_6_ok,
    mmFiber18Parent_7_ok]

def mmFiber19Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.b]

def mmFiber19Expected : List Nat :=
  []

def mmFiber19Rows : List DirectChainParentRow :=
  []

def mmFiber19RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber19Rows i default

def mmFiber19SourcesCheck : Bool :=
  (mmFiber19Rows.map fun row => row.source) == mmFiber19Expected

theorem mmFiber19SourcesCheck_ok :
    mmFiber19SourcesCheck = true := by
  decide

def mmFiber19RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber19Key mmFiber19Expected (mmFiber19RowAt i)

def mmFiber19ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber19Rows mmMaxParentDepth (listGetD mmFiber19Expected i 0) == 0

def mmFiber19CertificateAudit : Bool :=
  mmFiber19SourcesCheck

theorem mmFiber19CertificateAudit_ok :
    mmFiber19CertificateAudit = true := by
  simp [mmFiber19CertificateAudit,
    mmFiber19SourcesCheck_ok]

def mmFiber20Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.p]

def mmFiber20Expected : List Nat :=
  [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]

def mmFiber20Rows : List DirectChainParentRow :=
  [ directRow 80 80 16 80 16 80 default
  , directRow 81 80 16 81 16 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 82 80 16 82 16 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 83 81 16 83 16 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 84 82 16 100 16 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 85 87 16 101 16 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 86 81 16 102 16 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 87 80 16 103 16 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 88 80 17 88 16 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 89 81 17 89 16 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 90 82 17 90 16 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 91 83 17 91 16 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 92 84 17 108 16 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 93 85 17 109 16 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 94 86 17 110 16 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 95 87 17 111 16 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 96 80 18 16 16 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 97 81 18 17 16 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 98 82 18 18 16 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 99 83 18 19 16 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 100 96 18 32 18 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 101 97 18 33 18 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 102 86 18 34 16 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 103 87 18 35 16 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 104 88 19 24 17 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 105 89 19 25 17 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 106 90 19 26 17 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 107 91 19 27 17 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 108 104 19 40 19 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 109 105 19 41 19 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 110 94 19 42 17 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 111 95 19 43 17 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 160 80 32 148 16 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 161 81 32 149 16 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 162 82 32 150 16 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 163 160 32 151 32 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 164 160 32 164 32 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 165 161 32 165 32 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 166 86 32 166 16 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 167 87 32 167 16 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 168 88 33 156 17 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 169 89 33 157 17 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 170 90 33 158 17 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 171 168 33 159 33 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 172 168 33 172 33 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 173 169 33 173 33 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 174 94 33 174 17 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 175 95 33 175 17 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 176 96 34 0 18 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 177 97 34 1 18 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 178 98 34 2 18 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 179 99 34 3 18 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 180 168 34 48 33 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 181 169 34 49 33 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 182 102 34 50 18 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 183 103 34 51 18 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 184 167 35 8 32 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 185 166 35 9 32 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 186 164 35 10 32 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 187 165 35 11 32 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 188 160 35 56 32 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 189 161 35 57 32 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 190 162 35 58 32 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 191 163 35 59 32 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def mmFiber20RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber20Rows i default

def mmFiber20SourcesCheck : Bool :=
  (mmFiber20Rows.map fun row => row.source) == mmFiber20Expected

theorem mmFiber20SourcesCheck_ok :
    mmFiber20SourcesCheck = true := by
  decide

def mmFiber20RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt i)

theorem mmFiber20Row_0_ok : mmFiber20RowCheck 0 = true := by decide
theorem mmFiber20Row_1_ok : mmFiber20RowCheck 1 = true := by decide
theorem mmFiber20Row_2_ok : mmFiber20RowCheck 2 = true := by decide
theorem mmFiber20Row_3_ok : mmFiber20RowCheck 3 = true := by decide
theorem mmFiber20Row_4_ok : mmFiber20RowCheck 4 = true := by decide
theorem mmFiber20Row_5_ok : mmFiber20RowCheck 5 = true := by decide
theorem mmFiber20Row_6_ok : mmFiber20RowCheck 6 = true := by decide
theorem mmFiber20Row_7_ok : mmFiber20RowCheck 7 = true := by decide
theorem mmFiber20Row_8_ok : mmFiber20RowCheck 8 = true := by decide
theorem mmFiber20Row_9_ok : mmFiber20RowCheck 9 = true := by decide
theorem mmFiber20Row_10_ok : mmFiber20RowCheck 10 = true := by decide
theorem mmFiber20Row_11_ok : mmFiber20RowCheck 11 = true := by decide
theorem mmFiber20Row_12_ok : mmFiber20RowCheck 12 = true := by decide
theorem mmFiber20Row_13_ok : mmFiber20RowCheck 13 = true := by decide
theorem mmFiber20Row_14_ok : mmFiber20RowCheck 14 = true := by decide
theorem mmFiber20Row_15_ok : mmFiber20RowCheck 15 = true := by decide
theorem mmFiber20Row_16_ok : mmFiber20RowCheck 16 = true := by decide
theorem mmFiber20Row_17_ok : mmFiber20RowCheck 17 = true := by decide
theorem mmFiber20Row_18_ok : mmFiber20RowCheck 18 = true := by decide
theorem mmFiber20Row_19_ok : mmFiber20RowCheck 19 = true := by decide
theorem mmFiber20Row_20_ok : mmFiber20RowCheck 20 = true := by decide
theorem mmFiber20Row_21_ok : mmFiber20RowCheck 21 = true := by decide
theorem mmFiber20Row_22_ok : mmFiber20RowCheck 22 = true := by decide
theorem mmFiber20Row_23_ok : mmFiber20RowCheck 23 = true := by decide
theorem mmFiber20Row_24_ok : mmFiber20RowCheck 24 = true := by decide
theorem mmFiber20Row_25_ok : mmFiber20RowCheck 25 = true := by decide
theorem mmFiber20Row_26_ok : mmFiber20RowCheck 26 = true := by decide
theorem mmFiber20Row_27_ok : mmFiber20RowCheck 27 = true := by decide
theorem mmFiber20Row_28_ok : mmFiber20RowCheck 28 = true := by decide
theorem mmFiber20Row_29_ok : mmFiber20RowCheck 29 = true := by decide
theorem mmFiber20Row_30_ok : mmFiber20RowCheck 30 = true := by decide
theorem mmFiber20Row_31_ok : mmFiber20RowCheck 31 = true := by decide
theorem mmFiber20Row_32_ok : mmFiber20RowCheck 32 = true := by decide
theorem mmFiber20Row_33_ok : mmFiber20RowCheck 33 = true := by decide
theorem mmFiber20Row_34_ok : mmFiber20RowCheck 34 = true := by decide
theorem mmFiber20Row_35_ok : mmFiber20RowCheck 35 = true := by decide
theorem mmFiber20Row_36_ok : mmFiber20RowCheck 36 = true := by decide
theorem mmFiber20Row_37_ok : mmFiber20RowCheck 37 = true := by decide
theorem mmFiber20Row_38_ok : mmFiber20RowCheck 38 = true := by decide
theorem mmFiber20Row_39_ok : mmFiber20RowCheck 39 = true := by decide
theorem mmFiber20Row_40_ok : mmFiber20RowCheck 40 = true := by decide
theorem mmFiber20Row_41_ok : mmFiber20RowCheck 41 = true := by decide
theorem mmFiber20Row_42_ok : mmFiber20RowCheck 42 = true := by decide
theorem mmFiber20Row_43_ok : mmFiber20RowCheck 43 = true := by decide
theorem mmFiber20Row_44_ok : mmFiber20RowCheck 44 = true := by decide
theorem mmFiber20Row_45_ok : mmFiber20RowCheck 45 = true := by decide
theorem mmFiber20Row_46_ok : mmFiber20RowCheck 46 = true := by decide
theorem mmFiber20Row_47_ok : mmFiber20RowCheck 47 = true := by decide
theorem mmFiber20Row_48_ok : mmFiber20RowCheck 48 = true := by decide
theorem mmFiber20Row_49_ok : mmFiber20RowCheck 49 = true := by decide
theorem mmFiber20Row_50_ok : mmFiber20RowCheck 50 = true := by decide
theorem mmFiber20Row_51_ok : mmFiber20RowCheck 51 = true := by decide
theorem mmFiber20Row_52_ok : mmFiber20RowCheck 52 = true := by decide
theorem mmFiber20Row_53_ok : mmFiber20RowCheck 53 = true := by decide
theorem mmFiber20Row_54_ok : mmFiber20RowCheck 54 = true := by decide
theorem mmFiber20Row_55_ok : mmFiber20RowCheck 55 = true := by decide
theorem mmFiber20Row_56_ok : mmFiber20RowCheck 56 = true := by decide
theorem mmFiber20Row_57_ok : mmFiber20RowCheck 57 = true := by decide
theorem mmFiber20Row_58_ok : mmFiber20RowCheck 58 = true := by decide
theorem mmFiber20Row_59_ok : mmFiber20RowCheck 59 = true := by decide
theorem mmFiber20Row_60_ok : mmFiber20RowCheck 60 = true := by decide
theorem mmFiber20Row_61_ok : mmFiber20RowCheck 61 = true := by decide
theorem mmFiber20Row_62_ok : mmFiber20RowCheck 62 = true := by decide
theorem mmFiber20Row_63_ok : mmFiber20RowCheck 63 = true := by decide

def mmFiber20ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber20Rows mmMaxParentDepth (listGetD mmFiber20Expected i 0) == 80

theorem mmFiber20Parent_0_ok : mmFiber20ParentCheck 0 = true := by decide
theorem mmFiber20Parent_1_ok : mmFiber20ParentCheck 1 = true := by decide
theorem mmFiber20Parent_2_ok : mmFiber20ParentCheck 2 = true := by decide
theorem mmFiber20Parent_3_ok : mmFiber20ParentCheck 3 = true := by decide
theorem mmFiber20Parent_4_ok : mmFiber20ParentCheck 4 = true := by decide
theorem mmFiber20Parent_5_ok : mmFiber20ParentCheck 5 = true := by decide
theorem mmFiber20Parent_6_ok : mmFiber20ParentCheck 6 = true := by decide
theorem mmFiber20Parent_7_ok : mmFiber20ParentCheck 7 = true := by decide
theorem mmFiber20Parent_8_ok : mmFiber20ParentCheck 8 = true := by decide
theorem mmFiber20Parent_9_ok : mmFiber20ParentCheck 9 = true := by decide
theorem mmFiber20Parent_10_ok : mmFiber20ParentCheck 10 = true := by decide
theorem mmFiber20Parent_11_ok : mmFiber20ParentCheck 11 = true := by decide
theorem mmFiber20Parent_12_ok : mmFiber20ParentCheck 12 = true := by decide
theorem mmFiber20Parent_13_ok : mmFiber20ParentCheck 13 = true := by decide
theorem mmFiber20Parent_14_ok : mmFiber20ParentCheck 14 = true := by decide
theorem mmFiber20Parent_15_ok : mmFiber20ParentCheck 15 = true := by decide
theorem mmFiber20Parent_16_ok : mmFiber20ParentCheck 16 = true := by decide
theorem mmFiber20Parent_17_ok : mmFiber20ParentCheck 17 = true := by decide
theorem mmFiber20Parent_18_ok : mmFiber20ParentCheck 18 = true := by decide
theorem mmFiber20Parent_19_ok : mmFiber20ParentCheck 19 = true := by decide
theorem mmFiber20Parent_20_ok : mmFiber20ParentCheck 20 = true := by decide
theorem mmFiber20Parent_21_ok : mmFiber20ParentCheck 21 = true := by decide
theorem mmFiber20Parent_22_ok : mmFiber20ParentCheck 22 = true := by decide
theorem mmFiber20Parent_23_ok : mmFiber20ParentCheck 23 = true := by decide
theorem mmFiber20Parent_24_ok : mmFiber20ParentCheck 24 = true := by decide
theorem mmFiber20Parent_25_ok : mmFiber20ParentCheck 25 = true := by decide
theorem mmFiber20Parent_26_ok : mmFiber20ParentCheck 26 = true := by decide
theorem mmFiber20Parent_27_ok : mmFiber20ParentCheck 27 = true := by decide
theorem mmFiber20Parent_28_ok : mmFiber20ParentCheck 28 = true := by decide
theorem mmFiber20Parent_29_ok : mmFiber20ParentCheck 29 = true := by decide
theorem mmFiber20Parent_30_ok : mmFiber20ParentCheck 30 = true := by decide
theorem mmFiber20Parent_31_ok : mmFiber20ParentCheck 31 = true := by decide
theorem mmFiber20Parent_32_ok : mmFiber20ParentCheck 32 = true := by decide
theorem mmFiber20Parent_33_ok : mmFiber20ParentCheck 33 = true := by decide
theorem mmFiber20Parent_34_ok : mmFiber20ParentCheck 34 = true := by decide
theorem mmFiber20Parent_35_ok : mmFiber20ParentCheck 35 = true := by decide
theorem mmFiber20Parent_36_ok : mmFiber20ParentCheck 36 = true := by decide
theorem mmFiber20Parent_37_ok : mmFiber20ParentCheck 37 = true := by decide
theorem mmFiber20Parent_38_ok : mmFiber20ParentCheck 38 = true := by decide
theorem mmFiber20Parent_39_ok : mmFiber20ParentCheck 39 = true := by decide
theorem mmFiber20Parent_40_ok : mmFiber20ParentCheck 40 = true := by decide
theorem mmFiber20Parent_41_ok : mmFiber20ParentCheck 41 = true := by decide
theorem mmFiber20Parent_42_ok : mmFiber20ParentCheck 42 = true := by decide
theorem mmFiber20Parent_43_ok : mmFiber20ParentCheck 43 = true := by decide
theorem mmFiber20Parent_44_ok : mmFiber20ParentCheck 44 = true := by decide
theorem mmFiber20Parent_45_ok : mmFiber20ParentCheck 45 = true := by decide
theorem mmFiber20Parent_46_ok : mmFiber20ParentCheck 46 = true := by decide
theorem mmFiber20Parent_47_ok : mmFiber20ParentCheck 47 = true := by decide
theorem mmFiber20Parent_48_ok : mmFiber20ParentCheck 48 = true := by decide
theorem mmFiber20Parent_49_ok : mmFiber20ParentCheck 49 = true := by decide
theorem mmFiber20Parent_50_ok : mmFiber20ParentCheck 50 = true := by decide
theorem mmFiber20Parent_51_ok : mmFiber20ParentCheck 51 = true := by decide
theorem mmFiber20Parent_52_ok : mmFiber20ParentCheck 52 = true := by decide
theorem mmFiber20Parent_53_ok : mmFiber20ParentCheck 53 = true := by decide
theorem mmFiber20Parent_54_ok : mmFiber20ParentCheck 54 = true := by decide
theorem mmFiber20Parent_55_ok : mmFiber20ParentCheck 55 = true := by decide
theorem mmFiber20Parent_56_ok : mmFiber20ParentCheck 56 = true := by decide
theorem mmFiber20Parent_57_ok : mmFiber20ParentCheck 57 = true := by decide
theorem mmFiber20Parent_58_ok : mmFiber20ParentCheck 58 = true := by decide
theorem mmFiber20Parent_59_ok : mmFiber20ParentCheck 59 = true := by decide
theorem mmFiber20Parent_60_ok : mmFiber20ParentCheck 60 = true := by decide
theorem mmFiber20Parent_61_ok : mmFiber20ParentCheck 61 = true := by decide
theorem mmFiber20Parent_62_ok : mmFiber20ParentCheck 62 = true := by decide
theorem mmFiber20Parent_63_ok : mmFiber20ParentCheck 63 = true := by decide

def mmFiber20CertificateAudit : Bool :=
  mmFiber20SourcesCheck &&
    mmFiber20RowCheck 0 &&
    mmFiber20RowCheck 1 &&
    mmFiber20RowCheck 2 &&
    mmFiber20RowCheck 3 &&
    mmFiber20RowCheck 4 &&
    mmFiber20RowCheck 5 &&
    mmFiber20RowCheck 6 &&
    mmFiber20RowCheck 7 &&
    mmFiber20RowCheck 8 &&
    mmFiber20RowCheck 9 &&
    mmFiber20RowCheck 10 &&
    mmFiber20RowCheck 11 &&
    mmFiber20RowCheck 12 &&
    mmFiber20RowCheck 13 &&
    mmFiber20RowCheck 14 &&
    mmFiber20RowCheck 15 &&
    mmFiber20RowCheck 16 &&
    mmFiber20RowCheck 17 &&
    mmFiber20RowCheck 18 &&
    mmFiber20RowCheck 19 &&
    mmFiber20RowCheck 20 &&
    mmFiber20RowCheck 21 &&
    mmFiber20RowCheck 22 &&
    mmFiber20RowCheck 23 &&
    mmFiber20RowCheck 24 &&
    mmFiber20RowCheck 25 &&
    mmFiber20RowCheck 26 &&
    mmFiber20RowCheck 27 &&
    mmFiber20RowCheck 28 &&
    mmFiber20RowCheck 29 &&
    mmFiber20RowCheck 30 &&
    mmFiber20RowCheck 31 &&
    mmFiber20RowCheck 32 &&
    mmFiber20RowCheck 33 &&
    mmFiber20RowCheck 34 &&
    mmFiber20RowCheck 35 &&
    mmFiber20RowCheck 36 &&
    mmFiber20RowCheck 37 &&
    mmFiber20RowCheck 38 &&
    mmFiber20RowCheck 39 &&
    mmFiber20RowCheck 40 &&
    mmFiber20RowCheck 41 &&
    mmFiber20RowCheck 42 &&
    mmFiber20RowCheck 43 &&
    mmFiber20RowCheck 44 &&
    mmFiber20RowCheck 45 &&
    mmFiber20RowCheck 46 &&
    mmFiber20RowCheck 47 &&
    mmFiber20RowCheck 48 &&
    mmFiber20RowCheck 49 &&
    mmFiber20RowCheck 50 &&
    mmFiber20RowCheck 51 &&
    mmFiber20RowCheck 52 &&
    mmFiber20RowCheck 53 &&
    mmFiber20RowCheck 54 &&
    mmFiber20RowCheck 55 &&
    mmFiber20RowCheck 56 &&
    mmFiber20RowCheck 57 &&
    mmFiber20RowCheck 58 &&
    mmFiber20RowCheck 59 &&
    mmFiber20RowCheck 60 &&
    mmFiber20RowCheck 61 &&
    mmFiber20RowCheck 62 &&
    mmFiber20RowCheck 63 &&
    mmFiber20ParentCheck 0 &&
    mmFiber20ParentCheck 1 &&
    mmFiber20ParentCheck 2 &&
    mmFiber20ParentCheck 3 &&
    mmFiber20ParentCheck 4 &&
    mmFiber20ParentCheck 5 &&
    mmFiber20ParentCheck 6 &&
    mmFiber20ParentCheck 7 &&
    mmFiber20ParentCheck 8 &&
    mmFiber20ParentCheck 9 &&
    mmFiber20ParentCheck 10 &&
    mmFiber20ParentCheck 11 &&
    mmFiber20ParentCheck 12 &&
    mmFiber20ParentCheck 13 &&
    mmFiber20ParentCheck 14 &&
    mmFiber20ParentCheck 15 &&
    mmFiber20ParentCheck 16 &&
    mmFiber20ParentCheck 17 &&
    mmFiber20ParentCheck 18 &&
    mmFiber20ParentCheck 19 &&
    mmFiber20ParentCheck 20 &&
    mmFiber20ParentCheck 21 &&
    mmFiber20ParentCheck 22 &&
    mmFiber20ParentCheck 23 &&
    mmFiber20ParentCheck 24 &&
    mmFiber20ParentCheck 25 &&
    mmFiber20ParentCheck 26 &&
    mmFiber20ParentCheck 27 &&
    mmFiber20ParentCheck 28 &&
    mmFiber20ParentCheck 29 &&
    mmFiber20ParentCheck 30 &&
    mmFiber20ParentCheck 31 &&
    mmFiber20ParentCheck 32 &&
    mmFiber20ParentCheck 33 &&
    mmFiber20ParentCheck 34 &&
    mmFiber20ParentCheck 35 &&
    mmFiber20ParentCheck 36 &&
    mmFiber20ParentCheck 37 &&
    mmFiber20ParentCheck 38 &&
    mmFiber20ParentCheck 39 &&
    mmFiber20ParentCheck 40 &&
    mmFiber20ParentCheck 41 &&
    mmFiber20ParentCheck 42 &&
    mmFiber20ParentCheck 43 &&
    mmFiber20ParentCheck 44 &&
    mmFiber20ParentCheck 45 &&
    mmFiber20ParentCheck 46 &&
    mmFiber20ParentCheck 47 &&
    mmFiber20ParentCheck 48 &&
    mmFiber20ParentCheck 49 &&
    mmFiber20ParentCheck 50 &&
    mmFiber20ParentCheck 51 &&
    mmFiber20ParentCheck 52 &&
    mmFiber20ParentCheck 53 &&
    mmFiber20ParentCheck 54 &&
    mmFiber20ParentCheck 55 &&
    mmFiber20ParentCheck 56 &&
    mmFiber20ParentCheck 57 &&
    mmFiber20ParentCheck 58 &&
    mmFiber20ParentCheck 59 &&
    mmFiber20ParentCheck 60 &&
    mmFiber20ParentCheck 61 &&
    mmFiber20ParentCheck 62 &&
    mmFiber20ParentCheck 63

theorem mmFiber20CertificateAudit_ok :
    mmFiber20CertificateAudit = true := by
  simp [mmFiber20CertificateAudit,
    mmFiber20SourcesCheck_ok,
    mmFiber20Row_0_ok,
    mmFiber20Row_1_ok,
    mmFiber20Row_2_ok,
    mmFiber20Row_3_ok,
    mmFiber20Row_4_ok,
    mmFiber20Row_5_ok,
    mmFiber20Row_6_ok,
    mmFiber20Row_7_ok,
    mmFiber20Row_8_ok,
    mmFiber20Row_9_ok,
    mmFiber20Row_10_ok,
    mmFiber20Row_11_ok,
    mmFiber20Row_12_ok,
    mmFiber20Row_13_ok,
    mmFiber20Row_14_ok,
    mmFiber20Row_15_ok,
    mmFiber20Row_16_ok,
    mmFiber20Row_17_ok,
    mmFiber20Row_18_ok,
    mmFiber20Row_19_ok,
    mmFiber20Row_20_ok,
    mmFiber20Row_21_ok,
    mmFiber20Row_22_ok,
    mmFiber20Row_23_ok,
    mmFiber20Row_24_ok,
    mmFiber20Row_25_ok,
    mmFiber20Row_26_ok,
    mmFiber20Row_27_ok,
    mmFiber20Row_28_ok,
    mmFiber20Row_29_ok,
    mmFiber20Row_30_ok,
    mmFiber20Row_31_ok,
    mmFiber20Row_32_ok,
    mmFiber20Row_33_ok,
    mmFiber20Row_34_ok,
    mmFiber20Row_35_ok,
    mmFiber20Row_36_ok,
    mmFiber20Row_37_ok,
    mmFiber20Row_38_ok,
    mmFiber20Row_39_ok,
    mmFiber20Row_40_ok,
    mmFiber20Row_41_ok,
    mmFiber20Row_42_ok,
    mmFiber20Row_43_ok,
    mmFiber20Row_44_ok,
    mmFiber20Row_45_ok,
    mmFiber20Row_46_ok,
    mmFiber20Row_47_ok,
    mmFiber20Row_48_ok,
    mmFiber20Row_49_ok,
    mmFiber20Row_50_ok,
    mmFiber20Row_51_ok,
    mmFiber20Row_52_ok,
    mmFiber20Row_53_ok,
    mmFiber20Row_54_ok,
    mmFiber20Row_55_ok,
    mmFiber20Row_56_ok,
    mmFiber20Row_57_ok,
    mmFiber20Row_58_ok,
    mmFiber20Row_59_ok,
    mmFiber20Row_60_ok,
    mmFiber20Row_61_ok,
    mmFiber20Row_62_ok,
    mmFiber20Row_63_ok,
    mmFiber20Parent_0_ok,
    mmFiber20Parent_1_ok,
    mmFiber20Parent_2_ok,
    mmFiber20Parent_3_ok,
    mmFiber20Parent_4_ok,
    mmFiber20Parent_5_ok,
    mmFiber20Parent_6_ok,
    mmFiber20Parent_7_ok,
    mmFiber20Parent_8_ok,
    mmFiber20Parent_9_ok,
    mmFiber20Parent_10_ok,
    mmFiber20Parent_11_ok,
    mmFiber20Parent_12_ok,
    mmFiber20Parent_13_ok,
    mmFiber20Parent_14_ok,
    mmFiber20Parent_15_ok,
    mmFiber20Parent_16_ok,
    mmFiber20Parent_17_ok,
    mmFiber20Parent_18_ok,
    mmFiber20Parent_19_ok,
    mmFiber20Parent_20_ok,
    mmFiber20Parent_21_ok,
    mmFiber20Parent_22_ok,
    mmFiber20Parent_23_ok,
    mmFiber20Parent_24_ok,
    mmFiber20Parent_25_ok,
    mmFiber20Parent_26_ok,
    mmFiber20Parent_27_ok,
    mmFiber20Parent_28_ok,
    mmFiber20Parent_29_ok,
    mmFiber20Parent_30_ok,
    mmFiber20Parent_31_ok,
    mmFiber20Parent_32_ok,
    mmFiber20Parent_33_ok,
    mmFiber20Parent_34_ok,
    mmFiber20Parent_35_ok,
    mmFiber20Parent_36_ok,
    mmFiber20Parent_37_ok,
    mmFiber20Parent_38_ok,
    mmFiber20Parent_39_ok,
    mmFiber20Parent_40_ok,
    mmFiber20Parent_41_ok,
    mmFiber20Parent_42_ok,
    mmFiber20Parent_43_ok,
    mmFiber20Parent_44_ok,
    mmFiber20Parent_45_ok,
    mmFiber20Parent_46_ok,
    mmFiber20Parent_47_ok,
    mmFiber20Parent_48_ok,
    mmFiber20Parent_49_ok,
    mmFiber20Parent_50_ok,
    mmFiber20Parent_51_ok,
    mmFiber20Parent_52_ok,
    mmFiber20Parent_53_ok,
    mmFiber20Parent_54_ok,
    mmFiber20Parent_55_ok,
    mmFiber20Parent_56_ok,
    mmFiber20Parent_57_ok,
    mmFiber20Parent_58_ok,
    mmFiber20Parent_59_ok,
    mmFiber20Parent_60_ok,
    mmFiber20Parent_61_ok,
    mmFiber20Parent_62_ok,
    mmFiber20Parent_63_ok]

def mmFiber21Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.r]

def mmFiber21Expected : List Nat :=
  []

def mmFiber21Rows : List DirectChainParentRow :=
  []

def mmFiber21RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber21Rows i default

def mmFiber21SourcesCheck : Bool :=
  (mmFiber21Rows.map fun row => row.source) == mmFiber21Expected

theorem mmFiber21SourcesCheck_ok :
    mmFiber21SourcesCheck = true := by
  decide

def mmFiber21RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber21Key mmFiber21Expected (mmFiber21RowAt i)

def mmFiber21ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber21Rows mmMaxParentDepth (listGetD mmFiber21Expected i 0) == 0

def mmFiber21CertificateAudit : Bool :=
  mmFiber21SourcesCheck

theorem mmFiber21CertificateAudit_ok :
    mmFiber21CertificateAudit = true := by
  simp [mmFiber21CertificateAudit,
    mmFiber21SourcesCheck_ok]

def mmFiber22Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.b]

def mmFiber22Expected : List Nat :=
  [800, 801, 802, 803, 804, 805, 806, 807]

def mmFiber22Rows : List DirectChainParentRow :=
  [ directRow 800 800 160 20 160 20 default
  , directRow 801 800 160 21 160 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 802 800 160 22 160 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 803 801 160 23 160 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 804 800 161 28 160 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 805 801 161 29 160 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 806 802 161 30 160 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 807 803 161 31 160 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber22RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber22Rows i default

def mmFiber22SourcesCheck : Bool :=
  (mmFiber22Rows.map fun row => row.source) == mmFiber22Expected

theorem mmFiber22SourcesCheck_ok :
    mmFiber22SourcesCheck = true := by
  decide

def mmFiber22RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt i)

theorem mmFiber22Row_0_ok : mmFiber22RowCheck 0 = true := by decide
theorem mmFiber22Row_1_ok : mmFiber22RowCheck 1 = true := by decide
theorem mmFiber22Row_2_ok : mmFiber22RowCheck 2 = true := by decide
theorem mmFiber22Row_3_ok : mmFiber22RowCheck 3 = true := by decide
theorem mmFiber22Row_4_ok : mmFiber22RowCheck 4 = true := by decide
theorem mmFiber22Row_5_ok : mmFiber22RowCheck 5 = true := by decide
theorem mmFiber22Row_6_ok : mmFiber22RowCheck 6 = true := by decide
theorem mmFiber22Row_7_ok : mmFiber22RowCheck 7 = true := by decide

def mmFiber22ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber22Rows mmMaxParentDepth (listGetD mmFiber22Expected i 0) == 800

theorem mmFiber22Parent_0_ok : mmFiber22ParentCheck 0 = true := by decide
theorem mmFiber22Parent_1_ok : mmFiber22ParentCheck 1 = true := by decide
theorem mmFiber22Parent_2_ok : mmFiber22ParentCheck 2 = true := by decide
theorem mmFiber22Parent_3_ok : mmFiber22ParentCheck 3 = true := by decide
theorem mmFiber22Parent_4_ok : mmFiber22ParentCheck 4 = true := by decide
theorem mmFiber22Parent_5_ok : mmFiber22ParentCheck 5 = true := by decide
theorem mmFiber22Parent_6_ok : mmFiber22ParentCheck 6 = true := by decide
theorem mmFiber22Parent_7_ok : mmFiber22ParentCheck 7 = true := by decide

def mmFiber22CertificateAudit : Bool :=
  mmFiber22SourcesCheck &&
    mmFiber22RowCheck 0 &&
    mmFiber22RowCheck 1 &&
    mmFiber22RowCheck 2 &&
    mmFiber22RowCheck 3 &&
    mmFiber22RowCheck 4 &&
    mmFiber22RowCheck 5 &&
    mmFiber22RowCheck 6 &&
    mmFiber22RowCheck 7 &&
    mmFiber22ParentCheck 0 &&
    mmFiber22ParentCheck 1 &&
    mmFiber22ParentCheck 2 &&
    mmFiber22ParentCheck 3 &&
    mmFiber22ParentCheck 4 &&
    mmFiber22ParentCheck 5 &&
    mmFiber22ParentCheck 6 &&
    mmFiber22ParentCheck 7

theorem mmFiber22CertificateAudit_ok :
    mmFiber22CertificateAudit = true := by
  simp [mmFiber22CertificateAudit,
    mmFiber22SourcesCheck_ok,
    mmFiber22Row_0_ok,
    mmFiber22Row_1_ok,
    mmFiber22Row_2_ok,
    mmFiber22Row_3_ok,
    mmFiber22Row_4_ok,
    mmFiber22Row_5_ok,
    mmFiber22Row_6_ok,
    mmFiber22Row_7_ok,
    mmFiber22Parent_0_ok,
    mmFiber22Parent_1_ok,
    mmFiber22Parent_2_ok,
    mmFiber22Parent_3_ok,
    mmFiber22Parent_4_ok,
    mmFiber22Parent_5_ok,
    mmFiber22Parent_6_ok,
    mmFiber22Parent_7_ok]

def mmFiber23Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.p]

def mmFiber23Expected : List Nat :=
  [480, 481, 482, 483, 484, 485, 486, 487]

def mmFiber23Rows : List DirectChainParentRow :=
  [ directRow 480 480 98 52 98 52 default
  , directRow 481 480 98 53 98 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 482 481 98 54 98 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 483 480 98 55 98 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 484 480 99 60 98 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 485 481 99 61 98 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 486 482 99 62 98 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 487 483 99 63 98 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber23RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber23Rows i default

def mmFiber23SourcesCheck : Bool :=
  (mmFiber23Rows.map fun row => row.source) == mmFiber23Expected

theorem mmFiber23SourcesCheck_ok :
    mmFiber23SourcesCheck = true := by
  decide

def mmFiber23RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt i)

theorem mmFiber23Row_0_ok : mmFiber23RowCheck 0 = true := by decide
theorem mmFiber23Row_1_ok : mmFiber23RowCheck 1 = true := by decide
theorem mmFiber23Row_2_ok : mmFiber23RowCheck 2 = true := by decide
theorem mmFiber23Row_3_ok : mmFiber23RowCheck 3 = true := by decide
theorem mmFiber23Row_4_ok : mmFiber23RowCheck 4 = true := by decide
theorem mmFiber23Row_5_ok : mmFiber23RowCheck 5 = true := by decide
theorem mmFiber23Row_6_ok : mmFiber23RowCheck 6 = true := by decide
theorem mmFiber23Row_7_ok : mmFiber23RowCheck 7 = true := by decide

def mmFiber23ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber23Rows mmMaxParentDepth (listGetD mmFiber23Expected i 0) == 480

theorem mmFiber23Parent_0_ok : mmFiber23ParentCheck 0 = true := by decide
theorem mmFiber23Parent_1_ok : mmFiber23ParentCheck 1 = true := by decide
theorem mmFiber23Parent_2_ok : mmFiber23ParentCheck 2 = true := by decide
theorem mmFiber23Parent_3_ok : mmFiber23ParentCheck 3 = true := by decide
theorem mmFiber23Parent_4_ok : mmFiber23ParentCheck 4 = true := by decide
theorem mmFiber23Parent_5_ok : mmFiber23ParentCheck 5 = true := by decide
theorem mmFiber23Parent_6_ok : mmFiber23ParentCheck 6 = true := by decide
theorem mmFiber23Parent_7_ok : mmFiber23ParentCheck 7 = true := by decide

def mmFiber23CertificateAudit : Bool :=
  mmFiber23SourcesCheck &&
    mmFiber23RowCheck 0 &&
    mmFiber23RowCheck 1 &&
    mmFiber23RowCheck 2 &&
    mmFiber23RowCheck 3 &&
    mmFiber23RowCheck 4 &&
    mmFiber23RowCheck 5 &&
    mmFiber23RowCheck 6 &&
    mmFiber23RowCheck 7 &&
    mmFiber23ParentCheck 0 &&
    mmFiber23ParentCheck 1 &&
    mmFiber23ParentCheck 2 &&
    mmFiber23ParentCheck 3 &&
    mmFiber23ParentCheck 4 &&
    mmFiber23ParentCheck 5 &&
    mmFiber23ParentCheck 6 &&
    mmFiber23ParentCheck 7

theorem mmFiber23CertificateAudit_ok :
    mmFiber23CertificateAudit = true := by
  simp [mmFiber23CertificateAudit,
    mmFiber23SourcesCheck_ok,
    mmFiber23Row_0_ok,
    mmFiber23Row_1_ok,
    mmFiber23Row_2_ok,
    mmFiber23Row_3_ok,
    mmFiber23Row_4_ok,
    mmFiber23Row_5_ok,
    mmFiber23Row_6_ok,
    mmFiber23Row_7_ok,
    mmFiber23Parent_0_ok,
    mmFiber23Parent_1_ok,
    mmFiber23Parent_2_ok,
    mmFiber23Parent_3_ok,
    mmFiber23Parent_4_ok,
    mmFiber23Parent_5_ok,
    mmFiber23Parent_6_ok,
    mmFiber23Parent_7_ok]

def mmFiber24Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.r]

def mmFiber24Expected : List Nat :=
  []

def mmFiber24Rows : List DirectChainParentRow :=
  []

def mmFiber24RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber24Rows i default

def mmFiber24SourcesCheck : Bool :=
  (mmFiber24Rows.map fun row => row.source) == mmFiber24Expected

theorem mmFiber24SourcesCheck_ok :
    mmFiber24SourcesCheck = true := by
  decide

def mmFiber24RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber24Key mmFiber24Expected (mmFiber24RowAt i)

def mmFiber24ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber24Rows mmMaxParentDepth (listGetD mmFiber24Expected i 0) == 0

def mmFiber24CertificateAudit : Bool :=
  mmFiber24SourcesCheck

theorem mmFiber24CertificateAudit_ok :
    mmFiber24CertificateAudit = true := by
  simp [mmFiber24CertificateAudit,
    mmFiber24SourcesCheck_ok]

def mmFiber25Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.b]

def mmFiber25Expected : List Nat :=
  []

def mmFiber25Rows : List DirectChainParentRow :=
  []

def mmFiber25RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber25Rows i default

def mmFiber25SourcesCheck : Bool :=
  (mmFiber25Rows.map fun row => row.source) == mmFiber25Expected

theorem mmFiber25SourcesCheck_ok :
    mmFiber25SourcesCheck = true := by
  decide

def mmFiber25RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber25Key mmFiber25Expected (mmFiber25RowAt i)

def mmFiber25ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber25Rows mmMaxParentDepth (listGetD mmFiber25Expected i 0) == 0

def mmFiber25CertificateAudit : Bool :=
  mmFiber25SourcesCheck

theorem mmFiber25CertificateAudit_ok :
    mmFiber25CertificateAudit = true := by
  simp [mmFiber25CertificateAudit,
    mmFiber25SourcesCheck_ok]

def mmFiber26Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.p]

def mmFiber26Expected : List Nat :=
  []

def mmFiber26Rows : List DirectChainParentRow :=
  []

def mmFiber26RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber26Rows i default

def mmFiber26SourcesCheck : Bool :=
  (mmFiber26Rows.map fun row => row.source) == mmFiber26Expected

theorem mmFiber26SourcesCheck_ok :
    mmFiber26SourcesCheck = true := by
  decide

def mmFiber26RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber26Key mmFiber26Expected (mmFiber26RowAt i)

def mmFiber26ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber26Rows mmMaxParentDepth (listGetD mmFiber26Expected i 0) == 0

def mmFiber26CertificateAudit : Bool :=
  mmFiber26SourcesCheck

theorem mmFiber26CertificateAudit_ok :
    mmFiber26CertificateAudit = true := by
  simp [mmFiber26CertificateAudit,
    mmFiber26SourcesCheck_ok]

def mmFiber27Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.r]

def mmFiber27Expected : List Nat :=
  []

def mmFiber27Rows : List DirectChainParentRow :=
  []

def mmFiber27RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber27Rows i default

def mmFiber27SourcesCheck : Bool :=
  (mmFiber27Rows.map fun row => row.source) == mmFiber27Expected

theorem mmFiber27SourcesCheck_ok :
    mmFiber27SourcesCheck = true := by
  decide

def mmFiber27RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber27Key mmFiber27Expected (mmFiber27RowAt i)

def mmFiber27ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber27Rows mmMaxParentDepth (listGetD mmFiber27Expected i 0) == 0

def mmFiber27CertificateAudit : Bool :=
  mmFiber27SourcesCheck

theorem mmFiber27CertificateAudit_ok :
    mmFiber27CertificateAudit = true := by
  simp [mmFiber27CertificateAudit,
    mmFiber27SourcesCheck_ok]

def mmFiber28Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.b]

def mmFiber28Expected : List Nat :=
  []

def mmFiber28Rows : List DirectChainParentRow :=
  []

def mmFiber28RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber28Rows i default

def mmFiber28SourcesCheck : Bool :=
  (mmFiber28Rows.map fun row => row.source) == mmFiber28Expected

theorem mmFiber28SourcesCheck_ok :
    mmFiber28SourcesCheck = true := by
  decide

def mmFiber28RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber28Key mmFiber28Expected (mmFiber28RowAt i)

def mmFiber28ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber28Rows mmMaxParentDepth (listGetD mmFiber28Expected i 0) == 0

def mmFiber28CertificateAudit : Bool :=
  mmFiber28SourcesCheck

theorem mmFiber28CertificateAudit_ok :
    mmFiber28CertificateAudit = true := by
  simp [mmFiber28CertificateAudit,
    mmFiber28SourcesCheck_ok]

def mmFiber29Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.p]

def mmFiber29Expected : List Nat :=
  []

def mmFiber29Rows : List DirectChainParentRow :=
  []

def mmFiber29RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber29Rows i default

def mmFiber29SourcesCheck : Bool :=
  (mmFiber29Rows.map fun row => row.source) == mmFiber29Expected

theorem mmFiber29SourcesCheck_ok :
    mmFiber29SourcesCheck = true := by
  decide

def mmFiber29RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber29Key mmFiber29Expected (mmFiber29RowAt i)

def mmFiber29ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber29Rows mmMaxParentDepth (listGetD mmFiber29Expected i 0) == 0

def mmFiber29CertificateAudit : Bool :=
  mmFiber29SourcesCheck

theorem mmFiber29CertificateAudit_ok :
    mmFiber29CertificateAudit = true := by
  simp [mmFiber29CertificateAudit,
    mmFiber29SourcesCheck_ok]

def mmFiber30Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.r]

def mmFiber30Expected : List Nat :=
  [360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]

def mmFiber30Rows : List DirectChainParentRow :=
  [ directRow 360 360 72 80 72 80 default
  , directRow 361 360 72 81 72 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 362 360 72 82 72 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 363 361 72 83 72 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 364 362 72 100 72 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 365 367 72 101 72 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 366 361 72 102 72 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 367 360 72 103 72 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 368 360 73 88 72 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 369 361 73 89 72 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 370 362 73 90 72 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 371 363 73 91 72 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 372 364 73 108 72 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 373 365 73 109 72 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 374 366 73 110 72 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 375 367 73 111 72 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 376 360 74 16 72 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 377 361 74 17 72 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 378 362 74 18 72 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 379 363 74 19 72 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 380 376 74 32 74 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 381 377 74 33 74 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 382 366 74 34 72 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 383 367 74 35 72 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 384 368 75 24 73 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 385 369 75 25 73 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 386 370 75 26 73 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 387 371 75 27 73 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 388 384 75 40 75 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 389 385 75 41 75 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 390 374 75 42 73 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 391 375 75 43 73 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 608 624 124 132 126 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 609 625 124 133 126 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 610 382 124 134 74 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 611 383 124 135 74 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 612 378 124 180 74 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 613 615 124 181 124 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 614 377 124 182 74 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 615 376 124 183 74 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 616 632 125 140 127 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 617 633 125 141 127 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 618 634 125 142 127 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 619 616 125 143 125 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 620 616 125 188 125 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 621 617 125 189 125 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 622 638 125 190 127 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 623 639 125 191 127 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 624 368 126 64 73 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 625 369 126 65 73 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 626 370 126 66 73 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 627 371 126 67 73 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 628 372 126 116 73 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 629 373 126 117 73 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 630 374 126 118 73 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 631 375 126 119 73 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 632 360 127 72 72 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 633 361 127 73 72 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 634 362 127 74 72 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 635 363 127 75 72 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 636 364 127 124 72 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 637 365 127 125 72 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 638 366 127 126 72 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 639 367 127 127 72 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mmFiber30RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber30Rows i default

def mmFiber30SourcesCheck : Bool :=
  (mmFiber30Rows.map fun row => row.source) == mmFiber30Expected

theorem mmFiber30SourcesCheck_ok :
    mmFiber30SourcesCheck = true := by
  decide

def mmFiber30RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt i)

theorem mmFiber30Row_0_ok : mmFiber30RowCheck 0 = true := by decide
theorem mmFiber30Row_1_ok : mmFiber30RowCheck 1 = true := by decide
theorem mmFiber30Row_2_ok : mmFiber30RowCheck 2 = true := by decide
theorem mmFiber30Row_3_ok : mmFiber30RowCheck 3 = true := by decide
theorem mmFiber30Row_4_ok : mmFiber30RowCheck 4 = true := by decide
theorem mmFiber30Row_5_ok : mmFiber30RowCheck 5 = true := by decide
theorem mmFiber30Row_6_ok : mmFiber30RowCheck 6 = true := by decide
theorem mmFiber30Row_7_ok : mmFiber30RowCheck 7 = true := by decide
theorem mmFiber30Row_8_ok : mmFiber30RowCheck 8 = true := by decide
theorem mmFiber30Row_9_ok : mmFiber30RowCheck 9 = true := by decide
theorem mmFiber30Row_10_ok : mmFiber30RowCheck 10 = true := by decide
theorem mmFiber30Row_11_ok : mmFiber30RowCheck 11 = true := by decide
theorem mmFiber30Row_12_ok : mmFiber30RowCheck 12 = true := by decide
theorem mmFiber30Row_13_ok : mmFiber30RowCheck 13 = true := by decide
theorem mmFiber30Row_14_ok : mmFiber30RowCheck 14 = true := by decide
theorem mmFiber30Row_15_ok : mmFiber30RowCheck 15 = true := by decide
theorem mmFiber30Row_16_ok : mmFiber30RowCheck 16 = true := by decide
theorem mmFiber30Row_17_ok : mmFiber30RowCheck 17 = true := by decide
theorem mmFiber30Row_18_ok : mmFiber30RowCheck 18 = true := by decide
theorem mmFiber30Row_19_ok : mmFiber30RowCheck 19 = true := by decide
theorem mmFiber30Row_20_ok : mmFiber30RowCheck 20 = true := by decide
theorem mmFiber30Row_21_ok : mmFiber30RowCheck 21 = true := by decide
theorem mmFiber30Row_22_ok : mmFiber30RowCheck 22 = true := by decide
theorem mmFiber30Row_23_ok : mmFiber30RowCheck 23 = true := by decide
theorem mmFiber30Row_24_ok : mmFiber30RowCheck 24 = true := by decide
theorem mmFiber30Row_25_ok : mmFiber30RowCheck 25 = true := by decide
theorem mmFiber30Row_26_ok : mmFiber30RowCheck 26 = true := by decide
theorem mmFiber30Row_27_ok : mmFiber30RowCheck 27 = true := by decide
theorem mmFiber30Row_28_ok : mmFiber30RowCheck 28 = true := by decide
theorem mmFiber30Row_29_ok : mmFiber30RowCheck 29 = true := by decide
theorem mmFiber30Row_30_ok : mmFiber30RowCheck 30 = true := by decide
theorem mmFiber30Row_31_ok : mmFiber30RowCheck 31 = true := by decide
theorem mmFiber30Row_32_ok : mmFiber30RowCheck 32 = true := by decide
theorem mmFiber30Row_33_ok : mmFiber30RowCheck 33 = true := by decide
theorem mmFiber30Row_34_ok : mmFiber30RowCheck 34 = true := by decide
theorem mmFiber30Row_35_ok : mmFiber30RowCheck 35 = true := by decide
theorem mmFiber30Row_36_ok : mmFiber30RowCheck 36 = true := by decide
theorem mmFiber30Row_37_ok : mmFiber30RowCheck 37 = true := by decide
theorem mmFiber30Row_38_ok : mmFiber30RowCheck 38 = true := by decide
theorem mmFiber30Row_39_ok : mmFiber30RowCheck 39 = true := by decide
theorem mmFiber30Row_40_ok : mmFiber30RowCheck 40 = true := by decide
theorem mmFiber30Row_41_ok : mmFiber30RowCheck 41 = true := by decide
theorem mmFiber30Row_42_ok : mmFiber30RowCheck 42 = true := by decide
theorem mmFiber30Row_43_ok : mmFiber30RowCheck 43 = true := by decide
theorem mmFiber30Row_44_ok : mmFiber30RowCheck 44 = true := by decide
theorem mmFiber30Row_45_ok : mmFiber30RowCheck 45 = true := by decide
theorem mmFiber30Row_46_ok : mmFiber30RowCheck 46 = true := by decide
theorem mmFiber30Row_47_ok : mmFiber30RowCheck 47 = true := by decide
theorem mmFiber30Row_48_ok : mmFiber30RowCheck 48 = true := by decide
theorem mmFiber30Row_49_ok : mmFiber30RowCheck 49 = true := by decide
theorem mmFiber30Row_50_ok : mmFiber30RowCheck 50 = true := by decide
theorem mmFiber30Row_51_ok : mmFiber30RowCheck 51 = true := by decide
theorem mmFiber30Row_52_ok : mmFiber30RowCheck 52 = true := by decide
theorem mmFiber30Row_53_ok : mmFiber30RowCheck 53 = true := by decide
theorem mmFiber30Row_54_ok : mmFiber30RowCheck 54 = true := by decide
theorem mmFiber30Row_55_ok : mmFiber30RowCheck 55 = true := by decide
theorem mmFiber30Row_56_ok : mmFiber30RowCheck 56 = true := by decide
theorem mmFiber30Row_57_ok : mmFiber30RowCheck 57 = true := by decide
theorem mmFiber30Row_58_ok : mmFiber30RowCheck 58 = true := by decide
theorem mmFiber30Row_59_ok : mmFiber30RowCheck 59 = true := by decide
theorem mmFiber30Row_60_ok : mmFiber30RowCheck 60 = true := by decide
theorem mmFiber30Row_61_ok : mmFiber30RowCheck 61 = true := by decide
theorem mmFiber30Row_62_ok : mmFiber30RowCheck 62 = true := by decide
theorem mmFiber30Row_63_ok : mmFiber30RowCheck 63 = true := by decide

def mmFiber30ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber30Rows mmMaxParentDepth (listGetD mmFiber30Expected i 0) == 360

theorem mmFiber30Parent_0_ok : mmFiber30ParentCheck 0 = true := by decide
theorem mmFiber30Parent_1_ok : mmFiber30ParentCheck 1 = true := by decide
theorem mmFiber30Parent_2_ok : mmFiber30ParentCheck 2 = true := by decide
theorem mmFiber30Parent_3_ok : mmFiber30ParentCheck 3 = true := by decide
theorem mmFiber30Parent_4_ok : mmFiber30ParentCheck 4 = true := by decide
theorem mmFiber30Parent_5_ok : mmFiber30ParentCheck 5 = true := by decide
theorem mmFiber30Parent_6_ok : mmFiber30ParentCheck 6 = true := by decide
theorem mmFiber30Parent_7_ok : mmFiber30ParentCheck 7 = true := by decide
theorem mmFiber30Parent_8_ok : mmFiber30ParentCheck 8 = true := by decide
theorem mmFiber30Parent_9_ok : mmFiber30ParentCheck 9 = true := by decide
theorem mmFiber30Parent_10_ok : mmFiber30ParentCheck 10 = true := by decide
theorem mmFiber30Parent_11_ok : mmFiber30ParentCheck 11 = true := by decide
theorem mmFiber30Parent_12_ok : mmFiber30ParentCheck 12 = true := by decide
theorem mmFiber30Parent_13_ok : mmFiber30ParentCheck 13 = true := by decide
theorem mmFiber30Parent_14_ok : mmFiber30ParentCheck 14 = true := by decide
theorem mmFiber30Parent_15_ok : mmFiber30ParentCheck 15 = true := by decide
theorem mmFiber30Parent_16_ok : mmFiber30ParentCheck 16 = true := by decide
theorem mmFiber30Parent_17_ok : mmFiber30ParentCheck 17 = true := by decide
theorem mmFiber30Parent_18_ok : mmFiber30ParentCheck 18 = true := by decide
theorem mmFiber30Parent_19_ok : mmFiber30ParentCheck 19 = true := by decide
theorem mmFiber30Parent_20_ok : mmFiber30ParentCheck 20 = true := by decide
theorem mmFiber30Parent_21_ok : mmFiber30ParentCheck 21 = true := by decide
theorem mmFiber30Parent_22_ok : mmFiber30ParentCheck 22 = true := by decide
theorem mmFiber30Parent_23_ok : mmFiber30ParentCheck 23 = true := by decide
theorem mmFiber30Parent_24_ok : mmFiber30ParentCheck 24 = true := by decide
theorem mmFiber30Parent_25_ok : mmFiber30ParentCheck 25 = true := by decide
theorem mmFiber30Parent_26_ok : mmFiber30ParentCheck 26 = true := by decide
theorem mmFiber30Parent_27_ok : mmFiber30ParentCheck 27 = true := by decide
theorem mmFiber30Parent_28_ok : mmFiber30ParentCheck 28 = true := by decide
theorem mmFiber30Parent_29_ok : mmFiber30ParentCheck 29 = true := by decide
theorem mmFiber30Parent_30_ok : mmFiber30ParentCheck 30 = true := by decide
theorem mmFiber30Parent_31_ok : mmFiber30ParentCheck 31 = true := by decide
theorem mmFiber30Parent_32_ok : mmFiber30ParentCheck 32 = true := by decide
theorem mmFiber30Parent_33_ok : mmFiber30ParentCheck 33 = true := by decide
theorem mmFiber30Parent_34_ok : mmFiber30ParentCheck 34 = true := by decide
theorem mmFiber30Parent_35_ok : mmFiber30ParentCheck 35 = true := by decide
theorem mmFiber30Parent_36_ok : mmFiber30ParentCheck 36 = true := by decide
theorem mmFiber30Parent_37_ok : mmFiber30ParentCheck 37 = true := by decide
theorem mmFiber30Parent_38_ok : mmFiber30ParentCheck 38 = true := by decide
theorem mmFiber30Parent_39_ok : mmFiber30ParentCheck 39 = true := by decide
theorem mmFiber30Parent_40_ok : mmFiber30ParentCheck 40 = true := by decide
theorem mmFiber30Parent_41_ok : mmFiber30ParentCheck 41 = true := by decide
theorem mmFiber30Parent_42_ok : mmFiber30ParentCheck 42 = true := by decide
theorem mmFiber30Parent_43_ok : mmFiber30ParentCheck 43 = true := by decide
theorem mmFiber30Parent_44_ok : mmFiber30ParentCheck 44 = true := by decide
theorem mmFiber30Parent_45_ok : mmFiber30ParentCheck 45 = true := by decide
theorem mmFiber30Parent_46_ok : mmFiber30ParentCheck 46 = true := by decide
theorem mmFiber30Parent_47_ok : mmFiber30ParentCheck 47 = true := by decide
theorem mmFiber30Parent_48_ok : mmFiber30ParentCheck 48 = true := by decide
theorem mmFiber30Parent_49_ok : mmFiber30ParentCheck 49 = true := by decide
theorem mmFiber30Parent_50_ok : mmFiber30ParentCheck 50 = true := by decide
theorem mmFiber30Parent_51_ok : mmFiber30ParentCheck 51 = true := by decide
theorem mmFiber30Parent_52_ok : mmFiber30ParentCheck 52 = true := by decide
theorem mmFiber30Parent_53_ok : mmFiber30ParentCheck 53 = true := by decide
theorem mmFiber30Parent_54_ok : mmFiber30ParentCheck 54 = true := by decide
theorem mmFiber30Parent_55_ok : mmFiber30ParentCheck 55 = true := by decide
theorem mmFiber30Parent_56_ok : mmFiber30ParentCheck 56 = true := by decide
theorem mmFiber30Parent_57_ok : mmFiber30ParentCheck 57 = true := by decide
theorem mmFiber30Parent_58_ok : mmFiber30ParentCheck 58 = true := by decide
theorem mmFiber30Parent_59_ok : mmFiber30ParentCheck 59 = true := by decide
theorem mmFiber30Parent_60_ok : mmFiber30ParentCheck 60 = true := by decide
theorem mmFiber30Parent_61_ok : mmFiber30ParentCheck 61 = true := by decide
theorem mmFiber30Parent_62_ok : mmFiber30ParentCheck 62 = true := by decide
theorem mmFiber30Parent_63_ok : mmFiber30ParentCheck 63 = true := by decide

def mmFiber30CertificateAudit : Bool :=
  mmFiber30SourcesCheck &&
    mmFiber30RowCheck 0 &&
    mmFiber30RowCheck 1 &&
    mmFiber30RowCheck 2 &&
    mmFiber30RowCheck 3 &&
    mmFiber30RowCheck 4 &&
    mmFiber30RowCheck 5 &&
    mmFiber30RowCheck 6 &&
    mmFiber30RowCheck 7 &&
    mmFiber30RowCheck 8 &&
    mmFiber30RowCheck 9 &&
    mmFiber30RowCheck 10 &&
    mmFiber30RowCheck 11 &&
    mmFiber30RowCheck 12 &&
    mmFiber30RowCheck 13 &&
    mmFiber30RowCheck 14 &&
    mmFiber30RowCheck 15 &&
    mmFiber30RowCheck 16 &&
    mmFiber30RowCheck 17 &&
    mmFiber30RowCheck 18 &&
    mmFiber30RowCheck 19 &&
    mmFiber30RowCheck 20 &&
    mmFiber30RowCheck 21 &&
    mmFiber30RowCheck 22 &&
    mmFiber30RowCheck 23 &&
    mmFiber30RowCheck 24 &&
    mmFiber30RowCheck 25 &&
    mmFiber30RowCheck 26 &&
    mmFiber30RowCheck 27 &&
    mmFiber30RowCheck 28 &&
    mmFiber30RowCheck 29 &&
    mmFiber30RowCheck 30 &&
    mmFiber30RowCheck 31 &&
    mmFiber30RowCheck 32 &&
    mmFiber30RowCheck 33 &&
    mmFiber30RowCheck 34 &&
    mmFiber30RowCheck 35 &&
    mmFiber30RowCheck 36 &&
    mmFiber30RowCheck 37 &&
    mmFiber30RowCheck 38 &&
    mmFiber30RowCheck 39 &&
    mmFiber30RowCheck 40 &&
    mmFiber30RowCheck 41 &&
    mmFiber30RowCheck 42 &&
    mmFiber30RowCheck 43 &&
    mmFiber30RowCheck 44 &&
    mmFiber30RowCheck 45 &&
    mmFiber30RowCheck 46 &&
    mmFiber30RowCheck 47 &&
    mmFiber30RowCheck 48 &&
    mmFiber30RowCheck 49 &&
    mmFiber30RowCheck 50 &&
    mmFiber30RowCheck 51 &&
    mmFiber30RowCheck 52 &&
    mmFiber30RowCheck 53 &&
    mmFiber30RowCheck 54 &&
    mmFiber30RowCheck 55 &&
    mmFiber30RowCheck 56 &&
    mmFiber30RowCheck 57 &&
    mmFiber30RowCheck 58 &&
    mmFiber30RowCheck 59 &&
    mmFiber30RowCheck 60 &&
    mmFiber30RowCheck 61 &&
    mmFiber30RowCheck 62 &&
    mmFiber30RowCheck 63 &&
    mmFiber30ParentCheck 0 &&
    mmFiber30ParentCheck 1 &&
    mmFiber30ParentCheck 2 &&
    mmFiber30ParentCheck 3 &&
    mmFiber30ParentCheck 4 &&
    mmFiber30ParentCheck 5 &&
    mmFiber30ParentCheck 6 &&
    mmFiber30ParentCheck 7 &&
    mmFiber30ParentCheck 8 &&
    mmFiber30ParentCheck 9 &&
    mmFiber30ParentCheck 10 &&
    mmFiber30ParentCheck 11 &&
    mmFiber30ParentCheck 12 &&
    mmFiber30ParentCheck 13 &&
    mmFiber30ParentCheck 14 &&
    mmFiber30ParentCheck 15 &&
    mmFiber30ParentCheck 16 &&
    mmFiber30ParentCheck 17 &&
    mmFiber30ParentCheck 18 &&
    mmFiber30ParentCheck 19 &&
    mmFiber30ParentCheck 20 &&
    mmFiber30ParentCheck 21 &&
    mmFiber30ParentCheck 22 &&
    mmFiber30ParentCheck 23 &&
    mmFiber30ParentCheck 24 &&
    mmFiber30ParentCheck 25 &&
    mmFiber30ParentCheck 26 &&
    mmFiber30ParentCheck 27 &&
    mmFiber30ParentCheck 28 &&
    mmFiber30ParentCheck 29 &&
    mmFiber30ParentCheck 30 &&
    mmFiber30ParentCheck 31 &&
    mmFiber30ParentCheck 32 &&
    mmFiber30ParentCheck 33 &&
    mmFiber30ParentCheck 34 &&
    mmFiber30ParentCheck 35 &&
    mmFiber30ParentCheck 36 &&
    mmFiber30ParentCheck 37 &&
    mmFiber30ParentCheck 38 &&
    mmFiber30ParentCheck 39 &&
    mmFiber30ParentCheck 40 &&
    mmFiber30ParentCheck 41 &&
    mmFiber30ParentCheck 42 &&
    mmFiber30ParentCheck 43 &&
    mmFiber30ParentCheck 44 &&
    mmFiber30ParentCheck 45 &&
    mmFiber30ParentCheck 46 &&
    mmFiber30ParentCheck 47 &&
    mmFiber30ParentCheck 48 &&
    mmFiber30ParentCheck 49 &&
    mmFiber30ParentCheck 50 &&
    mmFiber30ParentCheck 51 &&
    mmFiber30ParentCheck 52 &&
    mmFiber30ParentCheck 53 &&
    mmFiber30ParentCheck 54 &&
    mmFiber30ParentCheck 55 &&
    mmFiber30ParentCheck 56 &&
    mmFiber30ParentCheck 57 &&
    mmFiber30ParentCheck 58 &&
    mmFiber30ParentCheck 59 &&
    mmFiber30ParentCheck 60 &&
    mmFiber30ParentCheck 61 &&
    mmFiber30ParentCheck 62 &&
    mmFiber30ParentCheck 63

theorem mmFiber30CertificateAudit_ok :
    mmFiber30CertificateAudit = true := by
  simp [mmFiber30CertificateAudit,
    mmFiber30SourcesCheck_ok,
    mmFiber30Row_0_ok,
    mmFiber30Row_1_ok,
    mmFiber30Row_2_ok,
    mmFiber30Row_3_ok,
    mmFiber30Row_4_ok,
    mmFiber30Row_5_ok,
    mmFiber30Row_6_ok,
    mmFiber30Row_7_ok,
    mmFiber30Row_8_ok,
    mmFiber30Row_9_ok,
    mmFiber30Row_10_ok,
    mmFiber30Row_11_ok,
    mmFiber30Row_12_ok,
    mmFiber30Row_13_ok,
    mmFiber30Row_14_ok,
    mmFiber30Row_15_ok,
    mmFiber30Row_16_ok,
    mmFiber30Row_17_ok,
    mmFiber30Row_18_ok,
    mmFiber30Row_19_ok,
    mmFiber30Row_20_ok,
    mmFiber30Row_21_ok,
    mmFiber30Row_22_ok,
    mmFiber30Row_23_ok,
    mmFiber30Row_24_ok,
    mmFiber30Row_25_ok,
    mmFiber30Row_26_ok,
    mmFiber30Row_27_ok,
    mmFiber30Row_28_ok,
    mmFiber30Row_29_ok,
    mmFiber30Row_30_ok,
    mmFiber30Row_31_ok,
    mmFiber30Row_32_ok,
    mmFiber30Row_33_ok,
    mmFiber30Row_34_ok,
    mmFiber30Row_35_ok,
    mmFiber30Row_36_ok,
    mmFiber30Row_37_ok,
    mmFiber30Row_38_ok,
    mmFiber30Row_39_ok,
    mmFiber30Row_40_ok,
    mmFiber30Row_41_ok,
    mmFiber30Row_42_ok,
    mmFiber30Row_43_ok,
    mmFiber30Row_44_ok,
    mmFiber30Row_45_ok,
    mmFiber30Row_46_ok,
    mmFiber30Row_47_ok,
    mmFiber30Row_48_ok,
    mmFiber30Row_49_ok,
    mmFiber30Row_50_ok,
    mmFiber30Row_51_ok,
    mmFiber30Row_52_ok,
    mmFiber30Row_53_ok,
    mmFiber30Row_54_ok,
    mmFiber30Row_55_ok,
    mmFiber30Row_56_ok,
    mmFiber30Row_57_ok,
    mmFiber30Row_58_ok,
    mmFiber30Row_59_ok,
    mmFiber30Row_60_ok,
    mmFiber30Row_61_ok,
    mmFiber30Row_62_ok,
    mmFiber30Row_63_ok,
    mmFiber30Parent_0_ok,
    mmFiber30Parent_1_ok,
    mmFiber30Parent_2_ok,
    mmFiber30Parent_3_ok,
    mmFiber30Parent_4_ok,
    mmFiber30Parent_5_ok,
    mmFiber30Parent_6_ok,
    mmFiber30Parent_7_ok,
    mmFiber30Parent_8_ok,
    mmFiber30Parent_9_ok,
    mmFiber30Parent_10_ok,
    mmFiber30Parent_11_ok,
    mmFiber30Parent_12_ok,
    mmFiber30Parent_13_ok,
    mmFiber30Parent_14_ok,
    mmFiber30Parent_15_ok,
    mmFiber30Parent_16_ok,
    mmFiber30Parent_17_ok,
    mmFiber30Parent_18_ok,
    mmFiber30Parent_19_ok,
    mmFiber30Parent_20_ok,
    mmFiber30Parent_21_ok,
    mmFiber30Parent_22_ok,
    mmFiber30Parent_23_ok,
    mmFiber30Parent_24_ok,
    mmFiber30Parent_25_ok,
    mmFiber30Parent_26_ok,
    mmFiber30Parent_27_ok,
    mmFiber30Parent_28_ok,
    mmFiber30Parent_29_ok,
    mmFiber30Parent_30_ok,
    mmFiber30Parent_31_ok,
    mmFiber30Parent_32_ok,
    mmFiber30Parent_33_ok,
    mmFiber30Parent_34_ok,
    mmFiber30Parent_35_ok,
    mmFiber30Parent_36_ok,
    mmFiber30Parent_37_ok,
    mmFiber30Parent_38_ok,
    mmFiber30Parent_39_ok,
    mmFiber30Parent_40_ok,
    mmFiber30Parent_41_ok,
    mmFiber30Parent_42_ok,
    mmFiber30Parent_43_ok,
    mmFiber30Parent_44_ok,
    mmFiber30Parent_45_ok,
    mmFiber30Parent_46_ok,
    mmFiber30Parent_47_ok,
    mmFiber30Parent_48_ok,
    mmFiber30Parent_49_ok,
    mmFiber30Parent_50_ok,
    mmFiber30Parent_51_ok,
    mmFiber30Parent_52_ok,
    mmFiber30Parent_53_ok,
    mmFiber30Parent_54_ok,
    mmFiber30Parent_55_ok,
    mmFiber30Parent_56_ok,
    mmFiber30Parent_57_ok,
    mmFiber30Parent_58_ok,
    mmFiber30Parent_59_ok,
    mmFiber30Parent_60_ok,
    mmFiber30Parent_61_ok,
    mmFiber30Parent_62_ok,
    mmFiber30Parent_63_ok]

def mmFiber31Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.b]

def mmFiber31Expected : List Nat :=
  [312, 313, 314, 315, 316, 317, 318, 319]

def mmFiber31Rows : List DirectChainParentRow :=
  [ directRow 312 312 62 112 62 112 default
  , directRow 313 312 62 113 62 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 314 312 62 114 62 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 315 313 62 115 62 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 316 312 63 120 62 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 317 313 63 121 62 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 318 314 63 122 62 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 319 315 63 123 62 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber31RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber31Rows i default

def mmFiber31SourcesCheck : Bool :=
  (mmFiber31Rows.map fun row => row.source) == mmFiber31Expected

theorem mmFiber31SourcesCheck_ok :
    mmFiber31SourcesCheck = true := by
  decide

def mmFiber31RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt i)

theorem mmFiber31Row_0_ok : mmFiber31RowCheck 0 = true := by decide
theorem mmFiber31Row_1_ok : mmFiber31RowCheck 1 = true := by decide
theorem mmFiber31Row_2_ok : mmFiber31RowCheck 2 = true := by decide
theorem mmFiber31Row_3_ok : mmFiber31RowCheck 3 = true := by decide
theorem mmFiber31Row_4_ok : mmFiber31RowCheck 4 = true := by decide
theorem mmFiber31Row_5_ok : mmFiber31RowCheck 5 = true := by decide
theorem mmFiber31Row_6_ok : mmFiber31RowCheck 6 = true := by decide
theorem mmFiber31Row_7_ok : mmFiber31RowCheck 7 = true := by decide

def mmFiber31ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber31Rows mmMaxParentDepth (listGetD mmFiber31Expected i 0) == 312

theorem mmFiber31Parent_0_ok : mmFiber31ParentCheck 0 = true := by decide
theorem mmFiber31Parent_1_ok : mmFiber31ParentCheck 1 = true := by decide
theorem mmFiber31Parent_2_ok : mmFiber31ParentCheck 2 = true := by decide
theorem mmFiber31Parent_3_ok : mmFiber31ParentCheck 3 = true := by decide
theorem mmFiber31Parent_4_ok : mmFiber31ParentCheck 4 = true := by decide
theorem mmFiber31Parent_5_ok : mmFiber31ParentCheck 5 = true := by decide
theorem mmFiber31Parent_6_ok : mmFiber31ParentCheck 6 = true := by decide
theorem mmFiber31Parent_7_ok : mmFiber31ParentCheck 7 = true := by decide

def mmFiber31CertificateAudit : Bool :=
  mmFiber31SourcesCheck &&
    mmFiber31RowCheck 0 &&
    mmFiber31RowCheck 1 &&
    mmFiber31RowCheck 2 &&
    mmFiber31RowCheck 3 &&
    mmFiber31RowCheck 4 &&
    mmFiber31RowCheck 5 &&
    mmFiber31RowCheck 6 &&
    mmFiber31RowCheck 7 &&
    mmFiber31ParentCheck 0 &&
    mmFiber31ParentCheck 1 &&
    mmFiber31ParentCheck 2 &&
    mmFiber31ParentCheck 3 &&
    mmFiber31ParentCheck 4 &&
    mmFiber31ParentCheck 5 &&
    mmFiber31ParentCheck 6 &&
    mmFiber31ParentCheck 7

theorem mmFiber31CertificateAudit_ok :
    mmFiber31CertificateAudit = true := by
  simp [mmFiber31CertificateAudit,
    mmFiber31SourcesCheck_ok,
    mmFiber31Row_0_ok,
    mmFiber31Row_1_ok,
    mmFiber31Row_2_ok,
    mmFiber31Row_3_ok,
    mmFiber31Row_4_ok,
    mmFiber31Row_5_ok,
    mmFiber31Row_6_ok,
    mmFiber31Row_7_ok,
    mmFiber31Parent_0_ok,
    mmFiber31Parent_1_ok,
    mmFiber31Parent_2_ok,
    mmFiber31Parent_3_ok,
    mmFiber31Parent_4_ok,
    mmFiber31Parent_5_ok,
    mmFiber31Parent_6_ok,
    mmFiber31Parent_7_ok]

def mmFiber32Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.p]

def mmFiber32Expected : List Nat :=
  []

def mmFiber32Rows : List DirectChainParentRow :=
  []

def mmFiber32RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber32Rows i default

def mmFiber32SourcesCheck : Bool :=
  (mmFiber32Rows.map fun row => row.source) == mmFiber32Expected

theorem mmFiber32SourcesCheck_ok :
    mmFiber32SourcesCheck = true := by
  decide

def mmFiber32RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber32Key mmFiber32Expected (mmFiber32RowAt i)

def mmFiber32ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber32Rows mmMaxParentDepth (listGetD mmFiber32Expected i 0) == 0

def mmFiber32CertificateAudit : Bool :=
  mmFiber32SourcesCheck

theorem mmFiber32CertificateAudit_ok :
    mmFiber32CertificateAudit = true := by
  simp [mmFiber32CertificateAudit,
    mmFiber32SourcesCheck_ok]

def mmFiber33Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.r]

def mmFiber33Expected : List Nat :=
  [680, 681, 682, 683, 684, 685, 686, 687]

def mmFiber33Rows : List DirectChainParentRow :=
  [ directRow 680 680 136 84 136 84 default
  , directRow 681 680 136 85 136 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 682 680 136 86 136 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 683 681 136 87 136 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 684 680 137 92 136 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 685 681 137 93 136 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 686 682 137 94 136 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 687 683 137 95 136 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber33RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber33Rows i default

def mmFiber33SourcesCheck : Bool :=
  (mmFiber33Rows.map fun row => row.source) == mmFiber33Expected

theorem mmFiber33SourcesCheck_ok :
    mmFiber33SourcesCheck = true := by
  decide

def mmFiber33RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt i)

theorem mmFiber33Row_0_ok : mmFiber33RowCheck 0 = true := by decide
theorem mmFiber33Row_1_ok : mmFiber33RowCheck 1 = true := by decide
theorem mmFiber33Row_2_ok : mmFiber33RowCheck 2 = true := by decide
theorem mmFiber33Row_3_ok : mmFiber33RowCheck 3 = true := by decide
theorem mmFiber33Row_4_ok : mmFiber33RowCheck 4 = true := by decide
theorem mmFiber33Row_5_ok : mmFiber33RowCheck 5 = true := by decide
theorem mmFiber33Row_6_ok : mmFiber33RowCheck 6 = true := by decide
theorem mmFiber33Row_7_ok : mmFiber33RowCheck 7 = true := by decide

def mmFiber33ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber33Rows mmMaxParentDepth (listGetD mmFiber33Expected i 0) == 680

theorem mmFiber33Parent_0_ok : mmFiber33ParentCheck 0 = true := by decide
theorem mmFiber33Parent_1_ok : mmFiber33ParentCheck 1 = true := by decide
theorem mmFiber33Parent_2_ok : mmFiber33ParentCheck 2 = true := by decide
theorem mmFiber33Parent_3_ok : mmFiber33ParentCheck 3 = true := by decide
theorem mmFiber33Parent_4_ok : mmFiber33ParentCheck 4 = true := by decide
theorem mmFiber33Parent_5_ok : mmFiber33ParentCheck 5 = true := by decide
theorem mmFiber33Parent_6_ok : mmFiber33ParentCheck 6 = true := by decide
theorem mmFiber33Parent_7_ok : mmFiber33ParentCheck 7 = true := by decide

def mmFiber33CertificateAudit : Bool :=
  mmFiber33SourcesCheck &&
    mmFiber33RowCheck 0 &&
    mmFiber33RowCheck 1 &&
    mmFiber33RowCheck 2 &&
    mmFiber33RowCheck 3 &&
    mmFiber33RowCheck 4 &&
    mmFiber33RowCheck 5 &&
    mmFiber33RowCheck 6 &&
    mmFiber33RowCheck 7 &&
    mmFiber33ParentCheck 0 &&
    mmFiber33ParentCheck 1 &&
    mmFiber33ParentCheck 2 &&
    mmFiber33ParentCheck 3 &&
    mmFiber33ParentCheck 4 &&
    mmFiber33ParentCheck 5 &&
    mmFiber33ParentCheck 6 &&
    mmFiber33ParentCheck 7

theorem mmFiber33CertificateAudit_ok :
    mmFiber33CertificateAudit = true := by
  simp [mmFiber33CertificateAudit,
    mmFiber33SourcesCheck_ok,
    mmFiber33Row_0_ok,
    mmFiber33Row_1_ok,
    mmFiber33Row_2_ok,
    mmFiber33Row_3_ok,
    mmFiber33Row_4_ok,
    mmFiber33Row_5_ok,
    mmFiber33Row_6_ok,
    mmFiber33Row_7_ok,
    mmFiber33Parent_0_ok,
    mmFiber33Parent_1_ok,
    mmFiber33Parent_2_ok,
    mmFiber33Parent_3_ok,
    mmFiber33Parent_4_ok,
    mmFiber33Parent_5_ok,
    mmFiber33Parent_6_ok,
    mmFiber33Parent_7_ok]

def mmFiber34Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.b]

def mmFiber34Expected : List Nat :=
  []

def mmFiber34Rows : List DirectChainParentRow :=
  []

def mmFiber34RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber34Rows i default

def mmFiber34SourcesCheck : Bool :=
  (mmFiber34Rows.map fun row => row.source) == mmFiber34Expected

theorem mmFiber34SourcesCheck_ok :
    mmFiber34SourcesCheck = true := by
  decide

def mmFiber34RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber34Key mmFiber34Expected (mmFiber34RowAt i)

def mmFiber34ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber34Rows mmMaxParentDepth (listGetD mmFiber34Expected i 0) == 0

def mmFiber34CertificateAudit : Bool :=
  mmFiber34SourcesCheck

theorem mmFiber34CertificateAudit_ok :
    mmFiber34CertificateAudit = true := by
  simp [mmFiber34CertificateAudit,
    mmFiber34SourcesCheck_ok]

def mmFiber35Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.p]

def mmFiber35Expected : List Nat :=
  [232, 233, 234, 235, 236, 237, 238, 239]

def mmFiber35Rows : List DirectChainParentRow :=
  [ directRow 232 232 46 112 46 112 default
  , directRow 233 232 46 113 46 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 234 232 46 114 46 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 235 233 46 115 46 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 236 232 47 120 46 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 237 233 47 121 46 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 238 234 47 122 46 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 239 235 47 123 46 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber35RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber35Rows i default

def mmFiber35SourcesCheck : Bool :=
  (mmFiber35Rows.map fun row => row.source) == mmFiber35Expected

theorem mmFiber35SourcesCheck_ok :
    mmFiber35SourcesCheck = true := by
  decide

def mmFiber35RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt i)

theorem mmFiber35Row_0_ok : mmFiber35RowCheck 0 = true := by decide
theorem mmFiber35Row_1_ok : mmFiber35RowCheck 1 = true := by decide
theorem mmFiber35Row_2_ok : mmFiber35RowCheck 2 = true := by decide
theorem mmFiber35Row_3_ok : mmFiber35RowCheck 3 = true := by decide
theorem mmFiber35Row_4_ok : mmFiber35RowCheck 4 = true := by decide
theorem mmFiber35Row_5_ok : mmFiber35RowCheck 5 = true := by decide
theorem mmFiber35Row_6_ok : mmFiber35RowCheck 6 = true := by decide
theorem mmFiber35Row_7_ok : mmFiber35RowCheck 7 = true := by decide

def mmFiber35ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber35Rows mmMaxParentDepth (listGetD mmFiber35Expected i 0) == 232

theorem mmFiber35Parent_0_ok : mmFiber35ParentCheck 0 = true := by decide
theorem mmFiber35Parent_1_ok : mmFiber35ParentCheck 1 = true := by decide
theorem mmFiber35Parent_2_ok : mmFiber35ParentCheck 2 = true := by decide
theorem mmFiber35Parent_3_ok : mmFiber35ParentCheck 3 = true := by decide
theorem mmFiber35Parent_4_ok : mmFiber35ParentCheck 4 = true := by decide
theorem mmFiber35Parent_5_ok : mmFiber35ParentCheck 5 = true := by decide
theorem mmFiber35Parent_6_ok : mmFiber35ParentCheck 6 = true := by decide
theorem mmFiber35Parent_7_ok : mmFiber35ParentCheck 7 = true := by decide

def mmFiber35CertificateAudit : Bool :=
  mmFiber35SourcesCheck &&
    mmFiber35RowCheck 0 &&
    mmFiber35RowCheck 1 &&
    mmFiber35RowCheck 2 &&
    mmFiber35RowCheck 3 &&
    mmFiber35RowCheck 4 &&
    mmFiber35RowCheck 5 &&
    mmFiber35RowCheck 6 &&
    mmFiber35RowCheck 7 &&
    mmFiber35ParentCheck 0 &&
    mmFiber35ParentCheck 1 &&
    mmFiber35ParentCheck 2 &&
    mmFiber35ParentCheck 3 &&
    mmFiber35ParentCheck 4 &&
    mmFiber35ParentCheck 5 &&
    mmFiber35ParentCheck 6 &&
    mmFiber35ParentCheck 7

theorem mmFiber35CertificateAudit_ok :
    mmFiber35CertificateAudit = true := by
  simp [mmFiber35CertificateAudit,
    mmFiber35SourcesCheck_ok,
    mmFiber35Row_0_ok,
    mmFiber35Row_1_ok,
    mmFiber35Row_2_ok,
    mmFiber35Row_3_ok,
    mmFiber35Row_4_ok,
    mmFiber35Row_5_ok,
    mmFiber35Row_6_ok,
    mmFiber35Row_7_ok,
    mmFiber35Parent_0_ok,
    mmFiber35Parent_1_ok,
    mmFiber35Parent_2_ok,
    mmFiber35Parent_3_ok,
    mmFiber35Parent_4_ok,
    mmFiber35Parent_5_ok,
    mmFiber35Parent_6_ok,
    mmFiber35Parent_7_ok]

def mmFiber36Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.r]

def mmFiber36Expected : List Nat :=
  [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599]

def mmFiber36Rows : List DirectChainParentRow :=
  [ directRow 320 320 64 80 64 80 default
  , directRow 321 320 64 81 64 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 322 320 64 82 64 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 323 321 64 83 64 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 324 322 64 100 64 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 325 327 64 101 64 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 326 321 64 102 64 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 327 320 64 103 64 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 328 320 65 88 64 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 329 321 65 89 64 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 330 322 65 90 64 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 331 323 65 91 64 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 332 324 65 108 64 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 333 325 65 109 64 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 334 326 65 110 64 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 335 327 65 111 64 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 336 320 66 16 64 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 337 321 66 17 64 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 338 322 66 18 64 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 339 323 66 19 64 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 340 336 66 32 66 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 341 337 66 33 66 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 342 326 66 34 64 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 343 327 66 35 64 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 344 328 67 24 65 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 345 329 67 25 65 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 346 330 67 26 65 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 347 331 67 27 65 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 348 344 67 40 67 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 349 345 67 41 67 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 350 334 67 42 65 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 351 335 67 43 65 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 568 584 116 132 118 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 569 585 116 133 118 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 570 342 116 134 66 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 571 343 116 135 66 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 572 338 116 180 66 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 573 575 116 181 116 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 574 337 116 182 66 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 575 336 116 183 66 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 576 592 117 140 119 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 577 593 117 141 119 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 578 594 117 142 119 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 579 576 117 143 117 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 580 576 117 188 117 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 581 577 117 189 117 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 582 598 117 190 119 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 583 599 117 191 119 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 584 328 118 64 65 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 585 329 118 65 65 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 586 330 118 66 65 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 587 331 118 67 65 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 588 332 118 116 65 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 589 333 118 117 65 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 590 334 118 118 65 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 591 335 118 119 65 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 592 320 119 72 64 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 593 321 119 73 64 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 594 322 119 74 64 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 595 323 119 75 64 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 596 324 119 124 64 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 597 325 119 125 64 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 598 326 119 126 64 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 599 327 119 127 64 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mmFiber36RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber36Rows i default

def mmFiber36SourcesCheck : Bool :=
  (mmFiber36Rows.map fun row => row.source) == mmFiber36Expected

theorem mmFiber36SourcesCheck_ok :
    mmFiber36SourcesCheck = true := by
  decide

def mmFiber36RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber36Key mmFiber36Expected (mmFiber36RowAt i)

theorem mmFiber36Row_0_ok : mmFiber36RowCheck 0 = true := by decide
theorem mmFiber36Row_1_ok : mmFiber36RowCheck 1 = true := by decide
theorem mmFiber36Row_2_ok : mmFiber36RowCheck 2 = true := by decide
theorem mmFiber36Row_3_ok : mmFiber36RowCheck 3 = true := by decide
theorem mmFiber36Row_4_ok : mmFiber36RowCheck 4 = true := by decide
theorem mmFiber36Row_5_ok : mmFiber36RowCheck 5 = true := by decide
theorem mmFiber36Row_6_ok : mmFiber36RowCheck 6 = true := by decide
theorem mmFiber36Row_7_ok : mmFiber36RowCheck 7 = true := by decide
theorem mmFiber36Row_8_ok : mmFiber36RowCheck 8 = true := by decide
theorem mmFiber36Row_9_ok : mmFiber36RowCheck 9 = true := by decide
theorem mmFiber36Row_10_ok : mmFiber36RowCheck 10 = true := by decide
theorem mmFiber36Row_11_ok : mmFiber36RowCheck 11 = true := by decide
theorem mmFiber36Row_12_ok : mmFiber36RowCheck 12 = true := by decide
theorem mmFiber36Row_13_ok : mmFiber36RowCheck 13 = true := by decide
theorem mmFiber36Row_14_ok : mmFiber36RowCheck 14 = true := by decide
theorem mmFiber36Row_15_ok : mmFiber36RowCheck 15 = true := by decide
theorem mmFiber36Row_16_ok : mmFiber36RowCheck 16 = true := by decide
theorem mmFiber36Row_17_ok : mmFiber36RowCheck 17 = true := by decide
theorem mmFiber36Row_18_ok : mmFiber36RowCheck 18 = true := by decide
theorem mmFiber36Row_19_ok : mmFiber36RowCheck 19 = true := by decide
theorem mmFiber36Row_20_ok : mmFiber36RowCheck 20 = true := by decide
theorem mmFiber36Row_21_ok : mmFiber36RowCheck 21 = true := by decide
theorem mmFiber36Row_22_ok : mmFiber36RowCheck 22 = true := by decide
theorem mmFiber36Row_23_ok : mmFiber36RowCheck 23 = true := by decide
theorem mmFiber36Row_24_ok : mmFiber36RowCheck 24 = true := by decide
theorem mmFiber36Row_25_ok : mmFiber36RowCheck 25 = true := by decide
theorem mmFiber36Row_26_ok : mmFiber36RowCheck 26 = true := by decide
theorem mmFiber36Row_27_ok : mmFiber36RowCheck 27 = true := by decide
theorem mmFiber36Row_28_ok : mmFiber36RowCheck 28 = true := by decide
theorem mmFiber36Row_29_ok : mmFiber36RowCheck 29 = true := by decide
theorem mmFiber36Row_30_ok : mmFiber36RowCheck 30 = true := by decide
theorem mmFiber36Row_31_ok : mmFiber36RowCheck 31 = true := by decide
theorem mmFiber36Row_32_ok : mmFiber36RowCheck 32 = true := by decide
theorem mmFiber36Row_33_ok : mmFiber36RowCheck 33 = true := by decide
theorem mmFiber36Row_34_ok : mmFiber36RowCheck 34 = true := by decide
theorem mmFiber36Row_35_ok : mmFiber36RowCheck 35 = true := by decide
theorem mmFiber36Row_36_ok : mmFiber36RowCheck 36 = true := by decide
theorem mmFiber36Row_37_ok : mmFiber36RowCheck 37 = true := by decide
theorem mmFiber36Row_38_ok : mmFiber36RowCheck 38 = true := by decide
theorem mmFiber36Row_39_ok : mmFiber36RowCheck 39 = true := by decide
theorem mmFiber36Row_40_ok : mmFiber36RowCheck 40 = true := by decide
theorem mmFiber36Row_41_ok : mmFiber36RowCheck 41 = true := by decide
theorem mmFiber36Row_42_ok : mmFiber36RowCheck 42 = true := by decide
theorem mmFiber36Row_43_ok : mmFiber36RowCheck 43 = true := by decide
theorem mmFiber36Row_44_ok : mmFiber36RowCheck 44 = true := by decide
theorem mmFiber36Row_45_ok : mmFiber36RowCheck 45 = true := by decide
theorem mmFiber36Row_46_ok : mmFiber36RowCheck 46 = true := by decide
theorem mmFiber36Row_47_ok : mmFiber36RowCheck 47 = true := by decide
theorem mmFiber36Row_48_ok : mmFiber36RowCheck 48 = true := by decide
theorem mmFiber36Row_49_ok : mmFiber36RowCheck 49 = true := by decide
theorem mmFiber36Row_50_ok : mmFiber36RowCheck 50 = true := by decide
theorem mmFiber36Row_51_ok : mmFiber36RowCheck 51 = true := by decide
theorem mmFiber36Row_52_ok : mmFiber36RowCheck 52 = true := by decide
theorem mmFiber36Row_53_ok : mmFiber36RowCheck 53 = true := by decide
theorem mmFiber36Row_54_ok : mmFiber36RowCheck 54 = true := by decide
theorem mmFiber36Row_55_ok : mmFiber36RowCheck 55 = true := by decide
theorem mmFiber36Row_56_ok : mmFiber36RowCheck 56 = true := by decide
theorem mmFiber36Row_57_ok : mmFiber36RowCheck 57 = true := by decide
theorem mmFiber36Row_58_ok : mmFiber36RowCheck 58 = true := by decide
theorem mmFiber36Row_59_ok : mmFiber36RowCheck 59 = true := by decide
theorem mmFiber36Row_60_ok : mmFiber36RowCheck 60 = true := by decide
theorem mmFiber36Row_61_ok : mmFiber36RowCheck 61 = true := by decide
theorem mmFiber36Row_62_ok : mmFiber36RowCheck 62 = true := by decide
theorem mmFiber36Row_63_ok : mmFiber36RowCheck 63 = true := by decide

def mmFiber36ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber36Rows mmMaxParentDepth (listGetD mmFiber36Expected i 0) == 320

theorem mmFiber36Parent_0_ok : mmFiber36ParentCheck 0 = true := by decide
theorem mmFiber36Parent_1_ok : mmFiber36ParentCheck 1 = true := by decide
theorem mmFiber36Parent_2_ok : mmFiber36ParentCheck 2 = true := by decide
theorem mmFiber36Parent_3_ok : mmFiber36ParentCheck 3 = true := by decide
theorem mmFiber36Parent_4_ok : mmFiber36ParentCheck 4 = true := by decide
theorem mmFiber36Parent_5_ok : mmFiber36ParentCheck 5 = true := by decide
theorem mmFiber36Parent_6_ok : mmFiber36ParentCheck 6 = true := by decide
theorem mmFiber36Parent_7_ok : mmFiber36ParentCheck 7 = true := by decide
theorem mmFiber36Parent_8_ok : mmFiber36ParentCheck 8 = true := by decide
theorem mmFiber36Parent_9_ok : mmFiber36ParentCheck 9 = true := by decide
theorem mmFiber36Parent_10_ok : mmFiber36ParentCheck 10 = true := by decide
theorem mmFiber36Parent_11_ok : mmFiber36ParentCheck 11 = true := by decide
theorem mmFiber36Parent_12_ok : mmFiber36ParentCheck 12 = true := by decide
theorem mmFiber36Parent_13_ok : mmFiber36ParentCheck 13 = true := by decide
theorem mmFiber36Parent_14_ok : mmFiber36ParentCheck 14 = true := by decide
theorem mmFiber36Parent_15_ok : mmFiber36ParentCheck 15 = true := by decide
theorem mmFiber36Parent_16_ok : mmFiber36ParentCheck 16 = true := by decide
theorem mmFiber36Parent_17_ok : mmFiber36ParentCheck 17 = true := by decide
theorem mmFiber36Parent_18_ok : mmFiber36ParentCheck 18 = true := by decide
theorem mmFiber36Parent_19_ok : mmFiber36ParentCheck 19 = true := by decide
theorem mmFiber36Parent_20_ok : mmFiber36ParentCheck 20 = true := by decide
theorem mmFiber36Parent_21_ok : mmFiber36ParentCheck 21 = true := by decide
theorem mmFiber36Parent_22_ok : mmFiber36ParentCheck 22 = true := by decide
theorem mmFiber36Parent_23_ok : mmFiber36ParentCheck 23 = true := by decide
theorem mmFiber36Parent_24_ok : mmFiber36ParentCheck 24 = true := by decide
theorem mmFiber36Parent_25_ok : mmFiber36ParentCheck 25 = true := by decide
theorem mmFiber36Parent_26_ok : mmFiber36ParentCheck 26 = true := by decide
theorem mmFiber36Parent_27_ok : mmFiber36ParentCheck 27 = true := by decide
theorem mmFiber36Parent_28_ok : mmFiber36ParentCheck 28 = true := by decide
theorem mmFiber36Parent_29_ok : mmFiber36ParentCheck 29 = true := by decide
theorem mmFiber36Parent_30_ok : mmFiber36ParentCheck 30 = true := by decide
theorem mmFiber36Parent_31_ok : mmFiber36ParentCheck 31 = true := by decide
theorem mmFiber36Parent_32_ok : mmFiber36ParentCheck 32 = true := by decide
theorem mmFiber36Parent_33_ok : mmFiber36ParentCheck 33 = true := by decide
theorem mmFiber36Parent_34_ok : mmFiber36ParentCheck 34 = true := by decide
theorem mmFiber36Parent_35_ok : mmFiber36ParentCheck 35 = true := by decide
theorem mmFiber36Parent_36_ok : mmFiber36ParentCheck 36 = true := by decide
theorem mmFiber36Parent_37_ok : mmFiber36ParentCheck 37 = true := by decide
theorem mmFiber36Parent_38_ok : mmFiber36ParentCheck 38 = true := by decide
theorem mmFiber36Parent_39_ok : mmFiber36ParentCheck 39 = true := by decide
theorem mmFiber36Parent_40_ok : mmFiber36ParentCheck 40 = true := by decide
theorem mmFiber36Parent_41_ok : mmFiber36ParentCheck 41 = true := by decide
theorem mmFiber36Parent_42_ok : mmFiber36ParentCheck 42 = true := by decide
theorem mmFiber36Parent_43_ok : mmFiber36ParentCheck 43 = true := by decide
theorem mmFiber36Parent_44_ok : mmFiber36ParentCheck 44 = true := by decide
theorem mmFiber36Parent_45_ok : mmFiber36ParentCheck 45 = true := by decide
theorem mmFiber36Parent_46_ok : mmFiber36ParentCheck 46 = true := by decide
theorem mmFiber36Parent_47_ok : mmFiber36ParentCheck 47 = true := by decide
theorem mmFiber36Parent_48_ok : mmFiber36ParentCheck 48 = true := by decide
theorem mmFiber36Parent_49_ok : mmFiber36ParentCheck 49 = true := by decide
theorem mmFiber36Parent_50_ok : mmFiber36ParentCheck 50 = true := by decide
theorem mmFiber36Parent_51_ok : mmFiber36ParentCheck 51 = true := by decide
theorem mmFiber36Parent_52_ok : mmFiber36ParentCheck 52 = true := by decide
theorem mmFiber36Parent_53_ok : mmFiber36ParentCheck 53 = true := by decide
theorem mmFiber36Parent_54_ok : mmFiber36ParentCheck 54 = true := by decide
theorem mmFiber36Parent_55_ok : mmFiber36ParentCheck 55 = true := by decide
theorem mmFiber36Parent_56_ok : mmFiber36ParentCheck 56 = true := by decide
theorem mmFiber36Parent_57_ok : mmFiber36ParentCheck 57 = true := by decide
theorem mmFiber36Parent_58_ok : mmFiber36ParentCheck 58 = true := by decide
theorem mmFiber36Parent_59_ok : mmFiber36ParentCheck 59 = true := by decide
theorem mmFiber36Parent_60_ok : mmFiber36ParentCheck 60 = true := by decide
theorem mmFiber36Parent_61_ok : mmFiber36ParentCheck 61 = true := by decide
theorem mmFiber36Parent_62_ok : mmFiber36ParentCheck 62 = true := by decide
theorem mmFiber36Parent_63_ok : mmFiber36ParentCheck 63 = true := by decide

def mmFiber36CertificateAudit : Bool :=
  mmFiber36SourcesCheck &&
    mmFiber36RowCheck 0 &&
    mmFiber36RowCheck 1 &&
    mmFiber36RowCheck 2 &&
    mmFiber36RowCheck 3 &&
    mmFiber36RowCheck 4 &&
    mmFiber36RowCheck 5 &&
    mmFiber36RowCheck 6 &&
    mmFiber36RowCheck 7 &&
    mmFiber36RowCheck 8 &&
    mmFiber36RowCheck 9 &&
    mmFiber36RowCheck 10 &&
    mmFiber36RowCheck 11 &&
    mmFiber36RowCheck 12 &&
    mmFiber36RowCheck 13 &&
    mmFiber36RowCheck 14 &&
    mmFiber36RowCheck 15 &&
    mmFiber36RowCheck 16 &&
    mmFiber36RowCheck 17 &&
    mmFiber36RowCheck 18 &&
    mmFiber36RowCheck 19 &&
    mmFiber36RowCheck 20 &&
    mmFiber36RowCheck 21 &&
    mmFiber36RowCheck 22 &&
    mmFiber36RowCheck 23 &&
    mmFiber36RowCheck 24 &&
    mmFiber36RowCheck 25 &&
    mmFiber36RowCheck 26 &&
    mmFiber36RowCheck 27 &&
    mmFiber36RowCheck 28 &&
    mmFiber36RowCheck 29 &&
    mmFiber36RowCheck 30 &&
    mmFiber36RowCheck 31 &&
    mmFiber36RowCheck 32 &&
    mmFiber36RowCheck 33 &&
    mmFiber36RowCheck 34 &&
    mmFiber36RowCheck 35 &&
    mmFiber36RowCheck 36 &&
    mmFiber36RowCheck 37 &&
    mmFiber36RowCheck 38 &&
    mmFiber36RowCheck 39 &&
    mmFiber36RowCheck 40 &&
    mmFiber36RowCheck 41 &&
    mmFiber36RowCheck 42 &&
    mmFiber36RowCheck 43 &&
    mmFiber36RowCheck 44 &&
    mmFiber36RowCheck 45 &&
    mmFiber36RowCheck 46 &&
    mmFiber36RowCheck 47 &&
    mmFiber36RowCheck 48 &&
    mmFiber36RowCheck 49 &&
    mmFiber36RowCheck 50 &&
    mmFiber36RowCheck 51 &&
    mmFiber36RowCheck 52 &&
    mmFiber36RowCheck 53 &&
    mmFiber36RowCheck 54 &&
    mmFiber36RowCheck 55 &&
    mmFiber36RowCheck 56 &&
    mmFiber36RowCheck 57 &&
    mmFiber36RowCheck 58 &&
    mmFiber36RowCheck 59 &&
    mmFiber36RowCheck 60 &&
    mmFiber36RowCheck 61 &&
    mmFiber36RowCheck 62 &&
    mmFiber36RowCheck 63 &&
    mmFiber36ParentCheck 0 &&
    mmFiber36ParentCheck 1 &&
    mmFiber36ParentCheck 2 &&
    mmFiber36ParentCheck 3 &&
    mmFiber36ParentCheck 4 &&
    mmFiber36ParentCheck 5 &&
    mmFiber36ParentCheck 6 &&
    mmFiber36ParentCheck 7 &&
    mmFiber36ParentCheck 8 &&
    mmFiber36ParentCheck 9 &&
    mmFiber36ParentCheck 10 &&
    mmFiber36ParentCheck 11 &&
    mmFiber36ParentCheck 12 &&
    mmFiber36ParentCheck 13 &&
    mmFiber36ParentCheck 14 &&
    mmFiber36ParentCheck 15 &&
    mmFiber36ParentCheck 16 &&
    mmFiber36ParentCheck 17 &&
    mmFiber36ParentCheck 18 &&
    mmFiber36ParentCheck 19 &&
    mmFiber36ParentCheck 20 &&
    mmFiber36ParentCheck 21 &&
    mmFiber36ParentCheck 22 &&
    mmFiber36ParentCheck 23 &&
    mmFiber36ParentCheck 24 &&
    mmFiber36ParentCheck 25 &&
    mmFiber36ParentCheck 26 &&
    mmFiber36ParentCheck 27 &&
    mmFiber36ParentCheck 28 &&
    mmFiber36ParentCheck 29 &&
    mmFiber36ParentCheck 30 &&
    mmFiber36ParentCheck 31 &&
    mmFiber36ParentCheck 32 &&
    mmFiber36ParentCheck 33 &&
    mmFiber36ParentCheck 34 &&
    mmFiber36ParentCheck 35 &&
    mmFiber36ParentCheck 36 &&
    mmFiber36ParentCheck 37 &&
    mmFiber36ParentCheck 38 &&
    mmFiber36ParentCheck 39 &&
    mmFiber36ParentCheck 40 &&
    mmFiber36ParentCheck 41 &&
    mmFiber36ParentCheck 42 &&
    mmFiber36ParentCheck 43 &&
    mmFiber36ParentCheck 44 &&
    mmFiber36ParentCheck 45 &&
    mmFiber36ParentCheck 46 &&
    mmFiber36ParentCheck 47 &&
    mmFiber36ParentCheck 48 &&
    mmFiber36ParentCheck 49 &&
    mmFiber36ParentCheck 50 &&
    mmFiber36ParentCheck 51 &&
    mmFiber36ParentCheck 52 &&
    mmFiber36ParentCheck 53 &&
    mmFiber36ParentCheck 54 &&
    mmFiber36ParentCheck 55 &&
    mmFiber36ParentCheck 56 &&
    mmFiber36ParentCheck 57 &&
    mmFiber36ParentCheck 58 &&
    mmFiber36ParentCheck 59 &&
    mmFiber36ParentCheck 60 &&
    mmFiber36ParentCheck 61 &&
    mmFiber36ParentCheck 62 &&
    mmFiber36ParentCheck 63

theorem mmFiber36CertificateAudit_ok :
    mmFiber36CertificateAudit = true := by
  simp [mmFiber36CertificateAudit,
    mmFiber36SourcesCheck_ok,
    mmFiber36Row_0_ok,
    mmFiber36Row_1_ok,
    mmFiber36Row_2_ok,
    mmFiber36Row_3_ok,
    mmFiber36Row_4_ok,
    mmFiber36Row_5_ok,
    mmFiber36Row_6_ok,
    mmFiber36Row_7_ok,
    mmFiber36Row_8_ok,
    mmFiber36Row_9_ok,
    mmFiber36Row_10_ok,
    mmFiber36Row_11_ok,
    mmFiber36Row_12_ok,
    mmFiber36Row_13_ok,
    mmFiber36Row_14_ok,
    mmFiber36Row_15_ok,
    mmFiber36Row_16_ok,
    mmFiber36Row_17_ok,
    mmFiber36Row_18_ok,
    mmFiber36Row_19_ok,
    mmFiber36Row_20_ok,
    mmFiber36Row_21_ok,
    mmFiber36Row_22_ok,
    mmFiber36Row_23_ok,
    mmFiber36Row_24_ok,
    mmFiber36Row_25_ok,
    mmFiber36Row_26_ok,
    mmFiber36Row_27_ok,
    mmFiber36Row_28_ok,
    mmFiber36Row_29_ok,
    mmFiber36Row_30_ok,
    mmFiber36Row_31_ok,
    mmFiber36Row_32_ok,
    mmFiber36Row_33_ok,
    mmFiber36Row_34_ok,
    mmFiber36Row_35_ok,
    mmFiber36Row_36_ok,
    mmFiber36Row_37_ok,
    mmFiber36Row_38_ok,
    mmFiber36Row_39_ok,
    mmFiber36Row_40_ok,
    mmFiber36Row_41_ok,
    mmFiber36Row_42_ok,
    mmFiber36Row_43_ok,
    mmFiber36Row_44_ok,
    mmFiber36Row_45_ok,
    mmFiber36Row_46_ok,
    mmFiber36Row_47_ok,
    mmFiber36Row_48_ok,
    mmFiber36Row_49_ok,
    mmFiber36Row_50_ok,
    mmFiber36Row_51_ok,
    mmFiber36Row_52_ok,
    mmFiber36Row_53_ok,
    mmFiber36Row_54_ok,
    mmFiber36Row_55_ok,
    mmFiber36Row_56_ok,
    mmFiber36Row_57_ok,
    mmFiber36Row_58_ok,
    mmFiber36Row_59_ok,
    mmFiber36Row_60_ok,
    mmFiber36Row_61_ok,
    mmFiber36Row_62_ok,
    mmFiber36Row_63_ok,
    mmFiber36Parent_0_ok,
    mmFiber36Parent_1_ok,
    mmFiber36Parent_2_ok,
    mmFiber36Parent_3_ok,
    mmFiber36Parent_4_ok,
    mmFiber36Parent_5_ok,
    mmFiber36Parent_6_ok,
    mmFiber36Parent_7_ok,
    mmFiber36Parent_8_ok,
    mmFiber36Parent_9_ok,
    mmFiber36Parent_10_ok,
    mmFiber36Parent_11_ok,
    mmFiber36Parent_12_ok,
    mmFiber36Parent_13_ok,
    mmFiber36Parent_14_ok,
    mmFiber36Parent_15_ok,
    mmFiber36Parent_16_ok,
    mmFiber36Parent_17_ok,
    mmFiber36Parent_18_ok,
    mmFiber36Parent_19_ok,
    mmFiber36Parent_20_ok,
    mmFiber36Parent_21_ok,
    mmFiber36Parent_22_ok,
    mmFiber36Parent_23_ok,
    mmFiber36Parent_24_ok,
    mmFiber36Parent_25_ok,
    mmFiber36Parent_26_ok,
    mmFiber36Parent_27_ok,
    mmFiber36Parent_28_ok,
    mmFiber36Parent_29_ok,
    mmFiber36Parent_30_ok,
    mmFiber36Parent_31_ok,
    mmFiber36Parent_32_ok,
    mmFiber36Parent_33_ok,
    mmFiber36Parent_34_ok,
    mmFiber36Parent_35_ok,
    mmFiber36Parent_36_ok,
    mmFiber36Parent_37_ok,
    mmFiber36Parent_38_ok,
    mmFiber36Parent_39_ok,
    mmFiber36Parent_40_ok,
    mmFiber36Parent_41_ok,
    mmFiber36Parent_42_ok,
    mmFiber36Parent_43_ok,
    mmFiber36Parent_44_ok,
    mmFiber36Parent_45_ok,
    mmFiber36Parent_46_ok,
    mmFiber36Parent_47_ok,
    mmFiber36Parent_48_ok,
    mmFiber36Parent_49_ok,
    mmFiber36Parent_50_ok,
    mmFiber36Parent_51_ok,
    mmFiber36Parent_52_ok,
    mmFiber36Parent_53_ok,
    mmFiber36Parent_54_ok,
    mmFiber36Parent_55_ok,
    mmFiber36Parent_56_ok,
    mmFiber36Parent_57_ok,
    mmFiber36Parent_58_ok,
    mmFiber36Parent_59_ok,
    mmFiber36Parent_60_ok,
    mmFiber36Parent_61_ok,
    mmFiber36Parent_62_ok,
    mmFiber36Parent_63_ok]

def mmFiber37Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.b]

def mmFiber37Expected : List Nat :=
  [272, 273, 274, 275, 276, 277, 278, 279]

def mmFiber37Rows : List DirectChainParentRow :=
  [ directRow 272 272 54 112 54 112 default
  , directRow 273 272 54 113 54 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 274 272 54 114 54 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 275 273 54 115 54 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 276 272 55 120 54 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 277 273 55 121 54 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 278 274 55 122 54 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 279 275 55 123 54 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber37RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber37Rows i default

def mmFiber37SourcesCheck : Bool :=
  (mmFiber37Rows.map fun row => row.source) == mmFiber37Expected

theorem mmFiber37SourcesCheck_ok :
    mmFiber37SourcesCheck = true := by
  decide

def mmFiber37RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt i)

theorem mmFiber37Row_0_ok : mmFiber37RowCheck 0 = true := by decide
theorem mmFiber37Row_1_ok : mmFiber37RowCheck 1 = true := by decide
theorem mmFiber37Row_2_ok : mmFiber37RowCheck 2 = true := by decide
theorem mmFiber37Row_3_ok : mmFiber37RowCheck 3 = true := by decide
theorem mmFiber37Row_4_ok : mmFiber37RowCheck 4 = true := by decide
theorem mmFiber37Row_5_ok : mmFiber37RowCheck 5 = true := by decide
theorem mmFiber37Row_6_ok : mmFiber37RowCheck 6 = true := by decide
theorem mmFiber37Row_7_ok : mmFiber37RowCheck 7 = true := by decide

def mmFiber37ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber37Rows mmMaxParentDepth (listGetD mmFiber37Expected i 0) == 272

theorem mmFiber37Parent_0_ok : mmFiber37ParentCheck 0 = true := by decide
theorem mmFiber37Parent_1_ok : mmFiber37ParentCheck 1 = true := by decide
theorem mmFiber37Parent_2_ok : mmFiber37ParentCheck 2 = true := by decide
theorem mmFiber37Parent_3_ok : mmFiber37ParentCheck 3 = true := by decide
theorem mmFiber37Parent_4_ok : mmFiber37ParentCheck 4 = true := by decide
theorem mmFiber37Parent_5_ok : mmFiber37ParentCheck 5 = true := by decide
theorem mmFiber37Parent_6_ok : mmFiber37ParentCheck 6 = true := by decide
theorem mmFiber37Parent_7_ok : mmFiber37ParentCheck 7 = true := by decide

def mmFiber37CertificateAudit : Bool :=
  mmFiber37SourcesCheck &&
    mmFiber37RowCheck 0 &&
    mmFiber37RowCheck 1 &&
    mmFiber37RowCheck 2 &&
    mmFiber37RowCheck 3 &&
    mmFiber37RowCheck 4 &&
    mmFiber37RowCheck 5 &&
    mmFiber37RowCheck 6 &&
    mmFiber37RowCheck 7 &&
    mmFiber37ParentCheck 0 &&
    mmFiber37ParentCheck 1 &&
    mmFiber37ParentCheck 2 &&
    mmFiber37ParentCheck 3 &&
    mmFiber37ParentCheck 4 &&
    mmFiber37ParentCheck 5 &&
    mmFiber37ParentCheck 6 &&
    mmFiber37ParentCheck 7

theorem mmFiber37CertificateAudit_ok :
    mmFiber37CertificateAudit = true := by
  simp [mmFiber37CertificateAudit,
    mmFiber37SourcesCheck_ok,
    mmFiber37Row_0_ok,
    mmFiber37Row_1_ok,
    mmFiber37Row_2_ok,
    mmFiber37Row_3_ok,
    mmFiber37Row_4_ok,
    mmFiber37Row_5_ok,
    mmFiber37Row_6_ok,
    mmFiber37Row_7_ok,
    mmFiber37Parent_0_ok,
    mmFiber37Parent_1_ok,
    mmFiber37Parent_2_ok,
    mmFiber37Parent_3_ok,
    mmFiber37Parent_4_ok,
    mmFiber37Parent_5_ok,
    mmFiber37Parent_6_ok,
    mmFiber37Parent_7_ok]

def mmFiber38Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.p]

def mmFiber38Expected : List Nat :=
  []

def mmFiber38Rows : List DirectChainParentRow :=
  []

def mmFiber38RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber38Rows i default

def mmFiber38SourcesCheck : Bool :=
  (mmFiber38Rows.map fun row => row.source) == mmFiber38Expected

theorem mmFiber38SourcesCheck_ok :
    mmFiber38SourcesCheck = true := by
  decide

def mmFiber38RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber38Key mmFiber38Expected (mmFiber38RowAt i)

def mmFiber38ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber38Rows mmMaxParentDepth (listGetD mmFiber38Expected i 0) == 0

def mmFiber38CertificateAudit : Bool :=
  mmFiber38SourcesCheck

theorem mmFiber38CertificateAudit_ok :
    mmFiber38CertificateAudit = true := by
  simp [mmFiber38CertificateAudit,
    mmFiber38SourcesCheck_ok]

def mmFiber39Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.r]

def mmFiber39Expected : List Nat :=
  []

def mmFiber39Rows : List DirectChainParentRow :=
  []

def mmFiber39RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber39Rows i default

def mmFiber39SourcesCheck : Bool :=
  (mmFiber39Rows.map fun row => row.source) == mmFiber39Expected

theorem mmFiber39SourcesCheck_ok :
    mmFiber39SourcesCheck = true := by
  decide

def mmFiber39RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber39Key mmFiber39Expected (mmFiber39RowAt i)

def mmFiber39ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber39Rows mmMaxParentDepth (listGetD mmFiber39Expected i 0) == 0

def mmFiber39CertificateAudit : Bool :=
  mmFiber39SourcesCheck

theorem mmFiber39CertificateAudit_ok :
    mmFiber39CertificateAudit = true := by
  simp [mmFiber39CertificateAudit,
    mmFiber39SourcesCheck_ok]

def mmFiber40Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.b]

def mmFiber40Expected : List Nat :=
  []

def mmFiber40Rows : List DirectChainParentRow :=
  []

def mmFiber40RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber40Rows i default

def mmFiber40SourcesCheck : Bool :=
  (mmFiber40Rows.map fun row => row.source) == mmFiber40Expected

theorem mmFiber40SourcesCheck_ok :
    mmFiber40SourcesCheck = true := by
  decide

def mmFiber40RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber40Key mmFiber40Expected (mmFiber40RowAt i)

def mmFiber40ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber40Rows mmMaxParentDepth (listGetD mmFiber40Expected i 0) == 0

def mmFiber40CertificateAudit : Bool :=
  mmFiber40SourcesCheck

theorem mmFiber40CertificateAudit_ok :
    mmFiber40CertificateAudit = true := by
  simp [mmFiber40CertificateAudit,
    mmFiber40SourcesCheck_ok]

def mmFiber41Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.p]

def mmFiber41Expected : List Nat :=
  []

def mmFiber41Rows : List DirectChainParentRow :=
  []

def mmFiber41RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber41Rows i default

def mmFiber41SourcesCheck : Bool :=
  (mmFiber41Rows.map fun row => row.source) == mmFiber41Expected

theorem mmFiber41SourcesCheck_ok :
    mmFiber41SourcesCheck = true := by
  decide

def mmFiber41RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber41Key mmFiber41Expected (mmFiber41RowAt i)

def mmFiber41ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber41Rows mmMaxParentDepth (listGetD mmFiber41Expected i 0) == 0

def mmFiber41CertificateAudit : Bool :=
  mmFiber41SourcesCheck

theorem mmFiber41CertificateAudit_ok :
    mmFiber41CertificateAudit = true := by
  simp [mmFiber41CertificateAudit,
    mmFiber41SourcesCheck_ok]

def mmFiber42Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.r]

def mmFiber42Expected : List Nat :=
  []

def mmFiber42Rows : List DirectChainParentRow :=
  []

def mmFiber42RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber42Rows i default

def mmFiber42SourcesCheck : Bool :=
  (mmFiber42Rows.map fun row => row.source) == mmFiber42Expected

theorem mmFiber42SourcesCheck_ok :
    mmFiber42SourcesCheck = true := by
  decide

def mmFiber42RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber42Key mmFiber42Expected (mmFiber42RowAt i)

def mmFiber42ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber42Rows mmMaxParentDepth (listGetD mmFiber42Expected i 0) == 0

def mmFiber42CertificateAudit : Bool :=
  mmFiber42SourcesCheck

theorem mmFiber42CertificateAudit_ok :
    mmFiber42CertificateAudit = true := by
  simp [mmFiber42CertificateAudit,
    mmFiber42SourcesCheck_ok]

def mmFiber43Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.b]

def mmFiber43Expected : List Nat :=
  [760, 761, 762, 763, 764, 765, 766, 767]

def mmFiber43Rows : List DirectChainParentRow :=
  [ directRow 760 760 152 84 152 84 default
  , directRow 761 760 152 85 152 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 762 760 152 86 152 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 763 761 152 87 152 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 764 760 153 92 152 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 765 761 153 93 152 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 766 762 153 94 152 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 767 763 153 95 152 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber43RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber43Rows i default

def mmFiber43SourcesCheck : Bool :=
  (mmFiber43Rows.map fun row => row.source) == mmFiber43Expected

theorem mmFiber43SourcesCheck_ok :
    mmFiber43SourcesCheck = true := by
  decide

def mmFiber43RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt i)

theorem mmFiber43Row_0_ok : mmFiber43RowCheck 0 = true := by decide
theorem mmFiber43Row_1_ok : mmFiber43RowCheck 1 = true := by decide
theorem mmFiber43Row_2_ok : mmFiber43RowCheck 2 = true := by decide
theorem mmFiber43Row_3_ok : mmFiber43RowCheck 3 = true := by decide
theorem mmFiber43Row_4_ok : mmFiber43RowCheck 4 = true := by decide
theorem mmFiber43Row_5_ok : mmFiber43RowCheck 5 = true := by decide
theorem mmFiber43Row_6_ok : mmFiber43RowCheck 6 = true := by decide
theorem mmFiber43Row_7_ok : mmFiber43RowCheck 7 = true := by decide

def mmFiber43ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber43Rows mmMaxParentDepth (listGetD mmFiber43Expected i 0) == 760

theorem mmFiber43Parent_0_ok : mmFiber43ParentCheck 0 = true := by decide
theorem mmFiber43Parent_1_ok : mmFiber43ParentCheck 1 = true := by decide
theorem mmFiber43Parent_2_ok : mmFiber43ParentCheck 2 = true := by decide
theorem mmFiber43Parent_3_ok : mmFiber43ParentCheck 3 = true := by decide
theorem mmFiber43Parent_4_ok : mmFiber43ParentCheck 4 = true := by decide
theorem mmFiber43Parent_5_ok : mmFiber43ParentCheck 5 = true := by decide
theorem mmFiber43Parent_6_ok : mmFiber43ParentCheck 6 = true := by decide
theorem mmFiber43Parent_7_ok : mmFiber43ParentCheck 7 = true := by decide

def mmFiber43CertificateAudit : Bool :=
  mmFiber43SourcesCheck &&
    mmFiber43RowCheck 0 &&
    mmFiber43RowCheck 1 &&
    mmFiber43RowCheck 2 &&
    mmFiber43RowCheck 3 &&
    mmFiber43RowCheck 4 &&
    mmFiber43RowCheck 5 &&
    mmFiber43RowCheck 6 &&
    mmFiber43RowCheck 7 &&
    mmFiber43ParentCheck 0 &&
    mmFiber43ParentCheck 1 &&
    mmFiber43ParentCheck 2 &&
    mmFiber43ParentCheck 3 &&
    mmFiber43ParentCheck 4 &&
    mmFiber43ParentCheck 5 &&
    mmFiber43ParentCheck 6 &&
    mmFiber43ParentCheck 7

theorem mmFiber43CertificateAudit_ok :
    mmFiber43CertificateAudit = true := by
  simp [mmFiber43CertificateAudit,
    mmFiber43SourcesCheck_ok,
    mmFiber43Row_0_ok,
    mmFiber43Row_1_ok,
    mmFiber43Row_2_ok,
    mmFiber43Row_3_ok,
    mmFiber43Row_4_ok,
    mmFiber43Row_5_ok,
    mmFiber43Row_6_ok,
    mmFiber43Row_7_ok,
    mmFiber43Parent_0_ok,
    mmFiber43Parent_1_ok,
    mmFiber43Parent_2_ok,
    mmFiber43Parent_3_ok,
    mmFiber43Parent_4_ok,
    mmFiber43Parent_5_ok,
    mmFiber43Parent_6_ok,
    mmFiber43Parent_7_ok]

def mmFiber44Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.p]

def mmFiber44Expected : List Nat :=
  [440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]

def mmFiber44Rows : List DirectChainParentRow :=
  [ directRow 440 440 88 80 88 80 default
  , directRow 441 440 88 81 88 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 442 440 88 82 88 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 443 441 88 83 88 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 444 442 88 100 88 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 445 447 88 101 88 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 446 441 88 102 88 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 447 440 88 103 88 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 448 440 89 88 88 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 449 441 89 89 88 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 450 442 89 90 88 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 451 443 89 91 88 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 452 444 89 108 88 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 453 445 89 109 88 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 454 446 89 110 88 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 455 447 89 111 88 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 456 440 90 16 88 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 457 441 90 17 88 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 458 442 90 18 88 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 459 443 90 19 88 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 460 456 90 32 90 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 461 457 90 33 90 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 462 446 90 34 88 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 463 447 90 35 88 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 464 448 91 24 89 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 465 449 91 25 89 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 466 450 91 26 89 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 467 451 91 27 89 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 468 464 91 40 91 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 469 465 91 41 91 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 470 454 91 42 89 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 471 455 91 43 89 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 528 544 108 132 110 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 529 545 108 133 110 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 530 462 108 134 90 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 531 463 108 135 90 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 532 458 108 180 90 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 533 535 108 181 108 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 534 457 108 182 90 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 535 456 108 183 90 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 536 552 109 140 111 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 537 553 109 141 111 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 538 554 109 142 111 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 539 536 109 143 109 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 540 536 109 188 109 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 541 537 109 189 109 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 542 558 109 190 111 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 543 559 109 191 111 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 544 448 110 64 89 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 545 449 110 65 89 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 546 450 110 66 89 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 547 451 110 67 89 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 548 452 110 116 89 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 549 453 110 117 89 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 550 454 110 118 89 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 551 455 110 119 89 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 552 440 111 72 88 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 553 441 111 73 88 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 554 442 111 74 88 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 555 443 111 75 88 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 556 444 111 124 88 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 557 445 111 125 88 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 558 446 111 126 88 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 559 447 111 127 88 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mmFiber44RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber44Rows i default

def mmFiber44SourcesCheck : Bool :=
  (mmFiber44Rows.map fun row => row.source) == mmFiber44Expected

theorem mmFiber44SourcesCheck_ok :
    mmFiber44SourcesCheck = true := by
  decide

def mmFiber44RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt i)

theorem mmFiber44Row_0_ok : mmFiber44RowCheck 0 = true := by decide
theorem mmFiber44Row_1_ok : mmFiber44RowCheck 1 = true := by decide
theorem mmFiber44Row_2_ok : mmFiber44RowCheck 2 = true := by decide
theorem mmFiber44Row_3_ok : mmFiber44RowCheck 3 = true := by decide
theorem mmFiber44Row_4_ok : mmFiber44RowCheck 4 = true := by decide
theorem mmFiber44Row_5_ok : mmFiber44RowCheck 5 = true := by decide
theorem mmFiber44Row_6_ok : mmFiber44RowCheck 6 = true := by decide
theorem mmFiber44Row_7_ok : mmFiber44RowCheck 7 = true := by decide
theorem mmFiber44Row_8_ok : mmFiber44RowCheck 8 = true := by decide
theorem mmFiber44Row_9_ok : mmFiber44RowCheck 9 = true := by decide
theorem mmFiber44Row_10_ok : mmFiber44RowCheck 10 = true := by decide
theorem mmFiber44Row_11_ok : mmFiber44RowCheck 11 = true := by decide
theorem mmFiber44Row_12_ok : mmFiber44RowCheck 12 = true := by decide
theorem mmFiber44Row_13_ok : mmFiber44RowCheck 13 = true := by decide
theorem mmFiber44Row_14_ok : mmFiber44RowCheck 14 = true := by decide
theorem mmFiber44Row_15_ok : mmFiber44RowCheck 15 = true := by decide
theorem mmFiber44Row_16_ok : mmFiber44RowCheck 16 = true := by decide
theorem mmFiber44Row_17_ok : mmFiber44RowCheck 17 = true := by decide
theorem mmFiber44Row_18_ok : mmFiber44RowCheck 18 = true := by decide
theorem mmFiber44Row_19_ok : mmFiber44RowCheck 19 = true := by decide
theorem mmFiber44Row_20_ok : mmFiber44RowCheck 20 = true := by decide
theorem mmFiber44Row_21_ok : mmFiber44RowCheck 21 = true := by decide
theorem mmFiber44Row_22_ok : mmFiber44RowCheck 22 = true := by decide
theorem mmFiber44Row_23_ok : mmFiber44RowCheck 23 = true := by decide
theorem mmFiber44Row_24_ok : mmFiber44RowCheck 24 = true := by decide
theorem mmFiber44Row_25_ok : mmFiber44RowCheck 25 = true := by decide
theorem mmFiber44Row_26_ok : mmFiber44RowCheck 26 = true := by decide
theorem mmFiber44Row_27_ok : mmFiber44RowCheck 27 = true := by decide
theorem mmFiber44Row_28_ok : mmFiber44RowCheck 28 = true := by decide
theorem mmFiber44Row_29_ok : mmFiber44RowCheck 29 = true := by decide
theorem mmFiber44Row_30_ok : mmFiber44RowCheck 30 = true := by decide
theorem mmFiber44Row_31_ok : mmFiber44RowCheck 31 = true := by decide
theorem mmFiber44Row_32_ok : mmFiber44RowCheck 32 = true := by decide
theorem mmFiber44Row_33_ok : mmFiber44RowCheck 33 = true := by decide
theorem mmFiber44Row_34_ok : mmFiber44RowCheck 34 = true := by decide
theorem mmFiber44Row_35_ok : mmFiber44RowCheck 35 = true := by decide
theorem mmFiber44Row_36_ok : mmFiber44RowCheck 36 = true := by decide
theorem mmFiber44Row_37_ok : mmFiber44RowCheck 37 = true := by decide
theorem mmFiber44Row_38_ok : mmFiber44RowCheck 38 = true := by decide
theorem mmFiber44Row_39_ok : mmFiber44RowCheck 39 = true := by decide
theorem mmFiber44Row_40_ok : mmFiber44RowCheck 40 = true := by decide
theorem mmFiber44Row_41_ok : mmFiber44RowCheck 41 = true := by decide
theorem mmFiber44Row_42_ok : mmFiber44RowCheck 42 = true := by decide
theorem mmFiber44Row_43_ok : mmFiber44RowCheck 43 = true := by decide
theorem mmFiber44Row_44_ok : mmFiber44RowCheck 44 = true := by decide
theorem mmFiber44Row_45_ok : mmFiber44RowCheck 45 = true := by decide
theorem mmFiber44Row_46_ok : mmFiber44RowCheck 46 = true := by decide
theorem mmFiber44Row_47_ok : mmFiber44RowCheck 47 = true := by decide
theorem mmFiber44Row_48_ok : mmFiber44RowCheck 48 = true := by decide
theorem mmFiber44Row_49_ok : mmFiber44RowCheck 49 = true := by decide
theorem mmFiber44Row_50_ok : mmFiber44RowCheck 50 = true := by decide
theorem mmFiber44Row_51_ok : mmFiber44RowCheck 51 = true := by decide
theorem mmFiber44Row_52_ok : mmFiber44RowCheck 52 = true := by decide
theorem mmFiber44Row_53_ok : mmFiber44RowCheck 53 = true := by decide
theorem mmFiber44Row_54_ok : mmFiber44RowCheck 54 = true := by decide
theorem mmFiber44Row_55_ok : mmFiber44RowCheck 55 = true := by decide
theorem mmFiber44Row_56_ok : mmFiber44RowCheck 56 = true := by decide
theorem mmFiber44Row_57_ok : mmFiber44RowCheck 57 = true := by decide
theorem mmFiber44Row_58_ok : mmFiber44RowCheck 58 = true := by decide
theorem mmFiber44Row_59_ok : mmFiber44RowCheck 59 = true := by decide
theorem mmFiber44Row_60_ok : mmFiber44RowCheck 60 = true := by decide
theorem mmFiber44Row_61_ok : mmFiber44RowCheck 61 = true := by decide
theorem mmFiber44Row_62_ok : mmFiber44RowCheck 62 = true := by decide
theorem mmFiber44Row_63_ok : mmFiber44RowCheck 63 = true := by decide

def mmFiber44ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber44Rows mmMaxParentDepth (listGetD mmFiber44Expected i 0) == 440

theorem mmFiber44Parent_0_ok : mmFiber44ParentCheck 0 = true := by decide
theorem mmFiber44Parent_1_ok : mmFiber44ParentCheck 1 = true := by decide
theorem mmFiber44Parent_2_ok : mmFiber44ParentCheck 2 = true := by decide
theorem mmFiber44Parent_3_ok : mmFiber44ParentCheck 3 = true := by decide
theorem mmFiber44Parent_4_ok : mmFiber44ParentCheck 4 = true := by decide
theorem mmFiber44Parent_5_ok : mmFiber44ParentCheck 5 = true := by decide
theorem mmFiber44Parent_6_ok : mmFiber44ParentCheck 6 = true := by decide
theorem mmFiber44Parent_7_ok : mmFiber44ParentCheck 7 = true := by decide
theorem mmFiber44Parent_8_ok : mmFiber44ParentCheck 8 = true := by decide
theorem mmFiber44Parent_9_ok : mmFiber44ParentCheck 9 = true := by decide
theorem mmFiber44Parent_10_ok : mmFiber44ParentCheck 10 = true := by decide
theorem mmFiber44Parent_11_ok : mmFiber44ParentCheck 11 = true := by decide
theorem mmFiber44Parent_12_ok : mmFiber44ParentCheck 12 = true := by decide
theorem mmFiber44Parent_13_ok : mmFiber44ParentCheck 13 = true := by decide
theorem mmFiber44Parent_14_ok : mmFiber44ParentCheck 14 = true := by decide
theorem mmFiber44Parent_15_ok : mmFiber44ParentCheck 15 = true := by decide
theorem mmFiber44Parent_16_ok : mmFiber44ParentCheck 16 = true := by decide
theorem mmFiber44Parent_17_ok : mmFiber44ParentCheck 17 = true := by decide
theorem mmFiber44Parent_18_ok : mmFiber44ParentCheck 18 = true := by decide
theorem mmFiber44Parent_19_ok : mmFiber44ParentCheck 19 = true := by decide
theorem mmFiber44Parent_20_ok : mmFiber44ParentCheck 20 = true := by decide
theorem mmFiber44Parent_21_ok : mmFiber44ParentCheck 21 = true := by decide
theorem mmFiber44Parent_22_ok : mmFiber44ParentCheck 22 = true := by decide
theorem mmFiber44Parent_23_ok : mmFiber44ParentCheck 23 = true := by decide
theorem mmFiber44Parent_24_ok : mmFiber44ParentCheck 24 = true := by decide
theorem mmFiber44Parent_25_ok : mmFiber44ParentCheck 25 = true := by decide
theorem mmFiber44Parent_26_ok : mmFiber44ParentCheck 26 = true := by decide
theorem mmFiber44Parent_27_ok : mmFiber44ParentCheck 27 = true := by decide
theorem mmFiber44Parent_28_ok : mmFiber44ParentCheck 28 = true := by decide
theorem mmFiber44Parent_29_ok : mmFiber44ParentCheck 29 = true := by decide
theorem mmFiber44Parent_30_ok : mmFiber44ParentCheck 30 = true := by decide
theorem mmFiber44Parent_31_ok : mmFiber44ParentCheck 31 = true := by decide
theorem mmFiber44Parent_32_ok : mmFiber44ParentCheck 32 = true := by decide
theorem mmFiber44Parent_33_ok : mmFiber44ParentCheck 33 = true := by decide
theorem mmFiber44Parent_34_ok : mmFiber44ParentCheck 34 = true := by decide
theorem mmFiber44Parent_35_ok : mmFiber44ParentCheck 35 = true := by decide
theorem mmFiber44Parent_36_ok : mmFiber44ParentCheck 36 = true := by decide
theorem mmFiber44Parent_37_ok : mmFiber44ParentCheck 37 = true := by decide
theorem mmFiber44Parent_38_ok : mmFiber44ParentCheck 38 = true := by decide
theorem mmFiber44Parent_39_ok : mmFiber44ParentCheck 39 = true := by decide
theorem mmFiber44Parent_40_ok : mmFiber44ParentCheck 40 = true := by decide
theorem mmFiber44Parent_41_ok : mmFiber44ParentCheck 41 = true := by decide
theorem mmFiber44Parent_42_ok : mmFiber44ParentCheck 42 = true := by decide
theorem mmFiber44Parent_43_ok : mmFiber44ParentCheck 43 = true := by decide
theorem mmFiber44Parent_44_ok : mmFiber44ParentCheck 44 = true := by decide
theorem mmFiber44Parent_45_ok : mmFiber44ParentCheck 45 = true := by decide
theorem mmFiber44Parent_46_ok : mmFiber44ParentCheck 46 = true := by decide
theorem mmFiber44Parent_47_ok : mmFiber44ParentCheck 47 = true := by decide
theorem mmFiber44Parent_48_ok : mmFiber44ParentCheck 48 = true := by decide
theorem mmFiber44Parent_49_ok : mmFiber44ParentCheck 49 = true := by decide
theorem mmFiber44Parent_50_ok : mmFiber44ParentCheck 50 = true := by decide
theorem mmFiber44Parent_51_ok : mmFiber44ParentCheck 51 = true := by decide
theorem mmFiber44Parent_52_ok : mmFiber44ParentCheck 52 = true := by decide
theorem mmFiber44Parent_53_ok : mmFiber44ParentCheck 53 = true := by decide
theorem mmFiber44Parent_54_ok : mmFiber44ParentCheck 54 = true := by decide
theorem mmFiber44Parent_55_ok : mmFiber44ParentCheck 55 = true := by decide
theorem mmFiber44Parent_56_ok : mmFiber44ParentCheck 56 = true := by decide
theorem mmFiber44Parent_57_ok : mmFiber44ParentCheck 57 = true := by decide
theorem mmFiber44Parent_58_ok : mmFiber44ParentCheck 58 = true := by decide
theorem mmFiber44Parent_59_ok : mmFiber44ParentCheck 59 = true := by decide
theorem mmFiber44Parent_60_ok : mmFiber44ParentCheck 60 = true := by decide
theorem mmFiber44Parent_61_ok : mmFiber44ParentCheck 61 = true := by decide
theorem mmFiber44Parent_62_ok : mmFiber44ParentCheck 62 = true := by decide
theorem mmFiber44Parent_63_ok : mmFiber44ParentCheck 63 = true := by decide

def mmFiber44CertificateAudit : Bool :=
  mmFiber44SourcesCheck &&
    mmFiber44RowCheck 0 &&
    mmFiber44RowCheck 1 &&
    mmFiber44RowCheck 2 &&
    mmFiber44RowCheck 3 &&
    mmFiber44RowCheck 4 &&
    mmFiber44RowCheck 5 &&
    mmFiber44RowCheck 6 &&
    mmFiber44RowCheck 7 &&
    mmFiber44RowCheck 8 &&
    mmFiber44RowCheck 9 &&
    mmFiber44RowCheck 10 &&
    mmFiber44RowCheck 11 &&
    mmFiber44RowCheck 12 &&
    mmFiber44RowCheck 13 &&
    mmFiber44RowCheck 14 &&
    mmFiber44RowCheck 15 &&
    mmFiber44RowCheck 16 &&
    mmFiber44RowCheck 17 &&
    mmFiber44RowCheck 18 &&
    mmFiber44RowCheck 19 &&
    mmFiber44RowCheck 20 &&
    mmFiber44RowCheck 21 &&
    mmFiber44RowCheck 22 &&
    mmFiber44RowCheck 23 &&
    mmFiber44RowCheck 24 &&
    mmFiber44RowCheck 25 &&
    mmFiber44RowCheck 26 &&
    mmFiber44RowCheck 27 &&
    mmFiber44RowCheck 28 &&
    mmFiber44RowCheck 29 &&
    mmFiber44RowCheck 30 &&
    mmFiber44RowCheck 31 &&
    mmFiber44RowCheck 32 &&
    mmFiber44RowCheck 33 &&
    mmFiber44RowCheck 34 &&
    mmFiber44RowCheck 35 &&
    mmFiber44RowCheck 36 &&
    mmFiber44RowCheck 37 &&
    mmFiber44RowCheck 38 &&
    mmFiber44RowCheck 39 &&
    mmFiber44RowCheck 40 &&
    mmFiber44RowCheck 41 &&
    mmFiber44RowCheck 42 &&
    mmFiber44RowCheck 43 &&
    mmFiber44RowCheck 44 &&
    mmFiber44RowCheck 45 &&
    mmFiber44RowCheck 46 &&
    mmFiber44RowCheck 47 &&
    mmFiber44RowCheck 48 &&
    mmFiber44RowCheck 49 &&
    mmFiber44RowCheck 50 &&
    mmFiber44RowCheck 51 &&
    mmFiber44RowCheck 52 &&
    mmFiber44RowCheck 53 &&
    mmFiber44RowCheck 54 &&
    mmFiber44RowCheck 55 &&
    mmFiber44RowCheck 56 &&
    mmFiber44RowCheck 57 &&
    mmFiber44RowCheck 58 &&
    mmFiber44RowCheck 59 &&
    mmFiber44RowCheck 60 &&
    mmFiber44RowCheck 61 &&
    mmFiber44RowCheck 62 &&
    mmFiber44RowCheck 63 &&
    mmFiber44ParentCheck 0 &&
    mmFiber44ParentCheck 1 &&
    mmFiber44ParentCheck 2 &&
    mmFiber44ParentCheck 3 &&
    mmFiber44ParentCheck 4 &&
    mmFiber44ParentCheck 5 &&
    mmFiber44ParentCheck 6 &&
    mmFiber44ParentCheck 7 &&
    mmFiber44ParentCheck 8 &&
    mmFiber44ParentCheck 9 &&
    mmFiber44ParentCheck 10 &&
    mmFiber44ParentCheck 11 &&
    mmFiber44ParentCheck 12 &&
    mmFiber44ParentCheck 13 &&
    mmFiber44ParentCheck 14 &&
    mmFiber44ParentCheck 15 &&
    mmFiber44ParentCheck 16 &&
    mmFiber44ParentCheck 17 &&
    mmFiber44ParentCheck 18 &&
    mmFiber44ParentCheck 19 &&
    mmFiber44ParentCheck 20 &&
    mmFiber44ParentCheck 21 &&
    mmFiber44ParentCheck 22 &&
    mmFiber44ParentCheck 23 &&
    mmFiber44ParentCheck 24 &&
    mmFiber44ParentCheck 25 &&
    mmFiber44ParentCheck 26 &&
    mmFiber44ParentCheck 27 &&
    mmFiber44ParentCheck 28 &&
    mmFiber44ParentCheck 29 &&
    mmFiber44ParentCheck 30 &&
    mmFiber44ParentCheck 31 &&
    mmFiber44ParentCheck 32 &&
    mmFiber44ParentCheck 33 &&
    mmFiber44ParentCheck 34 &&
    mmFiber44ParentCheck 35 &&
    mmFiber44ParentCheck 36 &&
    mmFiber44ParentCheck 37 &&
    mmFiber44ParentCheck 38 &&
    mmFiber44ParentCheck 39 &&
    mmFiber44ParentCheck 40 &&
    mmFiber44ParentCheck 41 &&
    mmFiber44ParentCheck 42 &&
    mmFiber44ParentCheck 43 &&
    mmFiber44ParentCheck 44 &&
    mmFiber44ParentCheck 45 &&
    mmFiber44ParentCheck 46 &&
    mmFiber44ParentCheck 47 &&
    mmFiber44ParentCheck 48 &&
    mmFiber44ParentCheck 49 &&
    mmFiber44ParentCheck 50 &&
    mmFiber44ParentCheck 51 &&
    mmFiber44ParentCheck 52 &&
    mmFiber44ParentCheck 53 &&
    mmFiber44ParentCheck 54 &&
    mmFiber44ParentCheck 55 &&
    mmFiber44ParentCheck 56 &&
    mmFiber44ParentCheck 57 &&
    mmFiber44ParentCheck 58 &&
    mmFiber44ParentCheck 59 &&
    mmFiber44ParentCheck 60 &&
    mmFiber44ParentCheck 61 &&
    mmFiber44ParentCheck 62 &&
    mmFiber44ParentCheck 63

theorem mmFiber44CertificateAudit_ok :
    mmFiber44CertificateAudit = true := by
  simp [mmFiber44CertificateAudit,
    mmFiber44SourcesCheck_ok,
    mmFiber44Row_0_ok,
    mmFiber44Row_1_ok,
    mmFiber44Row_2_ok,
    mmFiber44Row_3_ok,
    mmFiber44Row_4_ok,
    mmFiber44Row_5_ok,
    mmFiber44Row_6_ok,
    mmFiber44Row_7_ok,
    mmFiber44Row_8_ok,
    mmFiber44Row_9_ok,
    mmFiber44Row_10_ok,
    mmFiber44Row_11_ok,
    mmFiber44Row_12_ok,
    mmFiber44Row_13_ok,
    mmFiber44Row_14_ok,
    mmFiber44Row_15_ok,
    mmFiber44Row_16_ok,
    mmFiber44Row_17_ok,
    mmFiber44Row_18_ok,
    mmFiber44Row_19_ok,
    mmFiber44Row_20_ok,
    mmFiber44Row_21_ok,
    mmFiber44Row_22_ok,
    mmFiber44Row_23_ok,
    mmFiber44Row_24_ok,
    mmFiber44Row_25_ok,
    mmFiber44Row_26_ok,
    mmFiber44Row_27_ok,
    mmFiber44Row_28_ok,
    mmFiber44Row_29_ok,
    mmFiber44Row_30_ok,
    mmFiber44Row_31_ok,
    mmFiber44Row_32_ok,
    mmFiber44Row_33_ok,
    mmFiber44Row_34_ok,
    mmFiber44Row_35_ok,
    mmFiber44Row_36_ok,
    mmFiber44Row_37_ok,
    mmFiber44Row_38_ok,
    mmFiber44Row_39_ok,
    mmFiber44Row_40_ok,
    mmFiber44Row_41_ok,
    mmFiber44Row_42_ok,
    mmFiber44Row_43_ok,
    mmFiber44Row_44_ok,
    mmFiber44Row_45_ok,
    mmFiber44Row_46_ok,
    mmFiber44Row_47_ok,
    mmFiber44Row_48_ok,
    mmFiber44Row_49_ok,
    mmFiber44Row_50_ok,
    mmFiber44Row_51_ok,
    mmFiber44Row_52_ok,
    mmFiber44Row_53_ok,
    mmFiber44Row_54_ok,
    mmFiber44Row_55_ok,
    mmFiber44Row_56_ok,
    mmFiber44Row_57_ok,
    mmFiber44Row_58_ok,
    mmFiber44Row_59_ok,
    mmFiber44Row_60_ok,
    mmFiber44Row_61_ok,
    mmFiber44Row_62_ok,
    mmFiber44Row_63_ok,
    mmFiber44Parent_0_ok,
    mmFiber44Parent_1_ok,
    mmFiber44Parent_2_ok,
    mmFiber44Parent_3_ok,
    mmFiber44Parent_4_ok,
    mmFiber44Parent_5_ok,
    mmFiber44Parent_6_ok,
    mmFiber44Parent_7_ok,
    mmFiber44Parent_8_ok,
    mmFiber44Parent_9_ok,
    mmFiber44Parent_10_ok,
    mmFiber44Parent_11_ok,
    mmFiber44Parent_12_ok,
    mmFiber44Parent_13_ok,
    mmFiber44Parent_14_ok,
    mmFiber44Parent_15_ok,
    mmFiber44Parent_16_ok,
    mmFiber44Parent_17_ok,
    mmFiber44Parent_18_ok,
    mmFiber44Parent_19_ok,
    mmFiber44Parent_20_ok,
    mmFiber44Parent_21_ok,
    mmFiber44Parent_22_ok,
    mmFiber44Parent_23_ok,
    mmFiber44Parent_24_ok,
    mmFiber44Parent_25_ok,
    mmFiber44Parent_26_ok,
    mmFiber44Parent_27_ok,
    mmFiber44Parent_28_ok,
    mmFiber44Parent_29_ok,
    mmFiber44Parent_30_ok,
    mmFiber44Parent_31_ok,
    mmFiber44Parent_32_ok,
    mmFiber44Parent_33_ok,
    mmFiber44Parent_34_ok,
    mmFiber44Parent_35_ok,
    mmFiber44Parent_36_ok,
    mmFiber44Parent_37_ok,
    mmFiber44Parent_38_ok,
    mmFiber44Parent_39_ok,
    mmFiber44Parent_40_ok,
    mmFiber44Parent_41_ok,
    mmFiber44Parent_42_ok,
    mmFiber44Parent_43_ok,
    mmFiber44Parent_44_ok,
    mmFiber44Parent_45_ok,
    mmFiber44Parent_46_ok,
    mmFiber44Parent_47_ok,
    mmFiber44Parent_48_ok,
    mmFiber44Parent_49_ok,
    mmFiber44Parent_50_ok,
    mmFiber44Parent_51_ok,
    mmFiber44Parent_52_ok,
    mmFiber44Parent_53_ok,
    mmFiber44Parent_54_ok,
    mmFiber44Parent_55_ok,
    mmFiber44Parent_56_ok,
    mmFiber44Parent_57_ok,
    mmFiber44Parent_58_ok,
    mmFiber44Parent_59_ok,
    mmFiber44Parent_60_ok,
    mmFiber44Parent_61_ok,
    mmFiber44Parent_62_ok,
    mmFiber44Parent_63_ok]

def mmFiber45Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.r]

def mmFiber45Expected : List Nat :=
  [640, 641, 642, 643, 644, 645, 646, 647]

def mmFiber45Rows : List DirectChainParentRow :=
  [ directRow 640 640 128 84 128 84 default
  , directRow 641 640 128 85 128 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 642 640 128 86 128 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 643 641 128 87 128 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 644 640 129 92 128 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 645 641 129 93 128 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 646 642 129 94 128 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 647 643 129 95 128 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber45RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber45Rows i default

def mmFiber45SourcesCheck : Bool :=
  (mmFiber45Rows.map fun row => row.source) == mmFiber45Expected

theorem mmFiber45SourcesCheck_ok :
    mmFiber45SourcesCheck = true := by
  decide

def mmFiber45RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt i)

theorem mmFiber45Row_0_ok : mmFiber45RowCheck 0 = true := by decide
theorem mmFiber45Row_1_ok : mmFiber45RowCheck 1 = true := by decide
theorem mmFiber45Row_2_ok : mmFiber45RowCheck 2 = true := by decide
theorem mmFiber45Row_3_ok : mmFiber45RowCheck 3 = true := by decide
theorem mmFiber45Row_4_ok : mmFiber45RowCheck 4 = true := by decide
theorem mmFiber45Row_5_ok : mmFiber45RowCheck 5 = true := by decide
theorem mmFiber45Row_6_ok : mmFiber45RowCheck 6 = true := by decide
theorem mmFiber45Row_7_ok : mmFiber45RowCheck 7 = true := by decide

def mmFiber45ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber45Rows mmMaxParentDepth (listGetD mmFiber45Expected i 0) == 640

theorem mmFiber45Parent_0_ok : mmFiber45ParentCheck 0 = true := by decide
theorem mmFiber45Parent_1_ok : mmFiber45ParentCheck 1 = true := by decide
theorem mmFiber45Parent_2_ok : mmFiber45ParentCheck 2 = true := by decide
theorem mmFiber45Parent_3_ok : mmFiber45ParentCheck 3 = true := by decide
theorem mmFiber45Parent_4_ok : mmFiber45ParentCheck 4 = true := by decide
theorem mmFiber45Parent_5_ok : mmFiber45ParentCheck 5 = true := by decide
theorem mmFiber45Parent_6_ok : mmFiber45ParentCheck 6 = true := by decide
theorem mmFiber45Parent_7_ok : mmFiber45ParentCheck 7 = true := by decide

def mmFiber45CertificateAudit : Bool :=
  mmFiber45SourcesCheck &&
    mmFiber45RowCheck 0 &&
    mmFiber45RowCheck 1 &&
    mmFiber45RowCheck 2 &&
    mmFiber45RowCheck 3 &&
    mmFiber45RowCheck 4 &&
    mmFiber45RowCheck 5 &&
    mmFiber45RowCheck 6 &&
    mmFiber45RowCheck 7 &&
    mmFiber45ParentCheck 0 &&
    mmFiber45ParentCheck 1 &&
    mmFiber45ParentCheck 2 &&
    mmFiber45ParentCheck 3 &&
    mmFiber45ParentCheck 4 &&
    mmFiber45ParentCheck 5 &&
    mmFiber45ParentCheck 6 &&
    mmFiber45ParentCheck 7

theorem mmFiber45CertificateAudit_ok :
    mmFiber45CertificateAudit = true := by
  simp [mmFiber45CertificateAudit,
    mmFiber45SourcesCheck_ok,
    mmFiber45Row_0_ok,
    mmFiber45Row_1_ok,
    mmFiber45Row_2_ok,
    mmFiber45Row_3_ok,
    mmFiber45Row_4_ok,
    mmFiber45Row_5_ok,
    mmFiber45Row_6_ok,
    mmFiber45Row_7_ok,
    mmFiber45Parent_0_ok,
    mmFiber45Parent_1_ok,
    mmFiber45Parent_2_ok,
    mmFiber45Parent_3_ok,
    mmFiber45Parent_4_ok,
    mmFiber45Parent_5_ok,
    mmFiber45Parent_6_ok,
    mmFiber45Parent_7_ok]

def mmFiber46Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.b]

def mmFiber46Expected : List Nat :=
  []

def mmFiber46Rows : List DirectChainParentRow :=
  []

def mmFiber46RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber46Rows i default

def mmFiber46SourcesCheck : Bool :=
  (mmFiber46Rows.map fun row => row.source) == mmFiber46Expected

theorem mmFiber46SourcesCheck_ok :
    mmFiber46SourcesCheck = true := by
  decide

def mmFiber46RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber46Key mmFiber46Expected (mmFiber46RowAt i)

def mmFiber46ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber46Rows mmMaxParentDepth (listGetD mmFiber46Expected i 0) == 0

def mmFiber46CertificateAudit : Bool :=
  mmFiber46SourcesCheck

theorem mmFiber46CertificateAudit_ok :
    mmFiber46CertificateAudit = true := by
  simp [mmFiber46CertificateAudit,
    mmFiber46SourcesCheck_ok]

def mmFiber47Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.p]

def mmFiber47Expected : List Nat :=
  [192, 193, 194, 195, 196, 197, 198, 199]

def mmFiber47Rows : List DirectChainParentRow :=
  [ directRow 192 192 38 112 38 112 default
  , directRow 193 192 38 113 38 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 194 192 38 114 38 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 195 193 38 115 38 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 196 192 39 120 38 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 197 193 39 121 38 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 198 194 39 122 38 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 199 195 39 123 38 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def mmFiber47RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber47Rows i default

def mmFiber47SourcesCheck : Bool :=
  (mmFiber47Rows.map fun row => row.source) == mmFiber47Expected

theorem mmFiber47SourcesCheck_ok :
    mmFiber47SourcesCheck = true := by
  decide

def mmFiber47RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt i)

theorem mmFiber47Row_0_ok : mmFiber47RowCheck 0 = true := by decide
theorem mmFiber47Row_1_ok : mmFiber47RowCheck 1 = true := by decide
theorem mmFiber47Row_2_ok : mmFiber47RowCheck 2 = true := by decide
theorem mmFiber47Row_3_ok : mmFiber47RowCheck 3 = true := by decide
theorem mmFiber47Row_4_ok : mmFiber47RowCheck 4 = true := by decide
theorem mmFiber47Row_5_ok : mmFiber47RowCheck 5 = true := by decide
theorem mmFiber47Row_6_ok : mmFiber47RowCheck 6 = true := by decide
theorem mmFiber47Row_7_ok : mmFiber47RowCheck 7 = true := by decide

def mmFiber47ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber47Rows mmMaxParentDepth (listGetD mmFiber47Expected i 0) == 192

theorem mmFiber47Parent_0_ok : mmFiber47ParentCheck 0 = true := by decide
theorem mmFiber47Parent_1_ok : mmFiber47ParentCheck 1 = true := by decide
theorem mmFiber47Parent_2_ok : mmFiber47ParentCheck 2 = true := by decide
theorem mmFiber47Parent_3_ok : mmFiber47ParentCheck 3 = true := by decide
theorem mmFiber47Parent_4_ok : mmFiber47ParentCheck 4 = true := by decide
theorem mmFiber47Parent_5_ok : mmFiber47ParentCheck 5 = true := by decide
theorem mmFiber47Parent_6_ok : mmFiber47ParentCheck 6 = true := by decide
theorem mmFiber47Parent_7_ok : mmFiber47ParentCheck 7 = true := by decide

def mmFiber47CertificateAudit : Bool :=
  mmFiber47SourcesCheck &&
    mmFiber47RowCheck 0 &&
    mmFiber47RowCheck 1 &&
    mmFiber47RowCheck 2 &&
    mmFiber47RowCheck 3 &&
    mmFiber47RowCheck 4 &&
    mmFiber47RowCheck 5 &&
    mmFiber47RowCheck 6 &&
    mmFiber47RowCheck 7 &&
    mmFiber47ParentCheck 0 &&
    mmFiber47ParentCheck 1 &&
    mmFiber47ParentCheck 2 &&
    mmFiber47ParentCheck 3 &&
    mmFiber47ParentCheck 4 &&
    mmFiber47ParentCheck 5 &&
    mmFiber47ParentCheck 6 &&
    mmFiber47ParentCheck 7

theorem mmFiber47CertificateAudit_ok :
    mmFiber47CertificateAudit = true := by
  simp [mmFiber47CertificateAudit,
    mmFiber47SourcesCheck_ok,
    mmFiber47Row_0_ok,
    mmFiber47Row_1_ok,
    mmFiber47Row_2_ok,
    mmFiber47Row_3_ok,
    mmFiber47Row_4_ok,
    mmFiber47Row_5_ok,
    mmFiber47Row_6_ok,
    mmFiber47Row_7_ok,
    mmFiber47Parent_0_ok,
    mmFiber47Parent_1_ok,
    mmFiber47Parent_2_ok,
    mmFiber47Parent_3_ok,
    mmFiber47Parent_4_ok,
    mmFiber47Parent_5_ok,
    mmFiber47Parent_6_ok,
    mmFiber47Parent_7_ok]

def mmFiber48Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.r]

def mmFiber48Expected : List Nat :=
  []

def mmFiber48Rows : List DirectChainParentRow :=
  []

def mmFiber48RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber48Rows i default

def mmFiber48SourcesCheck : Bool :=
  (mmFiber48Rows.map fun row => row.source) == mmFiber48Expected

theorem mmFiber48SourcesCheck_ok :
    mmFiber48SourcesCheck = true := by
  decide

def mmFiber48RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber48Key mmFiber48Expected (mmFiber48RowAt i)

def mmFiber48ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber48Rows mmMaxParentDepth (listGetD mmFiber48Expected i 0) == 0

def mmFiber48CertificateAudit : Bool :=
  mmFiber48SourcesCheck

theorem mmFiber48CertificateAudit_ok :
    mmFiber48CertificateAudit = true := by
  simp [mmFiber48CertificateAudit,
    mmFiber48SourcesCheck_ok]

def mmFiber49Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.b]

def mmFiber49Expected : List Nat :=
  [720, 721, 722, 723, 724, 725, 726, 727]

def mmFiber49Rows : List DirectChainParentRow :=
  [ directRow 720 720 144 84 144 84 default
  , directRow 721 720 144 85 144 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 722 720 144 86 144 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 723 721 144 87 144 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 724 720 145 92 144 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 725 721 145 93 144 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 726 722 145 94 144 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 727 723 145 95 144 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber49RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber49Rows i default

def mmFiber49SourcesCheck : Bool :=
  (mmFiber49Rows.map fun row => row.source) == mmFiber49Expected

theorem mmFiber49SourcesCheck_ok :
    mmFiber49SourcesCheck = true := by
  decide

def mmFiber49RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt i)

theorem mmFiber49Row_0_ok : mmFiber49RowCheck 0 = true := by decide
theorem mmFiber49Row_1_ok : mmFiber49RowCheck 1 = true := by decide
theorem mmFiber49Row_2_ok : mmFiber49RowCheck 2 = true := by decide
theorem mmFiber49Row_3_ok : mmFiber49RowCheck 3 = true := by decide
theorem mmFiber49Row_4_ok : mmFiber49RowCheck 4 = true := by decide
theorem mmFiber49Row_5_ok : mmFiber49RowCheck 5 = true := by decide
theorem mmFiber49Row_6_ok : mmFiber49RowCheck 6 = true := by decide
theorem mmFiber49Row_7_ok : mmFiber49RowCheck 7 = true := by decide

def mmFiber49ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber49Rows mmMaxParentDepth (listGetD mmFiber49Expected i 0) == 720

theorem mmFiber49Parent_0_ok : mmFiber49ParentCheck 0 = true := by decide
theorem mmFiber49Parent_1_ok : mmFiber49ParentCheck 1 = true := by decide
theorem mmFiber49Parent_2_ok : mmFiber49ParentCheck 2 = true := by decide
theorem mmFiber49Parent_3_ok : mmFiber49ParentCheck 3 = true := by decide
theorem mmFiber49Parent_4_ok : mmFiber49ParentCheck 4 = true := by decide
theorem mmFiber49Parent_5_ok : mmFiber49ParentCheck 5 = true := by decide
theorem mmFiber49Parent_6_ok : mmFiber49ParentCheck 6 = true := by decide
theorem mmFiber49Parent_7_ok : mmFiber49ParentCheck 7 = true := by decide

def mmFiber49CertificateAudit : Bool :=
  mmFiber49SourcesCheck &&
    mmFiber49RowCheck 0 &&
    mmFiber49RowCheck 1 &&
    mmFiber49RowCheck 2 &&
    mmFiber49RowCheck 3 &&
    mmFiber49RowCheck 4 &&
    mmFiber49RowCheck 5 &&
    mmFiber49RowCheck 6 &&
    mmFiber49RowCheck 7 &&
    mmFiber49ParentCheck 0 &&
    mmFiber49ParentCheck 1 &&
    mmFiber49ParentCheck 2 &&
    mmFiber49ParentCheck 3 &&
    mmFiber49ParentCheck 4 &&
    mmFiber49ParentCheck 5 &&
    mmFiber49ParentCheck 6 &&
    mmFiber49ParentCheck 7

theorem mmFiber49CertificateAudit_ok :
    mmFiber49CertificateAudit = true := by
  simp [mmFiber49CertificateAudit,
    mmFiber49SourcesCheck_ok,
    mmFiber49Row_0_ok,
    mmFiber49Row_1_ok,
    mmFiber49Row_2_ok,
    mmFiber49Row_3_ok,
    mmFiber49Row_4_ok,
    mmFiber49Row_5_ok,
    mmFiber49Row_6_ok,
    mmFiber49Row_7_ok,
    mmFiber49Parent_0_ok,
    mmFiber49Parent_1_ok,
    mmFiber49Parent_2_ok,
    mmFiber49Parent_3_ok,
    mmFiber49Parent_4_ok,
    mmFiber49Parent_5_ok,
    mmFiber49Parent_6_ok,
    mmFiber49Parent_7_ok]

def mmFiber50Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.p]

def mmFiber50Expected : List Nat :=
  [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519]

def mmFiber50Rows : List DirectChainParentRow :=
  [ directRow 400 400 80 80 80 80 default
  , directRow 401 400 80 81 80 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 402 400 80 82 80 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 403 401 80 83 80 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 404 402 80 100 80 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 405 407 80 101 80 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 406 401 80 102 80 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 407 400 80 103 80 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 408 400 81 88 80 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 409 401 81 89 80 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 410 402 81 90 80 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 411 403 81 91 80 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 412 404 81 108 80 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 413 405 81 109 80 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 414 406 81 110 80 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 415 407 81 111 80 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 416 400 82 16 80 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 417 401 82 17 80 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 418 402 82 18 80 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 419 403 82 19 80 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 420 416 82 32 82 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 421 417 82 33 82 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 422 406 82 34 80 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 423 407 82 35 80 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 424 408 83 24 81 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 425 409 83 25 81 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 426 410 83 26 81 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 427 411 83 27 81 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 428 424 83 40 83 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 429 425 83 41 83 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 430 414 83 42 81 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 431 415 83 43 81 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 488 504 100 132 102 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 489 505 100 133 102 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 490 422 100 134 82 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 491 423 100 135 82 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 492 418 100 180 82 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 493 495 100 181 100 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 494 417 100 182 82 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 495 416 100 183 82 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 496 512 101 140 103 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 497 513 101 141 103 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 498 514 101 142 103 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 499 496 101 143 101 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 500 496 101 188 101 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 501 497 101 189 101 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 502 518 101 190 103 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 503 519 101 191 103 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 504 408 102 64 81 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 505 409 102 65 81 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 506 410 102 66 81 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 507 411 102 67 81 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 508 412 102 116 81 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 509 413 102 117 81 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 510 414 102 118 81 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 511 415 102 119 81 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 512 400 103 72 80 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 513 401 103 73 80 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 514 402 103 74 80 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 515 403 103 75 80 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 516 404 103 124 80 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 517 405 103 125 80 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 518 406 103 126 80 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 519 407 103 127 80 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def mmFiber50RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber50Rows i default

def mmFiber50SourcesCheck : Bool :=
  (mmFiber50Rows.map fun row => row.source) == mmFiber50Expected

theorem mmFiber50SourcesCheck_ok :
    mmFiber50SourcesCheck = true := by
  decide

def mmFiber50RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt i)

theorem mmFiber50Row_0_ok : mmFiber50RowCheck 0 = true := by decide
theorem mmFiber50Row_1_ok : mmFiber50RowCheck 1 = true := by decide
theorem mmFiber50Row_2_ok : mmFiber50RowCheck 2 = true := by decide
theorem mmFiber50Row_3_ok : mmFiber50RowCheck 3 = true := by decide
theorem mmFiber50Row_4_ok : mmFiber50RowCheck 4 = true := by decide
theorem mmFiber50Row_5_ok : mmFiber50RowCheck 5 = true := by decide
theorem mmFiber50Row_6_ok : mmFiber50RowCheck 6 = true := by decide
theorem mmFiber50Row_7_ok : mmFiber50RowCheck 7 = true := by decide
theorem mmFiber50Row_8_ok : mmFiber50RowCheck 8 = true := by decide
theorem mmFiber50Row_9_ok : mmFiber50RowCheck 9 = true := by decide
theorem mmFiber50Row_10_ok : mmFiber50RowCheck 10 = true := by decide
theorem mmFiber50Row_11_ok : mmFiber50RowCheck 11 = true := by decide
theorem mmFiber50Row_12_ok : mmFiber50RowCheck 12 = true := by decide
theorem mmFiber50Row_13_ok : mmFiber50RowCheck 13 = true := by decide
theorem mmFiber50Row_14_ok : mmFiber50RowCheck 14 = true := by decide
theorem mmFiber50Row_15_ok : mmFiber50RowCheck 15 = true := by decide
theorem mmFiber50Row_16_ok : mmFiber50RowCheck 16 = true := by decide
theorem mmFiber50Row_17_ok : mmFiber50RowCheck 17 = true := by decide
theorem mmFiber50Row_18_ok : mmFiber50RowCheck 18 = true := by decide
theorem mmFiber50Row_19_ok : mmFiber50RowCheck 19 = true := by decide
theorem mmFiber50Row_20_ok : mmFiber50RowCheck 20 = true := by decide
theorem mmFiber50Row_21_ok : mmFiber50RowCheck 21 = true := by decide
theorem mmFiber50Row_22_ok : mmFiber50RowCheck 22 = true := by decide
theorem mmFiber50Row_23_ok : mmFiber50RowCheck 23 = true := by decide
theorem mmFiber50Row_24_ok : mmFiber50RowCheck 24 = true := by decide
theorem mmFiber50Row_25_ok : mmFiber50RowCheck 25 = true := by decide
theorem mmFiber50Row_26_ok : mmFiber50RowCheck 26 = true := by decide
theorem mmFiber50Row_27_ok : mmFiber50RowCheck 27 = true := by decide
theorem mmFiber50Row_28_ok : mmFiber50RowCheck 28 = true := by decide
theorem mmFiber50Row_29_ok : mmFiber50RowCheck 29 = true := by decide
theorem mmFiber50Row_30_ok : mmFiber50RowCheck 30 = true := by decide
theorem mmFiber50Row_31_ok : mmFiber50RowCheck 31 = true := by decide
theorem mmFiber50Row_32_ok : mmFiber50RowCheck 32 = true := by decide
theorem mmFiber50Row_33_ok : mmFiber50RowCheck 33 = true := by decide
theorem mmFiber50Row_34_ok : mmFiber50RowCheck 34 = true := by decide
theorem mmFiber50Row_35_ok : mmFiber50RowCheck 35 = true := by decide
theorem mmFiber50Row_36_ok : mmFiber50RowCheck 36 = true := by decide
theorem mmFiber50Row_37_ok : mmFiber50RowCheck 37 = true := by decide
theorem mmFiber50Row_38_ok : mmFiber50RowCheck 38 = true := by decide
theorem mmFiber50Row_39_ok : mmFiber50RowCheck 39 = true := by decide
theorem mmFiber50Row_40_ok : mmFiber50RowCheck 40 = true := by decide
theorem mmFiber50Row_41_ok : mmFiber50RowCheck 41 = true := by decide
theorem mmFiber50Row_42_ok : mmFiber50RowCheck 42 = true := by decide
theorem mmFiber50Row_43_ok : mmFiber50RowCheck 43 = true := by decide
theorem mmFiber50Row_44_ok : mmFiber50RowCheck 44 = true := by decide
theorem mmFiber50Row_45_ok : mmFiber50RowCheck 45 = true := by decide
theorem mmFiber50Row_46_ok : mmFiber50RowCheck 46 = true := by decide
theorem mmFiber50Row_47_ok : mmFiber50RowCheck 47 = true := by decide
theorem mmFiber50Row_48_ok : mmFiber50RowCheck 48 = true := by decide
theorem mmFiber50Row_49_ok : mmFiber50RowCheck 49 = true := by decide
theorem mmFiber50Row_50_ok : mmFiber50RowCheck 50 = true := by decide
theorem mmFiber50Row_51_ok : mmFiber50RowCheck 51 = true := by decide
theorem mmFiber50Row_52_ok : mmFiber50RowCheck 52 = true := by decide
theorem mmFiber50Row_53_ok : mmFiber50RowCheck 53 = true := by decide
theorem mmFiber50Row_54_ok : mmFiber50RowCheck 54 = true := by decide
theorem mmFiber50Row_55_ok : mmFiber50RowCheck 55 = true := by decide
theorem mmFiber50Row_56_ok : mmFiber50RowCheck 56 = true := by decide
theorem mmFiber50Row_57_ok : mmFiber50RowCheck 57 = true := by decide
theorem mmFiber50Row_58_ok : mmFiber50RowCheck 58 = true := by decide
theorem mmFiber50Row_59_ok : mmFiber50RowCheck 59 = true := by decide
theorem mmFiber50Row_60_ok : mmFiber50RowCheck 60 = true := by decide
theorem mmFiber50Row_61_ok : mmFiber50RowCheck 61 = true := by decide
theorem mmFiber50Row_62_ok : mmFiber50RowCheck 62 = true := by decide
theorem mmFiber50Row_63_ok : mmFiber50RowCheck 63 = true := by decide

def mmFiber50ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber50Rows mmMaxParentDepth (listGetD mmFiber50Expected i 0) == 400

theorem mmFiber50Parent_0_ok : mmFiber50ParentCheck 0 = true := by decide
theorem mmFiber50Parent_1_ok : mmFiber50ParentCheck 1 = true := by decide
theorem mmFiber50Parent_2_ok : mmFiber50ParentCheck 2 = true := by decide
theorem mmFiber50Parent_3_ok : mmFiber50ParentCheck 3 = true := by decide
theorem mmFiber50Parent_4_ok : mmFiber50ParentCheck 4 = true := by decide
theorem mmFiber50Parent_5_ok : mmFiber50ParentCheck 5 = true := by decide
theorem mmFiber50Parent_6_ok : mmFiber50ParentCheck 6 = true := by decide
theorem mmFiber50Parent_7_ok : mmFiber50ParentCheck 7 = true := by decide
theorem mmFiber50Parent_8_ok : mmFiber50ParentCheck 8 = true := by decide
theorem mmFiber50Parent_9_ok : mmFiber50ParentCheck 9 = true := by decide
theorem mmFiber50Parent_10_ok : mmFiber50ParentCheck 10 = true := by decide
theorem mmFiber50Parent_11_ok : mmFiber50ParentCheck 11 = true := by decide
theorem mmFiber50Parent_12_ok : mmFiber50ParentCheck 12 = true := by decide
theorem mmFiber50Parent_13_ok : mmFiber50ParentCheck 13 = true := by decide
theorem mmFiber50Parent_14_ok : mmFiber50ParentCheck 14 = true := by decide
theorem mmFiber50Parent_15_ok : mmFiber50ParentCheck 15 = true := by decide
theorem mmFiber50Parent_16_ok : mmFiber50ParentCheck 16 = true := by decide
theorem mmFiber50Parent_17_ok : mmFiber50ParentCheck 17 = true := by decide
theorem mmFiber50Parent_18_ok : mmFiber50ParentCheck 18 = true := by decide
theorem mmFiber50Parent_19_ok : mmFiber50ParentCheck 19 = true := by decide
theorem mmFiber50Parent_20_ok : mmFiber50ParentCheck 20 = true := by decide
theorem mmFiber50Parent_21_ok : mmFiber50ParentCheck 21 = true := by decide
theorem mmFiber50Parent_22_ok : mmFiber50ParentCheck 22 = true := by decide
theorem mmFiber50Parent_23_ok : mmFiber50ParentCheck 23 = true := by decide
theorem mmFiber50Parent_24_ok : mmFiber50ParentCheck 24 = true := by decide
theorem mmFiber50Parent_25_ok : mmFiber50ParentCheck 25 = true := by decide
theorem mmFiber50Parent_26_ok : mmFiber50ParentCheck 26 = true := by decide
theorem mmFiber50Parent_27_ok : mmFiber50ParentCheck 27 = true := by decide
theorem mmFiber50Parent_28_ok : mmFiber50ParentCheck 28 = true := by decide
theorem mmFiber50Parent_29_ok : mmFiber50ParentCheck 29 = true := by decide
theorem mmFiber50Parent_30_ok : mmFiber50ParentCheck 30 = true := by decide
theorem mmFiber50Parent_31_ok : mmFiber50ParentCheck 31 = true := by decide
theorem mmFiber50Parent_32_ok : mmFiber50ParentCheck 32 = true := by decide
theorem mmFiber50Parent_33_ok : mmFiber50ParentCheck 33 = true := by decide
theorem mmFiber50Parent_34_ok : mmFiber50ParentCheck 34 = true := by decide
theorem mmFiber50Parent_35_ok : mmFiber50ParentCheck 35 = true := by decide
theorem mmFiber50Parent_36_ok : mmFiber50ParentCheck 36 = true := by decide
theorem mmFiber50Parent_37_ok : mmFiber50ParentCheck 37 = true := by decide
theorem mmFiber50Parent_38_ok : mmFiber50ParentCheck 38 = true := by decide
theorem mmFiber50Parent_39_ok : mmFiber50ParentCheck 39 = true := by decide
theorem mmFiber50Parent_40_ok : mmFiber50ParentCheck 40 = true := by decide
theorem mmFiber50Parent_41_ok : mmFiber50ParentCheck 41 = true := by decide
theorem mmFiber50Parent_42_ok : mmFiber50ParentCheck 42 = true := by decide
theorem mmFiber50Parent_43_ok : mmFiber50ParentCheck 43 = true := by decide
theorem mmFiber50Parent_44_ok : mmFiber50ParentCheck 44 = true := by decide
theorem mmFiber50Parent_45_ok : mmFiber50ParentCheck 45 = true := by decide
theorem mmFiber50Parent_46_ok : mmFiber50ParentCheck 46 = true := by decide
theorem mmFiber50Parent_47_ok : mmFiber50ParentCheck 47 = true := by decide
theorem mmFiber50Parent_48_ok : mmFiber50ParentCheck 48 = true := by decide
theorem mmFiber50Parent_49_ok : mmFiber50ParentCheck 49 = true := by decide
theorem mmFiber50Parent_50_ok : mmFiber50ParentCheck 50 = true := by decide
theorem mmFiber50Parent_51_ok : mmFiber50ParentCheck 51 = true := by decide
theorem mmFiber50Parent_52_ok : mmFiber50ParentCheck 52 = true := by decide
theorem mmFiber50Parent_53_ok : mmFiber50ParentCheck 53 = true := by decide
theorem mmFiber50Parent_54_ok : mmFiber50ParentCheck 54 = true := by decide
theorem mmFiber50Parent_55_ok : mmFiber50ParentCheck 55 = true := by decide
theorem mmFiber50Parent_56_ok : mmFiber50ParentCheck 56 = true := by decide
theorem mmFiber50Parent_57_ok : mmFiber50ParentCheck 57 = true := by decide
theorem mmFiber50Parent_58_ok : mmFiber50ParentCheck 58 = true := by decide
theorem mmFiber50Parent_59_ok : mmFiber50ParentCheck 59 = true := by decide
theorem mmFiber50Parent_60_ok : mmFiber50ParentCheck 60 = true := by decide
theorem mmFiber50Parent_61_ok : mmFiber50ParentCheck 61 = true := by decide
theorem mmFiber50Parent_62_ok : mmFiber50ParentCheck 62 = true := by decide
theorem mmFiber50Parent_63_ok : mmFiber50ParentCheck 63 = true := by decide

def mmFiber50CertificateAudit : Bool :=
  mmFiber50SourcesCheck &&
    mmFiber50RowCheck 0 &&
    mmFiber50RowCheck 1 &&
    mmFiber50RowCheck 2 &&
    mmFiber50RowCheck 3 &&
    mmFiber50RowCheck 4 &&
    mmFiber50RowCheck 5 &&
    mmFiber50RowCheck 6 &&
    mmFiber50RowCheck 7 &&
    mmFiber50RowCheck 8 &&
    mmFiber50RowCheck 9 &&
    mmFiber50RowCheck 10 &&
    mmFiber50RowCheck 11 &&
    mmFiber50RowCheck 12 &&
    mmFiber50RowCheck 13 &&
    mmFiber50RowCheck 14 &&
    mmFiber50RowCheck 15 &&
    mmFiber50RowCheck 16 &&
    mmFiber50RowCheck 17 &&
    mmFiber50RowCheck 18 &&
    mmFiber50RowCheck 19 &&
    mmFiber50RowCheck 20 &&
    mmFiber50RowCheck 21 &&
    mmFiber50RowCheck 22 &&
    mmFiber50RowCheck 23 &&
    mmFiber50RowCheck 24 &&
    mmFiber50RowCheck 25 &&
    mmFiber50RowCheck 26 &&
    mmFiber50RowCheck 27 &&
    mmFiber50RowCheck 28 &&
    mmFiber50RowCheck 29 &&
    mmFiber50RowCheck 30 &&
    mmFiber50RowCheck 31 &&
    mmFiber50RowCheck 32 &&
    mmFiber50RowCheck 33 &&
    mmFiber50RowCheck 34 &&
    mmFiber50RowCheck 35 &&
    mmFiber50RowCheck 36 &&
    mmFiber50RowCheck 37 &&
    mmFiber50RowCheck 38 &&
    mmFiber50RowCheck 39 &&
    mmFiber50RowCheck 40 &&
    mmFiber50RowCheck 41 &&
    mmFiber50RowCheck 42 &&
    mmFiber50RowCheck 43 &&
    mmFiber50RowCheck 44 &&
    mmFiber50RowCheck 45 &&
    mmFiber50RowCheck 46 &&
    mmFiber50RowCheck 47 &&
    mmFiber50RowCheck 48 &&
    mmFiber50RowCheck 49 &&
    mmFiber50RowCheck 50 &&
    mmFiber50RowCheck 51 &&
    mmFiber50RowCheck 52 &&
    mmFiber50RowCheck 53 &&
    mmFiber50RowCheck 54 &&
    mmFiber50RowCheck 55 &&
    mmFiber50RowCheck 56 &&
    mmFiber50RowCheck 57 &&
    mmFiber50RowCheck 58 &&
    mmFiber50RowCheck 59 &&
    mmFiber50RowCheck 60 &&
    mmFiber50RowCheck 61 &&
    mmFiber50RowCheck 62 &&
    mmFiber50RowCheck 63 &&
    mmFiber50ParentCheck 0 &&
    mmFiber50ParentCheck 1 &&
    mmFiber50ParentCheck 2 &&
    mmFiber50ParentCheck 3 &&
    mmFiber50ParentCheck 4 &&
    mmFiber50ParentCheck 5 &&
    mmFiber50ParentCheck 6 &&
    mmFiber50ParentCheck 7 &&
    mmFiber50ParentCheck 8 &&
    mmFiber50ParentCheck 9 &&
    mmFiber50ParentCheck 10 &&
    mmFiber50ParentCheck 11 &&
    mmFiber50ParentCheck 12 &&
    mmFiber50ParentCheck 13 &&
    mmFiber50ParentCheck 14 &&
    mmFiber50ParentCheck 15 &&
    mmFiber50ParentCheck 16 &&
    mmFiber50ParentCheck 17 &&
    mmFiber50ParentCheck 18 &&
    mmFiber50ParentCheck 19 &&
    mmFiber50ParentCheck 20 &&
    mmFiber50ParentCheck 21 &&
    mmFiber50ParentCheck 22 &&
    mmFiber50ParentCheck 23 &&
    mmFiber50ParentCheck 24 &&
    mmFiber50ParentCheck 25 &&
    mmFiber50ParentCheck 26 &&
    mmFiber50ParentCheck 27 &&
    mmFiber50ParentCheck 28 &&
    mmFiber50ParentCheck 29 &&
    mmFiber50ParentCheck 30 &&
    mmFiber50ParentCheck 31 &&
    mmFiber50ParentCheck 32 &&
    mmFiber50ParentCheck 33 &&
    mmFiber50ParentCheck 34 &&
    mmFiber50ParentCheck 35 &&
    mmFiber50ParentCheck 36 &&
    mmFiber50ParentCheck 37 &&
    mmFiber50ParentCheck 38 &&
    mmFiber50ParentCheck 39 &&
    mmFiber50ParentCheck 40 &&
    mmFiber50ParentCheck 41 &&
    mmFiber50ParentCheck 42 &&
    mmFiber50ParentCheck 43 &&
    mmFiber50ParentCheck 44 &&
    mmFiber50ParentCheck 45 &&
    mmFiber50ParentCheck 46 &&
    mmFiber50ParentCheck 47 &&
    mmFiber50ParentCheck 48 &&
    mmFiber50ParentCheck 49 &&
    mmFiber50ParentCheck 50 &&
    mmFiber50ParentCheck 51 &&
    mmFiber50ParentCheck 52 &&
    mmFiber50ParentCheck 53 &&
    mmFiber50ParentCheck 54 &&
    mmFiber50ParentCheck 55 &&
    mmFiber50ParentCheck 56 &&
    mmFiber50ParentCheck 57 &&
    mmFiber50ParentCheck 58 &&
    mmFiber50ParentCheck 59 &&
    mmFiber50ParentCheck 60 &&
    mmFiber50ParentCheck 61 &&
    mmFiber50ParentCheck 62 &&
    mmFiber50ParentCheck 63

theorem mmFiber50CertificateAudit_ok :
    mmFiber50CertificateAudit = true := by
  simp [mmFiber50CertificateAudit,
    mmFiber50SourcesCheck_ok,
    mmFiber50Row_0_ok,
    mmFiber50Row_1_ok,
    mmFiber50Row_2_ok,
    mmFiber50Row_3_ok,
    mmFiber50Row_4_ok,
    mmFiber50Row_5_ok,
    mmFiber50Row_6_ok,
    mmFiber50Row_7_ok,
    mmFiber50Row_8_ok,
    mmFiber50Row_9_ok,
    mmFiber50Row_10_ok,
    mmFiber50Row_11_ok,
    mmFiber50Row_12_ok,
    mmFiber50Row_13_ok,
    mmFiber50Row_14_ok,
    mmFiber50Row_15_ok,
    mmFiber50Row_16_ok,
    mmFiber50Row_17_ok,
    mmFiber50Row_18_ok,
    mmFiber50Row_19_ok,
    mmFiber50Row_20_ok,
    mmFiber50Row_21_ok,
    mmFiber50Row_22_ok,
    mmFiber50Row_23_ok,
    mmFiber50Row_24_ok,
    mmFiber50Row_25_ok,
    mmFiber50Row_26_ok,
    mmFiber50Row_27_ok,
    mmFiber50Row_28_ok,
    mmFiber50Row_29_ok,
    mmFiber50Row_30_ok,
    mmFiber50Row_31_ok,
    mmFiber50Row_32_ok,
    mmFiber50Row_33_ok,
    mmFiber50Row_34_ok,
    mmFiber50Row_35_ok,
    mmFiber50Row_36_ok,
    mmFiber50Row_37_ok,
    mmFiber50Row_38_ok,
    mmFiber50Row_39_ok,
    mmFiber50Row_40_ok,
    mmFiber50Row_41_ok,
    mmFiber50Row_42_ok,
    mmFiber50Row_43_ok,
    mmFiber50Row_44_ok,
    mmFiber50Row_45_ok,
    mmFiber50Row_46_ok,
    mmFiber50Row_47_ok,
    mmFiber50Row_48_ok,
    mmFiber50Row_49_ok,
    mmFiber50Row_50_ok,
    mmFiber50Row_51_ok,
    mmFiber50Row_52_ok,
    mmFiber50Row_53_ok,
    mmFiber50Row_54_ok,
    mmFiber50Row_55_ok,
    mmFiber50Row_56_ok,
    mmFiber50Row_57_ok,
    mmFiber50Row_58_ok,
    mmFiber50Row_59_ok,
    mmFiber50Row_60_ok,
    mmFiber50Row_61_ok,
    mmFiber50Row_62_ok,
    mmFiber50Row_63_ok,
    mmFiber50Parent_0_ok,
    mmFiber50Parent_1_ok,
    mmFiber50Parent_2_ok,
    mmFiber50Parent_3_ok,
    mmFiber50Parent_4_ok,
    mmFiber50Parent_5_ok,
    mmFiber50Parent_6_ok,
    mmFiber50Parent_7_ok,
    mmFiber50Parent_8_ok,
    mmFiber50Parent_9_ok,
    mmFiber50Parent_10_ok,
    mmFiber50Parent_11_ok,
    mmFiber50Parent_12_ok,
    mmFiber50Parent_13_ok,
    mmFiber50Parent_14_ok,
    mmFiber50Parent_15_ok,
    mmFiber50Parent_16_ok,
    mmFiber50Parent_17_ok,
    mmFiber50Parent_18_ok,
    mmFiber50Parent_19_ok,
    mmFiber50Parent_20_ok,
    mmFiber50Parent_21_ok,
    mmFiber50Parent_22_ok,
    mmFiber50Parent_23_ok,
    mmFiber50Parent_24_ok,
    mmFiber50Parent_25_ok,
    mmFiber50Parent_26_ok,
    mmFiber50Parent_27_ok,
    mmFiber50Parent_28_ok,
    mmFiber50Parent_29_ok,
    mmFiber50Parent_30_ok,
    mmFiber50Parent_31_ok,
    mmFiber50Parent_32_ok,
    mmFiber50Parent_33_ok,
    mmFiber50Parent_34_ok,
    mmFiber50Parent_35_ok,
    mmFiber50Parent_36_ok,
    mmFiber50Parent_37_ok,
    mmFiber50Parent_38_ok,
    mmFiber50Parent_39_ok,
    mmFiber50Parent_40_ok,
    mmFiber50Parent_41_ok,
    mmFiber50Parent_42_ok,
    mmFiber50Parent_43_ok,
    mmFiber50Parent_44_ok,
    mmFiber50Parent_45_ok,
    mmFiber50Parent_46_ok,
    mmFiber50Parent_47_ok,
    mmFiber50Parent_48_ok,
    mmFiber50Parent_49_ok,
    mmFiber50Parent_50_ok,
    mmFiber50Parent_51_ok,
    mmFiber50Parent_52_ok,
    mmFiber50Parent_53_ok,
    mmFiber50Parent_54_ok,
    mmFiber50Parent_55_ok,
    mmFiber50Parent_56_ok,
    mmFiber50Parent_57_ok,
    mmFiber50Parent_58_ok,
    mmFiber50Parent_59_ok,
    mmFiber50Parent_60_ok,
    mmFiber50Parent_61_ok,
    mmFiber50Parent_62_ok,
    mmFiber50Parent_63_ok]

def mmFiber51Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.r]

def mmFiber51Expected : List Nat :=
  []

def mmFiber51Rows : List DirectChainParentRow :=
  []

def mmFiber51RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber51Rows i default

def mmFiber51SourcesCheck : Bool :=
  (mmFiber51Rows.map fun row => row.source) == mmFiber51Expected

theorem mmFiber51SourcesCheck_ok :
    mmFiber51SourcesCheck = true := by
  decide

def mmFiber51RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber51Key mmFiber51Expected (mmFiber51RowAt i)

def mmFiber51ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber51Rows mmMaxParentDepth (listGetD mmFiber51Expected i 0) == 0

def mmFiber51CertificateAudit : Bool :=
  mmFiber51SourcesCheck

theorem mmFiber51CertificateAudit_ok :
    mmFiber51CertificateAudit = true := by
  simp [mmFiber51CertificateAudit,
    mmFiber51SourcesCheck_ok]

def mmFiber52Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.b]

def mmFiber52Expected : List Nat :=
  []

def mmFiber52Rows : List DirectChainParentRow :=
  []

def mmFiber52RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber52Rows i default

def mmFiber52SourcesCheck : Bool :=
  (mmFiber52Rows.map fun row => row.source) == mmFiber52Expected

theorem mmFiber52SourcesCheck_ok :
    mmFiber52SourcesCheck = true := by
  decide

def mmFiber52RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber52Key mmFiber52Expected (mmFiber52RowAt i)

def mmFiber52ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber52Rows mmMaxParentDepth (listGetD mmFiber52Expected i 0) == 0

def mmFiber52CertificateAudit : Bool :=
  mmFiber52SourcesCheck

theorem mmFiber52CertificateAudit_ok :
    mmFiber52CertificateAudit = true := by
  simp [mmFiber52CertificateAudit,
    mmFiber52SourcesCheck_ok]

def mmFiber53Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.p]

def mmFiber53Expected : List Nat :=
  []

def mmFiber53Rows : List DirectChainParentRow :=
  []

def mmFiber53RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber53Rows i default

def mmFiber53SourcesCheck : Bool :=
  (mmFiber53Rows.map fun row => row.source) == mmFiber53Expected

theorem mmFiber53SourcesCheck_ok :
    mmFiber53SourcesCheck = true := by
  decide

def mmFiber53RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber53Key mmFiber53Expected (mmFiber53RowAt i)

def mmFiber53ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber53Rows mmMaxParentDepth (listGetD mmFiber53Expected i 0) == 0

def mmFiber53CertificateAudit : Bool :=
  mmFiber53SourcesCheck

theorem mmFiber53CertificateAudit_ok :
    mmFiber53CertificateAudit = true := by
  simp [mmFiber53CertificateAudit,
    mmFiber53SourcesCheck_ok]

def mmFiber54Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.r]

def mmFiber54Expected : List Nat :=
  []

def mmFiber54Rows : List DirectChainParentRow :=
  []

def mmFiber54RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber54Rows i default

def mmFiber54SourcesCheck : Bool :=
  (mmFiber54Rows.map fun row => row.source) == mmFiber54Expected

theorem mmFiber54SourcesCheck_ok :
    mmFiber54SourcesCheck = true := by
  decide

def mmFiber54RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber54Key mmFiber54Expected (mmFiber54RowAt i)

def mmFiber54ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber54Rows mmMaxParentDepth (listGetD mmFiber54Expected i 0) == 0

def mmFiber54CertificateAudit : Bool :=
  mmFiber54SourcesCheck

theorem mmFiber54CertificateAudit_ok :
    mmFiber54CertificateAudit = true := by
  simp [mmFiber54CertificateAudit,
    mmFiber54SourcesCheck_ok]

def mmFiber55Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.b]

def mmFiber55Expected : List Nat :=
  []

def mmFiber55Rows : List DirectChainParentRow :=
  []

def mmFiber55RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber55Rows i default

def mmFiber55SourcesCheck : Bool :=
  (mmFiber55Rows.map fun row => row.source) == mmFiber55Expected

theorem mmFiber55SourcesCheck_ok :
    mmFiber55SourcesCheck = true := by
  decide

def mmFiber55RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber55Key mmFiber55Expected (mmFiber55RowAt i)

def mmFiber55ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber55Rows mmMaxParentDepth (listGetD mmFiber55Expected i 0) == 0

def mmFiber55CertificateAudit : Bool :=
  mmFiber55SourcesCheck

theorem mmFiber55CertificateAudit_ok :
    mmFiber55CertificateAudit = true := by
  simp [mmFiber55CertificateAudit,
    mmFiber55SourcesCheck_ok]

def mmFiber56Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.p]

def mmFiber56Expected : List Nat :=
  []

def mmFiber56Rows : List DirectChainParentRow :=
  []

def mmFiber56RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber56Rows i default

def mmFiber56SourcesCheck : Bool :=
  (mmFiber56Rows.map fun row => row.source) == mmFiber56Expected

theorem mmFiber56SourcesCheck_ok :
    mmFiber56SourcesCheck = true := by
  decide

def mmFiber56RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber56Key mmFiber56Expected (mmFiber56RowAt i)

def mmFiber56ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber56Rows mmMaxParentDepth (listGetD mmFiber56Expected i 0) == 0

def mmFiber56CertificateAudit : Bool :=
  mmFiber56SourcesCheck

theorem mmFiber56CertificateAudit_ok :
    mmFiber56CertificateAudit = true := by
  simp [mmFiber56CertificateAudit,
    mmFiber56SourcesCheck_ok]

def mmFiber57Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.r]

def mmFiber57Expected : List Nat :=
  [392, 393, 394, 395, 396, 397, 398, 399]

def mmFiber57Rows : List DirectChainParentRow :=
  [ directRow 392 392 76 144 76 144 default
  , directRow 393 392 76 145 76 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 394 393 76 146 76 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 395 392 76 147 76 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 396 392 77 152 76 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 397 393 77 153 76 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 398 394 77 154 76 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 399 395 77 155 76 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber57RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber57Rows i default

def mmFiber57SourcesCheck : Bool :=
  (mmFiber57Rows.map fun row => row.source) == mmFiber57Expected

theorem mmFiber57SourcesCheck_ok :
    mmFiber57SourcesCheck = true := by
  decide

def mmFiber57RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt i)

theorem mmFiber57Row_0_ok : mmFiber57RowCheck 0 = true := by decide
theorem mmFiber57Row_1_ok : mmFiber57RowCheck 1 = true := by decide
theorem mmFiber57Row_2_ok : mmFiber57RowCheck 2 = true := by decide
theorem mmFiber57Row_3_ok : mmFiber57RowCheck 3 = true := by decide
theorem mmFiber57Row_4_ok : mmFiber57RowCheck 4 = true := by decide
theorem mmFiber57Row_5_ok : mmFiber57RowCheck 5 = true := by decide
theorem mmFiber57Row_6_ok : mmFiber57RowCheck 6 = true := by decide
theorem mmFiber57Row_7_ok : mmFiber57RowCheck 7 = true := by decide

def mmFiber57ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber57Rows mmMaxParentDepth (listGetD mmFiber57Expected i 0) == 392

theorem mmFiber57Parent_0_ok : mmFiber57ParentCheck 0 = true := by decide
theorem mmFiber57Parent_1_ok : mmFiber57ParentCheck 1 = true := by decide
theorem mmFiber57Parent_2_ok : mmFiber57ParentCheck 2 = true := by decide
theorem mmFiber57Parent_3_ok : mmFiber57ParentCheck 3 = true := by decide
theorem mmFiber57Parent_4_ok : mmFiber57ParentCheck 4 = true := by decide
theorem mmFiber57Parent_5_ok : mmFiber57ParentCheck 5 = true := by decide
theorem mmFiber57Parent_6_ok : mmFiber57ParentCheck 6 = true := by decide
theorem mmFiber57Parent_7_ok : mmFiber57ParentCheck 7 = true := by decide

def mmFiber57CertificateAudit : Bool :=
  mmFiber57SourcesCheck &&
    mmFiber57RowCheck 0 &&
    mmFiber57RowCheck 1 &&
    mmFiber57RowCheck 2 &&
    mmFiber57RowCheck 3 &&
    mmFiber57RowCheck 4 &&
    mmFiber57RowCheck 5 &&
    mmFiber57RowCheck 6 &&
    mmFiber57RowCheck 7 &&
    mmFiber57ParentCheck 0 &&
    mmFiber57ParentCheck 1 &&
    mmFiber57ParentCheck 2 &&
    mmFiber57ParentCheck 3 &&
    mmFiber57ParentCheck 4 &&
    mmFiber57ParentCheck 5 &&
    mmFiber57ParentCheck 6 &&
    mmFiber57ParentCheck 7

theorem mmFiber57CertificateAudit_ok :
    mmFiber57CertificateAudit = true := by
  simp [mmFiber57CertificateAudit,
    mmFiber57SourcesCheck_ok,
    mmFiber57Row_0_ok,
    mmFiber57Row_1_ok,
    mmFiber57Row_2_ok,
    mmFiber57Row_3_ok,
    mmFiber57Row_4_ok,
    mmFiber57Row_5_ok,
    mmFiber57Row_6_ok,
    mmFiber57Row_7_ok,
    mmFiber57Parent_0_ok,
    mmFiber57Parent_1_ok,
    mmFiber57Parent_2_ok,
    mmFiber57Parent_3_ok,
    mmFiber57Parent_4_ok,
    mmFiber57Parent_5_ok,
    mmFiber57Parent_6_ok,
    mmFiber57Parent_7_ok]

def mmFiber58Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.b]

def mmFiber58Expected : List Nat :=
  [72, 73, 74, 75, 76, 77, 78, 79]

def mmFiber58Rows : List DirectChainParentRow :=
  [ directRow 72 72 14 176 14 176 default
  , directRow 73 72 14 177 14 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 74 72 14 178 14 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 75 73 14 179 14 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 76 72 15 184 14 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 77 73 15 185 14 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 78 74 15 186 14 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 79 75 15 187 14 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber58RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber58Rows i default

def mmFiber58SourcesCheck : Bool :=
  (mmFiber58Rows.map fun row => row.source) == mmFiber58Expected

theorem mmFiber58SourcesCheck_ok :
    mmFiber58SourcesCheck = true := by
  decide

def mmFiber58RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt i)

theorem mmFiber58Row_0_ok : mmFiber58RowCheck 0 = true := by decide
theorem mmFiber58Row_1_ok : mmFiber58RowCheck 1 = true := by decide
theorem mmFiber58Row_2_ok : mmFiber58RowCheck 2 = true := by decide
theorem mmFiber58Row_3_ok : mmFiber58RowCheck 3 = true := by decide
theorem mmFiber58Row_4_ok : mmFiber58RowCheck 4 = true := by decide
theorem mmFiber58Row_5_ok : mmFiber58RowCheck 5 = true := by decide
theorem mmFiber58Row_6_ok : mmFiber58RowCheck 6 = true := by decide
theorem mmFiber58Row_7_ok : mmFiber58RowCheck 7 = true := by decide

def mmFiber58ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber58Rows mmMaxParentDepth (listGetD mmFiber58Expected i 0) == 72

theorem mmFiber58Parent_0_ok : mmFiber58ParentCheck 0 = true := by decide
theorem mmFiber58Parent_1_ok : mmFiber58ParentCheck 1 = true := by decide
theorem mmFiber58Parent_2_ok : mmFiber58ParentCheck 2 = true := by decide
theorem mmFiber58Parent_3_ok : mmFiber58ParentCheck 3 = true := by decide
theorem mmFiber58Parent_4_ok : mmFiber58ParentCheck 4 = true := by decide
theorem mmFiber58Parent_5_ok : mmFiber58ParentCheck 5 = true := by decide
theorem mmFiber58Parent_6_ok : mmFiber58ParentCheck 6 = true := by decide
theorem mmFiber58Parent_7_ok : mmFiber58ParentCheck 7 = true := by decide

def mmFiber58CertificateAudit : Bool :=
  mmFiber58SourcesCheck &&
    mmFiber58RowCheck 0 &&
    mmFiber58RowCheck 1 &&
    mmFiber58RowCheck 2 &&
    mmFiber58RowCheck 3 &&
    mmFiber58RowCheck 4 &&
    mmFiber58RowCheck 5 &&
    mmFiber58RowCheck 6 &&
    mmFiber58RowCheck 7 &&
    mmFiber58ParentCheck 0 &&
    mmFiber58ParentCheck 1 &&
    mmFiber58ParentCheck 2 &&
    mmFiber58ParentCheck 3 &&
    mmFiber58ParentCheck 4 &&
    mmFiber58ParentCheck 5 &&
    mmFiber58ParentCheck 6 &&
    mmFiber58ParentCheck 7

theorem mmFiber58CertificateAudit_ok :
    mmFiber58CertificateAudit = true := by
  simp [mmFiber58CertificateAudit,
    mmFiber58SourcesCheck_ok,
    mmFiber58Row_0_ok,
    mmFiber58Row_1_ok,
    mmFiber58Row_2_ok,
    mmFiber58Row_3_ok,
    mmFiber58Row_4_ok,
    mmFiber58Row_5_ok,
    mmFiber58Row_6_ok,
    mmFiber58Row_7_ok,
    mmFiber58Parent_0_ok,
    mmFiber58Parent_1_ok,
    mmFiber58Parent_2_ok,
    mmFiber58Parent_3_ok,
    mmFiber58Parent_4_ok,
    mmFiber58Parent_5_ok,
    mmFiber58Parent_6_ok,
    mmFiber58Parent_7_ok]

def mmFiber59Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.p]

def mmFiber59Expected : List Nat :=
  []

def mmFiber59Rows : List DirectChainParentRow :=
  []

def mmFiber59RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber59Rows i default

def mmFiber59SourcesCheck : Bool :=
  (mmFiber59Rows.map fun row => row.source) == mmFiber59Expected

theorem mmFiber59SourcesCheck_ok :
    mmFiber59SourcesCheck = true := by
  decide

def mmFiber59RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber59Key mmFiber59Expected (mmFiber59RowAt i)

def mmFiber59ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber59Rows mmMaxParentDepth (listGetD mmFiber59Expected i 0) == 0

def mmFiber59CertificateAudit : Bool :=
  mmFiber59SourcesCheck

theorem mmFiber59CertificateAudit_ok :
    mmFiber59CertificateAudit = true := by
  simp [mmFiber59CertificateAudit,
    mmFiber59SourcesCheck_ok]

def mmFiber60Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.r]

def mmFiber60Expected : List Nat :=
  [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]

def mmFiber60Rows : List DirectChainParentRow :=
  [ directRow 688 688 140 148 140 148 default
  , directRow 689 688 140 149 140 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 690 689 140 150 140 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 691 688 140 151 140 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 692 688 140 164 140 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 693 689 140 165 140 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 694 692 140 166 140 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 695 691 140 167 140 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 696 688 141 156 140 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 697 689 141 157 140 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 698 690 141 158 140 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 699 691 141 159 140 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 700 692 141 172 140 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 701 693 141 173 140 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 702 694 141 174 140 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 703 695 141 175 140 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 704 708 142 0 142 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 705 709 142 1 142 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 706 700 142 2 141 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 707 701 142 3 141 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 708 696 142 48 141 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 709 697 142 49 141 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 710 698 142 50 141 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 711 699 142 51 141 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 712 716 143 8 143 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 713 717 143 9 143 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 714 692 143 10 140 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 715 693 143 11 140 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 716 688 143 56 140 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 717 689 143 57 140 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 718 690 143 58 140 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 719 691 143 59 140 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 928 688 188 132 140 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 929 689 188 133 140 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 930 690 188 134 140 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 931 691 188 135 140 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 932 692 188 180 140 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 933 693 188 181 140 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 934 694 188 182 140 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 935 695 188 183 140 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 936 696 189 140 141 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 937 697 189 141 141 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 938 698 189 142 141 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 939 699 189 143 141 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 940 700 189 188 141 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 941 701 189 189 141 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 942 702 189 190 141 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 943 703 189 191 141 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 944 928 190 64 188 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 945 929 190 65 188 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 946 944 190 66 190 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 947 931 190 67 188 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 948 932 190 116 188 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 949 933 190 117 188 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 950 945 190 118 190 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 951 944 190 119 190 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 952 936 191 72 189 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 953 937 191 73 189 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 954 714 191 74 143 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 955 715 191 75 143 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 956 716 191 124 143 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 957 717 191 125 143 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 958 956 191 126 191 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 959 719 191 127 143 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mmFiber60RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber60Rows i default

def mmFiber60SourcesCheck : Bool :=
  (mmFiber60Rows.map fun row => row.source) == mmFiber60Expected

theorem mmFiber60SourcesCheck_ok :
    mmFiber60SourcesCheck = true := by
  decide

def mmFiber60RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt i)

theorem mmFiber60Row_0_ok : mmFiber60RowCheck 0 = true := by decide
theorem mmFiber60Row_1_ok : mmFiber60RowCheck 1 = true := by decide
theorem mmFiber60Row_2_ok : mmFiber60RowCheck 2 = true := by decide
theorem mmFiber60Row_3_ok : mmFiber60RowCheck 3 = true := by decide
theorem mmFiber60Row_4_ok : mmFiber60RowCheck 4 = true := by decide
theorem mmFiber60Row_5_ok : mmFiber60RowCheck 5 = true := by decide
theorem mmFiber60Row_6_ok : mmFiber60RowCheck 6 = true := by decide
theorem mmFiber60Row_7_ok : mmFiber60RowCheck 7 = true := by decide
theorem mmFiber60Row_8_ok : mmFiber60RowCheck 8 = true := by decide
theorem mmFiber60Row_9_ok : mmFiber60RowCheck 9 = true := by decide
theorem mmFiber60Row_10_ok : mmFiber60RowCheck 10 = true := by decide
theorem mmFiber60Row_11_ok : mmFiber60RowCheck 11 = true := by decide
theorem mmFiber60Row_12_ok : mmFiber60RowCheck 12 = true := by decide
theorem mmFiber60Row_13_ok : mmFiber60RowCheck 13 = true := by decide
theorem mmFiber60Row_14_ok : mmFiber60RowCheck 14 = true := by decide
theorem mmFiber60Row_15_ok : mmFiber60RowCheck 15 = true := by decide
theorem mmFiber60Row_16_ok : mmFiber60RowCheck 16 = true := by decide
theorem mmFiber60Row_17_ok : mmFiber60RowCheck 17 = true := by decide
theorem mmFiber60Row_18_ok : mmFiber60RowCheck 18 = true := by decide
theorem mmFiber60Row_19_ok : mmFiber60RowCheck 19 = true := by decide
theorem mmFiber60Row_20_ok : mmFiber60RowCheck 20 = true := by decide
theorem mmFiber60Row_21_ok : mmFiber60RowCheck 21 = true := by decide
theorem mmFiber60Row_22_ok : mmFiber60RowCheck 22 = true := by decide
theorem mmFiber60Row_23_ok : mmFiber60RowCheck 23 = true := by decide
theorem mmFiber60Row_24_ok : mmFiber60RowCheck 24 = true := by decide
theorem mmFiber60Row_25_ok : mmFiber60RowCheck 25 = true := by decide
theorem mmFiber60Row_26_ok : mmFiber60RowCheck 26 = true := by decide
theorem mmFiber60Row_27_ok : mmFiber60RowCheck 27 = true := by decide
theorem mmFiber60Row_28_ok : mmFiber60RowCheck 28 = true := by decide
theorem mmFiber60Row_29_ok : mmFiber60RowCheck 29 = true := by decide
theorem mmFiber60Row_30_ok : mmFiber60RowCheck 30 = true := by decide
theorem mmFiber60Row_31_ok : mmFiber60RowCheck 31 = true := by decide
theorem mmFiber60Row_32_ok : mmFiber60RowCheck 32 = true := by decide
theorem mmFiber60Row_33_ok : mmFiber60RowCheck 33 = true := by decide
theorem mmFiber60Row_34_ok : mmFiber60RowCheck 34 = true := by decide
theorem mmFiber60Row_35_ok : mmFiber60RowCheck 35 = true := by decide
theorem mmFiber60Row_36_ok : mmFiber60RowCheck 36 = true := by decide
theorem mmFiber60Row_37_ok : mmFiber60RowCheck 37 = true := by decide
theorem mmFiber60Row_38_ok : mmFiber60RowCheck 38 = true := by decide
theorem mmFiber60Row_39_ok : mmFiber60RowCheck 39 = true := by decide
theorem mmFiber60Row_40_ok : mmFiber60RowCheck 40 = true := by decide
theorem mmFiber60Row_41_ok : mmFiber60RowCheck 41 = true := by decide
theorem mmFiber60Row_42_ok : mmFiber60RowCheck 42 = true := by decide
theorem mmFiber60Row_43_ok : mmFiber60RowCheck 43 = true := by decide
theorem mmFiber60Row_44_ok : mmFiber60RowCheck 44 = true := by decide
theorem mmFiber60Row_45_ok : mmFiber60RowCheck 45 = true := by decide
theorem mmFiber60Row_46_ok : mmFiber60RowCheck 46 = true := by decide
theorem mmFiber60Row_47_ok : mmFiber60RowCheck 47 = true := by decide
theorem mmFiber60Row_48_ok : mmFiber60RowCheck 48 = true := by decide
theorem mmFiber60Row_49_ok : mmFiber60RowCheck 49 = true := by decide
theorem mmFiber60Row_50_ok : mmFiber60RowCheck 50 = true := by decide
theorem mmFiber60Row_51_ok : mmFiber60RowCheck 51 = true := by decide
theorem mmFiber60Row_52_ok : mmFiber60RowCheck 52 = true := by decide
theorem mmFiber60Row_53_ok : mmFiber60RowCheck 53 = true := by decide
theorem mmFiber60Row_54_ok : mmFiber60RowCheck 54 = true := by decide
theorem mmFiber60Row_55_ok : mmFiber60RowCheck 55 = true := by decide
theorem mmFiber60Row_56_ok : mmFiber60RowCheck 56 = true := by decide
theorem mmFiber60Row_57_ok : mmFiber60RowCheck 57 = true := by decide
theorem mmFiber60Row_58_ok : mmFiber60RowCheck 58 = true := by decide
theorem mmFiber60Row_59_ok : mmFiber60RowCheck 59 = true := by decide
theorem mmFiber60Row_60_ok : mmFiber60RowCheck 60 = true := by decide
theorem mmFiber60Row_61_ok : mmFiber60RowCheck 61 = true := by decide
theorem mmFiber60Row_62_ok : mmFiber60RowCheck 62 = true := by decide
theorem mmFiber60Row_63_ok : mmFiber60RowCheck 63 = true := by decide

def mmFiber60ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber60Rows mmMaxParentDepth (listGetD mmFiber60Expected i 0) == 688

theorem mmFiber60Parent_0_ok : mmFiber60ParentCheck 0 = true := by decide
theorem mmFiber60Parent_1_ok : mmFiber60ParentCheck 1 = true := by decide
theorem mmFiber60Parent_2_ok : mmFiber60ParentCheck 2 = true := by decide
theorem mmFiber60Parent_3_ok : mmFiber60ParentCheck 3 = true := by decide
theorem mmFiber60Parent_4_ok : mmFiber60ParentCheck 4 = true := by decide
theorem mmFiber60Parent_5_ok : mmFiber60ParentCheck 5 = true := by decide
theorem mmFiber60Parent_6_ok : mmFiber60ParentCheck 6 = true := by decide
theorem mmFiber60Parent_7_ok : mmFiber60ParentCheck 7 = true := by decide
theorem mmFiber60Parent_8_ok : mmFiber60ParentCheck 8 = true := by decide
theorem mmFiber60Parent_9_ok : mmFiber60ParentCheck 9 = true := by decide
theorem mmFiber60Parent_10_ok : mmFiber60ParentCheck 10 = true := by decide
theorem mmFiber60Parent_11_ok : mmFiber60ParentCheck 11 = true := by decide
theorem mmFiber60Parent_12_ok : mmFiber60ParentCheck 12 = true := by decide
theorem mmFiber60Parent_13_ok : mmFiber60ParentCheck 13 = true := by decide
theorem mmFiber60Parent_14_ok : mmFiber60ParentCheck 14 = true := by decide
theorem mmFiber60Parent_15_ok : mmFiber60ParentCheck 15 = true := by decide
theorem mmFiber60Parent_16_ok : mmFiber60ParentCheck 16 = true := by decide
theorem mmFiber60Parent_17_ok : mmFiber60ParentCheck 17 = true := by decide
theorem mmFiber60Parent_18_ok : mmFiber60ParentCheck 18 = true := by decide
theorem mmFiber60Parent_19_ok : mmFiber60ParentCheck 19 = true := by decide
theorem mmFiber60Parent_20_ok : mmFiber60ParentCheck 20 = true := by decide
theorem mmFiber60Parent_21_ok : mmFiber60ParentCheck 21 = true := by decide
theorem mmFiber60Parent_22_ok : mmFiber60ParentCheck 22 = true := by decide
theorem mmFiber60Parent_23_ok : mmFiber60ParentCheck 23 = true := by decide
theorem mmFiber60Parent_24_ok : mmFiber60ParentCheck 24 = true := by decide
theorem mmFiber60Parent_25_ok : mmFiber60ParentCheck 25 = true := by decide
theorem mmFiber60Parent_26_ok : mmFiber60ParentCheck 26 = true := by decide
theorem mmFiber60Parent_27_ok : mmFiber60ParentCheck 27 = true := by decide
theorem mmFiber60Parent_28_ok : mmFiber60ParentCheck 28 = true := by decide
theorem mmFiber60Parent_29_ok : mmFiber60ParentCheck 29 = true := by decide
theorem mmFiber60Parent_30_ok : mmFiber60ParentCheck 30 = true := by decide
theorem mmFiber60Parent_31_ok : mmFiber60ParentCheck 31 = true := by decide
theorem mmFiber60Parent_32_ok : mmFiber60ParentCheck 32 = true := by decide
theorem mmFiber60Parent_33_ok : mmFiber60ParentCheck 33 = true := by decide
theorem mmFiber60Parent_34_ok : mmFiber60ParentCheck 34 = true := by decide
theorem mmFiber60Parent_35_ok : mmFiber60ParentCheck 35 = true := by decide
theorem mmFiber60Parent_36_ok : mmFiber60ParentCheck 36 = true := by decide
theorem mmFiber60Parent_37_ok : mmFiber60ParentCheck 37 = true := by decide
theorem mmFiber60Parent_38_ok : mmFiber60ParentCheck 38 = true := by decide
theorem mmFiber60Parent_39_ok : mmFiber60ParentCheck 39 = true := by decide
theorem mmFiber60Parent_40_ok : mmFiber60ParentCheck 40 = true := by decide
theorem mmFiber60Parent_41_ok : mmFiber60ParentCheck 41 = true := by decide
theorem mmFiber60Parent_42_ok : mmFiber60ParentCheck 42 = true := by decide
theorem mmFiber60Parent_43_ok : mmFiber60ParentCheck 43 = true := by decide
theorem mmFiber60Parent_44_ok : mmFiber60ParentCheck 44 = true := by decide
theorem mmFiber60Parent_45_ok : mmFiber60ParentCheck 45 = true := by decide
theorem mmFiber60Parent_46_ok : mmFiber60ParentCheck 46 = true := by decide
theorem mmFiber60Parent_47_ok : mmFiber60ParentCheck 47 = true := by decide
theorem mmFiber60Parent_48_ok : mmFiber60ParentCheck 48 = true := by decide
theorem mmFiber60Parent_49_ok : mmFiber60ParentCheck 49 = true := by decide
theorem mmFiber60Parent_50_ok : mmFiber60ParentCheck 50 = true := by decide
theorem mmFiber60Parent_51_ok : mmFiber60ParentCheck 51 = true := by decide
theorem mmFiber60Parent_52_ok : mmFiber60ParentCheck 52 = true := by decide
theorem mmFiber60Parent_53_ok : mmFiber60ParentCheck 53 = true := by decide
theorem mmFiber60Parent_54_ok : mmFiber60ParentCheck 54 = true := by decide
theorem mmFiber60Parent_55_ok : mmFiber60ParentCheck 55 = true := by decide
theorem mmFiber60Parent_56_ok : mmFiber60ParentCheck 56 = true := by decide
theorem mmFiber60Parent_57_ok : mmFiber60ParentCheck 57 = true := by decide
theorem mmFiber60Parent_58_ok : mmFiber60ParentCheck 58 = true := by decide
theorem mmFiber60Parent_59_ok : mmFiber60ParentCheck 59 = true := by decide
theorem mmFiber60Parent_60_ok : mmFiber60ParentCheck 60 = true := by decide
theorem mmFiber60Parent_61_ok : mmFiber60ParentCheck 61 = true := by decide
theorem mmFiber60Parent_62_ok : mmFiber60ParentCheck 62 = true := by decide
theorem mmFiber60Parent_63_ok : mmFiber60ParentCheck 63 = true := by decide

def mmFiber60CertificateAudit : Bool :=
  mmFiber60SourcesCheck &&
    mmFiber60RowCheck 0 &&
    mmFiber60RowCheck 1 &&
    mmFiber60RowCheck 2 &&
    mmFiber60RowCheck 3 &&
    mmFiber60RowCheck 4 &&
    mmFiber60RowCheck 5 &&
    mmFiber60RowCheck 6 &&
    mmFiber60RowCheck 7 &&
    mmFiber60RowCheck 8 &&
    mmFiber60RowCheck 9 &&
    mmFiber60RowCheck 10 &&
    mmFiber60RowCheck 11 &&
    mmFiber60RowCheck 12 &&
    mmFiber60RowCheck 13 &&
    mmFiber60RowCheck 14 &&
    mmFiber60RowCheck 15 &&
    mmFiber60RowCheck 16 &&
    mmFiber60RowCheck 17 &&
    mmFiber60RowCheck 18 &&
    mmFiber60RowCheck 19 &&
    mmFiber60RowCheck 20 &&
    mmFiber60RowCheck 21 &&
    mmFiber60RowCheck 22 &&
    mmFiber60RowCheck 23 &&
    mmFiber60RowCheck 24 &&
    mmFiber60RowCheck 25 &&
    mmFiber60RowCheck 26 &&
    mmFiber60RowCheck 27 &&
    mmFiber60RowCheck 28 &&
    mmFiber60RowCheck 29 &&
    mmFiber60RowCheck 30 &&
    mmFiber60RowCheck 31 &&
    mmFiber60RowCheck 32 &&
    mmFiber60RowCheck 33 &&
    mmFiber60RowCheck 34 &&
    mmFiber60RowCheck 35 &&
    mmFiber60RowCheck 36 &&
    mmFiber60RowCheck 37 &&
    mmFiber60RowCheck 38 &&
    mmFiber60RowCheck 39 &&
    mmFiber60RowCheck 40 &&
    mmFiber60RowCheck 41 &&
    mmFiber60RowCheck 42 &&
    mmFiber60RowCheck 43 &&
    mmFiber60RowCheck 44 &&
    mmFiber60RowCheck 45 &&
    mmFiber60RowCheck 46 &&
    mmFiber60RowCheck 47 &&
    mmFiber60RowCheck 48 &&
    mmFiber60RowCheck 49 &&
    mmFiber60RowCheck 50 &&
    mmFiber60RowCheck 51 &&
    mmFiber60RowCheck 52 &&
    mmFiber60RowCheck 53 &&
    mmFiber60RowCheck 54 &&
    mmFiber60RowCheck 55 &&
    mmFiber60RowCheck 56 &&
    mmFiber60RowCheck 57 &&
    mmFiber60RowCheck 58 &&
    mmFiber60RowCheck 59 &&
    mmFiber60RowCheck 60 &&
    mmFiber60RowCheck 61 &&
    mmFiber60RowCheck 62 &&
    mmFiber60RowCheck 63 &&
    mmFiber60ParentCheck 0 &&
    mmFiber60ParentCheck 1 &&
    mmFiber60ParentCheck 2 &&
    mmFiber60ParentCheck 3 &&
    mmFiber60ParentCheck 4 &&
    mmFiber60ParentCheck 5 &&
    mmFiber60ParentCheck 6 &&
    mmFiber60ParentCheck 7 &&
    mmFiber60ParentCheck 8 &&
    mmFiber60ParentCheck 9 &&
    mmFiber60ParentCheck 10 &&
    mmFiber60ParentCheck 11 &&
    mmFiber60ParentCheck 12 &&
    mmFiber60ParentCheck 13 &&
    mmFiber60ParentCheck 14 &&
    mmFiber60ParentCheck 15 &&
    mmFiber60ParentCheck 16 &&
    mmFiber60ParentCheck 17 &&
    mmFiber60ParentCheck 18 &&
    mmFiber60ParentCheck 19 &&
    mmFiber60ParentCheck 20 &&
    mmFiber60ParentCheck 21 &&
    mmFiber60ParentCheck 22 &&
    mmFiber60ParentCheck 23 &&
    mmFiber60ParentCheck 24 &&
    mmFiber60ParentCheck 25 &&
    mmFiber60ParentCheck 26 &&
    mmFiber60ParentCheck 27 &&
    mmFiber60ParentCheck 28 &&
    mmFiber60ParentCheck 29 &&
    mmFiber60ParentCheck 30 &&
    mmFiber60ParentCheck 31 &&
    mmFiber60ParentCheck 32 &&
    mmFiber60ParentCheck 33 &&
    mmFiber60ParentCheck 34 &&
    mmFiber60ParentCheck 35 &&
    mmFiber60ParentCheck 36 &&
    mmFiber60ParentCheck 37 &&
    mmFiber60ParentCheck 38 &&
    mmFiber60ParentCheck 39 &&
    mmFiber60ParentCheck 40 &&
    mmFiber60ParentCheck 41 &&
    mmFiber60ParentCheck 42 &&
    mmFiber60ParentCheck 43 &&
    mmFiber60ParentCheck 44 &&
    mmFiber60ParentCheck 45 &&
    mmFiber60ParentCheck 46 &&
    mmFiber60ParentCheck 47 &&
    mmFiber60ParentCheck 48 &&
    mmFiber60ParentCheck 49 &&
    mmFiber60ParentCheck 50 &&
    mmFiber60ParentCheck 51 &&
    mmFiber60ParentCheck 52 &&
    mmFiber60ParentCheck 53 &&
    mmFiber60ParentCheck 54 &&
    mmFiber60ParentCheck 55 &&
    mmFiber60ParentCheck 56 &&
    mmFiber60ParentCheck 57 &&
    mmFiber60ParentCheck 58 &&
    mmFiber60ParentCheck 59 &&
    mmFiber60ParentCheck 60 &&
    mmFiber60ParentCheck 61 &&
    mmFiber60ParentCheck 62 &&
    mmFiber60ParentCheck 63

theorem mmFiber60CertificateAudit_ok :
    mmFiber60CertificateAudit = true := by
  simp [mmFiber60CertificateAudit,
    mmFiber60SourcesCheck_ok,
    mmFiber60Row_0_ok,
    mmFiber60Row_1_ok,
    mmFiber60Row_2_ok,
    mmFiber60Row_3_ok,
    mmFiber60Row_4_ok,
    mmFiber60Row_5_ok,
    mmFiber60Row_6_ok,
    mmFiber60Row_7_ok,
    mmFiber60Row_8_ok,
    mmFiber60Row_9_ok,
    mmFiber60Row_10_ok,
    mmFiber60Row_11_ok,
    mmFiber60Row_12_ok,
    mmFiber60Row_13_ok,
    mmFiber60Row_14_ok,
    mmFiber60Row_15_ok,
    mmFiber60Row_16_ok,
    mmFiber60Row_17_ok,
    mmFiber60Row_18_ok,
    mmFiber60Row_19_ok,
    mmFiber60Row_20_ok,
    mmFiber60Row_21_ok,
    mmFiber60Row_22_ok,
    mmFiber60Row_23_ok,
    mmFiber60Row_24_ok,
    mmFiber60Row_25_ok,
    mmFiber60Row_26_ok,
    mmFiber60Row_27_ok,
    mmFiber60Row_28_ok,
    mmFiber60Row_29_ok,
    mmFiber60Row_30_ok,
    mmFiber60Row_31_ok,
    mmFiber60Row_32_ok,
    mmFiber60Row_33_ok,
    mmFiber60Row_34_ok,
    mmFiber60Row_35_ok,
    mmFiber60Row_36_ok,
    mmFiber60Row_37_ok,
    mmFiber60Row_38_ok,
    mmFiber60Row_39_ok,
    mmFiber60Row_40_ok,
    mmFiber60Row_41_ok,
    mmFiber60Row_42_ok,
    mmFiber60Row_43_ok,
    mmFiber60Row_44_ok,
    mmFiber60Row_45_ok,
    mmFiber60Row_46_ok,
    mmFiber60Row_47_ok,
    mmFiber60Row_48_ok,
    mmFiber60Row_49_ok,
    mmFiber60Row_50_ok,
    mmFiber60Row_51_ok,
    mmFiber60Row_52_ok,
    mmFiber60Row_53_ok,
    mmFiber60Row_54_ok,
    mmFiber60Row_55_ok,
    mmFiber60Row_56_ok,
    mmFiber60Row_57_ok,
    mmFiber60Row_58_ok,
    mmFiber60Row_59_ok,
    mmFiber60Row_60_ok,
    mmFiber60Row_61_ok,
    mmFiber60Row_62_ok,
    mmFiber60Row_63_ok,
    mmFiber60Parent_0_ok,
    mmFiber60Parent_1_ok,
    mmFiber60Parent_2_ok,
    mmFiber60Parent_3_ok,
    mmFiber60Parent_4_ok,
    mmFiber60Parent_5_ok,
    mmFiber60Parent_6_ok,
    mmFiber60Parent_7_ok,
    mmFiber60Parent_8_ok,
    mmFiber60Parent_9_ok,
    mmFiber60Parent_10_ok,
    mmFiber60Parent_11_ok,
    mmFiber60Parent_12_ok,
    mmFiber60Parent_13_ok,
    mmFiber60Parent_14_ok,
    mmFiber60Parent_15_ok,
    mmFiber60Parent_16_ok,
    mmFiber60Parent_17_ok,
    mmFiber60Parent_18_ok,
    mmFiber60Parent_19_ok,
    mmFiber60Parent_20_ok,
    mmFiber60Parent_21_ok,
    mmFiber60Parent_22_ok,
    mmFiber60Parent_23_ok,
    mmFiber60Parent_24_ok,
    mmFiber60Parent_25_ok,
    mmFiber60Parent_26_ok,
    mmFiber60Parent_27_ok,
    mmFiber60Parent_28_ok,
    mmFiber60Parent_29_ok,
    mmFiber60Parent_30_ok,
    mmFiber60Parent_31_ok,
    mmFiber60Parent_32_ok,
    mmFiber60Parent_33_ok,
    mmFiber60Parent_34_ok,
    mmFiber60Parent_35_ok,
    mmFiber60Parent_36_ok,
    mmFiber60Parent_37_ok,
    mmFiber60Parent_38_ok,
    mmFiber60Parent_39_ok,
    mmFiber60Parent_40_ok,
    mmFiber60Parent_41_ok,
    mmFiber60Parent_42_ok,
    mmFiber60Parent_43_ok,
    mmFiber60Parent_44_ok,
    mmFiber60Parent_45_ok,
    mmFiber60Parent_46_ok,
    mmFiber60Parent_47_ok,
    mmFiber60Parent_48_ok,
    mmFiber60Parent_49_ok,
    mmFiber60Parent_50_ok,
    mmFiber60Parent_51_ok,
    mmFiber60Parent_52_ok,
    mmFiber60Parent_53_ok,
    mmFiber60Parent_54_ok,
    mmFiber60Parent_55_ok,
    mmFiber60Parent_56_ok,
    mmFiber60Parent_57_ok,
    mmFiber60Parent_58_ok,
    mmFiber60Parent_59_ok,
    mmFiber60Parent_60_ok,
    mmFiber60Parent_61_ok,
    mmFiber60Parent_62_ok,
    mmFiber60Parent_63_ok]

def mmFiber61Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.b]

def mmFiber61Expected : List Nat :=
  []

def mmFiber61Rows : List DirectChainParentRow :=
  []

def mmFiber61RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber61Rows i default

def mmFiber61SourcesCheck : Bool :=
  (mmFiber61Rows.map fun row => row.source) == mmFiber61Expected

theorem mmFiber61SourcesCheck_ok :
    mmFiber61SourcesCheck = true := by
  decide

def mmFiber61RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber61Key mmFiber61Expected (mmFiber61RowAt i)

def mmFiber61ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber61Rows mmMaxParentDepth (listGetD mmFiber61Expected i 0) == 0

def mmFiber61CertificateAudit : Bool :=
  mmFiber61SourcesCheck

theorem mmFiber61CertificateAudit_ok :
    mmFiber61CertificateAudit = true := by
  simp [mmFiber61CertificateAudit,
    mmFiber61SourcesCheck_ok]

def mmFiber62Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.p]

def mmFiber62Expected : List Nat :=
  [152, 153, 154, 155, 156, 157, 158, 159]

def mmFiber62Rows : List DirectChainParentRow :=
  [ directRow 152 152 30 176 30 176 default
  , directRow 153 152 30 177 30 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 154 152 30 178 30 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 155 153 30 179 30 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 156 152 31 184 30 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 157 153 31 185 30 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 158 154 31 186 30 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 159 155 31 187 30 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber62RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber62Rows i default

def mmFiber62SourcesCheck : Bool :=
  (mmFiber62Rows.map fun row => row.source) == mmFiber62Expected

theorem mmFiber62SourcesCheck_ok :
    mmFiber62SourcesCheck = true := by
  decide

def mmFiber62RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt i)

theorem mmFiber62Row_0_ok : mmFiber62RowCheck 0 = true := by decide
theorem mmFiber62Row_1_ok : mmFiber62RowCheck 1 = true := by decide
theorem mmFiber62Row_2_ok : mmFiber62RowCheck 2 = true := by decide
theorem mmFiber62Row_3_ok : mmFiber62RowCheck 3 = true := by decide
theorem mmFiber62Row_4_ok : mmFiber62RowCheck 4 = true := by decide
theorem mmFiber62Row_5_ok : mmFiber62RowCheck 5 = true := by decide
theorem mmFiber62Row_6_ok : mmFiber62RowCheck 6 = true := by decide
theorem mmFiber62Row_7_ok : mmFiber62RowCheck 7 = true := by decide

def mmFiber62ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber62Rows mmMaxParentDepth (listGetD mmFiber62Expected i 0) == 152

theorem mmFiber62Parent_0_ok : mmFiber62ParentCheck 0 = true := by decide
theorem mmFiber62Parent_1_ok : mmFiber62ParentCheck 1 = true := by decide
theorem mmFiber62Parent_2_ok : mmFiber62ParentCheck 2 = true := by decide
theorem mmFiber62Parent_3_ok : mmFiber62ParentCheck 3 = true := by decide
theorem mmFiber62Parent_4_ok : mmFiber62ParentCheck 4 = true := by decide
theorem mmFiber62Parent_5_ok : mmFiber62ParentCheck 5 = true := by decide
theorem mmFiber62Parent_6_ok : mmFiber62ParentCheck 6 = true := by decide
theorem mmFiber62Parent_7_ok : mmFiber62ParentCheck 7 = true := by decide

def mmFiber62CertificateAudit : Bool :=
  mmFiber62SourcesCheck &&
    mmFiber62RowCheck 0 &&
    mmFiber62RowCheck 1 &&
    mmFiber62RowCheck 2 &&
    mmFiber62RowCheck 3 &&
    mmFiber62RowCheck 4 &&
    mmFiber62RowCheck 5 &&
    mmFiber62RowCheck 6 &&
    mmFiber62RowCheck 7 &&
    mmFiber62ParentCheck 0 &&
    mmFiber62ParentCheck 1 &&
    mmFiber62ParentCheck 2 &&
    mmFiber62ParentCheck 3 &&
    mmFiber62ParentCheck 4 &&
    mmFiber62ParentCheck 5 &&
    mmFiber62ParentCheck 6 &&
    mmFiber62ParentCheck 7

theorem mmFiber62CertificateAudit_ok :
    mmFiber62CertificateAudit = true := by
  simp [mmFiber62CertificateAudit,
    mmFiber62SourcesCheck_ok,
    mmFiber62Row_0_ok,
    mmFiber62Row_1_ok,
    mmFiber62Row_2_ok,
    mmFiber62Row_3_ok,
    mmFiber62Row_4_ok,
    mmFiber62Row_5_ok,
    mmFiber62Row_6_ok,
    mmFiber62Row_7_ok,
    mmFiber62Parent_0_ok,
    mmFiber62Parent_1_ok,
    mmFiber62Parent_2_ok,
    mmFiber62Parent_3_ok,
    mmFiber62Parent_4_ok,
    mmFiber62Parent_5_ok,
    mmFiber62Parent_6_ok,
    mmFiber62Parent_7_ok]

def mmFiber63Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.r]

def mmFiber63Expected : List Nat :=
  [352, 353, 354, 355, 356, 357, 358, 359]

def mmFiber63Rows : List DirectChainParentRow :=
  [ directRow 352 352 68 144 68 144 default
  , directRow 353 352 68 145 68 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 354 353 68 146 68 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 355 352 68 147 68 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 356 352 69 152 68 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 357 353 69 153 68 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 358 354 69 154 68 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 359 355 69 155 68 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber63RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber63Rows i default

def mmFiber63SourcesCheck : Bool :=
  (mmFiber63Rows.map fun row => row.source) == mmFiber63Expected

theorem mmFiber63SourcesCheck_ok :
    mmFiber63SourcesCheck = true := by
  decide

def mmFiber63RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt i)

theorem mmFiber63Row_0_ok : mmFiber63RowCheck 0 = true := by decide
theorem mmFiber63Row_1_ok : mmFiber63RowCheck 1 = true := by decide
theorem mmFiber63Row_2_ok : mmFiber63RowCheck 2 = true := by decide
theorem mmFiber63Row_3_ok : mmFiber63RowCheck 3 = true := by decide
theorem mmFiber63Row_4_ok : mmFiber63RowCheck 4 = true := by decide
theorem mmFiber63Row_5_ok : mmFiber63RowCheck 5 = true := by decide
theorem mmFiber63Row_6_ok : mmFiber63RowCheck 6 = true := by decide
theorem mmFiber63Row_7_ok : mmFiber63RowCheck 7 = true := by decide

def mmFiber63ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber63Rows mmMaxParentDepth (listGetD mmFiber63Expected i 0) == 352

theorem mmFiber63Parent_0_ok : mmFiber63ParentCheck 0 = true := by decide
theorem mmFiber63Parent_1_ok : mmFiber63ParentCheck 1 = true := by decide
theorem mmFiber63Parent_2_ok : mmFiber63ParentCheck 2 = true := by decide
theorem mmFiber63Parent_3_ok : mmFiber63ParentCheck 3 = true := by decide
theorem mmFiber63Parent_4_ok : mmFiber63ParentCheck 4 = true := by decide
theorem mmFiber63Parent_5_ok : mmFiber63ParentCheck 5 = true := by decide
theorem mmFiber63Parent_6_ok : mmFiber63ParentCheck 6 = true := by decide
theorem mmFiber63Parent_7_ok : mmFiber63ParentCheck 7 = true := by decide

def mmFiber63CertificateAudit : Bool :=
  mmFiber63SourcesCheck &&
    mmFiber63RowCheck 0 &&
    mmFiber63RowCheck 1 &&
    mmFiber63RowCheck 2 &&
    mmFiber63RowCheck 3 &&
    mmFiber63RowCheck 4 &&
    mmFiber63RowCheck 5 &&
    mmFiber63RowCheck 6 &&
    mmFiber63RowCheck 7 &&
    mmFiber63ParentCheck 0 &&
    mmFiber63ParentCheck 1 &&
    mmFiber63ParentCheck 2 &&
    mmFiber63ParentCheck 3 &&
    mmFiber63ParentCheck 4 &&
    mmFiber63ParentCheck 5 &&
    mmFiber63ParentCheck 6 &&
    mmFiber63ParentCheck 7

theorem mmFiber63CertificateAudit_ok :
    mmFiber63CertificateAudit = true := by
  simp [mmFiber63CertificateAudit,
    mmFiber63SourcesCheck_ok,
    mmFiber63Row_0_ok,
    mmFiber63Row_1_ok,
    mmFiber63Row_2_ok,
    mmFiber63Row_3_ok,
    mmFiber63Row_4_ok,
    mmFiber63Row_5_ok,
    mmFiber63Row_6_ok,
    mmFiber63Row_7_ok,
    mmFiber63Parent_0_ok,
    mmFiber63Parent_1_ok,
    mmFiber63Parent_2_ok,
    mmFiber63Parent_3_ok,
    mmFiber63Parent_4_ok,
    mmFiber63Parent_5_ok,
    mmFiber63Parent_6_ok,
    mmFiber63Parent_7_ok]

def mmFiber64Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.b]

def mmFiber64Expected : List Nat :=
  [32, 33, 34, 35, 36, 37, 38, 39]

def mmFiber64Rows : List DirectChainParentRow :=
  [ directRow 32 32 6 176 6 176 default
  , directRow 33 32 6 177 6 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 34 32 6 178 6 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 35 33 6 179 6 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 36 32 7 184 6 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 37 33 7 185 6 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 38 34 7 186 6 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 39 35 7 187 6 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber64RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber64Rows i default

def mmFiber64SourcesCheck : Bool :=
  (mmFiber64Rows.map fun row => row.source) == mmFiber64Expected

theorem mmFiber64SourcesCheck_ok :
    mmFiber64SourcesCheck = true := by
  decide

def mmFiber64RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt i)

theorem mmFiber64Row_0_ok : mmFiber64RowCheck 0 = true := by decide
theorem mmFiber64Row_1_ok : mmFiber64RowCheck 1 = true := by decide
theorem mmFiber64Row_2_ok : mmFiber64RowCheck 2 = true := by decide
theorem mmFiber64Row_3_ok : mmFiber64RowCheck 3 = true := by decide
theorem mmFiber64Row_4_ok : mmFiber64RowCheck 4 = true := by decide
theorem mmFiber64Row_5_ok : mmFiber64RowCheck 5 = true := by decide
theorem mmFiber64Row_6_ok : mmFiber64RowCheck 6 = true := by decide
theorem mmFiber64Row_7_ok : mmFiber64RowCheck 7 = true := by decide

def mmFiber64ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber64Rows mmMaxParentDepth (listGetD mmFiber64Expected i 0) == 32

theorem mmFiber64Parent_0_ok : mmFiber64ParentCheck 0 = true := by decide
theorem mmFiber64Parent_1_ok : mmFiber64ParentCheck 1 = true := by decide
theorem mmFiber64Parent_2_ok : mmFiber64ParentCheck 2 = true := by decide
theorem mmFiber64Parent_3_ok : mmFiber64ParentCheck 3 = true := by decide
theorem mmFiber64Parent_4_ok : mmFiber64ParentCheck 4 = true := by decide
theorem mmFiber64Parent_5_ok : mmFiber64ParentCheck 5 = true := by decide
theorem mmFiber64Parent_6_ok : mmFiber64ParentCheck 6 = true := by decide
theorem mmFiber64Parent_7_ok : mmFiber64ParentCheck 7 = true := by decide

def mmFiber64CertificateAudit : Bool :=
  mmFiber64SourcesCheck &&
    mmFiber64RowCheck 0 &&
    mmFiber64RowCheck 1 &&
    mmFiber64RowCheck 2 &&
    mmFiber64RowCheck 3 &&
    mmFiber64RowCheck 4 &&
    mmFiber64RowCheck 5 &&
    mmFiber64RowCheck 6 &&
    mmFiber64RowCheck 7 &&
    mmFiber64ParentCheck 0 &&
    mmFiber64ParentCheck 1 &&
    mmFiber64ParentCheck 2 &&
    mmFiber64ParentCheck 3 &&
    mmFiber64ParentCheck 4 &&
    mmFiber64ParentCheck 5 &&
    mmFiber64ParentCheck 6 &&
    mmFiber64ParentCheck 7

theorem mmFiber64CertificateAudit_ok :
    mmFiber64CertificateAudit = true := by
  simp [mmFiber64CertificateAudit,
    mmFiber64SourcesCheck_ok,
    mmFiber64Row_0_ok,
    mmFiber64Row_1_ok,
    mmFiber64Row_2_ok,
    mmFiber64Row_3_ok,
    mmFiber64Row_4_ok,
    mmFiber64Row_5_ok,
    mmFiber64Row_6_ok,
    mmFiber64Row_7_ok,
    mmFiber64Parent_0_ok,
    mmFiber64Parent_1_ok,
    mmFiber64Parent_2_ok,
    mmFiber64Parent_3_ok,
    mmFiber64Parent_4_ok,
    mmFiber64Parent_5_ok,
    mmFiber64Parent_6_ok,
    mmFiber64Parent_7_ok]

def mmFiber65Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.p]

def mmFiber65Expected : List Nat :=
  []

def mmFiber65Rows : List DirectChainParentRow :=
  []

def mmFiber65RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber65Rows i default

def mmFiber65SourcesCheck : Bool :=
  (mmFiber65Rows.map fun row => row.source) == mmFiber65Expected

theorem mmFiber65SourcesCheck_ok :
    mmFiber65SourcesCheck = true := by
  decide

def mmFiber65RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber65Key mmFiber65Expected (mmFiber65RowAt i)

def mmFiber65ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber65Rows mmMaxParentDepth (listGetD mmFiber65Expected i 0) == 0

def mmFiber65CertificateAudit : Bool :=
  mmFiber65SourcesCheck

theorem mmFiber65CertificateAudit_ok :
    mmFiber65CertificateAudit = true := by
  simp [mmFiber65CertificateAudit,
    mmFiber65SourcesCheck_ok]

def mmFiber66Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.r]

def mmFiber66Expected : List Nat :=
  []

def mmFiber66Rows : List DirectChainParentRow :=
  []

def mmFiber66RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber66Rows i default

def mmFiber66SourcesCheck : Bool :=
  (mmFiber66Rows.map fun row => row.source) == mmFiber66Expected

theorem mmFiber66SourcesCheck_ok :
    mmFiber66SourcesCheck = true := by
  decide

def mmFiber66RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber66Key mmFiber66Expected (mmFiber66RowAt i)

def mmFiber66ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber66Rows mmMaxParentDepth (listGetD mmFiber66Expected i 0) == 0

def mmFiber66CertificateAudit : Bool :=
  mmFiber66SourcesCheck

theorem mmFiber66CertificateAudit_ok :
    mmFiber66CertificateAudit = true := by
  simp [mmFiber66CertificateAudit,
    mmFiber66SourcesCheck_ok]

def mmFiber67Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.b]

def mmFiber67Expected : List Nat :=
  []

def mmFiber67Rows : List DirectChainParentRow :=
  []

def mmFiber67RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber67Rows i default

def mmFiber67SourcesCheck : Bool :=
  (mmFiber67Rows.map fun row => row.source) == mmFiber67Expected

theorem mmFiber67SourcesCheck_ok :
    mmFiber67SourcesCheck = true := by
  decide

def mmFiber67RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber67Key mmFiber67Expected (mmFiber67RowAt i)

def mmFiber67ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber67Rows mmMaxParentDepth (listGetD mmFiber67Expected i 0) == 0

def mmFiber67CertificateAudit : Bool :=
  mmFiber67SourcesCheck

theorem mmFiber67CertificateAudit_ok :
    mmFiber67CertificateAudit = true := by
  simp [mmFiber67CertificateAudit,
    mmFiber67SourcesCheck_ok]

def mmFiber68Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.p]

def mmFiber68Expected : List Nat :=
  []

def mmFiber68Rows : List DirectChainParentRow :=
  []

def mmFiber68RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber68Rows i default

def mmFiber68SourcesCheck : Bool :=
  (mmFiber68Rows.map fun row => row.source) == mmFiber68Expected

theorem mmFiber68SourcesCheck_ok :
    mmFiber68SourcesCheck = true := by
  decide

def mmFiber68RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber68Key mmFiber68Expected (mmFiber68RowAt i)

def mmFiber68ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber68Rows mmMaxParentDepth (listGetD mmFiber68Expected i 0) == 0

def mmFiber68CertificateAudit : Bool :=
  mmFiber68SourcesCheck

theorem mmFiber68CertificateAudit_ok :
    mmFiber68CertificateAudit = true := by
  simp [mmFiber68CertificateAudit,
    mmFiber68SourcesCheck_ok]

def mmFiber69Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.r]

def mmFiber69Expected : List Nat :=
  []

def mmFiber69Rows : List DirectChainParentRow :=
  []

def mmFiber69RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber69Rows i default

def mmFiber69SourcesCheck : Bool :=
  (mmFiber69Rows.map fun row => row.source) == mmFiber69Expected

theorem mmFiber69SourcesCheck_ok :
    mmFiber69SourcesCheck = true := by
  decide

def mmFiber69RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber69Key mmFiber69Expected (mmFiber69RowAt i)

def mmFiber69ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber69Rows mmMaxParentDepth (listGetD mmFiber69Expected i 0) == 0

def mmFiber69CertificateAudit : Bool :=
  mmFiber69SourcesCheck

theorem mmFiber69CertificateAudit_ok :
    mmFiber69CertificateAudit = true := by
  simp [mmFiber69CertificateAudit,
    mmFiber69SourcesCheck_ok]

def mmFiber70Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.b]

def mmFiber70Expected : List Nat :=
  [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]

def mmFiber70Rows : List DirectChainParentRow :=
  [ directRow 768 768 156 148 156 148 default
  , directRow 769 768 156 149 156 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 770 769 156 150 156 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 771 768 156 151 156 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 772 768 156 164 156 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 773 769 156 165 156 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 774 772 156 166 156 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 775 771 156 167 156 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 776 768 157 156 156 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 777 769 157 157 156 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 778 770 157 158 156 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 779 771 157 159 156 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 780 772 157 172 156 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 781 773 157 173 156 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 782 774 157 174 156 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 783 775 157 175 156 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 784 788 158 0 158 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 785 789 158 1 158 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 786 780 158 2 157 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 787 781 158 3 157 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 788 776 158 48 157 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 789 777 158 49 157 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 790 778 158 50 157 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 791 779 158 51 157 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 792 796 159 8 159 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 793 797 159 9 159 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 794 772 159 10 156 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 795 773 159 11 156 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 796 768 159 56 156 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 797 769 159 57 156 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 798 770 159 58 156 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 799 771 159 59 156 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 848 768 172 132 156 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 849 769 172 133 156 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 850 770 172 134 156 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 851 771 172 135 156 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 852 772 172 180 156 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 853 773 172 181 156 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 854 774 172 182 156 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 855 775 172 183 156 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 856 776 173 140 157 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 857 777 173 141 157 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 858 778 173 142 157 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 859 779 173 143 157 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 860 780 173 188 157 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 861 781 173 189 157 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 862 782 173 190 157 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 863 783 173 191 157 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 864 848 174 64 172 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 865 849 174 65 172 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 866 864 174 66 174 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 867 851 174 67 172 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 868 852 174 116 172 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 869 853 174 117 172 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 870 865 174 118 174 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 871 864 174 119 174 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 872 856 175 72 173 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 873 857 175 73 173 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 874 794 175 74 159 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 875 795 175 75 159 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 876 796 175 124 159 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 877 797 175 125 159 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 878 876 175 126 175 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 879 799 175 127 159 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mmFiber70RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber70Rows i default

def mmFiber70SourcesCheck : Bool :=
  (mmFiber70Rows.map fun row => row.source) == mmFiber70Expected

theorem mmFiber70SourcesCheck_ok :
    mmFiber70SourcesCheck = true := by
  decide

def mmFiber70RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt i)

theorem mmFiber70Row_0_ok : mmFiber70RowCheck 0 = true := by decide
theorem mmFiber70Row_1_ok : mmFiber70RowCheck 1 = true := by decide
theorem mmFiber70Row_2_ok : mmFiber70RowCheck 2 = true := by decide
theorem mmFiber70Row_3_ok : mmFiber70RowCheck 3 = true := by decide
theorem mmFiber70Row_4_ok : mmFiber70RowCheck 4 = true := by decide
theorem mmFiber70Row_5_ok : mmFiber70RowCheck 5 = true := by decide
theorem mmFiber70Row_6_ok : mmFiber70RowCheck 6 = true := by decide
theorem mmFiber70Row_7_ok : mmFiber70RowCheck 7 = true := by decide
theorem mmFiber70Row_8_ok : mmFiber70RowCheck 8 = true := by decide
theorem mmFiber70Row_9_ok : mmFiber70RowCheck 9 = true := by decide
theorem mmFiber70Row_10_ok : mmFiber70RowCheck 10 = true := by decide
theorem mmFiber70Row_11_ok : mmFiber70RowCheck 11 = true := by decide
theorem mmFiber70Row_12_ok : mmFiber70RowCheck 12 = true := by decide
theorem mmFiber70Row_13_ok : mmFiber70RowCheck 13 = true := by decide
theorem mmFiber70Row_14_ok : mmFiber70RowCheck 14 = true := by decide
theorem mmFiber70Row_15_ok : mmFiber70RowCheck 15 = true := by decide
theorem mmFiber70Row_16_ok : mmFiber70RowCheck 16 = true := by decide
theorem mmFiber70Row_17_ok : mmFiber70RowCheck 17 = true := by decide
theorem mmFiber70Row_18_ok : mmFiber70RowCheck 18 = true := by decide
theorem mmFiber70Row_19_ok : mmFiber70RowCheck 19 = true := by decide
theorem mmFiber70Row_20_ok : mmFiber70RowCheck 20 = true := by decide
theorem mmFiber70Row_21_ok : mmFiber70RowCheck 21 = true := by decide
theorem mmFiber70Row_22_ok : mmFiber70RowCheck 22 = true := by decide
theorem mmFiber70Row_23_ok : mmFiber70RowCheck 23 = true := by decide
theorem mmFiber70Row_24_ok : mmFiber70RowCheck 24 = true := by decide
theorem mmFiber70Row_25_ok : mmFiber70RowCheck 25 = true := by decide
theorem mmFiber70Row_26_ok : mmFiber70RowCheck 26 = true := by decide
theorem mmFiber70Row_27_ok : mmFiber70RowCheck 27 = true := by decide
theorem mmFiber70Row_28_ok : mmFiber70RowCheck 28 = true := by decide
theorem mmFiber70Row_29_ok : mmFiber70RowCheck 29 = true := by decide
theorem mmFiber70Row_30_ok : mmFiber70RowCheck 30 = true := by decide
theorem mmFiber70Row_31_ok : mmFiber70RowCheck 31 = true := by decide
theorem mmFiber70Row_32_ok : mmFiber70RowCheck 32 = true := by decide
theorem mmFiber70Row_33_ok : mmFiber70RowCheck 33 = true := by decide
theorem mmFiber70Row_34_ok : mmFiber70RowCheck 34 = true := by decide
theorem mmFiber70Row_35_ok : mmFiber70RowCheck 35 = true := by decide
theorem mmFiber70Row_36_ok : mmFiber70RowCheck 36 = true := by decide
theorem mmFiber70Row_37_ok : mmFiber70RowCheck 37 = true := by decide
theorem mmFiber70Row_38_ok : mmFiber70RowCheck 38 = true := by decide
theorem mmFiber70Row_39_ok : mmFiber70RowCheck 39 = true := by decide
theorem mmFiber70Row_40_ok : mmFiber70RowCheck 40 = true := by decide
theorem mmFiber70Row_41_ok : mmFiber70RowCheck 41 = true := by decide
theorem mmFiber70Row_42_ok : mmFiber70RowCheck 42 = true := by decide
theorem mmFiber70Row_43_ok : mmFiber70RowCheck 43 = true := by decide
theorem mmFiber70Row_44_ok : mmFiber70RowCheck 44 = true := by decide
theorem mmFiber70Row_45_ok : mmFiber70RowCheck 45 = true := by decide
theorem mmFiber70Row_46_ok : mmFiber70RowCheck 46 = true := by decide
theorem mmFiber70Row_47_ok : mmFiber70RowCheck 47 = true := by decide
theorem mmFiber70Row_48_ok : mmFiber70RowCheck 48 = true := by decide
theorem mmFiber70Row_49_ok : mmFiber70RowCheck 49 = true := by decide
theorem mmFiber70Row_50_ok : mmFiber70RowCheck 50 = true := by decide
theorem mmFiber70Row_51_ok : mmFiber70RowCheck 51 = true := by decide
theorem mmFiber70Row_52_ok : mmFiber70RowCheck 52 = true := by decide
theorem mmFiber70Row_53_ok : mmFiber70RowCheck 53 = true := by decide
theorem mmFiber70Row_54_ok : mmFiber70RowCheck 54 = true := by decide
theorem mmFiber70Row_55_ok : mmFiber70RowCheck 55 = true := by decide
theorem mmFiber70Row_56_ok : mmFiber70RowCheck 56 = true := by decide
theorem mmFiber70Row_57_ok : mmFiber70RowCheck 57 = true := by decide
theorem mmFiber70Row_58_ok : mmFiber70RowCheck 58 = true := by decide
theorem mmFiber70Row_59_ok : mmFiber70RowCheck 59 = true := by decide
theorem mmFiber70Row_60_ok : mmFiber70RowCheck 60 = true := by decide
theorem mmFiber70Row_61_ok : mmFiber70RowCheck 61 = true := by decide
theorem mmFiber70Row_62_ok : mmFiber70RowCheck 62 = true := by decide
theorem mmFiber70Row_63_ok : mmFiber70RowCheck 63 = true := by decide

def mmFiber70ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber70Rows mmMaxParentDepth (listGetD mmFiber70Expected i 0) == 768

theorem mmFiber70Parent_0_ok : mmFiber70ParentCheck 0 = true := by decide
theorem mmFiber70Parent_1_ok : mmFiber70ParentCheck 1 = true := by decide
theorem mmFiber70Parent_2_ok : mmFiber70ParentCheck 2 = true := by decide
theorem mmFiber70Parent_3_ok : mmFiber70ParentCheck 3 = true := by decide
theorem mmFiber70Parent_4_ok : mmFiber70ParentCheck 4 = true := by decide
theorem mmFiber70Parent_5_ok : mmFiber70ParentCheck 5 = true := by decide
theorem mmFiber70Parent_6_ok : mmFiber70ParentCheck 6 = true := by decide
theorem mmFiber70Parent_7_ok : mmFiber70ParentCheck 7 = true := by decide
theorem mmFiber70Parent_8_ok : mmFiber70ParentCheck 8 = true := by decide
theorem mmFiber70Parent_9_ok : mmFiber70ParentCheck 9 = true := by decide
theorem mmFiber70Parent_10_ok : mmFiber70ParentCheck 10 = true := by decide
theorem mmFiber70Parent_11_ok : mmFiber70ParentCheck 11 = true := by decide
theorem mmFiber70Parent_12_ok : mmFiber70ParentCheck 12 = true := by decide
theorem mmFiber70Parent_13_ok : mmFiber70ParentCheck 13 = true := by decide
theorem mmFiber70Parent_14_ok : mmFiber70ParentCheck 14 = true := by decide
theorem mmFiber70Parent_15_ok : mmFiber70ParentCheck 15 = true := by decide
theorem mmFiber70Parent_16_ok : mmFiber70ParentCheck 16 = true := by decide
theorem mmFiber70Parent_17_ok : mmFiber70ParentCheck 17 = true := by decide
theorem mmFiber70Parent_18_ok : mmFiber70ParentCheck 18 = true := by decide
theorem mmFiber70Parent_19_ok : mmFiber70ParentCheck 19 = true := by decide
theorem mmFiber70Parent_20_ok : mmFiber70ParentCheck 20 = true := by decide
theorem mmFiber70Parent_21_ok : mmFiber70ParentCheck 21 = true := by decide
theorem mmFiber70Parent_22_ok : mmFiber70ParentCheck 22 = true := by decide
theorem mmFiber70Parent_23_ok : mmFiber70ParentCheck 23 = true := by decide
theorem mmFiber70Parent_24_ok : mmFiber70ParentCheck 24 = true := by decide
theorem mmFiber70Parent_25_ok : mmFiber70ParentCheck 25 = true := by decide
theorem mmFiber70Parent_26_ok : mmFiber70ParentCheck 26 = true := by decide
theorem mmFiber70Parent_27_ok : mmFiber70ParentCheck 27 = true := by decide
theorem mmFiber70Parent_28_ok : mmFiber70ParentCheck 28 = true := by decide
theorem mmFiber70Parent_29_ok : mmFiber70ParentCheck 29 = true := by decide
theorem mmFiber70Parent_30_ok : mmFiber70ParentCheck 30 = true := by decide
theorem mmFiber70Parent_31_ok : mmFiber70ParentCheck 31 = true := by decide
theorem mmFiber70Parent_32_ok : mmFiber70ParentCheck 32 = true := by decide
theorem mmFiber70Parent_33_ok : mmFiber70ParentCheck 33 = true := by decide
theorem mmFiber70Parent_34_ok : mmFiber70ParentCheck 34 = true := by decide
theorem mmFiber70Parent_35_ok : mmFiber70ParentCheck 35 = true := by decide
theorem mmFiber70Parent_36_ok : mmFiber70ParentCheck 36 = true := by decide
theorem mmFiber70Parent_37_ok : mmFiber70ParentCheck 37 = true := by decide
theorem mmFiber70Parent_38_ok : mmFiber70ParentCheck 38 = true := by decide
theorem mmFiber70Parent_39_ok : mmFiber70ParentCheck 39 = true := by decide
theorem mmFiber70Parent_40_ok : mmFiber70ParentCheck 40 = true := by decide
theorem mmFiber70Parent_41_ok : mmFiber70ParentCheck 41 = true := by decide
theorem mmFiber70Parent_42_ok : mmFiber70ParentCheck 42 = true := by decide
theorem mmFiber70Parent_43_ok : mmFiber70ParentCheck 43 = true := by decide
theorem mmFiber70Parent_44_ok : mmFiber70ParentCheck 44 = true := by decide
theorem mmFiber70Parent_45_ok : mmFiber70ParentCheck 45 = true := by decide
theorem mmFiber70Parent_46_ok : mmFiber70ParentCheck 46 = true := by decide
theorem mmFiber70Parent_47_ok : mmFiber70ParentCheck 47 = true := by decide
theorem mmFiber70Parent_48_ok : mmFiber70ParentCheck 48 = true := by decide
theorem mmFiber70Parent_49_ok : mmFiber70ParentCheck 49 = true := by decide
theorem mmFiber70Parent_50_ok : mmFiber70ParentCheck 50 = true := by decide
theorem mmFiber70Parent_51_ok : mmFiber70ParentCheck 51 = true := by decide
theorem mmFiber70Parent_52_ok : mmFiber70ParentCheck 52 = true := by decide
theorem mmFiber70Parent_53_ok : mmFiber70ParentCheck 53 = true := by decide
theorem mmFiber70Parent_54_ok : mmFiber70ParentCheck 54 = true := by decide
theorem mmFiber70Parent_55_ok : mmFiber70ParentCheck 55 = true := by decide
theorem mmFiber70Parent_56_ok : mmFiber70ParentCheck 56 = true := by decide
theorem mmFiber70Parent_57_ok : mmFiber70ParentCheck 57 = true := by decide
theorem mmFiber70Parent_58_ok : mmFiber70ParentCheck 58 = true := by decide
theorem mmFiber70Parent_59_ok : mmFiber70ParentCheck 59 = true := by decide
theorem mmFiber70Parent_60_ok : mmFiber70ParentCheck 60 = true := by decide
theorem mmFiber70Parent_61_ok : mmFiber70ParentCheck 61 = true := by decide
theorem mmFiber70Parent_62_ok : mmFiber70ParentCheck 62 = true := by decide
theorem mmFiber70Parent_63_ok : mmFiber70ParentCheck 63 = true := by decide

def mmFiber70CertificateAudit : Bool :=
  mmFiber70SourcesCheck &&
    mmFiber70RowCheck 0 &&
    mmFiber70RowCheck 1 &&
    mmFiber70RowCheck 2 &&
    mmFiber70RowCheck 3 &&
    mmFiber70RowCheck 4 &&
    mmFiber70RowCheck 5 &&
    mmFiber70RowCheck 6 &&
    mmFiber70RowCheck 7 &&
    mmFiber70RowCheck 8 &&
    mmFiber70RowCheck 9 &&
    mmFiber70RowCheck 10 &&
    mmFiber70RowCheck 11 &&
    mmFiber70RowCheck 12 &&
    mmFiber70RowCheck 13 &&
    mmFiber70RowCheck 14 &&
    mmFiber70RowCheck 15 &&
    mmFiber70RowCheck 16 &&
    mmFiber70RowCheck 17 &&
    mmFiber70RowCheck 18 &&
    mmFiber70RowCheck 19 &&
    mmFiber70RowCheck 20 &&
    mmFiber70RowCheck 21 &&
    mmFiber70RowCheck 22 &&
    mmFiber70RowCheck 23 &&
    mmFiber70RowCheck 24 &&
    mmFiber70RowCheck 25 &&
    mmFiber70RowCheck 26 &&
    mmFiber70RowCheck 27 &&
    mmFiber70RowCheck 28 &&
    mmFiber70RowCheck 29 &&
    mmFiber70RowCheck 30 &&
    mmFiber70RowCheck 31 &&
    mmFiber70RowCheck 32 &&
    mmFiber70RowCheck 33 &&
    mmFiber70RowCheck 34 &&
    mmFiber70RowCheck 35 &&
    mmFiber70RowCheck 36 &&
    mmFiber70RowCheck 37 &&
    mmFiber70RowCheck 38 &&
    mmFiber70RowCheck 39 &&
    mmFiber70RowCheck 40 &&
    mmFiber70RowCheck 41 &&
    mmFiber70RowCheck 42 &&
    mmFiber70RowCheck 43 &&
    mmFiber70RowCheck 44 &&
    mmFiber70RowCheck 45 &&
    mmFiber70RowCheck 46 &&
    mmFiber70RowCheck 47 &&
    mmFiber70RowCheck 48 &&
    mmFiber70RowCheck 49 &&
    mmFiber70RowCheck 50 &&
    mmFiber70RowCheck 51 &&
    mmFiber70RowCheck 52 &&
    mmFiber70RowCheck 53 &&
    mmFiber70RowCheck 54 &&
    mmFiber70RowCheck 55 &&
    mmFiber70RowCheck 56 &&
    mmFiber70RowCheck 57 &&
    mmFiber70RowCheck 58 &&
    mmFiber70RowCheck 59 &&
    mmFiber70RowCheck 60 &&
    mmFiber70RowCheck 61 &&
    mmFiber70RowCheck 62 &&
    mmFiber70RowCheck 63 &&
    mmFiber70ParentCheck 0 &&
    mmFiber70ParentCheck 1 &&
    mmFiber70ParentCheck 2 &&
    mmFiber70ParentCheck 3 &&
    mmFiber70ParentCheck 4 &&
    mmFiber70ParentCheck 5 &&
    mmFiber70ParentCheck 6 &&
    mmFiber70ParentCheck 7 &&
    mmFiber70ParentCheck 8 &&
    mmFiber70ParentCheck 9 &&
    mmFiber70ParentCheck 10 &&
    mmFiber70ParentCheck 11 &&
    mmFiber70ParentCheck 12 &&
    mmFiber70ParentCheck 13 &&
    mmFiber70ParentCheck 14 &&
    mmFiber70ParentCheck 15 &&
    mmFiber70ParentCheck 16 &&
    mmFiber70ParentCheck 17 &&
    mmFiber70ParentCheck 18 &&
    mmFiber70ParentCheck 19 &&
    mmFiber70ParentCheck 20 &&
    mmFiber70ParentCheck 21 &&
    mmFiber70ParentCheck 22 &&
    mmFiber70ParentCheck 23 &&
    mmFiber70ParentCheck 24 &&
    mmFiber70ParentCheck 25 &&
    mmFiber70ParentCheck 26 &&
    mmFiber70ParentCheck 27 &&
    mmFiber70ParentCheck 28 &&
    mmFiber70ParentCheck 29 &&
    mmFiber70ParentCheck 30 &&
    mmFiber70ParentCheck 31 &&
    mmFiber70ParentCheck 32 &&
    mmFiber70ParentCheck 33 &&
    mmFiber70ParentCheck 34 &&
    mmFiber70ParentCheck 35 &&
    mmFiber70ParentCheck 36 &&
    mmFiber70ParentCheck 37 &&
    mmFiber70ParentCheck 38 &&
    mmFiber70ParentCheck 39 &&
    mmFiber70ParentCheck 40 &&
    mmFiber70ParentCheck 41 &&
    mmFiber70ParentCheck 42 &&
    mmFiber70ParentCheck 43 &&
    mmFiber70ParentCheck 44 &&
    mmFiber70ParentCheck 45 &&
    mmFiber70ParentCheck 46 &&
    mmFiber70ParentCheck 47 &&
    mmFiber70ParentCheck 48 &&
    mmFiber70ParentCheck 49 &&
    mmFiber70ParentCheck 50 &&
    mmFiber70ParentCheck 51 &&
    mmFiber70ParentCheck 52 &&
    mmFiber70ParentCheck 53 &&
    mmFiber70ParentCheck 54 &&
    mmFiber70ParentCheck 55 &&
    mmFiber70ParentCheck 56 &&
    mmFiber70ParentCheck 57 &&
    mmFiber70ParentCheck 58 &&
    mmFiber70ParentCheck 59 &&
    mmFiber70ParentCheck 60 &&
    mmFiber70ParentCheck 61 &&
    mmFiber70ParentCheck 62 &&
    mmFiber70ParentCheck 63

theorem mmFiber70CertificateAudit_ok :
    mmFiber70CertificateAudit = true := by
  simp [mmFiber70CertificateAudit,
    mmFiber70SourcesCheck_ok,
    mmFiber70Row_0_ok,
    mmFiber70Row_1_ok,
    mmFiber70Row_2_ok,
    mmFiber70Row_3_ok,
    mmFiber70Row_4_ok,
    mmFiber70Row_5_ok,
    mmFiber70Row_6_ok,
    mmFiber70Row_7_ok,
    mmFiber70Row_8_ok,
    mmFiber70Row_9_ok,
    mmFiber70Row_10_ok,
    mmFiber70Row_11_ok,
    mmFiber70Row_12_ok,
    mmFiber70Row_13_ok,
    mmFiber70Row_14_ok,
    mmFiber70Row_15_ok,
    mmFiber70Row_16_ok,
    mmFiber70Row_17_ok,
    mmFiber70Row_18_ok,
    mmFiber70Row_19_ok,
    mmFiber70Row_20_ok,
    mmFiber70Row_21_ok,
    mmFiber70Row_22_ok,
    mmFiber70Row_23_ok,
    mmFiber70Row_24_ok,
    mmFiber70Row_25_ok,
    mmFiber70Row_26_ok,
    mmFiber70Row_27_ok,
    mmFiber70Row_28_ok,
    mmFiber70Row_29_ok,
    mmFiber70Row_30_ok,
    mmFiber70Row_31_ok,
    mmFiber70Row_32_ok,
    mmFiber70Row_33_ok,
    mmFiber70Row_34_ok,
    mmFiber70Row_35_ok,
    mmFiber70Row_36_ok,
    mmFiber70Row_37_ok,
    mmFiber70Row_38_ok,
    mmFiber70Row_39_ok,
    mmFiber70Row_40_ok,
    mmFiber70Row_41_ok,
    mmFiber70Row_42_ok,
    mmFiber70Row_43_ok,
    mmFiber70Row_44_ok,
    mmFiber70Row_45_ok,
    mmFiber70Row_46_ok,
    mmFiber70Row_47_ok,
    mmFiber70Row_48_ok,
    mmFiber70Row_49_ok,
    mmFiber70Row_50_ok,
    mmFiber70Row_51_ok,
    mmFiber70Row_52_ok,
    mmFiber70Row_53_ok,
    mmFiber70Row_54_ok,
    mmFiber70Row_55_ok,
    mmFiber70Row_56_ok,
    mmFiber70Row_57_ok,
    mmFiber70Row_58_ok,
    mmFiber70Row_59_ok,
    mmFiber70Row_60_ok,
    mmFiber70Row_61_ok,
    mmFiber70Row_62_ok,
    mmFiber70Row_63_ok,
    mmFiber70Parent_0_ok,
    mmFiber70Parent_1_ok,
    mmFiber70Parent_2_ok,
    mmFiber70Parent_3_ok,
    mmFiber70Parent_4_ok,
    mmFiber70Parent_5_ok,
    mmFiber70Parent_6_ok,
    mmFiber70Parent_7_ok,
    mmFiber70Parent_8_ok,
    mmFiber70Parent_9_ok,
    mmFiber70Parent_10_ok,
    mmFiber70Parent_11_ok,
    mmFiber70Parent_12_ok,
    mmFiber70Parent_13_ok,
    mmFiber70Parent_14_ok,
    mmFiber70Parent_15_ok,
    mmFiber70Parent_16_ok,
    mmFiber70Parent_17_ok,
    mmFiber70Parent_18_ok,
    mmFiber70Parent_19_ok,
    mmFiber70Parent_20_ok,
    mmFiber70Parent_21_ok,
    mmFiber70Parent_22_ok,
    mmFiber70Parent_23_ok,
    mmFiber70Parent_24_ok,
    mmFiber70Parent_25_ok,
    mmFiber70Parent_26_ok,
    mmFiber70Parent_27_ok,
    mmFiber70Parent_28_ok,
    mmFiber70Parent_29_ok,
    mmFiber70Parent_30_ok,
    mmFiber70Parent_31_ok,
    mmFiber70Parent_32_ok,
    mmFiber70Parent_33_ok,
    mmFiber70Parent_34_ok,
    mmFiber70Parent_35_ok,
    mmFiber70Parent_36_ok,
    mmFiber70Parent_37_ok,
    mmFiber70Parent_38_ok,
    mmFiber70Parent_39_ok,
    mmFiber70Parent_40_ok,
    mmFiber70Parent_41_ok,
    mmFiber70Parent_42_ok,
    mmFiber70Parent_43_ok,
    mmFiber70Parent_44_ok,
    mmFiber70Parent_45_ok,
    mmFiber70Parent_46_ok,
    mmFiber70Parent_47_ok,
    mmFiber70Parent_48_ok,
    mmFiber70Parent_49_ok,
    mmFiber70Parent_50_ok,
    mmFiber70Parent_51_ok,
    mmFiber70Parent_52_ok,
    mmFiber70Parent_53_ok,
    mmFiber70Parent_54_ok,
    mmFiber70Parent_55_ok,
    mmFiber70Parent_56_ok,
    mmFiber70Parent_57_ok,
    mmFiber70Parent_58_ok,
    mmFiber70Parent_59_ok,
    mmFiber70Parent_60_ok,
    mmFiber70Parent_61_ok,
    mmFiber70Parent_62_ok,
    mmFiber70Parent_63_ok]

def mmFiber71Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.p]

def mmFiber71Expected : List Nat :=
  [472, 473, 474, 475, 476, 477, 478, 479]

def mmFiber71Rows : List DirectChainParentRow :=
  [ directRow 472 472 92 144 92 144 default
  , directRow 473 472 92 145 92 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 474 473 92 146 92 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 475 472 92 147 92 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 476 472 93 152 92 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 477 473 93 153 92 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 478 474 93 154 92 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 479 475 93 155 92 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber71RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber71Rows i default

def mmFiber71SourcesCheck : Bool :=
  (mmFiber71Rows.map fun row => row.source) == mmFiber71Expected

theorem mmFiber71SourcesCheck_ok :
    mmFiber71SourcesCheck = true := by
  decide

def mmFiber71RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt i)

theorem mmFiber71Row_0_ok : mmFiber71RowCheck 0 = true := by decide
theorem mmFiber71Row_1_ok : mmFiber71RowCheck 1 = true := by decide
theorem mmFiber71Row_2_ok : mmFiber71RowCheck 2 = true := by decide
theorem mmFiber71Row_3_ok : mmFiber71RowCheck 3 = true := by decide
theorem mmFiber71Row_4_ok : mmFiber71RowCheck 4 = true := by decide
theorem mmFiber71Row_5_ok : mmFiber71RowCheck 5 = true := by decide
theorem mmFiber71Row_6_ok : mmFiber71RowCheck 6 = true := by decide
theorem mmFiber71Row_7_ok : mmFiber71RowCheck 7 = true := by decide

def mmFiber71ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber71Rows mmMaxParentDepth (listGetD mmFiber71Expected i 0) == 472

theorem mmFiber71Parent_0_ok : mmFiber71ParentCheck 0 = true := by decide
theorem mmFiber71Parent_1_ok : mmFiber71ParentCheck 1 = true := by decide
theorem mmFiber71Parent_2_ok : mmFiber71ParentCheck 2 = true := by decide
theorem mmFiber71Parent_3_ok : mmFiber71ParentCheck 3 = true := by decide
theorem mmFiber71Parent_4_ok : mmFiber71ParentCheck 4 = true := by decide
theorem mmFiber71Parent_5_ok : mmFiber71ParentCheck 5 = true := by decide
theorem mmFiber71Parent_6_ok : mmFiber71ParentCheck 6 = true := by decide
theorem mmFiber71Parent_7_ok : mmFiber71ParentCheck 7 = true := by decide

def mmFiber71CertificateAudit : Bool :=
  mmFiber71SourcesCheck &&
    mmFiber71RowCheck 0 &&
    mmFiber71RowCheck 1 &&
    mmFiber71RowCheck 2 &&
    mmFiber71RowCheck 3 &&
    mmFiber71RowCheck 4 &&
    mmFiber71RowCheck 5 &&
    mmFiber71RowCheck 6 &&
    mmFiber71RowCheck 7 &&
    mmFiber71ParentCheck 0 &&
    mmFiber71ParentCheck 1 &&
    mmFiber71ParentCheck 2 &&
    mmFiber71ParentCheck 3 &&
    mmFiber71ParentCheck 4 &&
    mmFiber71ParentCheck 5 &&
    mmFiber71ParentCheck 6 &&
    mmFiber71ParentCheck 7

theorem mmFiber71CertificateAudit_ok :
    mmFiber71CertificateAudit = true := by
  simp [mmFiber71CertificateAudit,
    mmFiber71SourcesCheck_ok,
    mmFiber71Row_0_ok,
    mmFiber71Row_1_ok,
    mmFiber71Row_2_ok,
    mmFiber71Row_3_ok,
    mmFiber71Row_4_ok,
    mmFiber71Row_5_ok,
    mmFiber71Row_6_ok,
    mmFiber71Row_7_ok,
    mmFiber71Parent_0_ok,
    mmFiber71Parent_1_ok,
    mmFiber71Parent_2_ok,
    mmFiber71Parent_3_ok,
    mmFiber71Parent_4_ok,
    mmFiber71Parent_5_ok,
    mmFiber71Parent_6_ok,
    mmFiber71Parent_7_ok]

def mmFiber72Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.r]

def mmFiber72Expected : List Nat :=
  [648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919]

def mmFiber72Rows : List DirectChainParentRow :=
  [ directRow 648 648 132 148 132 148 default
  , directRow 649 648 132 149 132 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 650 649 132 150 132 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 651 648 132 151 132 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 652 648 132 164 132 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 653 649 132 165 132 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 654 652 132 166 132 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 655 651 132 167 132 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 656 648 133 156 132 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 657 649 133 157 132 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 658 650 133 158 132 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 659 651 133 159 132 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 660 652 133 172 132 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 661 653 133 173 132 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 662 654 133 174 132 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 663 655 133 175 132 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 664 668 134 0 134 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 665 669 134 1 134 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 666 660 134 2 133 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 667 661 134 3 133 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 668 656 134 48 133 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 669 657 134 49 133 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 670 658 134 50 133 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 671 659 134 51 133 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 672 676 135 8 135 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 673 677 135 9 135 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 674 652 135 10 132 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 675 653 135 11 132 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 676 648 135 56 132 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 677 649 135 57 132 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 678 650 135 58 132 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 679 651 135 59 132 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 888 648 180 132 132 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 889 649 180 133 132 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 890 650 180 134 132 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 891 651 180 135 132 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 892 652 180 180 132 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 893 653 180 181 132 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 894 654 180 182 132 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 895 655 180 183 132 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 896 656 181 140 133 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 897 657 181 141 133 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 898 658 181 142 133 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 899 659 181 143 133 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 900 660 181 188 133 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 901 661 181 189 133 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 902 662 181 190 133 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 903 663 181 191 133 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 904 888 182 64 180 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 905 889 182 65 180 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 906 904 182 66 182 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 907 891 182 67 180 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 908 892 182 116 180 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 909 893 182 117 180 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 910 905 182 118 182 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 911 904 182 119 182 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 912 896 183 72 181 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 913 897 183 73 181 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 914 674 183 74 135 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 915 675 183 75 135 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 916 676 183 124 135 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 917 677 183 125 135 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 918 916 183 126 183 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 919 679 183 127 135 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mmFiber72RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber72Rows i default

def mmFiber72SourcesCheck : Bool :=
  (mmFiber72Rows.map fun row => row.source) == mmFiber72Expected

theorem mmFiber72SourcesCheck_ok :
    mmFiber72SourcesCheck = true := by
  decide

def mmFiber72RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt i)

theorem mmFiber72Row_0_ok : mmFiber72RowCheck 0 = true := by decide
theorem mmFiber72Row_1_ok : mmFiber72RowCheck 1 = true := by decide
theorem mmFiber72Row_2_ok : mmFiber72RowCheck 2 = true := by decide
theorem mmFiber72Row_3_ok : mmFiber72RowCheck 3 = true := by decide
theorem mmFiber72Row_4_ok : mmFiber72RowCheck 4 = true := by decide
theorem mmFiber72Row_5_ok : mmFiber72RowCheck 5 = true := by decide
theorem mmFiber72Row_6_ok : mmFiber72RowCheck 6 = true := by decide
theorem mmFiber72Row_7_ok : mmFiber72RowCheck 7 = true := by decide
theorem mmFiber72Row_8_ok : mmFiber72RowCheck 8 = true := by decide
theorem mmFiber72Row_9_ok : mmFiber72RowCheck 9 = true := by decide
theorem mmFiber72Row_10_ok : mmFiber72RowCheck 10 = true := by decide
theorem mmFiber72Row_11_ok : mmFiber72RowCheck 11 = true := by decide
theorem mmFiber72Row_12_ok : mmFiber72RowCheck 12 = true := by decide
theorem mmFiber72Row_13_ok : mmFiber72RowCheck 13 = true := by decide
theorem mmFiber72Row_14_ok : mmFiber72RowCheck 14 = true := by decide
theorem mmFiber72Row_15_ok : mmFiber72RowCheck 15 = true := by decide
theorem mmFiber72Row_16_ok : mmFiber72RowCheck 16 = true := by decide
theorem mmFiber72Row_17_ok : mmFiber72RowCheck 17 = true := by decide
theorem mmFiber72Row_18_ok : mmFiber72RowCheck 18 = true := by decide
theorem mmFiber72Row_19_ok : mmFiber72RowCheck 19 = true := by decide
theorem mmFiber72Row_20_ok : mmFiber72RowCheck 20 = true := by decide
theorem mmFiber72Row_21_ok : mmFiber72RowCheck 21 = true := by decide
theorem mmFiber72Row_22_ok : mmFiber72RowCheck 22 = true := by decide
theorem mmFiber72Row_23_ok : mmFiber72RowCheck 23 = true := by decide
theorem mmFiber72Row_24_ok : mmFiber72RowCheck 24 = true := by decide
theorem mmFiber72Row_25_ok : mmFiber72RowCheck 25 = true := by decide
theorem mmFiber72Row_26_ok : mmFiber72RowCheck 26 = true := by decide
theorem mmFiber72Row_27_ok : mmFiber72RowCheck 27 = true := by decide
theorem mmFiber72Row_28_ok : mmFiber72RowCheck 28 = true := by decide
theorem mmFiber72Row_29_ok : mmFiber72RowCheck 29 = true := by decide
theorem mmFiber72Row_30_ok : mmFiber72RowCheck 30 = true := by decide
theorem mmFiber72Row_31_ok : mmFiber72RowCheck 31 = true := by decide
theorem mmFiber72Row_32_ok : mmFiber72RowCheck 32 = true := by decide
theorem mmFiber72Row_33_ok : mmFiber72RowCheck 33 = true := by decide
theorem mmFiber72Row_34_ok : mmFiber72RowCheck 34 = true := by decide
theorem mmFiber72Row_35_ok : mmFiber72RowCheck 35 = true := by decide
theorem mmFiber72Row_36_ok : mmFiber72RowCheck 36 = true := by decide
theorem mmFiber72Row_37_ok : mmFiber72RowCheck 37 = true := by decide
theorem mmFiber72Row_38_ok : mmFiber72RowCheck 38 = true := by decide
theorem mmFiber72Row_39_ok : mmFiber72RowCheck 39 = true := by decide
theorem mmFiber72Row_40_ok : mmFiber72RowCheck 40 = true := by decide
theorem mmFiber72Row_41_ok : mmFiber72RowCheck 41 = true := by decide
theorem mmFiber72Row_42_ok : mmFiber72RowCheck 42 = true := by decide
theorem mmFiber72Row_43_ok : mmFiber72RowCheck 43 = true := by decide
theorem mmFiber72Row_44_ok : mmFiber72RowCheck 44 = true := by decide
theorem mmFiber72Row_45_ok : mmFiber72RowCheck 45 = true := by decide
theorem mmFiber72Row_46_ok : mmFiber72RowCheck 46 = true := by decide
theorem mmFiber72Row_47_ok : mmFiber72RowCheck 47 = true := by decide
theorem mmFiber72Row_48_ok : mmFiber72RowCheck 48 = true := by decide
theorem mmFiber72Row_49_ok : mmFiber72RowCheck 49 = true := by decide
theorem mmFiber72Row_50_ok : mmFiber72RowCheck 50 = true := by decide
theorem mmFiber72Row_51_ok : mmFiber72RowCheck 51 = true := by decide
theorem mmFiber72Row_52_ok : mmFiber72RowCheck 52 = true := by decide
theorem mmFiber72Row_53_ok : mmFiber72RowCheck 53 = true := by decide
theorem mmFiber72Row_54_ok : mmFiber72RowCheck 54 = true := by decide
theorem mmFiber72Row_55_ok : mmFiber72RowCheck 55 = true := by decide
theorem mmFiber72Row_56_ok : mmFiber72RowCheck 56 = true := by decide
theorem mmFiber72Row_57_ok : mmFiber72RowCheck 57 = true := by decide
theorem mmFiber72Row_58_ok : mmFiber72RowCheck 58 = true := by decide
theorem mmFiber72Row_59_ok : mmFiber72RowCheck 59 = true := by decide
theorem mmFiber72Row_60_ok : mmFiber72RowCheck 60 = true := by decide
theorem mmFiber72Row_61_ok : mmFiber72RowCheck 61 = true := by decide
theorem mmFiber72Row_62_ok : mmFiber72RowCheck 62 = true := by decide
theorem mmFiber72Row_63_ok : mmFiber72RowCheck 63 = true := by decide

def mmFiber72ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber72Rows mmMaxParentDepth (listGetD mmFiber72Expected i 0) == 648

theorem mmFiber72Parent_0_ok : mmFiber72ParentCheck 0 = true := by decide
theorem mmFiber72Parent_1_ok : mmFiber72ParentCheck 1 = true := by decide
theorem mmFiber72Parent_2_ok : mmFiber72ParentCheck 2 = true := by decide
theorem mmFiber72Parent_3_ok : mmFiber72ParentCheck 3 = true := by decide
theorem mmFiber72Parent_4_ok : mmFiber72ParentCheck 4 = true := by decide
theorem mmFiber72Parent_5_ok : mmFiber72ParentCheck 5 = true := by decide
theorem mmFiber72Parent_6_ok : mmFiber72ParentCheck 6 = true := by decide
theorem mmFiber72Parent_7_ok : mmFiber72ParentCheck 7 = true := by decide
theorem mmFiber72Parent_8_ok : mmFiber72ParentCheck 8 = true := by decide
theorem mmFiber72Parent_9_ok : mmFiber72ParentCheck 9 = true := by decide
theorem mmFiber72Parent_10_ok : mmFiber72ParentCheck 10 = true := by decide
theorem mmFiber72Parent_11_ok : mmFiber72ParentCheck 11 = true := by decide
theorem mmFiber72Parent_12_ok : mmFiber72ParentCheck 12 = true := by decide
theorem mmFiber72Parent_13_ok : mmFiber72ParentCheck 13 = true := by decide
theorem mmFiber72Parent_14_ok : mmFiber72ParentCheck 14 = true := by decide
theorem mmFiber72Parent_15_ok : mmFiber72ParentCheck 15 = true := by decide
theorem mmFiber72Parent_16_ok : mmFiber72ParentCheck 16 = true := by decide
theorem mmFiber72Parent_17_ok : mmFiber72ParentCheck 17 = true := by decide
theorem mmFiber72Parent_18_ok : mmFiber72ParentCheck 18 = true := by decide
theorem mmFiber72Parent_19_ok : mmFiber72ParentCheck 19 = true := by decide
theorem mmFiber72Parent_20_ok : mmFiber72ParentCheck 20 = true := by decide
theorem mmFiber72Parent_21_ok : mmFiber72ParentCheck 21 = true := by decide
theorem mmFiber72Parent_22_ok : mmFiber72ParentCheck 22 = true := by decide
theorem mmFiber72Parent_23_ok : mmFiber72ParentCheck 23 = true := by decide
theorem mmFiber72Parent_24_ok : mmFiber72ParentCheck 24 = true := by decide
theorem mmFiber72Parent_25_ok : mmFiber72ParentCheck 25 = true := by decide
theorem mmFiber72Parent_26_ok : mmFiber72ParentCheck 26 = true := by decide
theorem mmFiber72Parent_27_ok : mmFiber72ParentCheck 27 = true := by decide
theorem mmFiber72Parent_28_ok : mmFiber72ParentCheck 28 = true := by decide
theorem mmFiber72Parent_29_ok : mmFiber72ParentCheck 29 = true := by decide
theorem mmFiber72Parent_30_ok : mmFiber72ParentCheck 30 = true := by decide
theorem mmFiber72Parent_31_ok : mmFiber72ParentCheck 31 = true := by decide
theorem mmFiber72Parent_32_ok : mmFiber72ParentCheck 32 = true := by decide
theorem mmFiber72Parent_33_ok : mmFiber72ParentCheck 33 = true := by decide
theorem mmFiber72Parent_34_ok : mmFiber72ParentCheck 34 = true := by decide
theorem mmFiber72Parent_35_ok : mmFiber72ParentCheck 35 = true := by decide
theorem mmFiber72Parent_36_ok : mmFiber72ParentCheck 36 = true := by decide
theorem mmFiber72Parent_37_ok : mmFiber72ParentCheck 37 = true := by decide
theorem mmFiber72Parent_38_ok : mmFiber72ParentCheck 38 = true := by decide
theorem mmFiber72Parent_39_ok : mmFiber72ParentCheck 39 = true := by decide
theorem mmFiber72Parent_40_ok : mmFiber72ParentCheck 40 = true := by decide
theorem mmFiber72Parent_41_ok : mmFiber72ParentCheck 41 = true := by decide
theorem mmFiber72Parent_42_ok : mmFiber72ParentCheck 42 = true := by decide
theorem mmFiber72Parent_43_ok : mmFiber72ParentCheck 43 = true := by decide
theorem mmFiber72Parent_44_ok : mmFiber72ParentCheck 44 = true := by decide
theorem mmFiber72Parent_45_ok : mmFiber72ParentCheck 45 = true := by decide
theorem mmFiber72Parent_46_ok : mmFiber72ParentCheck 46 = true := by decide
theorem mmFiber72Parent_47_ok : mmFiber72ParentCheck 47 = true := by decide
theorem mmFiber72Parent_48_ok : mmFiber72ParentCheck 48 = true := by decide
theorem mmFiber72Parent_49_ok : mmFiber72ParentCheck 49 = true := by decide
theorem mmFiber72Parent_50_ok : mmFiber72ParentCheck 50 = true := by decide
theorem mmFiber72Parent_51_ok : mmFiber72ParentCheck 51 = true := by decide
theorem mmFiber72Parent_52_ok : mmFiber72ParentCheck 52 = true := by decide
theorem mmFiber72Parent_53_ok : mmFiber72ParentCheck 53 = true := by decide
theorem mmFiber72Parent_54_ok : mmFiber72ParentCheck 54 = true := by decide
theorem mmFiber72Parent_55_ok : mmFiber72ParentCheck 55 = true := by decide
theorem mmFiber72Parent_56_ok : mmFiber72ParentCheck 56 = true := by decide
theorem mmFiber72Parent_57_ok : mmFiber72ParentCheck 57 = true := by decide
theorem mmFiber72Parent_58_ok : mmFiber72ParentCheck 58 = true := by decide
theorem mmFiber72Parent_59_ok : mmFiber72ParentCheck 59 = true := by decide
theorem mmFiber72Parent_60_ok : mmFiber72ParentCheck 60 = true := by decide
theorem mmFiber72Parent_61_ok : mmFiber72ParentCheck 61 = true := by decide
theorem mmFiber72Parent_62_ok : mmFiber72ParentCheck 62 = true := by decide
theorem mmFiber72Parent_63_ok : mmFiber72ParentCheck 63 = true := by decide

def mmFiber72CertificateAudit : Bool :=
  mmFiber72SourcesCheck &&
    mmFiber72RowCheck 0 &&
    mmFiber72RowCheck 1 &&
    mmFiber72RowCheck 2 &&
    mmFiber72RowCheck 3 &&
    mmFiber72RowCheck 4 &&
    mmFiber72RowCheck 5 &&
    mmFiber72RowCheck 6 &&
    mmFiber72RowCheck 7 &&
    mmFiber72RowCheck 8 &&
    mmFiber72RowCheck 9 &&
    mmFiber72RowCheck 10 &&
    mmFiber72RowCheck 11 &&
    mmFiber72RowCheck 12 &&
    mmFiber72RowCheck 13 &&
    mmFiber72RowCheck 14 &&
    mmFiber72RowCheck 15 &&
    mmFiber72RowCheck 16 &&
    mmFiber72RowCheck 17 &&
    mmFiber72RowCheck 18 &&
    mmFiber72RowCheck 19 &&
    mmFiber72RowCheck 20 &&
    mmFiber72RowCheck 21 &&
    mmFiber72RowCheck 22 &&
    mmFiber72RowCheck 23 &&
    mmFiber72RowCheck 24 &&
    mmFiber72RowCheck 25 &&
    mmFiber72RowCheck 26 &&
    mmFiber72RowCheck 27 &&
    mmFiber72RowCheck 28 &&
    mmFiber72RowCheck 29 &&
    mmFiber72RowCheck 30 &&
    mmFiber72RowCheck 31 &&
    mmFiber72RowCheck 32 &&
    mmFiber72RowCheck 33 &&
    mmFiber72RowCheck 34 &&
    mmFiber72RowCheck 35 &&
    mmFiber72RowCheck 36 &&
    mmFiber72RowCheck 37 &&
    mmFiber72RowCheck 38 &&
    mmFiber72RowCheck 39 &&
    mmFiber72RowCheck 40 &&
    mmFiber72RowCheck 41 &&
    mmFiber72RowCheck 42 &&
    mmFiber72RowCheck 43 &&
    mmFiber72RowCheck 44 &&
    mmFiber72RowCheck 45 &&
    mmFiber72RowCheck 46 &&
    mmFiber72RowCheck 47 &&
    mmFiber72RowCheck 48 &&
    mmFiber72RowCheck 49 &&
    mmFiber72RowCheck 50 &&
    mmFiber72RowCheck 51 &&
    mmFiber72RowCheck 52 &&
    mmFiber72RowCheck 53 &&
    mmFiber72RowCheck 54 &&
    mmFiber72RowCheck 55 &&
    mmFiber72RowCheck 56 &&
    mmFiber72RowCheck 57 &&
    mmFiber72RowCheck 58 &&
    mmFiber72RowCheck 59 &&
    mmFiber72RowCheck 60 &&
    mmFiber72RowCheck 61 &&
    mmFiber72RowCheck 62 &&
    mmFiber72RowCheck 63 &&
    mmFiber72ParentCheck 0 &&
    mmFiber72ParentCheck 1 &&
    mmFiber72ParentCheck 2 &&
    mmFiber72ParentCheck 3 &&
    mmFiber72ParentCheck 4 &&
    mmFiber72ParentCheck 5 &&
    mmFiber72ParentCheck 6 &&
    mmFiber72ParentCheck 7 &&
    mmFiber72ParentCheck 8 &&
    mmFiber72ParentCheck 9 &&
    mmFiber72ParentCheck 10 &&
    mmFiber72ParentCheck 11 &&
    mmFiber72ParentCheck 12 &&
    mmFiber72ParentCheck 13 &&
    mmFiber72ParentCheck 14 &&
    mmFiber72ParentCheck 15 &&
    mmFiber72ParentCheck 16 &&
    mmFiber72ParentCheck 17 &&
    mmFiber72ParentCheck 18 &&
    mmFiber72ParentCheck 19 &&
    mmFiber72ParentCheck 20 &&
    mmFiber72ParentCheck 21 &&
    mmFiber72ParentCheck 22 &&
    mmFiber72ParentCheck 23 &&
    mmFiber72ParentCheck 24 &&
    mmFiber72ParentCheck 25 &&
    mmFiber72ParentCheck 26 &&
    mmFiber72ParentCheck 27 &&
    mmFiber72ParentCheck 28 &&
    mmFiber72ParentCheck 29 &&
    mmFiber72ParentCheck 30 &&
    mmFiber72ParentCheck 31 &&
    mmFiber72ParentCheck 32 &&
    mmFiber72ParentCheck 33 &&
    mmFiber72ParentCheck 34 &&
    mmFiber72ParentCheck 35 &&
    mmFiber72ParentCheck 36 &&
    mmFiber72ParentCheck 37 &&
    mmFiber72ParentCheck 38 &&
    mmFiber72ParentCheck 39 &&
    mmFiber72ParentCheck 40 &&
    mmFiber72ParentCheck 41 &&
    mmFiber72ParentCheck 42 &&
    mmFiber72ParentCheck 43 &&
    mmFiber72ParentCheck 44 &&
    mmFiber72ParentCheck 45 &&
    mmFiber72ParentCheck 46 &&
    mmFiber72ParentCheck 47 &&
    mmFiber72ParentCheck 48 &&
    mmFiber72ParentCheck 49 &&
    mmFiber72ParentCheck 50 &&
    mmFiber72ParentCheck 51 &&
    mmFiber72ParentCheck 52 &&
    mmFiber72ParentCheck 53 &&
    mmFiber72ParentCheck 54 &&
    mmFiber72ParentCheck 55 &&
    mmFiber72ParentCheck 56 &&
    mmFiber72ParentCheck 57 &&
    mmFiber72ParentCheck 58 &&
    mmFiber72ParentCheck 59 &&
    mmFiber72ParentCheck 60 &&
    mmFiber72ParentCheck 61 &&
    mmFiber72ParentCheck 62 &&
    mmFiber72ParentCheck 63

theorem mmFiber72CertificateAudit_ok :
    mmFiber72CertificateAudit = true := by
  simp [mmFiber72CertificateAudit,
    mmFiber72SourcesCheck_ok,
    mmFiber72Row_0_ok,
    mmFiber72Row_1_ok,
    mmFiber72Row_2_ok,
    mmFiber72Row_3_ok,
    mmFiber72Row_4_ok,
    mmFiber72Row_5_ok,
    mmFiber72Row_6_ok,
    mmFiber72Row_7_ok,
    mmFiber72Row_8_ok,
    mmFiber72Row_9_ok,
    mmFiber72Row_10_ok,
    mmFiber72Row_11_ok,
    mmFiber72Row_12_ok,
    mmFiber72Row_13_ok,
    mmFiber72Row_14_ok,
    mmFiber72Row_15_ok,
    mmFiber72Row_16_ok,
    mmFiber72Row_17_ok,
    mmFiber72Row_18_ok,
    mmFiber72Row_19_ok,
    mmFiber72Row_20_ok,
    mmFiber72Row_21_ok,
    mmFiber72Row_22_ok,
    mmFiber72Row_23_ok,
    mmFiber72Row_24_ok,
    mmFiber72Row_25_ok,
    mmFiber72Row_26_ok,
    mmFiber72Row_27_ok,
    mmFiber72Row_28_ok,
    mmFiber72Row_29_ok,
    mmFiber72Row_30_ok,
    mmFiber72Row_31_ok,
    mmFiber72Row_32_ok,
    mmFiber72Row_33_ok,
    mmFiber72Row_34_ok,
    mmFiber72Row_35_ok,
    mmFiber72Row_36_ok,
    mmFiber72Row_37_ok,
    mmFiber72Row_38_ok,
    mmFiber72Row_39_ok,
    mmFiber72Row_40_ok,
    mmFiber72Row_41_ok,
    mmFiber72Row_42_ok,
    mmFiber72Row_43_ok,
    mmFiber72Row_44_ok,
    mmFiber72Row_45_ok,
    mmFiber72Row_46_ok,
    mmFiber72Row_47_ok,
    mmFiber72Row_48_ok,
    mmFiber72Row_49_ok,
    mmFiber72Row_50_ok,
    mmFiber72Row_51_ok,
    mmFiber72Row_52_ok,
    mmFiber72Row_53_ok,
    mmFiber72Row_54_ok,
    mmFiber72Row_55_ok,
    mmFiber72Row_56_ok,
    mmFiber72Row_57_ok,
    mmFiber72Row_58_ok,
    mmFiber72Row_59_ok,
    mmFiber72Row_60_ok,
    mmFiber72Row_61_ok,
    mmFiber72Row_62_ok,
    mmFiber72Row_63_ok,
    mmFiber72Parent_0_ok,
    mmFiber72Parent_1_ok,
    mmFiber72Parent_2_ok,
    mmFiber72Parent_3_ok,
    mmFiber72Parent_4_ok,
    mmFiber72Parent_5_ok,
    mmFiber72Parent_6_ok,
    mmFiber72Parent_7_ok,
    mmFiber72Parent_8_ok,
    mmFiber72Parent_9_ok,
    mmFiber72Parent_10_ok,
    mmFiber72Parent_11_ok,
    mmFiber72Parent_12_ok,
    mmFiber72Parent_13_ok,
    mmFiber72Parent_14_ok,
    mmFiber72Parent_15_ok,
    mmFiber72Parent_16_ok,
    mmFiber72Parent_17_ok,
    mmFiber72Parent_18_ok,
    mmFiber72Parent_19_ok,
    mmFiber72Parent_20_ok,
    mmFiber72Parent_21_ok,
    mmFiber72Parent_22_ok,
    mmFiber72Parent_23_ok,
    mmFiber72Parent_24_ok,
    mmFiber72Parent_25_ok,
    mmFiber72Parent_26_ok,
    mmFiber72Parent_27_ok,
    mmFiber72Parent_28_ok,
    mmFiber72Parent_29_ok,
    mmFiber72Parent_30_ok,
    mmFiber72Parent_31_ok,
    mmFiber72Parent_32_ok,
    mmFiber72Parent_33_ok,
    mmFiber72Parent_34_ok,
    mmFiber72Parent_35_ok,
    mmFiber72Parent_36_ok,
    mmFiber72Parent_37_ok,
    mmFiber72Parent_38_ok,
    mmFiber72Parent_39_ok,
    mmFiber72Parent_40_ok,
    mmFiber72Parent_41_ok,
    mmFiber72Parent_42_ok,
    mmFiber72Parent_43_ok,
    mmFiber72Parent_44_ok,
    mmFiber72Parent_45_ok,
    mmFiber72Parent_46_ok,
    mmFiber72Parent_47_ok,
    mmFiber72Parent_48_ok,
    mmFiber72Parent_49_ok,
    mmFiber72Parent_50_ok,
    mmFiber72Parent_51_ok,
    mmFiber72Parent_52_ok,
    mmFiber72Parent_53_ok,
    mmFiber72Parent_54_ok,
    mmFiber72Parent_55_ok,
    mmFiber72Parent_56_ok,
    mmFiber72Parent_57_ok,
    mmFiber72Parent_58_ok,
    mmFiber72Parent_59_ok,
    mmFiber72Parent_60_ok,
    mmFiber72Parent_61_ok,
    mmFiber72Parent_62_ok,
    mmFiber72Parent_63_ok]

def mmFiber73Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.b]

def mmFiber73Expected : List Nat :=
  []

def mmFiber73Rows : List DirectChainParentRow :=
  []

def mmFiber73RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber73Rows i default

def mmFiber73SourcesCheck : Bool :=
  (mmFiber73Rows.map fun row => row.source) == mmFiber73Expected

theorem mmFiber73SourcesCheck_ok :
    mmFiber73SourcesCheck = true := by
  decide

def mmFiber73RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber73Key mmFiber73Expected (mmFiber73RowAt i)

def mmFiber73ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber73Rows mmMaxParentDepth (listGetD mmFiber73Expected i 0) == 0

def mmFiber73CertificateAudit : Bool :=
  mmFiber73SourcesCheck

theorem mmFiber73CertificateAudit_ok :
    mmFiber73CertificateAudit = true := by
  simp [mmFiber73CertificateAudit,
    mmFiber73SourcesCheck_ok]

def mmFiber74Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.p]

def mmFiber74Expected : List Nat :=
  [112, 113, 114, 115, 116, 117, 118, 119]

def mmFiber74Rows : List DirectChainParentRow :=
  [ directRow 112 112 22 176 22 176 default
  , directRow 113 112 22 177 22 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 114 112 22 178 22 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 115 113 22 179 22 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 116 112 23 184 22 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 117 113 23 185 22 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 118 114 23 186 22 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 119 115 23 187 22 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def mmFiber74RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber74Rows i default

def mmFiber74SourcesCheck : Bool :=
  (mmFiber74Rows.map fun row => row.source) == mmFiber74Expected

theorem mmFiber74SourcesCheck_ok :
    mmFiber74SourcesCheck = true := by
  decide

def mmFiber74RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt i)

theorem mmFiber74Row_0_ok : mmFiber74RowCheck 0 = true := by decide
theorem mmFiber74Row_1_ok : mmFiber74RowCheck 1 = true := by decide
theorem mmFiber74Row_2_ok : mmFiber74RowCheck 2 = true := by decide
theorem mmFiber74Row_3_ok : mmFiber74RowCheck 3 = true := by decide
theorem mmFiber74Row_4_ok : mmFiber74RowCheck 4 = true := by decide
theorem mmFiber74Row_5_ok : mmFiber74RowCheck 5 = true := by decide
theorem mmFiber74Row_6_ok : mmFiber74RowCheck 6 = true := by decide
theorem mmFiber74Row_7_ok : mmFiber74RowCheck 7 = true := by decide

def mmFiber74ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber74Rows mmMaxParentDepth (listGetD mmFiber74Expected i 0) == 112

theorem mmFiber74Parent_0_ok : mmFiber74ParentCheck 0 = true := by decide
theorem mmFiber74Parent_1_ok : mmFiber74ParentCheck 1 = true := by decide
theorem mmFiber74Parent_2_ok : mmFiber74ParentCheck 2 = true := by decide
theorem mmFiber74Parent_3_ok : mmFiber74ParentCheck 3 = true := by decide
theorem mmFiber74Parent_4_ok : mmFiber74ParentCheck 4 = true := by decide
theorem mmFiber74Parent_5_ok : mmFiber74ParentCheck 5 = true := by decide
theorem mmFiber74Parent_6_ok : mmFiber74ParentCheck 6 = true := by decide
theorem mmFiber74Parent_7_ok : mmFiber74ParentCheck 7 = true := by decide

def mmFiber74CertificateAudit : Bool :=
  mmFiber74SourcesCheck &&
    mmFiber74RowCheck 0 &&
    mmFiber74RowCheck 1 &&
    mmFiber74RowCheck 2 &&
    mmFiber74RowCheck 3 &&
    mmFiber74RowCheck 4 &&
    mmFiber74RowCheck 5 &&
    mmFiber74RowCheck 6 &&
    mmFiber74RowCheck 7 &&
    mmFiber74ParentCheck 0 &&
    mmFiber74ParentCheck 1 &&
    mmFiber74ParentCheck 2 &&
    mmFiber74ParentCheck 3 &&
    mmFiber74ParentCheck 4 &&
    mmFiber74ParentCheck 5 &&
    mmFiber74ParentCheck 6 &&
    mmFiber74ParentCheck 7

theorem mmFiber74CertificateAudit_ok :
    mmFiber74CertificateAudit = true := by
  simp [mmFiber74CertificateAudit,
    mmFiber74SourcesCheck_ok,
    mmFiber74Row_0_ok,
    mmFiber74Row_1_ok,
    mmFiber74Row_2_ok,
    mmFiber74Row_3_ok,
    mmFiber74Row_4_ok,
    mmFiber74Row_5_ok,
    mmFiber74Row_6_ok,
    mmFiber74Row_7_ok,
    mmFiber74Parent_0_ok,
    mmFiber74Parent_1_ok,
    mmFiber74Parent_2_ok,
    mmFiber74Parent_3_ok,
    mmFiber74Parent_4_ok,
    mmFiber74Parent_5_ok,
    mmFiber74Parent_6_ok,
    mmFiber74Parent_7_ok]

def mmFiber75Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.r]

def mmFiber75Expected : List Nat :=
  []

def mmFiber75Rows : List DirectChainParentRow :=
  []

def mmFiber75RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber75Rows i default

def mmFiber75SourcesCheck : Bool :=
  (mmFiber75Rows.map fun row => row.source) == mmFiber75Expected

theorem mmFiber75SourcesCheck_ok :
    mmFiber75SourcesCheck = true := by
  decide

def mmFiber75RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber75Key mmFiber75Expected (mmFiber75RowAt i)

def mmFiber75ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber75Rows mmMaxParentDepth (listGetD mmFiber75Expected i 0) == 0

def mmFiber75CertificateAudit : Bool :=
  mmFiber75SourcesCheck

theorem mmFiber75CertificateAudit_ok :
    mmFiber75CertificateAudit = true := by
  simp [mmFiber75CertificateAudit,
    mmFiber75SourcesCheck_ok]

def mmFiber76Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.b]

def mmFiber76Expected : List Nat :=
  [728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839]

def mmFiber76Rows : List DirectChainParentRow :=
  [ directRow 728 728 148 148 148 148 default
  , directRow 729 728 148 149 148 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 730 729 148 150 148 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 731 728 148 151 148 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 732 728 148 164 148 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 733 729 148 165 148 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 734 732 148 166 148 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 735 731 148 167 148 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 736 728 149 156 148 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 737 729 149 157 148 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 738 730 149 158 148 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 739 731 149 159 148 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 740 732 149 172 148 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 741 733 149 173 148 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 742 734 149 174 148 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 743 735 149 175 148 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 744 748 150 0 150 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 745 749 150 1 150 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 746 740 150 2 149 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 747 741 150 3 149 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 748 736 150 48 149 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 749 737 150 49 149 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 750 738 150 50 149 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 751 739 150 51 149 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 752 756 151 8 151 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 753 757 151 9 151 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 754 732 151 10 148 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 755 733 151 11 148 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 756 728 151 56 148 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 757 729 151 57 148 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 758 730 151 58 148 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 759 731 151 59 148 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 808 728 164 132 148 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 809 729 164 133 148 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 810 730 164 134 148 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 811 731 164 135 148 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 812 732 164 180 148 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 813 733 164 181 148 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 814 734 164 182 148 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 815 735 164 183 148 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 816 736 165 140 149 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 817 737 165 141 149 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 818 738 165 142 149 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 819 739 165 143 149 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 820 740 165 188 149 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 821 741 165 189 149 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 822 742 165 190 149 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 823 743 165 191 149 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 824 808 166 64 164 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 825 809 166 65 164 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 826 824 166 66 166 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 827 811 166 67 164 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 828 812 166 116 164 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 829 813 166 117 164 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 830 825 166 118 166 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 831 824 166 119 166 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 832 816 167 72 165 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 833 817 167 73 165 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 834 754 167 74 151 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 835 755 167 75 151 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 836 756 167 124 151 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 837 757 167 125 151 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 838 836 167 126 167 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 839 759 167 127 151 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def mmFiber76RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber76Rows i default

def mmFiber76SourcesCheck : Bool :=
  (mmFiber76Rows.map fun row => row.source) == mmFiber76Expected

theorem mmFiber76SourcesCheck_ok :
    mmFiber76SourcesCheck = true := by
  decide

def mmFiber76RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt i)

theorem mmFiber76Row_0_ok : mmFiber76RowCheck 0 = true := by decide
theorem mmFiber76Row_1_ok : mmFiber76RowCheck 1 = true := by decide
theorem mmFiber76Row_2_ok : mmFiber76RowCheck 2 = true := by decide
theorem mmFiber76Row_3_ok : mmFiber76RowCheck 3 = true := by decide
theorem mmFiber76Row_4_ok : mmFiber76RowCheck 4 = true := by decide
theorem mmFiber76Row_5_ok : mmFiber76RowCheck 5 = true := by decide
theorem mmFiber76Row_6_ok : mmFiber76RowCheck 6 = true := by decide
theorem mmFiber76Row_7_ok : mmFiber76RowCheck 7 = true := by decide
theorem mmFiber76Row_8_ok : mmFiber76RowCheck 8 = true := by decide
theorem mmFiber76Row_9_ok : mmFiber76RowCheck 9 = true := by decide
theorem mmFiber76Row_10_ok : mmFiber76RowCheck 10 = true := by decide
theorem mmFiber76Row_11_ok : mmFiber76RowCheck 11 = true := by decide
theorem mmFiber76Row_12_ok : mmFiber76RowCheck 12 = true := by decide
theorem mmFiber76Row_13_ok : mmFiber76RowCheck 13 = true := by decide
theorem mmFiber76Row_14_ok : mmFiber76RowCheck 14 = true := by decide
theorem mmFiber76Row_15_ok : mmFiber76RowCheck 15 = true := by decide
theorem mmFiber76Row_16_ok : mmFiber76RowCheck 16 = true := by decide
theorem mmFiber76Row_17_ok : mmFiber76RowCheck 17 = true := by decide
theorem mmFiber76Row_18_ok : mmFiber76RowCheck 18 = true := by decide
theorem mmFiber76Row_19_ok : mmFiber76RowCheck 19 = true := by decide
theorem mmFiber76Row_20_ok : mmFiber76RowCheck 20 = true := by decide
theorem mmFiber76Row_21_ok : mmFiber76RowCheck 21 = true := by decide
theorem mmFiber76Row_22_ok : mmFiber76RowCheck 22 = true := by decide
theorem mmFiber76Row_23_ok : mmFiber76RowCheck 23 = true := by decide
theorem mmFiber76Row_24_ok : mmFiber76RowCheck 24 = true := by decide
theorem mmFiber76Row_25_ok : mmFiber76RowCheck 25 = true := by decide
theorem mmFiber76Row_26_ok : mmFiber76RowCheck 26 = true := by decide
theorem mmFiber76Row_27_ok : mmFiber76RowCheck 27 = true := by decide
theorem mmFiber76Row_28_ok : mmFiber76RowCheck 28 = true := by decide
theorem mmFiber76Row_29_ok : mmFiber76RowCheck 29 = true := by decide
theorem mmFiber76Row_30_ok : mmFiber76RowCheck 30 = true := by decide
theorem mmFiber76Row_31_ok : mmFiber76RowCheck 31 = true := by decide
theorem mmFiber76Row_32_ok : mmFiber76RowCheck 32 = true := by decide
theorem mmFiber76Row_33_ok : mmFiber76RowCheck 33 = true := by decide
theorem mmFiber76Row_34_ok : mmFiber76RowCheck 34 = true := by decide
theorem mmFiber76Row_35_ok : mmFiber76RowCheck 35 = true := by decide
theorem mmFiber76Row_36_ok : mmFiber76RowCheck 36 = true := by decide
theorem mmFiber76Row_37_ok : mmFiber76RowCheck 37 = true := by decide
theorem mmFiber76Row_38_ok : mmFiber76RowCheck 38 = true := by decide
theorem mmFiber76Row_39_ok : mmFiber76RowCheck 39 = true := by decide
theorem mmFiber76Row_40_ok : mmFiber76RowCheck 40 = true := by decide
theorem mmFiber76Row_41_ok : mmFiber76RowCheck 41 = true := by decide
theorem mmFiber76Row_42_ok : mmFiber76RowCheck 42 = true := by decide
theorem mmFiber76Row_43_ok : mmFiber76RowCheck 43 = true := by decide
theorem mmFiber76Row_44_ok : mmFiber76RowCheck 44 = true := by decide
theorem mmFiber76Row_45_ok : mmFiber76RowCheck 45 = true := by decide
theorem mmFiber76Row_46_ok : mmFiber76RowCheck 46 = true := by decide
theorem mmFiber76Row_47_ok : mmFiber76RowCheck 47 = true := by decide
theorem mmFiber76Row_48_ok : mmFiber76RowCheck 48 = true := by decide
theorem mmFiber76Row_49_ok : mmFiber76RowCheck 49 = true := by decide
theorem mmFiber76Row_50_ok : mmFiber76RowCheck 50 = true := by decide
theorem mmFiber76Row_51_ok : mmFiber76RowCheck 51 = true := by decide
theorem mmFiber76Row_52_ok : mmFiber76RowCheck 52 = true := by decide
theorem mmFiber76Row_53_ok : mmFiber76RowCheck 53 = true := by decide
theorem mmFiber76Row_54_ok : mmFiber76RowCheck 54 = true := by decide
theorem mmFiber76Row_55_ok : mmFiber76RowCheck 55 = true := by decide
theorem mmFiber76Row_56_ok : mmFiber76RowCheck 56 = true := by decide
theorem mmFiber76Row_57_ok : mmFiber76RowCheck 57 = true := by decide
theorem mmFiber76Row_58_ok : mmFiber76RowCheck 58 = true := by decide
theorem mmFiber76Row_59_ok : mmFiber76RowCheck 59 = true := by decide
theorem mmFiber76Row_60_ok : mmFiber76RowCheck 60 = true := by decide
theorem mmFiber76Row_61_ok : mmFiber76RowCheck 61 = true := by decide
theorem mmFiber76Row_62_ok : mmFiber76RowCheck 62 = true := by decide
theorem mmFiber76Row_63_ok : mmFiber76RowCheck 63 = true := by decide

def mmFiber76ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber76Rows mmMaxParentDepth (listGetD mmFiber76Expected i 0) == 728

theorem mmFiber76Parent_0_ok : mmFiber76ParentCheck 0 = true := by decide
theorem mmFiber76Parent_1_ok : mmFiber76ParentCheck 1 = true := by decide
theorem mmFiber76Parent_2_ok : mmFiber76ParentCheck 2 = true := by decide
theorem mmFiber76Parent_3_ok : mmFiber76ParentCheck 3 = true := by decide
theorem mmFiber76Parent_4_ok : mmFiber76ParentCheck 4 = true := by decide
theorem mmFiber76Parent_5_ok : mmFiber76ParentCheck 5 = true := by decide
theorem mmFiber76Parent_6_ok : mmFiber76ParentCheck 6 = true := by decide
theorem mmFiber76Parent_7_ok : mmFiber76ParentCheck 7 = true := by decide
theorem mmFiber76Parent_8_ok : mmFiber76ParentCheck 8 = true := by decide
theorem mmFiber76Parent_9_ok : mmFiber76ParentCheck 9 = true := by decide
theorem mmFiber76Parent_10_ok : mmFiber76ParentCheck 10 = true := by decide
theorem mmFiber76Parent_11_ok : mmFiber76ParentCheck 11 = true := by decide
theorem mmFiber76Parent_12_ok : mmFiber76ParentCheck 12 = true := by decide
theorem mmFiber76Parent_13_ok : mmFiber76ParentCheck 13 = true := by decide
theorem mmFiber76Parent_14_ok : mmFiber76ParentCheck 14 = true := by decide
theorem mmFiber76Parent_15_ok : mmFiber76ParentCheck 15 = true := by decide
theorem mmFiber76Parent_16_ok : mmFiber76ParentCheck 16 = true := by decide
theorem mmFiber76Parent_17_ok : mmFiber76ParentCheck 17 = true := by decide
theorem mmFiber76Parent_18_ok : mmFiber76ParentCheck 18 = true := by decide
theorem mmFiber76Parent_19_ok : mmFiber76ParentCheck 19 = true := by decide
theorem mmFiber76Parent_20_ok : mmFiber76ParentCheck 20 = true := by decide
theorem mmFiber76Parent_21_ok : mmFiber76ParentCheck 21 = true := by decide
theorem mmFiber76Parent_22_ok : mmFiber76ParentCheck 22 = true := by decide
theorem mmFiber76Parent_23_ok : mmFiber76ParentCheck 23 = true := by decide
theorem mmFiber76Parent_24_ok : mmFiber76ParentCheck 24 = true := by decide
theorem mmFiber76Parent_25_ok : mmFiber76ParentCheck 25 = true := by decide
theorem mmFiber76Parent_26_ok : mmFiber76ParentCheck 26 = true := by decide
theorem mmFiber76Parent_27_ok : mmFiber76ParentCheck 27 = true := by decide
theorem mmFiber76Parent_28_ok : mmFiber76ParentCheck 28 = true := by decide
theorem mmFiber76Parent_29_ok : mmFiber76ParentCheck 29 = true := by decide
theorem mmFiber76Parent_30_ok : mmFiber76ParentCheck 30 = true := by decide
theorem mmFiber76Parent_31_ok : mmFiber76ParentCheck 31 = true := by decide
theorem mmFiber76Parent_32_ok : mmFiber76ParentCheck 32 = true := by decide
theorem mmFiber76Parent_33_ok : mmFiber76ParentCheck 33 = true := by decide
theorem mmFiber76Parent_34_ok : mmFiber76ParentCheck 34 = true := by decide
theorem mmFiber76Parent_35_ok : mmFiber76ParentCheck 35 = true := by decide
theorem mmFiber76Parent_36_ok : mmFiber76ParentCheck 36 = true := by decide
theorem mmFiber76Parent_37_ok : mmFiber76ParentCheck 37 = true := by decide
theorem mmFiber76Parent_38_ok : mmFiber76ParentCheck 38 = true := by decide
theorem mmFiber76Parent_39_ok : mmFiber76ParentCheck 39 = true := by decide
theorem mmFiber76Parent_40_ok : mmFiber76ParentCheck 40 = true := by decide
theorem mmFiber76Parent_41_ok : mmFiber76ParentCheck 41 = true := by decide
theorem mmFiber76Parent_42_ok : mmFiber76ParentCheck 42 = true := by decide
theorem mmFiber76Parent_43_ok : mmFiber76ParentCheck 43 = true := by decide
theorem mmFiber76Parent_44_ok : mmFiber76ParentCheck 44 = true := by decide
theorem mmFiber76Parent_45_ok : mmFiber76ParentCheck 45 = true := by decide
theorem mmFiber76Parent_46_ok : mmFiber76ParentCheck 46 = true := by decide
theorem mmFiber76Parent_47_ok : mmFiber76ParentCheck 47 = true := by decide
theorem mmFiber76Parent_48_ok : mmFiber76ParentCheck 48 = true := by decide
theorem mmFiber76Parent_49_ok : mmFiber76ParentCheck 49 = true := by decide
theorem mmFiber76Parent_50_ok : mmFiber76ParentCheck 50 = true := by decide
theorem mmFiber76Parent_51_ok : mmFiber76ParentCheck 51 = true := by decide
theorem mmFiber76Parent_52_ok : mmFiber76ParentCheck 52 = true := by decide
theorem mmFiber76Parent_53_ok : mmFiber76ParentCheck 53 = true := by decide
theorem mmFiber76Parent_54_ok : mmFiber76ParentCheck 54 = true := by decide
theorem mmFiber76Parent_55_ok : mmFiber76ParentCheck 55 = true := by decide
theorem mmFiber76Parent_56_ok : mmFiber76ParentCheck 56 = true := by decide
theorem mmFiber76Parent_57_ok : mmFiber76ParentCheck 57 = true := by decide
theorem mmFiber76Parent_58_ok : mmFiber76ParentCheck 58 = true := by decide
theorem mmFiber76Parent_59_ok : mmFiber76ParentCheck 59 = true := by decide
theorem mmFiber76Parent_60_ok : mmFiber76ParentCheck 60 = true := by decide
theorem mmFiber76Parent_61_ok : mmFiber76ParentCheck 61 = true := by decide
theorem mmFiber76Parent_62_ok : mmFiber76ParentCheck 62 = true := by decide
theorem mmFiber76Parent_63_ok : mmFiber76ParentCheck 63 = true := by decide

def mmFiber76CertificateAudit : Bool :=
  mmFiber76SourcesCheck &&
    mmFiber76RowCheck 0 &&
    mmFiber76RowCheck 1 &&
    mmFiber76RowCheck 2 &&
    mmFiber76RowCheck 3 &&
    mmFiber76RowCheck 4 &&
    mmFiber76RowCheck 5 &&
    mmFiber76RowCheck 6 &&
    mmFiber76RowCheck 7 &&
    mmFiber76RowCheck 8 &&
    mmFiber76RowCheck 9 &&
    mmFiber76RowCheck 10 &&
    mmFiber76RowCheck 11 &&
    mmFiber76RowCheck 12 &&
    mmFiber76RowCheck 13 &&
    mmFiber76RowCheck 14 &&
    mmFiber76RowCheck 15 &&
    mmFiber76RowCheck 16 &&
    mmFiber76RowCheck 17 &&
    mmFiber76RowCheck 18 &&
    mmFiber76RowCheck 19 &&
    mmFiber76RowCheck 20 &&
    mmFiber76RowCheck 21 &&
    mmFiber76RowCheck 22 &&
    mmFiber76RowCheck 23 &&
    mmFiber76RowCheck 24 &&
    mmFiber76RowCheck 25 &&
    mmFiber76RowCheck 26 &&
    mmFiber76RowCheck 27 &&
    mmFiber76RowCheck 28 &&
    mmFiber76RowCheck 29 &&
    mmFiber76RowCheck 30 &&
    mmFiber76RowCheck 31 &&
    mmFiber76RowCheck 32 &&
    mmFiber76RowCheck 33 &&
    mmFiber76RowCheck 34 &&
    mmFiber76RowCheck 35 &&
    mmFiber76RowCheck 36 &&
    mmFiber76RowCheck 37 &&
    mmFiber76RowCheck 38 &&
    mmFiber76RowCheck 39 &&
    mmFiber76RowCheck 40 &&
    mmFiber76RowCheck 41 &&
    mmFiber76RowCheck 42 &&
    mmFiber76RowCheck 43 &&
    mmFiber76RowCheck 44 &&
    mmFiber76RowCheck 45 &&
    mmFiber76RowCheck 46 &&
    mmFiber76RowCheck 47 &&
    mmFiber76RowCheck 48 &&
    mmFiber76RowCheck 49 &&
    mmFiber76RowCheck 50 &&
    mmFiber76RowCheck 51 &&
    mmFiber76RowCheck 52 &&
    mmFiber76RowCheck 53 &&
    mmFiber76RowCheck 54 &&
    mmFiber76RowCheck 55 &&
    mmFiber76RowCheck 56 &&
    mmFiber76RowCheck 57 &&
    mmFiber76RowCheck 58 &&
    mmFiber76RowCheck 59 &&
    mmFiber76RowCheck 60 &&
    mmFiber76RowCheck 61 &&
    mmFiber76RowCheck 62 &&
    mmFiber76RowCheck 63 &&
    mmFiber76ParentCheck 0 &&
    mmFiber76ParentCheck 1 &&
    mmFiber76ParentCheck 2 &&
    mmFiber76ParentCheck 3 &&
    mmFiber76ParentCheck 4 &&
    mmFiber76ParentCheck 5 &&
    mmFiber76ParentCheck 6 &&
    mmFiber76ParentCheck 7 &&
    mmFiber76ParentCheck 8 &&
    mmFiber76ParentCheck 9 &&
    mmFiber76ParentCheck 10 &&
    mmFiber76ParentCheck 11 &&
    mmFiber76ParentCheck 12 &&
    mmFiber76ParentCheck 13 &&
    mmFiber76ParentCheck 14 &&
    mmFiber76ParentCheck 15 &&
    mmFiber76ParentCheck 16 &&
    mmFiber76ParentCheck 17 &&
    mmFiber76ParentCheck 18 &&
    mmFiber76ParentCheck 19 &&
    mmFiber76ParentCheck 20 &&
    mmFiber76ParentCheck 21 &&
    mmFiber76ParentCheck 22 &&
    mmFiber76ParentCheck 23 &&
    mmFiber76ParentCheck 24 &&
    mmFiber76ParentCheck 25 &&
    mmFiber76ParentCheck 26 &&
    mmFiber76ParentCheck 27 &&
    mmFiber76ParentCheck 28 &&
    mmFiber76ParentCheck 29 &&
    mmFiber76ParentCheck 30 &&
    mmFiber76ParentCheck 31 &&
    mmFiber76ParentCheck 32 &&
    mmFiber76ParentCheck 33 &&
    mmFiber76ParentCheck 34 &&
    mmFiber76ParentCheck 35 &&
    mmFiber76ParentCheck 36 &&
    mmFiber76ParentCheck 37 &&
    mmFiber76ParentCheck 38 &&
    mmFiber76ParentCheck 39 &&
    mmFiber76ParentCheck 40 &&
    mmFiber76ParentCheck 41 &&
    mmFiber76ParentCheck 42 &&
    mmFiber76ParentCheck 43 &&
    mmFiber76ParentCheck 44 &&
    mmFiber76ParentCheck 45 &&
    mmFiber76ParentCheck 46 &&
    mmFiber76ParentCheck 47 &&
    mmFiber76ParentCheck 48 &&
    mmFiber76ParentCheck 49 &&
    mmFiber76ParentCheck 50 &&
    mmFiber76ParentCheck 51 &&
    mmFiber76ParentCheck 52 &&
    mmFiber76ParentCheck 53 &&
    mmFiber76ParentCheck 54 &&
    mmFiber76ParentCheck 55 &&
    mmFiber76ParentCheck 56 &&
    mmFiber76ParentCheck 57 &&
    mmFiber76ParentCheck 58 &&
    mmFiber76ParentCheck 59 &&
    mmFiber76ParentCheck 60 &&
    mmFiber76ParentCheck 61 &&
    mmFiber76ParentCheck 62 &&
    mmFiber76ParentCheck 63

theorem mmFiber76CertificateAudit_ok :
    mmFiber76CertificateAudit = true := by
  simp [mmFiber76CertificateAudit,
    mmFiber76SourcesCheck_ok,
    mmFiber76Row_0_ok,
    mmFiber76Row_1_ok,
    mmFiber76Row_2_ok,
    mmFiber76Row_3_ok,
    mmFiber76Row_4_ok,
    mmFiber76Row_5_ok,
    mmFiber76Row_6_ok,
    mmFiber76Row_7_ok,
    mmFiber76Row_8_ok,
    mmFiber76Row_9_ok,
    mmFiber76Row_10_ok,
    mmFiber76Row_11_ok,
    mmFiber76Row_12_ok,
    mmFiber76Row_13_ok,
    mmFiber76Row_14_ok,
    mmFiber76Row_15_ok,
    mmFiber76Row_16_ok,
    mmFiber76Row_17_ok,
    mmFiber76Row_18_ok,
    mmFiber76Row_19_ok,
    mmFiber76Row_20_ok,
    mmFiber76Row_21_ok,
    mmFiber76Row_22_ok,
    mmFiber76Row_23_ok,
    mmFiber76Row_24_ok,
    mmFiber76Row_25_ok,
    mmFiber76Row_26_ok,
    mmFiber76Row_27_ok,
    mmFiber76Row_28_ok,
    mmFiber76Row_29_ok,
    mmFiber76Row_30_ok,
    mmFiber76Row_31_ok,
    mmFiber76Row_32_ok,
    mmFiber76Row_33_ok,
    mmFiber76Row_34_ok,
    mmFiber76Row_35_ok,
    mmFiber76Row_36_ok,
    mmFiber76Row_37_ok,
    mmFiber76Row_38_ok,
    mmFiber76Row_39_ok,
    mmFiber76Row_40_ok,
    mmFiber76Row_41_ok,
    mmFiber76Row_42_ok,
    mmFiber76Row_43_ok,
    mmFiber76Row_44_ok,
    mmFiber76Row_45_ok,
    mmFiber76Row_46_ok,
    mmFiber76Row_47_ok,
    mmFiber76Row_48_ok,
    mmFiber76Row_49_ok,
    mmFiber76Row_50_ok,
    mmFiber76Row_51_ok,
    mmFiber76Row_52_ok,
    mmFiber76Row_53_ok,
    mmFiber76Row_54_ok,
    mmFiber76Row_55_ok,
    mmFiber76Row_56_ok,
    mmFiber76Row_57_ok,
    mmFiber76Row_58_ok,
    mmFiber76Row_59_ok,
    mmFiber76Row_60_ok,
    mmFiber76Row_61_ok,
    mmFiber76Row_62_ok,
    mmFiber76Row_63_ok,
    mmFiber76Parent_0_ok,
    mmFiber76Parent_1_ok,
    mmFiber76Parent_2_ok,
    mmFiber76Parent_3_ok,
    mmFiber76Parent_4_ok,
    mmFiber76Parent_5_ok,
    mmFiber76Parent_6_ok,
    mmFiber76Parent_7_ok,
    mmFiber76Parent_8_ok,
    mmFiber76Parent_9_ok,
    mmFiber76Parent_10_ok,
    mmFiber76Parent_11_ok,
    mmFiber76Parent_12_ok,
    mmFiber76Parent_13_ok,
    mmFiber76Parent_14_ok,
    mmFiber76Parent_15_ok,
    mmFiber76Parent_16_ok,
    mmFiber76Parent_17_ok,
    mmFiber76Parent_18_ok,
    mmFiber76Parent_19_ok,
    mmFiber76Parent_20_ok,
    mmFiber76Parent_21_ok,
    mmFiber76Parent_22_ok,
    mmFiber76Parent_23_ok,
    mmFiber76Parent_24_ok,
    mmFiber76Parent_25_ok,
    mmFiber76Parent_26_ok,
    mmFiber76Parent_27_ok,
    mmFiber76Parent_28_ok,
    mmFiber76Parent_29_ok,
    mmFiber76Parent_30_ok,
    mmFiber76Parent_31_ok,
    mmFiber76Parent_32_ok,
    mmFiber76Parent_33_ok,
    mmFiber76Parent_34_ok,
    mmFiber76Parent_35_ok,
    mmFiber76Parent_36_ok,
    mmFiber76Parent_37_ok,
    mmFiber76Parent_38_ok,
    mmFiber76Parent_39_ok,
    mmFiber76Parent_40_ok,
    mmFiber76Parent_41_ok,
    mmFiber76Parent_42_ok,
    mmFiber76Parent_43_ok,
    mmFiber76Parent_44_ok,
    mmFiber76Parent_45_ok,
    mmFiber76Parent_46_ok,
    mmFiber76Parent_47_ok,
    mmFiber76Parent_48_ok,
    mmFiber76Parent_49_ok,
    mmFiber76Parent_50_ok,
    mmFiber76Parent_51_ok,
    mmFiber76Parent_52_ok,
    mmFiber76Parent_53_ok,
    mmFiber76Parent_54_ok,
    mmFiber76Parent_55_ok,
    mmFiber76Parent_56_ok,
    mmFiber76Parent_57_ok,
    mmFiber76Parent_58_ok,
    mmFiber76Parent_59_ok,
    mmFiber76Parent_60_ok,
    mmFiber76Parent_61_ok,
    mmFiber76Parent_62_ok,
    mmFiber76Parent_63_ok]

def mmFiber77Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.p]

def mmFiber77Expected : List Nat :=
  [432, 433, 434, 435, 436, 437, 438, 439]

def mmFiber77Rows : List DirectChainParentRow :=
  [ directRow 432 432 84 144 84 144 default
  , directRow 433 432 84 145 84 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 434 433 84 146 84 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 435 432 84 147 84 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 436 432 85 152 84 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 437 433 85 153 84 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 438 434 85 154 84 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 439 435 85 155 84 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def mmFiber77RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber77Rows i default

def mmFiber77SourcesCheck : Bool :=
  (mmFiber77Rows.map fun row => row.source) == mmFiber77Expected

theorem mmFiber77SourcesCheck_ok :
    mmFiber77SourcesCheck = true := by
  decide

def mmFiber77RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt i)

theorem mmFiber77Row_0_ok : mmFiber77RowCheck 0 = true := by decide
theorem mmFiber77Row_1_ok : mmFiber77RowCheck 1 = true := by decide
theorem mmFiber77Row_2_ok : mmFiber77RowCheck 2 = true := by decide
theorem mmFiber77Row_3_ok : mmFiber77RowCheck 3 = true := by decide
theorem mmFiber77Row_4_ok : mmFiber77RowCheck 4 = true := by decide
theorem mmFiber77Row_5_ok : mmFiber77RowCheck 5 = true := by decide
theorem mmFiber77Row_6_ok : mmFiber77RowCheck 6 = true := by decide
theorem mmFiber77Row_7_ok : mmFiber77RowCheck 7 = true := by decide

def mmFiber77ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber77Rows mmMaxParentDepth (listGetD mmFiber77Expected i 0) == 432

theorem mmFiber77Parent_0_ok : mmFiber77ParentCheck 0 = true := by decide
theorem mmFiber77Parent_1_ok : mmFiber77ParentCheck 1 = true := by decide
theorem mmFiber77Parent_2_ok : mmFiber77ParentCheck 2 = true := by decide
theorem mmFiber77Parent_3_ok : mmFiber77ParentCheck 3 = true := by decide
theorem mmFiber77Parent_4_ok : mmFiber77ParentCheck 4 = true := by decide
theorem mmFiber77Parent_5_ok : mmFiber77ParentCheck 5 = true := by decide
theorem mmFiber77Parent_6_ok : mmFiber77ParentCheck 6 = true := by decide
theorem mmFiber77Parent_7_ok : mmFiber77ParentCheck 7 = true := by decide

def mmFiber77CertificateAudit : Bool :=
  mmFiber77SourcesCheck &&
    mmFiber77RowCheck 0 &&
    mmFiber77RowCheck 1 &&
    mmFiber77RowCheck 2 &&
    mmFiber77RowCheck 3 &&
    mmFiber77RowCheck 4 &&
    mmFiber77RowCheck 5 &&
    mmFiber77RowCheck 6 &&
    mmFiber77RowCheck 7 &&
    mmFiber77ParentCheck 0 &&
    mmFiber77ParentCheck 1 &&
    mmFiber77ParentCheck 2 &&
    mmFiber77ParentCheck 3 &&
    mmFiber77ParentCheck 4 &&
    mmFiber77ParentCheck 5 &&
    mmFiber77ParentCheck 6 &&
    mmFiber77ParentCheck 7

theorem mmFiber77CertificateAudit_ok :
    mmFiber77CertificateAudit = true := by
  simp [mmFiber77CertificateAudit,
    mmFiber77SourcesCheck_ok,
    mmFiber77Row_0_ok,
    mmFiber77Row_1_ok,
    mmFiber77Row_2_ok,
    mmFiber77Row_3_ok,
    mmFiber77Row_4_ok,
    mmFiber77Row_5_ok,
    mmFiber77Row_6_ok,
    mmFiber77Row_7_ok,
    mmFiber77Parent_0_ok,
    mmFiber77Parent_1_ok,
    mmFiber77Parent_2_ok,
    mmFiber77Parent_3_ok,
    mmFiber77Parent_4_ok,
    mmFiber77Parent_5_ok,
    mmFiber77Parent_6_ok,
    mmFiber77Parent_7_ok]

def mmFiber78Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.r]

def mmFiber78Expected : List Nat :=
  []

def mmFiber78Rows : List DirectChainParentRow :=
  []

def mmFiber78RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber78Rows i default

def mmFiber78SourcesCheck : Bool :=
  (mmFiber78Rows.map fun row => row.source) == mmFiber78Expected

theorem mmFiber78SourcesCheck_ok :
    mmFiber78SourcesCheck = true := by
  decide

def mmFiber78RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber78Key mmFiber78Expected (mmFiber78RowAt i)

def mmFiber78ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber78Rows mmMaxParentDepth (listGetD mmFiber78Expected i 0) == 0

def mmFiber78CertificateAudit : Bool :=
  mmFiber78SourcesCheck

theorem mmFiber78CertificateAudit_ok :
    mmFiber78CertificateAudit = true := by
  simp [mmFiber78CertificateAudit,
    mmFiber78SourcesCheck_ok]

def mmFiber79Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.b]

def mmFiber79Expected : List Nat :=
  []

def mmFiber79Rows : List DirectChainParentRow :=
  []

def mmFiber79RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber79Rows i default

def mmFiber79SourcesCheck : Bool :=
  (mmFiber79Rows.map fun row => row.source) == mmFiber79Expected

theorem mmFiber79SourcesCheck_ok :
    mmFiber79SourcesCheck = true := by
  decide

def mmFiber79RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber79Key mmFiber79Expected (mmFiber79RowAt i)

def mmFiber79ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber79Rows mmMaxParentDepth (listGetD mmFiber79Expected i 0) == 0

def mmFiber79CertificateAudit : Bool :=
  mmFiber79SourcesCheck

theorem mmFiber79CertificateAudit_ok :
    mmFiber79CertificateAudit = true := by
  simp [mmFiber79CertificateAudit,
    mmFiber79SourcesCheck_ok]

def mmFiber80Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.p]

def mmFiber80Expected : List Nat :=
  []

def mmFiber80Rows : List DirectChainParentRow :=
  []

def mmFiber80RowAt (i : Nat) : DirectChainParentRow :=
  listGetD mmFiber80Rows i default

def mmFiber80SourcesCheck : Bool :=
  (mmFiber80Rows.map fun row => row.source) == mmFiber80Expected

theorem mmFiber80SourcesCheck_ok :
    mmFiber80SourcesCheck = true := by
  decide

def mmFiber80RowCheck (i : Nat) : Bool :=
  mmRowValid mmFiber80Key mmFiber80Expected (mmFiber80RowAt i)

def mmFiber80ParentCheck (i : Nat) : Bool :=
  directParentIter mmFiber80Rows mmMaxParentDepth (listGetD mmFiber80Expected i 0) == 0

def mmFiber80CertificateAudit : Bool :=
  mmFiber80SourcesCheck

theorem mmFiber80CertificateAudit_ok :
    mmFiber80CertificateAudit = true := by
  simp [mmFiber80CertificateAudit,
    mmFiber80SourcesCheck_ok]

def mmAllFiberCertificateAudit : Bool :=
  mmFiber0CertificateAudit &&
    mmFiber1CertificateAudit &&
    mmFiber2CertificateAudit &&
    mmFiber3CertificateAudit &&
    mmFiber4CertificateAudit &&
    mmFiber5CertificateAudit &&
    mmFiber6CertificateAudit &&
    mmFiber7CertificateAudit &&
    mmFiber8CertificateAudit &&
    mmFiber9CertificateAudit &&
    mmFiber10CertificateAudit &&
    mmFiber11CertificateAudit &&
    mmFiber12CertificateAudit &&
    mmFiber13CertificateAudit &&
    mmFiber14CertificateAudit &&
    mmFiber15CertificateAudit &&
    mmFiber16CertificateAudit &&
    mmFiber17CertificateAudit &&
    mmFiber18CertificateAudit &&
    mmFiber19CertificateAudit &&
    mmFiber20CertificateAudit &&
    mmFiber21CertificateAudit &&
    mmFiber22CertificateAudit &&
    mmFiber23CertificateAudit &&
    mmFiber24CertificateAudit &&
    mmFiber25CertificateAudit &&
    mmFiber26CertificateAudit &&
    mmFiber27CertificateAudit &&
    mmFiber28CertificateAudit &&
    mmFiber29CertificateAudit &&
    mmFiber30CertificateAudit &&
    mmFiber31CertificateAudit &&
    mmFiber32CertificateAudit &&
    mmFiber33CertificateAudit &&
    mmFiber34CertificateAudit &&
    mmFiber35CertificateAudit &&
    mmFiber36CertificateAudit &&
    mmFiber37CertificateAudit &&
    mmFiber38CertificateAudit &&
    mmFiber39CertificateAudit &&
    mmFiber40CertificateAudit &&
    mmFiber41CertificateAudit &&
    mmFiber42CertificateAudit &&
    mmFiber43CertificateAudit &&
    mmFiber44CertificateAudit &&
    mmFiber45CertificateAudit &&
    mmFiber46CertificateAudit &&
    mmFiber47CertificateAudit &&
    mmFiber48CertificateAudit &&
    mmFiber49CertificateAudit &&
    mmFiber50CertificateAudit &&
    mmFiber51CertificateAudit &&
    mmFiber52CertificateAudit &&
    mmFiber53CertificateAudit &&
    mmFiber54CertificateAudit &&
    mmFiber55CertificateAudit &&
    mmFiber56CertificateAudit &&
    mmFiber57CertificateAudit &&
    mmFiber58CertificateAudit &&
    mmFiber59CertificateAudit &&
    mmFiber60CertificateAudit &&
    mmFiber61CertificateAudit &&
    mmFiber62CertificateAudit &&
    mmFiber63CertificateAudit &&
    mmFiber64CertificateAudit &&
    mmFiber65CertificateAudit &&
    mmFiber66CertificateAudit &&
    mmFiber67CertificateAudit &&
    mmFiber68CertificateAudit &&
    mmFiber69CertificateAudit &&
    mmFiber70CertificateAudit &&
    mmFiber71CertificateAudit &&
    mmFiber72CertificateAudit &&
    mmFiber73CertificateAudit &&
    mmFiber74CertificateAudit &&
    mmFiber75CertificateAudit &&
    mmFiber76CertificateAudit &&
    mmFiber77CertificateAudit &&
    mmFiber78CertificateAudit &&
    mmFiber79CertificateAudit &&
    mmFiber80CertificateAudit

theorem mmAllFiberCertificateAudit_ok :
    mmAllFiberCertificateAudit = true := by
  simp [mmAllFiberCertificateAudit,
    mmFiber0CertificateAudit_ok,
    mmFiber1CertificateAudit_ok,
    mmFiber2CertificateAudit_ok,
    mmFiber3CertificateAudit_ok,
    mmFiber4CertificateAudit_ok,
    mmFiber5CertificateAudit_ok,
    mmFiber6CertificateAudit_ok,
    mmFiber7CertificateAudit_ok,
    mmFiber8CertificateAudit_ok,
    mmFiber9CertificateAudit_ok,
    mmFiber10CertificateAudit_ok,
    mmFiber11CertificateAudit_ok,
    mmFiber12CertificateAudit_ok,
    mmFiber13CertificateAudit_ok,
    mmFiber14CertificateAudit_ok,
    mmFiber15CertificateAudit_ok,
    mmFiber16CertificateAudit_ok,
    mmFiber17CertificateAudit_ok,
    mmFiber18CertificateAudit_ok,
    mmFiber19CertificateAudit_ok,
    mmFiber20CertificateAudit_ok,
    mmFiber21CertificateAudit_ok,
    mmFiber22CertificateAudit_ok,
    mmFiber23CertificateAudit_ok,
    mmFiber24CertificateAudit_ok,
    mmFiber25CertificateAudit_ok,
    mmFiber26CertificateAudit_ok,
    mmFiber27CertificateAudit_ok,
    mmFiber28CertificateAudit_ok,
    mmFiber29CertificateAudit_ok,
    mmFiber30CertificateAudit_ok,
    mmFiber31CertificateAudit_ok,
    mmFiber32CertificateAudit_ok,
    mmFiber33CertificateAudit_ok,
    mmFiber34CertificateAudit_ok,
    mmFiber35CertificateAudit_ok,
    mmFiber36CertificateAudit_ok,
    mmFiber37CertificateAudit_ok,
    mmFiber38CertificateAudit_ok,
    mmFiber39CertificateAudit_ok,
    mmFiber40CertificateAudit_ok,
    mmFiber41CertificateAudit_ok,
    mmFiber42CertificateAudit_ok,
    mmFiber43CertificateAudit_ok,
    mmFiber44CertificateAudit_ok,
    mmFiber45CertificateAudit_ok,
    mmFiber46CertificateAudit_ok,
    mmFiber47CertificateAudit_ok,
    mmFiber48CertificateAudit_ok,
    mmFiber49CertificateAudit_ok,
    mmFiber50CertificateAudit_ok,
    mmFiber51CertificateAudit_ok,
    mmFiber52CertificateAudit_ok,
    mmFiber53CertificateAudit_ok,
    mmFiber54CertificateAudit_ok,
    mmFiber55CertificateAudit_ok,
    mmFiber56CertificateAudit_ok,
    mmFiber57CertificateAudit_ok,
    mmFiber58CertificateAudit_ok,
    mmFiber59CertificateAudit_ok,
    mmFiber60CertificateAudit_ok,
    mmFiber61CertificateAudit_ok,
    mmFiber62CertificateAudit_ok,
    mmFiber63CertificateAudit_ok,
    mmFiber64CertificateAudit_ok,
    mmFiber65CertificateAudit_ok,
    mmFiber66CertificateAudit_ok,
    mmFiber67CertificateAudit_ok,
    mmFiber68CertificateAudit_ok,
    mmFiber69CertificateAudit_ok,
    mmFiber70CertificateAudit_ok,
    mmFiber71CertificateAudit_ok,
    mmFiber72CertificateAudit_ok,
    mmFiber73CertificateAudit_ok,
    mmFiber74CertificateAudit_ok,
    mmFiber75CertificateAudit_ok,
    mmFiber76CertificateAudit_ok,
    mmFiber77CertificateAudit_ok,
    mmFiber78CertificateAudit_ok,
    mmFiber79CertificateAudit_ok,
    mmFiber80CertificateAudit_ok]

end GoertzelLemma818MirrorMirrorCertificate

end Mettapedia.GraphTheory.FourColor
