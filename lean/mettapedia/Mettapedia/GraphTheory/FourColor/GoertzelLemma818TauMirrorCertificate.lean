import Mettapedia.GraphTheory.FourColor.GoertzelLemma818CompositeCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: generated `normal-mirror` length-2 certificate

This file checks the generated direct parent/path table for all 81
fixed-input keys of the `normal-mirror` composite.  The checks are row-split;
the all-chain frontier/DFA lift is a separate theorem.
-/

namespace GoertzelLemma818TauMirrorCertificate

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def tmWord : List TauOrient :=
  [TauOrient.normal, TauOrient.mirror]

def tmNonemptyFiberCount : Nat := 36
def tmCompositeStateCount : Nat := 1152
def tmMaxParentDepth : Nat := 4

def tmRowValid (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) : Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := directStates row.sourceLeft row.sourceRight
    let t := directStates row.parentLeft row.parentRight
    compatibleChainStates tmWord s && compatibleChainStates tmWord t &&
      chainInputKey tmWord s == key && chainInputKey tmWord t == key &&
        (row.source == row.parent || chainSpecifiedKempeStep tmWord s t row.move)

def tmFiber0Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.r]

def tmFiber0Expected : List Nat :=
  []

def tmFiber0Rows : List DirectChainParentRow :=
  []

def tmFiber0RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber0Rows i default

def tmFiber0SourcesCheck : Bool :=
  (tmFiber0Rows.map fun row => row.source) == tmFiber0Expected

theorem tmFiber0SourcesCheck_ok :
    tmFiber0SourcesCheck = true := by
  decide

def tmFiber0RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber0Key tmFiber0Expected (tmFiber0RowAt i)

def tmFiber0ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber0Rows tmMaxParentDepth (listGetD tmFiber0Expected i 0) == 0

def tmFiber0CertificateAudit : Bool :=
  tmFiber0SourcesCheck

theorem tmFiber0CertificateAudit_ok :
    tmFiber0CertificateAudit = true := by
  simp [tmFiber0CertificateAudit,
    tmFiber0SourcesCheck_ok]

def tmFiber1Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.b]

def tmFiber1Expected : List Nat :=
  []

def tmFiber1Rows : List DirectChainParentRow :=
  []

def tmFiber1RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber1Rows i default

def tmFiber1SourcesCheck : Bool :=
  (tmFiber1Rows.map fun row => row.source) == tmFiber1Expected

theorem tmFiber1SourcesCheck_ok :
    tmFiber1SourcesCheck = true := by
  decide

def tmFiber1RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber1Key tmFiber1Expected (tmFiber1RowAt i)

def tmFiber1ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber1Rows tmMaxParentDepth (listGetD tmFiber1Expected i 0) == 0

def tmFiber1CertificateAudit : Bool :=
  tmFiber1SourcesCheck

theorem tmFiber1CertificateAudit_ok :
    tmFiber1CertificateAudit = true := by
  simp [tmFiber1CertificateAudit,
    tmFiber1SourcesCheck_ok]

def tmFiber2Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.p]

def tmFiber2Expected : List Nat :=
  []

def tmFiber2Rows : List DirectChainParentRow :=
  []

def tmFiber2RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber2Rows i default

def tmFiber2SourcesCheck : Bool :=
  (tmFiber2Rows.map fun row => row.source) == tmFiber2Expected

theorem tmFiber2SourcesCheck_ok :
    tmFiber2SourcesCheck = true := by
  decide

def tmFiber2RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber2Key tmFiber2Expected (tmFiber2RowAt i)

def tmFiber2ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber2Rows tmMaxParentDepth (listGetD tmFiber2Expected i 0) == 0

def tmFiber2CertificateAudit : Bool :=
  tmFiber2SourcesCheck

theorem tmFiber2CertificateAudit_ok :
    tmFiber2CertificateAudit = true := by
  simp [tmFiber2CertificateAudit,
    tmFiber2SourcesCheck_ok]

def tmFiber3Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.r]

def tmFiber3Expected : List Nat :=
  [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]

def tmFiber3Rows : List DirectChainParentRow :=
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

def tmFiber3RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber3Rows i default

def tmFiber3SourcesCheck : Bool :=
  (tmFiber3Rows.map fun row => row.source) == tmFiber3Expected

theorem tmFiber3SourcesCheck_ok :
    tmFiber3SourcesCheck = true := by
  decide

def tmFiber3RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt i)

theorem tmFiber3Row_0_ok : tmFiber3RowCheck 0 = true := by decide
theorem tmFiber3Row_1_ok : tmFiber3RowCheck 1 = true := by decide
theorem tmFiber3Row_2_ok : tmFiber3RowCheck 2 = true := by decide
theorem tmFiber3Row_3_ok : tmFiber3RowCheck 3 = true := by decide
theorem tmFiber3Row_4_ok : tmFiber3RowCheck 4 = true := by decide
theorem tmFiber3Row_5_ok : tmFiber3RowCheck 5 = true := by decide
theorem tmFiber3Row_6_ok : tmFiber3RowCheck 6 = true := by decide
theorem tmFiber3Row_7_ok : tmFiber3RowCheck 7 = true := by decide
theorem tmFiber3Row_8_ok : tmFiber3RowCheck 8 = true := by decide
theorem tmFiber3Row_9_ok : tmFiber3RowCheck 9 = true := by decide
theorem tmFiber3Row_10_ok : tmFiber3RowCheck 10 = true := by decide
theorem tmFiber3Row_11_ok : tmFiber3RowCheck 11 = true := by decide
theorem tmFiber3Row_12_ok : tmFiber3RowCheck 12 = true := by decide
theorem tmFiber3Row_13_ok : tmFiber3RowCheck 13 = true := by decide
theorem tmFiber3Row_14_ok : tmFiber3RowCheck 14 = true := by decide
theorem tmFiber3Row_15_ok : tmFiber3RowCheck 15 = true := by decide

def tmFiber3ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber3Rows tmMaxParentDepth (listGetD tmFiber3Expected i 0) == 672

theorem tmFiber3Parent_0_ok : tmFiber3ParentCheck 0 = true := by decide
theorem tmFiber3Parent_1_ok : tmFiber3ParentCheck 1 = true := by decide
theorem tmFiber3Parent_2_ok : tmFiber3ParentCheck 2 = true := by decide
theorem tmFiber3Parent_3_ok : tmFiber3ParentCheck 3 = true := by decide
theorem tmFiber3Parent_4_ok : tmFiber3ParentCheck 4 = true := by decide
theorem tmFiber3Parent_5_ok : tmFiber3ParentCheck 5 = true := by decide
theorem tmFiber3Parent_6_ok : tmFiber3ParentCheck 6 = true := by decide
theorem tmFiber3Parent_7_ok : tmFiber3ParentCheck 7 = true := by decide
theorem tmFiber3Parent_8_ok : tmFiber3ParentCheck 8 = true := by decide
theorem tmFiber3Parent_9_ok : tmFiber3ParentCheck 9 = true := by decide
theorem tmFiber3Parent_10_ok : tmFiber3ParentCheck 10 = true := by decide
theorem tmFiber3Parent_11_ok : tmFiber3ParentCheck 11 = true := by decide
theorem tmFiber3Parent_12_ok : tmFiber3ParentCheck 12 = true := by decide
theorem tmFiber3Parent_13_ok : tmFiber3ParentCheck 13 = true := by decide
theorem tmFiber3Parent_14_ok : tmFiber3ParentCheck 14 = true := by decide
theorem tmFiber3Parent_15_ok : tmFiber3ParentCheck 15 = true := by decide

def tmFiber3CertificateAudit : Bool :=
  tmFiber3SourcesCheck &&
    tmFiber3RowCheck 0 &&
    tmFiber3RowCheck 1 &&
    tmFiber3RowCheck 2 &&
    tmFiber3RowCheck 3 &&
    tmFiber3RowCheck 4 &&
    tmFiber3RowCheck 5 &&
    tmFiber3RowCheck 6 &&
    tmFiber3RowCheck 7 &&
    tmFiber3RowCheck 8 &&
    tmFiber3RowCheck 9 &&
    tmFiber3RowCheck 10 &&
    tmFiber3RowCheck 11 &&
    tmFiber3RowCheck 12 &&
    tmFiber3RowCheck 13 &&
    tmFiber3RowCheck 14 &&
    tmFiber3RowCheck 15 &&
    tmFiber3ParentCheck 0 &&
    tmFiber3ParentCheck 1 &&
    tmFiber3ParentCheck 2 &&
    tmFiber3ParentCheck 3 &&
    tmFiber3ParentCheck 4 &&
    tmFiber3ParentCheck 5 &&
    tmFiber3ParentCheck 6 &&
    tmFiber3ParentCheck 7 &&
    tmFiber3ParentCheck 8 &&
    tmFiber3ParentCheck 9 &&
    tmFiber3ParentCheck 10 &&
    tmFiber3ParentCheck 11 &&
    tmFiber3ParentCheck 12 &&
    tmFiber3ParentCheck 13 &&
    tmFiber3ParentCheck 14 &&
    tmFiber3ParentCheck 15

theorem tmFiber3CertificateAudit_ok :
    tmFiber3CertificateAudit = true := by
  simp [tmFiber3CertificateAudit,
    tmFiber3SourcesCheck_ok,
    tmFiber3Row_0_ok,
    tmFiber3Row_1_ok,
    tmFiber3Row_2_ok,
    tmFiber3Row_3_ok,
    tmFiber3Row_4_ok,
    tmFiber3Row_5_ok,
    tmFiber3Row_6_ok,
    tmFiber3Row_7_ok,
    tmFiber3Row_8_ok,
    tmFiber3Row_9_ok,
    tmFiber3Row_10_ok,
    tmFiber3Row_11_ok,
    tmFiber3Row_12_ok,
    tmFiber3Row_13_ok,
    tmFiber3Row_14_ok,
    tmFiber3Row_15_ok,
    tmFiber3Parent_0_ok,
    tmFiber3Parent_1_ok,
    tmFiber3Parent_2_ok,
    tmFiber3Parent_3_ok,
    tmFiber3Parent_4_ok,
    tmFiber3Parent_5_ok,
    tmFiber3Parent_6_ok,
    tmFiber3Parent_7_ok,
    tmFiber3Parent_8_ok,
    tmFiber3Parent_9_ok,
    tmFiber3Parent_10_ok,
    tmFiber3Parent_11_ok,
    tmFiber3Parent_12_ok,
    tmFiber3Parent_13_ok,
    tmFiber3Parent_14_ok,
    tmFiber3Parent_15_ok]

def tmFiber4Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.b]

def tmFiber4Expected : List Nat :=
  [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]

def tmFiber4Rows : List DirectChainParentRow :=
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

def tmFiber4RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber4Rows i default

def tmFiber4SourcesCheck : Bool :=
  (tmFiber4Rows.map fun row => row.source) == tmFiber4Expected

theorem tmFiber4SourcesCheck_ok :
    tmFiber4SourcesCheck = true := by
  decide

def tmFiber4RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber4Key tmFiber4Expected (tmFiber4RowAt i)

theorem tmFiber4Row_0_ok : tmFiber4RowCheck 0 = true := by decide
theorem tmFiber4Row_1_ok : tmFiber4RowCheck 1 = true := by decide
theorem tmFiber4Row_2_ok : tmFiber4RowCheck 2 = true := by decide
theorem tmFiber4Row_3_ok : tmFiber4RowCheck 3 = true := by decide
theorem tmFiber4Row_4_ok : tmFiber4RowCheck 4 = true := by decide
theorem tmFiber4Row_5_ok : tmFiber4RowCheck 5 = true := by decide
theorem tmFiber4Row_6_ok : tmFiber4RowCheck 6 = true := by decide
theorem tmFiber4Row_7_ok : tmFiber4RowCheck 7 = true := by decide
theorem tmFiber4Row_8_ok : tmFiber4RowCheck 8 = true := by decide
theorem tmFiber4Row_9_ok : tmFiber4RowCheck 9 = true := by decide
theorem tmFiber4Row_10_ok : tmFiber4RowCheck 10 = true := by decide
theorem tmFiber4Row_11_ok : tmFiber4RowCheck 11 = true := by decide
theorem tmFiber4Row_12_ok : tmFiber4RowCheck 12 = true := by decide
theorem tmFiber4Row_13_ok : tmFiber4RowCheck 13 = true := by decide
theorem tmFiber4Row_14_ok : tmFiber4RowCheck 14 = true := by decide
theorem tmFiber4Row_15_ok : tmFiber4RowCheck 15 = true := by decide
theorem tmFiber4Row_16_ok : tmFiber4RowCheck 16 = true := by decide
theorem tmFiber4Row_17_ok : tmFiber4RowCheck 17 = true := by decide
theorem tmFiber4Row_18_ok : tmFiber4RowCheck 18 = true := by decide
theorem tmFiber4Row_19_ok : tmFiber4RowCheck 19 = true := by decide
theorem tmFiber4Row_20_ok : tmFiber4RowCheck 20 = true := by decide
theorem tmFiber4Row_21_ok : tmFiber4RowCheck 21 = true := by decide
theorem tmFiber4Row_22_ok : tmFiber4RowCheck 22 = true := by decide
theorem tmFiber4Row_23_ok : tmFiber4RowCheck 23 = true := by decide
theorem tmFiber4Row_24_ok : tmFiber4RowCheck 24 = true := by decide
theorem tmFiber4Row_25_ok : tmFiber4RowCheck 25 = true := by decide
theorem tmFiber4Row_26_ok : tmFiber4RowCheck 26 = true := by decide
theorem tmFiber4Row_27_ok : tmFiber4RowCheck 27 = true := by decide
theorem tmFiber4Row_28_ok : tmFiber4RowCheck 28 = true := by decide
theorem tmFiber4Row_29_ok : tmFiber4RowCheck 29 = true := by decide
theorem tmFiber4Row_30_ok : tmFiber4RowCheck 30 = true := by decide
theorem tmFiber4Row_31_ok : tmFiber4RowCheck 31 = true := by decide
theorem tmFiber4Row_32_ok : tmFiber4RowCheck 32 = true := by decide
theorem tmFiber4Row_33_ok : tmFiber4RowCheck 33 = true := by decide
theorem tmFiber4Row_34_ok : tmFiber4RowCheck 34 = true := by decide
theorem tmFiber4Row_35_ok : tmFiber4RowCheck 35 = true := by decide
theorem tmFiber4Row_36_ok : tmFiber4RowCheck 36 = true := by decide
theorem tmFiber4Row_37_ok : tmFiber4RowCheck 37 = true := by decide
theorem tmFiber4Row_38_ok : tmFiber4RowCheck 38 = true := by decide
theorem tmFiber4Row_39_ok : tmFiber4RowCheck 39 = true := by decide
theorem tmFiber4Row_40_ok : tmFiber4RowCheck 40 = true := by decide
theorem tmFiber4Row_41_ok : tmFiber4RowCheck 41 = true := by decide
theorem tmFiber4Row_42_ok : tmFiber4RowCheck 42 = true := by decide
theorem tmFiber4Row_43_ok : tmFiber4RowCheck 43 = true := by decide
theorem tmFiber4Row_44_ok : tmFiber4RowCheck 44 = true := by decide
theorem tmFiber4Row_45_ok : tmFiber4RowCheck 45 = true := by decide
theorem tmFiber4Row_46_ok : tmFiber4RowCheck 46 = true := by decide
theorem tmFiber4Row_47_ok : tmFiber4RowCheck 47 = true := by decide
theorem tmFiber4Row_48_ok : tmFiber4RowCheck 48 = true := by decide
theorem tmFiber4Row_49_ok : tmFiber4RowCheck 49 = true := by decide
theorem tmFiber4Row_50_ok : tmFiber4RowCheck 50 = true := by decide
theorem tmFiber4Row_51_ok : tmFiber4RowCheck 51 = true := by decide
theorem tmFiber4Row_52_ok : tmFiber4RowCheck 52 = true := by decide
theorem tmFiber4Row_53_ok : tmFiber4RowCheck 53 = true := by decide
theorem tmFiber4Row_54_ok : tmFiber4RowCheck 54 = true := by decide
theorem tmFiber4Row_55_ok : tmFiber4RowCheck 55 = true := by decide
theorem tmFiber4Row_56_ok : tmFiber4RowCheck 56 = true := by decide
theorem tmFiber4Row_57_ok : tmFiber4RowCheck 57 = true := by decide
theorem tmFiber4Row_58_ok : tmFiber4RowCheck 58 = true := by decide
theorem tmFiber4Row_59_ok : tmFiber4RowCheck 59 = true := by decide
theorem tmFiber4Row_60_ok : tmFiber4RowCheck 60 = true := by decide
theorem tmFiber4Row_61_ok : tmFiber4RowCheck 61 = true := by decide
theorem tmFiber4Row_62_ok : tmFiber4RowCheck 62 = true := by decide
theorem tmFiber4Row_63_ok : tmFiber4RowCheck 63 = true := by decide

def tmFiber4ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber4Rows tmMaxParentDepth (listGetD tmFiber4Expected i 0) == 384

theorem tmFiber4Parent_0_ok : tmFiber4ParentCheck 0 = true := by decide
theorem tmFiber4Parent_1_ok : tmFiber4ParentCheck 1 = true := by decide
theorem tmFiber4Parent_2_ok : tmFiber4ParentCheck 2 = true := by decide
theorem tmFiber4Parent_3_ok : tmFiber4ParentCheck 3 = true := by decide
theorem tmFiber4Parent_4_ok : tmFiber4ParentCheck 4 = true := by decide
theorem tmFiber4Parent_5_ok : tmFiber4ParentCheck 5 = true := by decide
theorem tmFiber4Parent_6_ok : tmFiber4ParentCheck 6 = true := by decide
theorem tmFiber4Parent_7_ok : tmFiber4ParentCheck 7 = true := by decide
theorem tmFiber4Parent_8_ok : tmFiber4ParentCheck 8 = true := by decide
theorem tmFiber4Parent_9_ok : tmFiber4ParentCheck 9 = true := by decide
theorem tmFiber4Parent_10_ok : tmFiber4ParentCheck 10 = true := by decide
theorem tmFiber4Parent_11_ok : tmFiber4ParentCheck 11 = true := by decide
theorem tmFiber4Parent_12_ok : tmFiber4ParentCheck 12 = true := by decide
theorem tmFiber4Parent_13_ok : tmFiber4ParentCheck 13 = true := by decide
theorem tmFiber4Parent_14_ok : tmFiber4ParentCheck 14 = true := by decide
theorem tmFiber4Parent_15_ok : tmFiber4ParentCheck 15 = true := by decide
theorem tmFiber4Parent_16_ok : tmFiber4ParentCheck 16 = true := by decide
theorem tmFiber4Parent_17_ok : tmFiber4ParentCheck 17 = true := by decide
theorem tmFiber4Parent_18_ok : tmFiber4ParentCheck 18 = true := by decide
theorem tmFiber4Parent_19_ok : tmFiber4ParentCheck 19 = true := by decide
theorem tmFiber4Parent_20_ok : tmFiber4ParentCheck 20 = true := by decide
theorem tmFiber4Parent_21_ok : tmFiber4ParentCheck 21 = true := by decide
theorem tmFiber4Parent_22_ok : tmFiber4ParentCheck 22 = true := by decide
theorem tmFiber4Parent_23_ok : tmFiber4ParentCheck 23 = true := by decide
theorem tmFiber4Parent_24_ok : tmFiber4ParentCheck 24 = true := by decide
theorem tmFiber4Parent_25_ok : tmFiber4ParentCheck 25 = true := by decide
theorem tmFiber4Parent_26_ok : tmFiber4ParentCheck 26 = true := by decide
theorem tmFiber4Parent_27_ok : tmFiber4ParentCheck 27 = true := by decide
theorem tmFiber4Parent_28_ok : tmFiber4ParentCheck 28 = true := by decide
theorem tmFiber4Parent_29_ok : tmFiber4ParentCheck 29 = true := by decide
theorem tmFiber4Parent_30_ok : tmFiber4ParentCheck 30 = true := by decide
theorem tmFiber4Parent_31_ok : tmFiber4ParentCheck 31 = true := by decide
theorem tmFiber4Parent_32_ok : tmFiber4ParentCheck 32 = true := by decide
theorem tmFiber4Parent_33_ok : tmFiber4ParentCheck 33 = true := by decide
theorem tmFiber4Parent_34_ok : tmFiber4ParentCheck 34 = true := by decide
theorem tmFiber4Parent_35_ok : tmFiber4ParentCheck 35 = true := by decide
theorem tmFiber4Parent_36_ok : tmFiber4ParentCheck 36 = true := by decide
theorem tmFiber4Parent_37_ok : tmFiber4ParentCheck 37 = true := by decide
theorem tmFiber4Parent_38_ok : tmFiber4ParentCheck 38 = true := by decide
theorem tmFiber4Parent_39_ok : tmFiber4ParentCheck 39 = true := by decide
theorem tmFiber4Parent_40_ok : tmFiber4ParentCheck 40 = true := by decide
theorem tmFiber4Parent_41_ok : tmFiber4ParentCheck 41 = true := by decide
theorem tmFiber4Parent_42_ok : tmFiber4ParentCheck 42 = true := by decide
theorem tmFiber4Parent_43_ok : tmFiber4ParentCheck 43 = true := by decide
theorem tmFiber4Parent_44_ok : tmFiber4ParentCheck 44 = true := by decide
theorem tmFiber4Parent_45_ok : tmFiber4ParentCheck 45 = true := by decide
theorem tmFiber4Parent_46_ok : tmFiber4ParentCheck 46 = true := by decide
theorem tmFiber4Parent_47_ok : tmFiber4ParentCheck 47 = true := by decide
theorem tmFiber4Parent_48_ok : tmFiber4ParentCheck 48 = true := by decide
theorem tmFiber4Parent_49_ok : tmFiber4ParentCheck 49 = true := by decide
theorem tmFiber4Parent_50_ok : tmFiber4ParentCheck 50 = true := by decide
theorem tmFiber4Parent_51_ok : tmFiber4ParentCheck 51 = true := by decide
theorem tmFiber4Parent_52_ok : tmFiber4ParentCheck 52 = true := by decide
theorem tmFiber4Parent_53_ok : tmFiber4ParentCheck 53 = true := by decide
theorem tmFiber4Parent_54_ok : tmFiber4ParentCheck 54 = true := by decide
theorem tmFiber4Parent_55_ok : tmFiber4ParentCheck 55 = true := by decide
theorem tmFiber4Parent_56_ok : tmFiber4ParentCheck 56 = true := by decide
theorem tmFiber4Parent_57_ok : tmFiber4ParentCheck 57 = true := by decide
theorem tmFiber4Parent_58_ok : tmFiber4ParentCheck 58 = true := by decide
theorem tmFiber4Parent_59_ok : tmFiber4ParentCheck 59 = true := by decide
theorem tmFiber4Parent_60_ok : tmFiber4ParentCheck 60 = true := by decide
theorem tmFiber4Parent_61_ok : tmFiber4ParentCheck 61 = true := by decide
theorem tmFiber4Parent_62_ok : tmFiber4ParentCheck 62 = true := by decide
theorem tmFiber4Parent_63_ok : tmFiber4ParentCheck 63 = true := by decide

def tmFiber4CertificateAudit : Bool :=
  tmFiber4SourcesCheck &&
    tmFiber4RowCheck 0 &&
    tmFiber4RowCheck 1 &&
    tmFiber4RowCheck 2 &&
    tmFiber4RowCheck 3 &&
    tmFiber4RowCheck 4 &&
    tmFiber4RowCheck 5 &&
    tmFiber4RowCheck 6 &&
    tmFiber4RowCheck 7 &&
    tmFiber4RowCheck 8 &&
    tmFiber4RowCheck 9 &&
    tmFiber4RowCheck 10 &&
    tmFiber4RowCheck 11 &&
    tmFiber4RowCheck 12 &&
    tmFiber4RowCheck 13 &&
    tmFiber4RowCheck 14 &&
    tmFiber4RowCheck 15 &&
    tmFiber4RowCheck 16 &&
    tmFiber4RowCheck 17 &&
    tmFiber4RowCheck 18 &&
    tmFiber4RowCheck 19 &&
    tmFiber4RowCheck 20 &&
    tmFiber4RowCheck 21 &&
    tmFiber4RowCheck 22 &&
    tmFiber4RowCheck 23 &&
    tmFiber4RowCheck 24 &&
    tmFiber4RowCheck 25 &&
    tmFiber4RowCheck 26 &&
    tmFiber4RowCheck 27 &&
    tmFiber4RowCheck 28 &&
    tmFiber4RowCheck 29 &&
    tmFiber4RowCheck 30 &&
    tmFiber4RowCheck 31 &&
    tmFiber4RowCheck 32 &&
    tmFiber4RowCheck 33 &&
    tmFiber4RowCheck 34 &&
    tmFiber4RowCheck 35 &&
    tmFiber4RowCheck 36 &&
    tmFiber4RowCheck 37 &&
    tmFiber4RowCheck 38 &&
    tmFiber4RowCheck 39 &&
    tmFiber4RowCheck 40 &&
    tmFiber4RowCheck 41 &&
    tmFiber4RowCheck 42 &&
    tmFiber4RowCheck 43 &&
    tmFiber4RowCheck 44 &&
    tmFiber4RowCheck 45 &&
    tmFiber4RowCheck 46 &&
    tmFiber4RowCheck 47 &&
    tmFiber4RowCheck 48 &&
    tmFiber4RowCheck 49 &&
    tmFiber4RowCheck 50 &&
    tmFiber4RowCheck 51 &&
    tmFiber4RowCheck 52 &&
    tmFiber4RowCheck 53 &&
    tmFiber4RowCheck 54 &&
    tmFiber4RowCheck 55 &&
    tmFiber4RowCheck 56 &&
    tmFiber4RowCheck 57 &&
    tmFiber4RowCheck 58 &&
    tmFiber4RowCheck 59 &&
    tmFiber4RowCheck 60 &&
    tmFiber4RowCheck 61 &&
    tmFiber4RowCheck 62 &&
    tmFiber4RowCheck 63 &&
    tmFiber4ParentCheck 0 &&
    tmFiber4ParentCheck 1 &&
    tmFiber4ParentCheck 2 &&
    tmFiber4ParentCheck 3 &&
    tmFiber4ParentCheck 4 &&
    tmFiber4ParentCheck 5 &&
    tmFiber4ParentCheck 6 &&
    tmFiber4ParentCheck 7 &&
    tmFiber4ParentCheck 8 &&
    tmFiber4ParentCheck 9 &&
    tmFiber4ParentCheck 10 &&
    tmFiber4ParentCheck 11 &&
    tmFiber4ParentCheck 12 &&
    tmFiber4ParentCheck 13 &&
    tmFiber4ParentCheck 14 &&
    tmFiber4ParentCheck 15 &&
    tmFiber4ParentCheck 16 &&
    tmFiber4ParentCheck 17 &&
    tmFiber4ParentCheck 18 &&
    tmFiber4ParentCheck 19 &&
    tmFiber4ParentCheck 20 &&
    tmFiber4ParentCheck 21 &&
    tmFiber4ParentCheck 22 &&
    tmFiber4ParentCheck 23 &&
    tmFiber4ParentCheck 24 &&
    tmFiber4ParentCheck 25 &&
    tmFiber4ParentCheck 26 &&
    tmFiber4ParentCheck 27 &&
    tmFiber4ParentCheck 28 &&
    tmFiber4ParentCheck 29 &&
    tmFiber4ParentCheck 30 &&
    tmFiber4ParentCheck 31 &&
    tmFiber4ParentCheck 32 &&
    tmFiber4ParentCheck 33 &&
    tmFiber4ParentCheck 34 &&
    tmFiber4ParentCheck 35 &&
    tmFiber4ParentCheck 36 &&
    tmFiber4ParentCheck 37 &&
    tmFiber4ParentCheck 38 &&
    tmFiber4ParentCheck 39 &&
    tmFiber4ParentCheck 40 &&
    tmFiber4ParentCheck 41 &&
    tmFiber4ParentCheck 42 &&
    tmFiber4ParentCheck 43 &&
    tmFiber4ParentCheck 44 &&
    tmFiber4ParentCheck 45 &&
    tmFiber4ParentCheck 46 &&
    tmFiber4ParentCheck 47 &&
    tmFiber4ParentCheck 48 &&
    tmFiber4ParentCheck 49 &&
    tmFiber4ParentCheck 50 &&
    tmFiber4ParentCheck 51 &&
    tmFiber4ParentCheck 52 &&
    tmFiber4ParentCheck 53 &&
    tmFiber4ParentCheck 54 &&
    tmFiber4ParentCheck 55 &&
    tmFiber4ParentCheck 56 &&
    tmFiber4ParentCheck 57 &&
    tmFiber4ParentCheck 58 &&
    tmFiber4ParentCheck 59 &&
    tmFiber4ParentCheck 60 &&
    tmFiber4ParentCheck 61 &&
    tmFiber4ParentCheck 62 &&
    tmFiber4ParentCheck 63

theorem tmFiber4CertificateAudit_ok :
    tmFiber4CertificateAudit = true := by
  simp [tmFiber4CertificateAudit,
    tmFiber4SourcesCheck_ok,
    tmFiber4Row_0_ok,
    tmFiber4Row_1_ok,
    tmFiber4Row_2_ok,
    tmFiber4Row_3_ok,
    tmFiber4Row_4_ok,
    tmFiber4Row_5_ok,
    tmFiber4Row_6_ok,
    tmFiber4Row_7_ok,
    tmFiber4Row_8_ok,
    tmFiber4Row_9_ok,
    tmFiber4Row_10_ok,
    tmFiber4Row_11_ok,
    tmFiber4Row_12_ok,
    tmFiber4Row_13_ok,
    tmFiber4Row_14_ok,
    tmFiber4Row_15_ok,
    tmFiber4Row_16_ok,
    tmFiber4Row_17_ok,
    tmFiber4Row_18_ok,
    tmFiber4Row_19_ok,
    tmFiber4Row_20_ok,
    tmFiber4Row_21_ok,
    tmFiber4Row_22_ok,
    tmFiber4Row_23_ok,
    tmFiber4Row_24_ok,
    tmFiber4Row_25_ok,
    tmFiber4Row_26_ok,
    tmFiber4Row_27_ok,
    tmFiber4Row_28_ok,
    tmFiber4Row_29_ok,
    tmFiber4Row_30_ok,
    tmFiber4Row_31_ok,
    tmFiber4Row_32_ok,
    tmFiber4Row_33_ok,
    tmFiber4Row_34_ok,
    tmFiber4Row_35_ok,
    tmFiber4Row_36_ok,
    tmFiber4Row_37_ok,
    tmFiber4Row_38_ok,
    tmFiber4Row_39_ok,
    tmFiber4Row_40_ok,
    tmFiber4Row_41_ok,
    tmFiber4Row_42_ok,
    tmFiber4Row_43_ok,
    tmFiber4Row_44_ok,
    tmFiber4Row_45_ok,
    tmFiber4Row_46_ok,
    tmFiber4Row_47_ok,
    tmFiber4Row_48_ok,
    tmFiber4Row_49_ok,
    tmFiber4Row_50_ok,
    tmFiber4Row_51_ok,
    tmFiber4Row_52_ok,
    tmFiber4Row_53_ok,
    tmFiber4Row_54_ok,
    tmFiber4Row_55_ok,
    tmFiber4Row_56_ok,
    tmFiber4Row_57_ok,
    tmFiber4Row_58_ok,
    tmFiber4Row_59_ok,
    tmFiber4Row_60_ok,
    tmFiber4Row_61_ok,
    tmFiber4Row_62_ok,
    tmFiber4Row_63_ok,
    tmFiber4Parent_0_ok,
    tmFiber4Parent_1_ok,
    tmFiber4Parent_2_ok,
    tmFiber4Parent_3_ok,
    tmFiber4Parent_4_ok,
    tmFiber4Parent_5_ok,
    tmFiber4Parent_6_ok,
    tmFiber4Parent_7_ok,
    tmFiber4Parent_8_ok,
    tmFiber4Parent_9_ok,
    tmFiber4Parent_10_ok,
    tmFiber4Parent_11_ok,
    tmFiber4Parent_12_ok,
    tmFiber4Parent_13_ok,
    tmFiber4Parent_14_ok,
    tmFiber4Parent_15_ok,
    tmFiber4Parent_16_ok,
    tmFiber4Parent_17_ok,
    tmFiber4Parent_18_ok,
    tmFiber4Parent_19_ok,
    tmFiber4Parent_20_ok,
    tmFiber4Parent_21_ok,
    tmFiber4Parent_22_ok,
    tmFiber4Parent_23_ok,
    tmFiber4Parent_24_ok,
    tmFiber4Parent_25_ok,
    tmFiber4Parent_26_ok,
    tmFiber4Parent_27_ok,
    tmFiber4Parent_28_ok,
    tmFiber4Parent_29_ok,
    tmFiber4Parent_30_ok,
    tmFiber4Parent_31_ok,
    tmFiber4Parent_32_ok,
    tmFiber4Parent_33_ok,
    tmFiber4Parent_34_ok,
    tmFiber4Parent_35_ok,
    tmFiber4Parent_36_ok,
    tmFiber4Parent_37_ok,
    tmFiber4Parent_38_ok,
    tmFiber4Parent_39_ok,
    tmFiber4Parent_40_ok,
    tmFiber4Parent_41_ok,
    tmFiber4Parent_42_ok,
    tmFiber4Parent_43_ok,
    tmFiber4Parent_44_ok,
    tmFiber4Parent_45_ok,
    tmFiber4Parent_46_ok,
    tmFiber4Parent_47_ok,
    tmFiber4Parent_48_ok,
    tmFiber4Parent_49_ok,
    tmFiber4Parent_50_ok,
    tmFiber4Parent_51_ok,
    tmFiber4Parent_52_ok,
    tmFiber4Parent_53_ok,
    tmFiber4Parent_54_ok,
    tmFiber4Parent_55_ok,
    tmFiber4Parent_56_ok,
    tmFiber4Parent_57_ok,
    tmFiber4Parent_58_ok,
    tmFiber4Parent_59_ok,
    tmFiber4Parent_60_ok,
    tmFiber4Parent_61_ok,
    tmFiber4Parent_62_ok,
    tmFiber4Parent_63_ok]

def tmFiber5Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.p]

def tmFiber5Expected : List Nat :=
  [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]

def tmFiber5Rows : List DirectChainParentRow :=
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

def tmFiber5RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber5Rows i default

def tmFiber5SourcesCheck : Bool :=
  (tmFiber5Rows.map fun row => row.source) == tmFiber5Expected

theorem tmFiber5SourcesCheck_ok :
    tmFiber5SourcesCheck = true := by
  decide

def tmFiber5RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt i)

theorem tmFiber5Row_0_ok : tmFiber5RowCheck 0 = true := by decide
theorem tmFiber5Row_1_ok : tmFiber5RowCheck 1 = true := by decide
theorem tmFiber5Row_2_ok : tmFiber5RowCheck 2 = true := by decide
theorem tmFiber5Row_3_ok : tmFiber5RowCheck 3 = true := by decide
theorem tmFiber5Row_4_ok : tmFiber5RowCheck 4 = true := by decide
theorem tmFiber5Row_5_ok : tmFiber5RowCheck 5 = true := by decide
theorem tmFiber5Row_6_ok : tmFiber5RowCheck 6 = true := by decide
theorem tmFiber5Row_7_ok : tmFiber5RowCheck 7 = true := by decide
theorem tmFiber5Row_8_ok : tmFiber5RowCheck 8 = true := by decide
theorem tmFiber5Row_9_ok : tmFiber5RowCheck 9 = true := by decide
theorem tmFiber5Row_10_ok : tmFiber5RowCheck 10 = true := by decide
theorem tmFiber5Row_11_ok : tmFiber5RowCheck 11 = true := by decide
theorem tmFiber5Row_12_ok : tmFiber5RowCheck 12 = true := by decide
theorem tmFiber5Row_13_ok : tmFiber5RowCheck 13 = true := by decide
theorem tmFiber5Row_14_ok : tmFiber5RowCheck 14 = true := by decide
theorem tmFiber5Row_15_ok : tmFiber5RowCheck 15 = true := by decide

def tmFiber5ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber5Rows tmMaxParentDepth (listGetD tmFiber5Expected i 0) == 416

theorem tmFiber5Parent_0_ok : tmFiber5ParentCheck 0 = true := by decide
theorem tmFiber5Parent_1_ok : tmFiber5ParentCheck 1 = true := by decide
theorem tmFiber5Parent_2_ok : tmFiber5ParentCheck 2 = true := by decide
theorem tmFiber5Parent_3_ok : tmFiber5ParentCheck 3 = true := by decide
theorem tmFiber5Parent_4_ok : tmFiber5ParentCheck 4 = true := by decide
theorem tmFiber5Parent_5_ok : tmFiber5ParentCheck 5 = true := by decide
theorem tmFiber5Parent_6_ok : tmFiber5ParentCheck 6 = true := by decide
theorem tmFiber5Parent_7_ok : tmFiber5ParentCheck 7 = true := by decide
theorem tmFiber5Parent_8_ok : tmFiber5ParentCheck 8 = true := by decide
theorem tmFiber5Parent_9_ok : tmFiber5ParentCheck 9 = true := by decide
theorem tmFiber5Parent_10_ok : tmFiber5ParentCheck 10 = true := by decide
theorem tmFiber5Parent_11_ok : tmFiber5ParentCheck 11 = true := by decide
theorem tmFiber5Parent_12_ok : tmFiber5ParentCheck 12 = true := by decide
theorem tmFiber5Parent_13_ok : tmFiber5ParentCheck 13 = true := by decide
theorem tmFiber5Parent_14_ok : tmFiber5ParentCheck 14 = true := by decide
theorem tmFiber5Parent_15_ok : tmFiber5ParentCheck 15 = true := by decide

def tmFiber5CertificateAudit : Bool :=
  tmFiber5SourcesCheck &&
    tmFiber5RowCheck 0 &&
    tmFiber5RowCheck 1 &&
    tmFiber5RowCheck 2 &&
    tmFiber5RowCheck 3 &&
    tmFiber5RowCheck 4 &&
    tmFiber5RowCheck 5 &&
    tmFiber5RowCheck 6 &&
    tmFiber5RowCheck 7 &&
    tmFiber5RowCheck 8 &&
    tmFiber5RowCheck 9 &&
    tmFiber5RowCheck 10 &&
    tmFiber5RowCheck 11 &&
    tmFiber5RowCheck 12 &&
    tmFiber5RowCheck 13 &&
    tmFiber5RowCheck 14 &&
    tmFiber5RowCheck 15 &&
    tmFiber5ParentCheck 0 &&
    tmFiber5ParentCheck 1 &&
    tmFiber5ParentCheck 2 &&
    tmFiber5ParentCheck 3 &&
    tmFiber5ParentCheck 4 &&
    tmFiber5ParentCheck 5 &&
    tmFiber5ParentCheck 6 &&
    tmFiber5ParentCheck 7 &&
    tmFiber5ParentCheck 8 &&
    tmFiber5ParentCheck 9 &&
    tmFiber5ParentCheck 10 &&
    tmFiber5ParentCheck 11 &&
    tmFiber5ParentCheck 12 &&
    tmFiber5ParentCheck 13 &&
    tmFiber5ParentCheck 14 &&
    tmFiber5ParentCheck 15

theorem tmFiber5CertificateAudit_ok :
    tmFiber5CertificateAudit = true := by
  simp [tmFiber5CertificateAudit,
    tmFiber5SourcesCheck_ok,
    tmFiber5Row_0_ok,
    tmFiber5Row_1_ok,
    tmFiber5Row_2_ok,
    tmFiber5Row_3_ok,
    tmFiber5Row_4_ok,
    tmFiber5Row_5_ok,
    tmFiber5Row_6_ok,
    tmFiber5Row_7_ok,
    tmFiber5Row_8_ok,
    tmFiber5Row_9_ok,
    tmFiber5Row_10_ok,
    tmFiber5Row_11_ok,
    tmFiber5Row_12_ok,
    tmFiber5Row_13_ok,
    tmFiber5Row_14_ok,
    tmFiber5Row_15_ok,
    tmFiber5Parent_0_ok,
    tmFiber5Parent_1_ok,
    tmFiber5Parent_2_ok,
    tmFiber5Parent_3_ok,
    tmFiber5Parent_4_ok,
    tmFiber5Parent_5_ok,
    tmFiber5Parent_6_ok,
    tmFiber5Parent_7_ok,
    tmFiber5Parent_8_ok,
    tmFiber5Parent_9_ok,
    tmFiber5Parent_10_ok,
    tmFiber5Parent_11_ok,
    tmFiber5Parent_12_ok,
    tmFiber5Parent_13_ok,
    tmFiber5Parent_14_ok,
    tmFiber5Parent_15_ok]

def tmFiber6Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.r]

def tmFiber6Expected : List Nat :=
  [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]

def tmFiber6Rows : List DirectChainParentRow :=
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

def tmFiber6RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber6Rows i default

def tmFiber6SourcesCheck : Bool :=
  (tmFiber6Rows.map fun row => row.source) == tmFiber6Expected

theorem tmFiber6SourcesCheck_ok :
    tmFiber6SourcesCheck = true := by
  decide

def tmFiber6RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt i)

theorem tmFiber6Row_0_ok : tmFiber6RowCheck 0 = true := by decide
theorem tmFiber6Row_1_ok : tmFiber6RowCheck 1 = true := by decide
theorem tmFiber6Row_2_ok : tmFiber6RowCheck 2 = true := by decide
theorem tmFiber6Row_3_ok : tmFiber6RowCheck 3 = true := by decide
theorem tmFiber6Row_4_ok : tmFiber6RowCheck 4 = true := by decide
theorem tmFiber6Row_5_ok : tmFiber6RowCheck 5 = true := by decide
theorem tmFiber6Row_6_ok : tmFiber6RowCheck 6 = true := by decide
theorem tmFiber6Row_7_ok : tmFiber6RowCheck 7 = true := by decide
theorem tmFiber6Row_8_ok : tmFiber6RowCheck 8 = true := by decide
theorem tmFiber6Row_9_ok : tmFiber6RowCheck 9 = true := by decide
theorem tmFiber6Row_10_ok : tmFiber6RowCheck 10 = true := by decide
theorem tmFiber6Row_11_ok : tmFiber6RowCheck 11 = true := by decide
theorem tmFiber6Row_12_ok : tmFiber6RowCheck 12 = true := by decide
theorem tmFiber6Row_13_ok : tmFiber6RowCheck 13 = true := by decide
theorem tmFiber6Row_14_ok : tmFiber6RowCheck 14 = true := by decide
theorem tmFiber6Row_15_ok : tmFiber6RowCheck 15 = true := by decide

def tmFiber6ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber6Rows tmMaxParentDepth (listGetD tmFiber6Expected i 0) == 1056

theorem tmFiber6Parent_0_ok : tmFiber6ParentCheck 0 = true := by decide
theorem tmFiber6Parent_1_ok : tmFiber6ParentCheck 1 = true := by decide
theorem tmFiber6Parent_2_ok : tmFiber6ParentCheck 2 = true := by decide
theorem tmFiber6Parent_3_ok : tmFiber6ParentCheck 3 = true := by decide
theorem tmFiber6Parent_4_ok : tmFiber6ParentCheck 4 = true := by decide
theorem tmFiber6Parent_5_ok : tmFiber6ParentCheck 5 = true := by decide
theorem tmFiber6Parent_6_ok : tmFiber6ParentCheck 6 = true := by decide
theorem tmFiber6Parent_7_ok : tmFiber6ParentCheck 7 = true := by decide
theorem tmFiber6Parent_8_ok : tmFiber6ParentCheck 8 = true := by decide
theorem tmFiber6Parent_9_ok : tmFiber6ParentCheck 9 = true := by decide
theorem tmFiber6Parent_10_ok : tmFiber6ParentCheck 10 = true := by decide
theorem tmFiber6Parent_11_ok : tmFiber6ParentCheck 11 = true := by decide
theorem tmFiber6Parent_12_ok : tmFiber6ParentCheck 12 = true := by decide
theorem tmFiber6Parent_13_ok : tmFiber6ParentCheck 13 = true := by decide
theorem tmFiber6Parent_14_ok : tmFiber6ParentCheck 14 = true := by decide
theorem tmFiber6Parent_15_ok : tmFiber6ParentCheck 15 = true := by decide

def tmFiber6CertificateAudit : Bool :=
  tmFiber6SourcesCheck &&
    tmFiber6RowCheck 0 &&
    tmFiber6RowCheck 1 &&
    tmFiber6RowCheck 2 &&
    tmFiber6RowCheck 3 &&
    tmFiber6RowCheck 4 &&
    tmFiber6RowCheck 5 &&
    tmFiber6RowCheck 6 &&
    tmFiber6RowCheck 7 &&
    tmFiber6RowCheck 8 &&
    tmFiber6RowCheck 9 &&
    tmFiber6RowCheck 10 &&
    tmFiber6RowCheck 11 &&
    tmFiber6RowCheck 12 &&
    tmFiber6RowCheck 13 &&
    tmFiber6RowCheck 14 &&
    tmFiber6RowCheck 15 &&
    tmFiber6ParentCheck 0 &&
    tmFiber6ParentCheck 1 &&
    tmFiber6ParentCheck 2 &&
    tmFiber6ParentCheck 3 &&
    tmFiber6ParentCheck 4 &&
    tmFiber6ParentCheck 5 &&
    tmFiber6ParentCheck 6 &&
    tmFiber6ParentCheck 7 &&
    tmFiber6ParentCheck 8 &&
    tmFiber6ParentCheck 9 &&
    tmFiber6ParentCheck 10 &&
    tmFiber6ParentCheck 11 &&
    tmFiber6ParentCheck 12 &&
    tmFiber6ParentCheck 13 &&
    tmFiber6ParentCheck 14 &&
    tmFiber6ParentCheck 15

theorem tmFiber6CertificateAudit_ok :
    tmFiber6CertificateAudit = true := by
  simp [tmFiber6CertificateAudit,
    tmFiber6SourcesCheck_ok,
    tmFiber6Row_0_ok,
    tmFiber6Row_1_ok,
    tmFiber6Row_2_ok,
    tmFiber6Row_3_ok,
    tmFiber6Row_4_ok,
    tmFiber6Row_5_ok,
    tmFiber6Row_6_ok,
    tmFiber6Row_7_ok,
    tmFiber6Row_8_ok,
    tmFiber6Row_9_ok,
    tmFiber6Row_10_ok,
    tmFiber6Row_11_ok,
    tmFiber6Row_12_ok,
    tmFiber6Row_13_ok,
    tmFiber6Row_14_ok,
    tmFiber6Row_15_ok,
    tmFiber6Parent_0_ok,
    tmFiber6Parent_1_ok,
    tmFiber6Parent_2_ok,
    tmFiber6Parent_3_ok,
    tmFiber6Parent_4_ok,
    tmFiber6Parent_5_ok,
    tmFiber6Parent_6_ok,
    tmFiber6Parent_7_ok,
    tmFiber6Parent_8_ok,
    tmFiber6Parent_9_ok,
    tmFiber6Parent_10_ok,
    tmFiber6Parent_11_ok,
    tmFiber6Parent_12_ok,
    tmFiber6Parent_13_ok,
    tmFiber6Parent_14_ok,
    tmFiber6Parent_15_ok]

def tmFiber7Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.b]

def tmFiber7Expected : List Nat :=
  [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783]

def tmFiber7Rows : List DirectChainParentRow :=
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

def tmFiber7RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber7Rows i default

def tmFiber7SourcesCheck : Bool :=
  (tmFiber7Rows.map fun row => row.source) == tmFiber7Expected

theorem tmFiber7SourcesCheck_ok :
    tmFiber7SourcesCheck = true := by
  decide

def tmFiber7RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt i)

theorem tmFiber7Row_0_ok : tmFiber7RowCheck 0 = true := by decide
theorem tmFiber7Row_1_ok : tmFiber7RowCheck 1 = true := by decide
theorem tmFiber7Row_2_ok : tmFiber7RowCheck 2 = true := by decide
theorem tmFiber7Row_3_ok : tmFiber7RowCheck 3 = true := by decide
theorem tmFiber7Row_4_ok : tmFiber7RowCheck 4 = true := by decide
theorem tmFiber7Row_5_ok : tmFiber7RowCheck 5 = true := by decide
theorem tmFiber7Row_6_ok : tmFiber7RowCheck 6 = true := by decide
theorem tmFiber7Row_7_ok : tmFiber7RowCheck 7 = true := by decide
theorem tmFiber7Row_8_ok : tmFiber7RowCheck 8 = true := by decide
theorem tmFiber7Row_9_ok : tmFiber7RowCheck 9 = true := by decide
theorem tmFiber7Row_10_ok : tmFiber7RowCheck 10 = true := by decide
theorem tmFiber7Row_11_ok : tmFiber7RowCheck 11 = true := by decide
theorem tmFiber7Row_12_ok : tmFiber7RowCheck 12 = true := by decide
theorem tmFiber7Row_13_ok : tmFiber7RowCheck 13 = true := by decide
theorem tmFiber7Row_14_ok : tmFiber7RowCheck 14 = true := by decide
theorem tmFiber7Row_15_ok : tmFiber7RowCheck 15 = true := by decide

def tmFiber7ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber7Rows tmMaxParentDepth (listGetD tmFiber7Expected i 0) == 768

theorem tmFiber7Parent_0_ok : tmFiber7ParentCheck 0 = true := by decide
theorem tmFiber7Parent_1_ok : tmFiber7ParentCheck 1 = true := by decide
theorem tmFiber7Parent_2_ok : tmFiber7ParentCheck 2 = true := by decide
theorem tmFiber7Parent_3_ok : tmFiber7ParentCheck 3 = true := by decide
theorem tmFiber7Parent_4_ok : tmFiber7ParentCheck 4 = true := by decide
theorem tmFiber7Parent_5_ok : tmFiber7ParentCheck 5 = true := by decide
theorem tmFiber7Parent_6_ok : tmFiber7ParentCheck 6 = true := by decide
theorem tmFiber7Parent_7_ok : tmFiber7ParentCheck 7 = true := by decide
theorem tmFiber7Parent_8_ok : tmFiber7ParentCheck 8 = true := by decide
theorem tmFiber7Parent_9_ok : tmFiber7ParentCheck 9 = true := by decide
theorem tmFiber7Parent_10_ok : tmFiber7ParentCheck 10 = true := by decide
theorem tmFiber7Parent_11_ok : tmFiber7ParentCheck 11 = true := by decide
theorem tmFiber7Parent_12_ok : tmFiber7ParentCheck 12 = true := by decide
theorem tmFiber7Parent_13_ok : tmFiber7ParentCheck 13 = true := by decide
theorem tmFiber7Parent_14_ok : tmFiber7ParentCheck 14 = true := by decide
theorem tmFiber7Parent_15_ok : tmFiber7ParentCheck 15 = true := by decide

def tmFiber7CertificateAudit : Bool :=
  tmFiber7SourcesCheck &&
    tmFiber7RowCheck 0 &&
    tmFiber7RowCheck 1 &&
    tmFiber7RowCheck 2 &&
    tmFiber7RowCheck 3 &&
    tmFiber7RowCheck 4 &&
    tmFiber7RowCheck 5 &&
    tmFiber7RowCheck 6 &&
    tmFiber7RowCheck 7 &&
    tmFiber7RowCheck 8 &&
    tmFiber7RowCheck 9 &&
    tmFiber7RowCheck 10 &&
    tmFiber7RowCheck 11 &&
    tmFiber7RowCheck 12 &&
    tmFiber7RowCheck 13 &&
    tmFiber7RowCheck 14 &&
    tmFiber7RowCheck 15 &&
    tmFiber7ParentCheck 0 &&
    tmFiber7ParentCheck 1 &&
    tmFiber7ParentCheck 2 &&
    tmFiber7ParentCheck 3 &&
    tmFiber7ParentCheck 4 &&
    tmFiber7ParentCheck 5 &&
    tmFiber7ParentCheck 6 &&
    tmFiber7ParentCheck 7 &&
    tmFiber7ParentCheck 8 &&
    tmFiber7ParentCheck 9 &&
    tmFiber7ParentCheck 10 &&
    tmFiber7ParentCheck 11 &&
    tmFiber7ParentCheck 12 &&
    tmFiber7ParentCheck 13 &&
    tmFiber7ParentCheck 14 &&
    tmFiber7ParentCheck 15

theorem tmFiber7CertificateAudit_ok :
    tmFiber7CertificateAudit = true := by
  simp [tmFiber7CertificateAudit,
    tmFiber7SourcesCheck_ok,
    tmFiber7Row_0_ok,
    tmFiber7Row_1_ok,
    tmFiber7Row_2_ok,
    tmFiber7Row_3_ok,
    tmFiber7Row_4_ok,
    tmFiber7Row_5_ok,
    tmFiber7Row_6_ok,
    tmFiber7Row_7_ok,
    tmFiber7Row_8_ok,
    tmFiber7Row_9_ok,
    tmFiber7Row_10_ok,
    tmFiber7Row_11_ok,
    tmFiber7Row_12_ok,
    tmFiber7Row_13_ok,
    tmFiber7Row_14_ok,
    tmFiber7Row_15_ok,
    tmFiber7Parent_0_ok,
    tmFiber7Parent_1_ok,
    tmFiber7Parent_2_ok,
    tmFiber7Parent_3_ok,
    tmFiber7Parent_4_ok,
    tmFiber7Parent_5_ok,
    tmFiber7Parent_6_ok,
    tmFiber7Parent_7_ok,
    tmFiber7Parent_8_ok,
    tmFiber7Parent_9_ok,
    tmFiber7Parent_10_ok,
    tmFiber7Parent_11_ok,
    tmFiber7Parent_12_ok,
    tmFiber7Parent_13_ok,
    tmFiber7Parent_14_ok,
    tmFiber7Parent_15_ok]

def tmFiber8Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.p]

def tmFiber8Expected : List Nat :=
  [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]

def tmFiber8Rows : List DirectChainParentRow :=
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

def tmFiber8RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber8Rows i default

def tmFiber8SourcesCheck : Bool :=
  (tmFiber8Rows.map fun row => row.source) == tmFiber8Expected

theorem tmFiber8SourcesCheck_ok :
    tmFiber8SourcesCheck = true := by
  decide

def tmFiber8RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber8Key tmFiber8Expected (tmFiber8RowAt i)

theorem tmFiber8Row_0_ok : tmFiber8RowCheck 0 = true := by decide
theorem tmFiber8Row_1_ok : tmFiber8RowCheck 1 = true := by decide
theorem tmFiber8Row_2_ok : tmFiber8RowCheck 2 = true := by decide
theorem tmFiber8Row_3_ok : tmFiber8RowCheck 3 = true := by decide
theorem tmFiber8Row_4_ok : tmFiber8RowCheck 4 = true := by decide
theorem tmFiber8Row_5_ok : tmFiber8RowCheck 5 = true := by decide
theorem tmFiber8Row_6_ok : tmFiber8RowCheck 6 = true := by decide
theorem tmFiber8Row_7_ok : tmFiber8RowCheck 7 = true := by decide
theorem tmFiber8Row_8_ok : tmFiber8RowCheck 8 = true := by decide
theorem tmFiber8Row_9_ok : tmFiber8RowCheck 9 = true := by decide
theorem tmFiber8Row_10_ok : tmFiber8RowCheck 10 = true := by decide
theorem tmFiber8Row_11_ok : tmFiber8RowCheck 11 = true := by decide
theorem tmFiber8Row_12_ok : tmFiber8RowCheck 12 = true := by decide
theorem tmFiber8Row_13_ok : tmFiber8RowCheck 13 = true := by decide
theorem tmFiber8Row_14_ok : tmFiber8RowCheck 14 = true := by decide
theorem tmFiber8Row_15_ok : tmFiber8RowCheck 15 = true := by decide
theorem tmFiber8Row_16_ok : tmFiber8RowCheck 16 = true := by decide
theorem tmFiber8Row_17_ok : tmFiber8RowCheck 17 = true := by decide
theorem tmFiber8Row_18_ok : tmFiber8RowCheck 18 = true := by decide
theorem tmFiber8Row_19_ok : tmFiber8RowCheck 19 = true := by decide
theorem tmFiber8Row_20_ok : tmFiber8RowCheck 20 = true := by decide
theorem tmFiber8Row_21_ok : tmFiber8RowCheck 21 = true := by decide
theorem tmFiber8Row_22_ok : tmFiber8RowCheck 22 = true := by decide
theorem tmFiber8Row_23_ok : tmFiber8RowCheck 23 = true := by decide
theorem tmFiber8Row_24_ok : tmFiber8RowCheck 24 = true := by decide
theorem tmFiber8Row_25_ok : tmFiber8RowCheck 25 = true := by decide
theorem tmFiber8Row_26_ok : tmFiber8RowCheck 26 = true := by decide
theorem tmFiber8Row_27_ok : tmFiber8RowCheck 27 = true := by decide
theorem tmFiber8Row_28_ok : tmFiber8RowCheck 28 = true := by decide
theorem tmFiber8Row_29_ok : tmFiber8RowCheck 29 = true := by decide
theorem tmFiber8Row_30_ok : tmFiber8RowCheck 30 = true := by decide
theorem tmFiber8Row_31_ok : tmFiber8RowCheck 31 = true := by decide
theorem tmFiber8Row_32_ok : tmFiber8RowCheck 32 = true := by decide
theorem tmFiber8Row_33_ok : tmFiber8RowCheck 33 = true := by decide
theorem tmFiber8Row_34_ok : tmFiber8RowCheck 34 = true := by decide
theorem tmFiber8Row_35_ok : tmFiber8RowCheck 35 = true := by decide
theorem tmFiber8Row_36_ok : tmFiber8RowCheck 36 = true := by decide
theorem tmFiber8Row_37_ok : tmFiber8RowCheck 37 = true := by decide
theorem tmFiber8Row_38_ok : tmFiber8RowCheck 38 = true := by decide
theorem tmFiber8Row_39_ok : tmFiber8RowCheck 39 = true := by decide
theorem tmFiber8Row_40_ok : tmFiber8RowCheck 40 = true := by decide
theorem tmFiber8Row_41_ok : tmFiber8RowCheck 41 = true := by decide
theorem tmFiber8Row_42_ok : tmFiber8RowCheck 42 = true := by decide
theorem tmFiber8Row_43_ok : tmFiber8RowCheck 43 = true := by decide
theorem tmFiber8Row_44_ok : tmFiber8RowCheck 44 = true := by decide
theorem tmFiber8Row_45_ok : tmFiber8RowCheck 45 = true := by decide
theorem tmFiber8Row_46_ok : tmFiber8RowCheck 46 = true := by decide
theorem tmFiber8Row_47_ok : tmFiber8RowCheck 47 = true := by decide
theorem tmFiber8Row_48_ok : tmFiber8RowCheck 48 = true := by decide
theorem tmFiber8Row_49_ok : tmFiber8RowCheck 49 = true := by decide
theorem tmFiber8Row_50_ok : tmFiber8RowCheck 50 = true := by decide
theorem tmFiber8Row_51_ok : tmFiber8RowCheck 51 = true := by decide
theorem tmFiber8Row_52_ok : tmFiber8RowCheck 52 = true := by decide
theorem tmFiber8Row_53_ok : tmFiber8RowCheck 53 = true := by decide
theorem tmFiber8Row_54_ok : tmFiber8RowCheck 54 = true := by decide
theorem tmFiber8Row_55_ok : tmFiber8RowCheck 55 = true := by decide
theorem tmFiber8Row_56_ok : tmFiber8RowCheck 56 = true := by decide
theorem tmFiber8Row_57_ok : tmFiber8RowCheck 57 = true := by decide
theorem tmFiber8Row_58_ok : tmFiber8RowCheck 58 = true := by decide
theorem tmFiber8Row_59_ok : tmFiber8RowCheck 59 = true := by decide
theorem tmFiber8Row_60_ok : tmFiber8RowCheck 60 = true := by decide
theorem tmFiber8Row_61_ok : tmFiber8RowCheck 61 = true := by decide
theorem tmFiber8Row_62_ok : tmFiber8RowCheck 62 = true := by decide
theorem tmFiber8Row_63_ok : tmFiber8RowCheck 63 = true := by decide

def tmFiber8ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber8Rows tmMaxParentDepth (listGetD tmFiber8Expected i 0) == 784

theorem tmFiber8Parent_0_ok : tmFiber8ParentCheck 0 = true := by decide
theorem tmFiber8Parent_1_ok : tmFiber8ParentCheck 1 = true := by decide
theorem tmFiber8Parent_2_ok : tmFiber8ParentCheck 2 = true := by decide
theorem tmFiber8Parent_3_ok : tmFiber8ParentCheck 3 = true := by decide
theorem tmFiber8Parent_4_ok : tmFiber8ParentCheck 4 = true := by decide
theorem tmFiber8Parent_5_ok : tmFiber8ParentCheck 5 = true := by decide
theorem tmFiber8Parent_6_ok : tmFiber8ParentCheck 6 = true := by decide
theorem tmFiber8Parent_7_ok : tmFiber8ParentCheck 7 = true := by decide
theorem tmFiber8Parent_8_ok : tmFiber8ParentCheck 8 = true := by decide
theorem tmFiber8Parent_9_ok : tmFiber8ParentCheck 9 = true := by decide
theorem tmFiber8Parent_10_ok : tmFiber8ParentCheck 10 = true := by decide
theorem tmFiber8Parent_11_ok : tmFiber8ParentCheck 11 = true := by decide
theorem tmFiber8Parent_12_ok : tmFiber8ParentCheck 12 = true := by decide
theorem tmFiber8Parent_13_ok : tmFiber8ParentCheck 13 = true := by decide
theorem tmFiber8Parent_14_ok : tmFiber8ParentCheck 14 = true := by decide
theorem tmFiber8Parent_15_ok : tmFiber8ParentCheck 15 = true := by decide
theorem tmFiber8Parent_16_ok : tmFiber8ParentCheck 16 = true := by decide
theorem tmFiber8Parent_17_ok : tmFiber8ParentCheck 17 = true := by decide
theorem tmFiber8Parent_18_ok : tmFiber8ParentCheck 18 = true := by decide
theorem tmFiber8Parent_19_ok : tmFiber8ParentCheck 19 = true := by decide
theorem tmFiber8Parent_20_ok : tmFiber8ParentCheck 20 = true := by decide
theorem tmFiber8Parent_21_ok : tmFiber8ParentCheck 21 = true := by decide
theorem tmFiber8Parent_22_ok : tmFiber8ParentCheck 22 = true := by decide
theorem tmFiber8Parent_23_ok : tmFiber8ParentCheck 23 = true := by decide
theorem tmFiber8Parent_24_ok : tmFiber8ParentCheck 24 = true := by decide
theorem tmFiber8Parent_25_ok : tmFiber8ParentCheck 25 = true := by decide
theorem tmFiber8Parent_26_ok : tmFiber8ParentCheck 26 = true := by decide
theorem tmFiber8Parent_27_ok : tmFiber8ParentCheck 27 = true := by decide
theorem tmFiber8Parent_28_ok : tmFiber8ParentCheck 28 = true := by decide
theorem tmFiber8Parent_29_ok : tmFiber8ParentCheck 29 = true := by decide
theorem tmFiber8Parent_30_ok : tmFiber8ParentCheck 30 = true := by decide
theorem tmFiber8Parent_31_ok : tmFiber8ParentCheck 31 = true := by decide
theorem tmFiber8Parent_32_ok : tmFiber8ParentCheck 32 = true := by decide
theorem tmFiber8Parent_33_ok : tmFiber8ParentCheck 33 = true := by decide
theorem tmFiber8Parent_34_ok : tmFiber8ParentCheck 34 = true := by decide
theorem tmFiber8Parent_35_ok : tmFiber8ParentCheck 35 = true := by decide
theorem tmFiber8Parent_36_ok : tmFiber8ParentCheck 36 = true := by decide
theorem tmFiber8Parent_37_ok : tmFiber8ParentCheck 37 = true := by decide
theorem tmFiber8Parent_38_ok : tmFiber8ParentCheck 38 = true := by decide
theorem tmFiber8Parent_39_ok : tmFiber8ParentCheck 39 = true := by decide
theorem tmFiber8Parent_40_ok : tmFiber8ParentCheck 40 = true := by decide
theorem tmFiber8Parent_41_ok : tmFiber8ParentCheck 41 = true := by decide
theorem tmFiber8Parent_42_ok : tmFiber8ParentCheck 42 = true := by decide
theorem tmFiber8Parent_43_ok : tmFiber8ParentCheck 43 = true := by decide
theorem tmFiber8Parent_44_ok : tmFiber8ParentCheck 44 = true := by decide
theorem tmFiber8Parent_45_ok : tmFiber8ParentCheck 45 = true := by decide
theorem tmFiber8Parent_46_ok : tmFiber8ParentCheck 46 = true := by decide
theorem tmFiber8Parent_47_ok : tmFiber8ParentCheck 47 = true := by decide
theorem tmFiber8Parent_48_ok : tmFiber8ParentCheck 48 = true := by decide
theorem tmFiber8Parent_49_ok : tmFiber8ParentCheck 49 = true := by decide
theorem tmFiber8Parent_50_ok : tmFiber8ParentCheck 50 = true := by decide
theorem tmFiber8Parent_51_ok : tmFiber8ParentCheck 51 = true := by decide
theorem tmFiber8Parent_52_ok : tmFiber8ParentCheck 52 = true := by decide
theorem tmFiber8Parent_53_ok : tmFiber8ParentCheck 53 = true := by decide
theorem tmFiber8Parent_54_ok : tmFiber8ParentCheck 54 = true := by decide
theorem tmFiber8Parent_55_ok : tmFiber8ParentCheck 55 = true := by decide
theorem tmFiber8Parent_56_ok : tmFiber8ParentCheck 56 = true := by decide
theorem tmFiber8Parent_57_ok : tmFiber8ParentCheck 57 = true := by decide
theorem tmFiber8Parent_58_ok : tmFiber8ParentCheck 58 = true := by decide
theorem tmFiber8Parent_59_ok : tmFiber8ParentCheck 59 = true := by decide
theorem tmFiber8Parent_60_ok : tmFiber8ParentCheck 60 = true := by decide
theorem tmFiber8Parent_61_ok : tmFiber8ParentCheck 61 = true := by decide
theorem tmFiber8Parent_62_ok : tmFiber8ParentCheck 62 = true := by decide
theorem tmFiber8Parent_63_ok : tmFiber8ParentCheck 63 = true := by decide

def tmFiber8CertificateAudit : Bool :=
  tmFiber8SourcesCheck &&
    tmFiber8RowCheck 0 &&
    tmFiber8RowCheck 1 &&
    tmFiber8RowCheck 2 &&
    tmFiber8RowCheck 3 &&
    tmFiber8RowCheck 4 &&
    tmFiber8RowCheck 5 &&
    tmFiber8RowCheck 6 &&
    tmFiber8RowCheck 7 &&
    tmFiber8RowCheck 8 &&
    tmFiber8RowCheck 9 &&
    tmFiber8RowCheck 10 &&
    tmFiber8RowCheck 11 &&
    tmFiber8RowCheck 12 &&
    tmFiber8RowCheck 13 &&
    tmFiber8RowCheck 14 &&
    tmFiber8RowCheck 15 &&
    tmFiber8RowCheck 16 &&
    tmFiber8RowCheck 17 &&
    tmFiber8RowCheck 18 &&
    tmFiber8RowCheck 19 &&
    tmFiber8RowCheck 20 &&
    tmFiber8RowCheck 21 &&
    tmFiber8RowCheck 22 &&
    tmFiber8RowCheck 23 &&
    tmFiber8RowCheck 24 &&
    tmFiber8RowCheck 25 &&
    tmFiber8RowCheck 26 &&
    tmFiber8RowCheck 27 &&
    tmFiber8RowCheck 28 &&
    tmFiber8RowCheck 29 &&
    tmFiber8RowCheck 30 &&
    tmFiber8RowCheck 31 &&
    tmFiber8RowCheck 32 &&
    tmFiber8RowCheck 33 &&
    tmFiber8RowCheck 34 &&
    tmFiber8RowCheck 35 &&
    tmFiber8RowCheck 36 &&
    tmFiber8RowCheck 37 &&
    tmFiber8RowCheck 38 &&
    tmFiber8RowCheck 39 &&
    tmFiber8RowCheck 40 &&
    tmFiber8RowCheck 41 &&
    tmFiber8RowCheck 42 &&
    tmFiber8RowCheck 43 &&
    tmFiber8RowCheck 44 &&
    tmFiber8RowCheck 45 &&
    tmFiber8RowCheck 46 &&
    tmFiber8RowCheck 47 &&
    tmFiber8RowCheck 48 &&
    tmFiber8RowCheck 49 &&
    tmFiber8RowCheck 50 &&
    tmFiber8RowCheck 51 &&
    tmFiber8RowCheck 52 &&
    tmFiber8RowCheck 53 &&
    tmFiber8RowCheck 54 &&
    tmFiber8RowCheck 55 &&
    tmFiber8RowCheck 56 &&
    tmFiber8RowCheck 57 &&
    tmFiber8RowCheck 58 &&
    tmFiber8RowCheck 59 &&
    tmFiber8RowCheck 60 &&
    tmFiber8RowCheck 61 &&
    tmFiber8RowCheck 62 &&
    tmFiber8RowCheck 63 &&
    tmFiber8ParentCheck 0 &&
    tmFiber8ParentCheck 1 &&
    tmFiber8ParentCheck 2 &&
    tmFiber8ParentCheck 3 &&
    tmFiber8ParentCheck 4 &&
    tmFiber8ParentCheck 5 &&
    tmFiber8ParentCheck 6 &&
    tmFiber8ParentCheck 7 &&
    tmFiber8ParentCheck 8 &&
    tmFiber8ParentCheck 9 &&
    tmFiber8ParentCheck 10 &&
    tmFiber8ParentCheck 11 &&
    tmFiber8ParentCheck 12 &&
    tmFiber8ParentCheck 13 &&
    tmFiber8ParentCheck 14 &&
    tmFiber8ParentCheck 15 &&
    tmFiber8ParentCheck 16 &&
    tmFiber8ParentCheck 17 &&
    tmFiber8ParentCheck 18 &&
    tmFiber8ParentCheck 19 &&
    tmFiber8ParentCheck 20 &&
    tmFiber8ParentCheck 21 &&
    tmFiber8ParentCheck 22 &&
    tmFiber8ParentCheck 23 &&
    tmFiber8ParentCheck 24 &&
    tmFiber8ParentCheck 25 &&
    tmFiber8ParentCheck 26 &&
    tmFiber8ParentCheck 27 &&
    tmFiber8ParentCheck 28 &&
    tmFiber8ParentCheck 29 &&
    tmFiber8ParentCheck 30 &&
    tmFiber8ParentCheck 31 &&
    tmFiber8ParentCheck 32 &&
    tmFiber8ParentCheck 33 &&
    tmFiber8ParentCheck 34 &&
    tmFiber8ParentCheck 35 &&
    tmFiber8ParentCheck 36 &&
    tmFiber8ParentCheck 37 &&
    tmFiber8ParentCheck 38 &&
    tmFiber8ParentCheck 39 &&
    tmFiber8ParentCheck 40 &&
    tmFiber8ParentCheck 41 &&
    tmFiber8ParentCheck 42 &&
    tmFiber8ParentCheck 43 &&
    tmFiber8ParentCheck 44 &&
    tmFiber8ParentCheck 45 &&
    tmFiber8ParentCheck 46 &&
    tmFiber8ParentCheck 47 &&
    tmFiber8ParentCheck 48 &&
    tmFiber8ParentCheck 49 &&
    tmFiber8ParentCheck 50 &&
    tmFiber8ParentCheck 51 &&
    tmFiber8ParentCheck 52 &&
    tmFiber8ParentCheck 53 &&
    tmFiber8ParentCheck 54 &&
    tmFiber8ParentCheck 55 &&
    tmFiber8ParentCheck 56 &&
    tmFiber8ParentCheck 57 &&
    tmFiber8ParentCheck 58 &&
    tmFiber8ParentCheck 59 &&
    tmFiber8ParentCheck 60 &&
    tmFiber8ParentCheck 61 &&
    tmFiber8ParentCheck 62 &&
    tmFiber8ParentCheck 63

theorem tmFiber8CertificateAudit_ok :
    tmFiber8CertificateAudit = true := by
  simp [tmFiber8CertificateAudit,
    tmFiber8SourcesCheck_ok,
    tmFiber8Row_0_ok,
    tmFiber8Row_1_ok,
    tmFiber8Row_2_ok,
    tmFiber8Row_3_ok,
    tmFiber8Row_4_ok,
    tmFiber8Row_5_ok,
    tmFiber8Row_6_ok,
    tmFiber8Row_7_ok,
    tmFiber8Row_8_ok,
    tmFiber8Row_9_ok,
    tmFiber8Row_10_ok,
    tmFiber8Row_11_ok,
    tmFiber8Row_12_ok,
    tmFiber8Row_13_ok,
    tmFiber8Row_14_ok,
    tmFiber8Row_15_ok,
    tmFiber8Row_16_ok,
    tmFiber8Row_17_ok,
    tmFiber8Row_18_ok,
    tmFiber8Row_19_ok,
    tmFiber8Row_20_ok,
    tmFiber8Row_21_ok,
    tmFiber8Row_22_ok,
    tmFiber8Row_23_ok,
    tmFiber8Row_24_ok,
    tmFiber8Row_25_ok,
    tmFiber8Row_26_ok,
    tmFiber8Row_27_ok,
    tmFiber8Row_28_ok,
    tmFiber8Row_29_ok,
    tmFiber8Row_30_ok,
    tmFiber8Row_31_ok,
    tmFiber8Row_32_ok,
    tmFiber8Row_33_ok,
    tmFiber8Row_34_ok,
    tmFiber8Row_35_ok,
    tmFiber8Row_36_ok,
    tmFiber8Row_37_ok,
    tmFiber8Row_38_ok,
    tmFiber8Row_39_ok,
    tmFiber8Row_40_ok,
    tmFiber8Row_41_ok,
    tmFiber8Row_42_ok,
    tmFiber8Row_43_ok,
    tmFiber8Row_44_ok,
    tmFiber8Row_45_ok,
    tmFiber8Row_46_ok,
    tmFiber8Row_47_ok,
    tmFiber8Row_48_ok,
    tmFiber8Row_49_ok,
    tmFiber8Row_50_ok,
    tmFiber8Row_51_ok,
    tmFiber8Row_52_ok,
    tmFiber8Row_53_ok,
    tmFiber8Row_54_ok,
    tmFiber8Row_55_ok,
    tmFiber8Row_56_ok,
    tmFiber8Row_57_ok,
    tmFiber8Row_58_ok,
    tmFiber8Row_59_ok,
    tmFiber8Row_60_ok,
    tmFiber8Row_61_ok,
    tmFiber8Row_62_ok,
    tmFiber8Row_63_ok,
    tmFiber8Parent_0_ok,
    tmFiber8Parent_1_ok,
    tmFiber8Parent_2_ok,
    tmFiber8Parent_3_ok,
    tmFiber8Parent_4_ok,
    tmFiber8Parent_5_ok,
    tmFiber8Parent_6_ok,
    tmFiber8Parent_7_ok,
    tmFiber8Parent_8_ok,
    tmFiber8Parent_9_ok,
    tmFiber8Parent_10_ok,
    tmFiber8Parent_11_ok,
    tmFiber8Parent_12_ok,
    tmFiber8Parent_13_ok,
    tmFiber8Parent_14_ok,
    tmFiber8Parent_15_ok,
    tmFiber8Parent_16_ok,
    tmFiber8Parent_17_ok,
    tmFiber8Parent_18_ok,
    tmFiber8Parent_19_ok,
    tmFiber8Parent_20_ok,
    tmFiber8Parent_21_ok,
    tmFiber8Parent_22_ok,
    tmFiber8Parent_23_ok,
    tmFiber8Parent_24_ok,
    tmFiber8Parent_25_ok,
    tmFiber8Parent_26_ok,
    tmFiber8Parent_27_ok,
    tmFiber8Parent_28_ok,
    tmFiber8Parent_29_ok,
    tmFiber8Parent_30_ok,
    tmFiber8Parent_31_ok,
    tmFiber8Parent_32_ok,
    tmFiber8Parent_33_ok,
    tmFiber8Parent_34_ok,
    tmFiber8Parent_35_ok,
    tmFiber8Parent_36_ok,
    tmFiber8Parent_37_ok,
    tmFiber8Parent_38_ok,
    tmFiber8Parent_39_ok,
    tmFiber8Parent_40_ok,
    tmFiber8Parent_41_ok,
    tmFiber8Parent_42_ok,
    tmFiber8Parent_43_ok,
    tmFiber8Parent_44_ok,
    tmFiber8Parent_45_ok,
    tmFiber8Parent_46_ok,
    tmFiber8Parent_47_ok,
    tmFiber8Parent_48_ok,
    tmFiber8Parent_49_ok,
    tmFiber8Parent_50_ok,
    tmFiber8Parent_51_ok,
    tmFiber8Parent_52_ok,
    tmFiber8Parent_53_ok,
    tmFiber8Parent_54_ok,
    tmFiber8Parent_55_ok,
    tmFiber8Parent_56_ok,
    tmFiber8Parent_57_ok,
    tmFiber8Parent_58_ok,
    tmFiber8Parent_59_ok,
    tmFiber8Parent_60_ok,
    tmFiber8Parent_61_ok,
    tmFiber8Parent_62_ok,
    tmFiber8Parent_63_ok]

def tmFiber9Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.r]

def tmFiber9Expected : List Nat :=
  [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]

def tmFiber9Rows : List DirectChainParentRow :=
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

def tmFiber9RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber9Rows i default

def tmFiber9SourcesCheck : Bool :=
  (tmFiber9Rows.map fun row => row.source) == tmFiber9Expected

theorem tmFiber9SourcesCheck_ok :
    tmFiber9SourcesCheck = true := by
  decide

def tmFiber9RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt i)

theorem tmFiber9Row_0_ok : tmFiber9RowCheck 0 = true := by decide
theorem tmFiber9Row_1_ok : tmFiber9RowCheck 1 = true := by decide
theorem tmFiber9Row_2_ok : tmFiber9RowCheck 2 = true := by decide
theorem tmFiber9Row_3_ok : tmFiber9RowCheck 3 = true := by decide
theorem tmFiber9Row_4_ok : tmFiber9RowCheck 4 = true := by decide
theorem tmFiber9Row_5_ok : tmFiber9RowCheck 5 = true := by decide
theorem tmFiber9Row_6_ok : tmFiber9RowCheck 6 = true := by decide
theorem tmFiber9Row_7_ok : tmFiber9RowCheck 7 = true := by decide
theorem tmFiber9Row_8_ok : tmFiber9RowCheck 8 = true := by decide
theorem tmFiber9Row_9_ok : tmFiber9RowCheck 9 = true := by decide
theorem tmFiber9Row_10_ok : tmFiber9RowCheck 10 = true := by decide
theorem tmFiber9Row_11_ok : tmFiber9RowCheck 11 = true := by decide
theorem tmFiber9Row_12_ok : tmFiber9RowCheck 12 = true := by decide
theorem tmFiber9Row_13_ok : tmFiber9RowCheck 13 = true := by decide
theorem tmFiber9Row_14_ok : tmFiber9RowCheck 14 = true := by decide
theorem tmFiber9Row_15_ok : tmFiber9RowCheck 15 = true := by decide

def tmFiber9ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber9Rows tmMaxParentDepth (listGetD tmFiber9Expected i 0) == 720

theorem tmFiber9Parent_0_ok : tmFiber9ParentCheck 0 = true := by decide
theorem tmFiber9Parent_1_ok : tmFiber9ParentCheck 1 = true := by decide
theorem tmFiber9Parent_2_ok : tmFiber9ParentCheck 2 = true := by decide
theorem tmFiber9Parent_3_ok : tmFiber9ParentCheck 3 = true := by decide
theorem tmFiber9Parent_4_ok : tmFiber9ParentCheck 4 = true := by decide
theorem tmFiber9Parent_5_ok : tmFiber9ParentCheck 5 = true := by decide
theorem tmFiber9Parent_6_ok : tmFiber9ParentCheck 6 = true := by decide
theorem tmFiber9Parent_7_ok : tmFiber9ParentCheck 7 = true := by decide
theorem tmFiber9Parent_8_ok : tmFiber9ParentCheck 8 = true := by decide
theorem tmFiber9Parent_9_ok : tmFiber9ParentCheck 9 = true := by decide
theorem tmFiber9Parent_10_ok : tmFiber9ParentCheck 10 = true := by decide
theorem tmFiber9Parent_11_ok : tmFiber9ParentCheck 11 = true := by decide
theorem tmFiber9Parent_12_ok : tmFiber9ParentCheck 12 = true := by decide
theorem tmFiber9Parent_13_ok : tmFiber9ParentCheck 13 = true := by decide
theorem tmFiber9Parent_14_ok : tmFiber9ParentCheck 14 = true := by decide
theorem tmFiber9Parent_15_ok : tmFiber9ParentCheck 15 = true := by decide

def tmFiber9CertificateAudit : Bool :=
  tmFiber9SourcesCheck &&
    tmFiber9RowCheck 0 &&
    tmFiber9RowCheck 1 &&
    tmFiber9RowCheck 2 &&
    tmFiber9RowCheck 3 &&
    tmFiber9RowCheck 4 &&
    tmFiber9RowCheck 5 &&
    tmFiber9RowCheck 6 &&
    tmFiber9RowCheck 7 &&
    tmFiber9RowCheck 8 &&
    tmFiber9RowCheck 9 &&
    tmFiber9RowCheck 10 &&
    tmFiber9RowCheck 11 &&
    tmFiber9RowCheck 12 &&
    tmFiber9RowCheck 13 &&
    tmFiber9RowCheck 14 &&
    tmFiber9RowCheck 15 &&
    tmFiber9ParentCheck 0 &&
    tmFiber9ParentCheck 1 &&
    tmFiber9ParentCheck 2 &&
    tmFiber9ParentCheck 3 &&
    tmFiber9ParentCheck 4 &&
    tmFiber9ParentCheck 5 &&
    tmFiber9ParentCheck 6 &&
    tmFiber9ParentCheck 7 &&
    tmFiber9ParentCheck 8 &&
    tmFiber9ParentCheck 9 &&
    tmFiber9ParentCheck 10 &&
    tmFiber9ParentCheck 11 &&
    tmFiber9ParentCheck 12 &&
    tmFiber9ParentCheck 13 &&
    tmFiber9ParentCheck 14 &&
    tmFiber9ParentCheck 15

theorem tmFiber9CertificateAudit_ok :
    tmFiber9CertificateAudit = true := by
  simp [tmFiber9CertificateAudit,
    tmFiber9SourcesCheck_ok,
    tmFiber9Row_0_ok,
    tmFiber9Row_1_ok,
    tmFiber9Row_2_ok,
    tmFiber9Row_3_ok,
    tmFiber9Row_4_ok,
    tmFiber9Row_5_ok,
    tmFiber9Row_6_ok,
    tmFiber9Row_7_ok,
    tmFiber9Row_8_ok,
    tmFiber9Row_9_ok,
    tmFiber9Row_10_ok,
    tmFiber9Row_11_ok,
    tmFiber9Row_12_ok,
    tmFiber9Row_13_ok,
    tmFiber9Row_14_ok,
    tmFiber9Row_15_ok,
    tmFiber9Parent_0_ok,
    tmFiber9Parent_1_ok,
    tmFiber9Parent_2_ok,
    tmFiber9Parent_3_ok,
    tmFiber9Parent_4_ok,
    tmFiber9Parent_5_ok,
    tmFiber9Parent_6_ok,
    tmFiber9Parent_7_ok,
    tmFiber9Parent_8_ok,
    tmFiber9Parent_9_ok,
    tmFiber9Parent_10_ok,
    tmFiber9Parent_11_ok,
    tmFiber9Parent_12_ok,
    tmFiber9Parent_13_ok,
    tmFiber9Parent_14_ok,
    tmFiber9Parent_15_ok]

def tmFiber10Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.b]

def tmFiber10Expected : List Nat :=
  [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]

def tmFiber10Rows : List DirectChainParentRow :=
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

def tmFiber10RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber10Rows i default

def tmFiber10SourcesCheck : Bool :=
  (tmFiber10Rows.map fun row => row.source) == tmFiber10Expected

theorem tmFiber10SourcesCheck_ok :
    tmFiber10SourcesCheck = true := by
  decide

def tmFiber10RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber10Key tmFiber10Expected (tmFiber10RowAt i)

theorem tmFiber10Row_0_ok : tmFiber10RowCheck 0 = true := by decide
theorem tmFiber10Row_1_ok : tmFiber10RowCheck 1 = true := by decide
theorem tmFiber10Row_2_ok : tmFiber10RowCheck 2 = true := by decide
theorem tmFiber10Row_3_ok : tmFiber10RowCheck 3 = true := by decide
theorem tmFiber10Row_4_ok : tmFiber10RowCheck 4 = true := by decide
theorem tmFiber10Row_5_ok : tmFiber10RowCheck 5 = true := by decide
theorem tmFiber10Row_6_ok : tmFiber10RowCheck 6 = true := by decide
theorem tmFiber10Row_7_ok : tmFiber10RowCheck 7 = true := by decide
theorem tmFiber10Row_8_ok : tmFiber10RowCheck 8 = true := by decide
theorem tmFiber10Row_9_ok : tmFiber10RowCheck 9 = true := by decide
theorem tmFiber10Row_10_ok : tmFiber10RowCheck 10 = true := by decide
theorem tmFiber10Row_11_ok : tmFiber10RowCheck 11 = true := by decide
theorem tmFiber10Row_12_ok : tmFiber10RowCheck 12 = true := by decide
theorem tmFiber10Row_13_ok : tmFiber10RowCheck 13 = true := by decide
theorem tmFiber10Row_14_ok : tmFiber10RowCheck 14 = true := by decide
theorem tmFiber10Row_15_ok : tmFiber10RowCheck 15 = true := by decide
theorem tmFiber10Row_16_ok : tmFiber10RowCheck 16 = true := by decide
theorem tmFiber10Row_17_ok : tmFiber10RowCheck 17 = true := by decide
theorem tmFiber10Row_18_ok : tmFiber10RowCheck 18 = true := by decide
theorem tmFiber10Row_19_ok : tmFiber10RowCheck 19 = true := by decide
theorem tmFiber10Row_20_ok : tmFiber10RowCheck 20 = true := by decide
theorem tmFiber10Row_21_ok : tmFiber10RowCheck 21 = true := by decide
theorem tmFiber10Row_22_ok : tmFiber10RowCheck 22 = true := by decide
theorem tmFiber10Row_23_ok : tmFiber10RowCheck 23 = true := by decide
theorem tmFiber10Row_24_ok : tmFiber10RowCheck 24 = true := by decide
theorem tmFiber10Row_25_ok : tmFiber10RowCheck 25 = true := by decide
theorem tmFiber10Row_26_ok : tmFiber10RowCheck 26 = true := by decide
theorem tmFiber10Row_27_ok : tmFiber10RowCheck 27 = true := by decide
theorem tmFiber10Row_28_ok : tmFiber10RowCheck 28 = true := by decide
theorem tmFiber10Row_29_ok : tmFiber10RowCheck 29 = true := by decide
theorem tmFiber10Row_30_ok : tmFiber10RowCheck 30 = true := by decide
theorem tmFiber10Row_31_ok : tmFiber10RowCheck 31 = true := by decide
theorem tmFiber10Row_32_ok : tmFiber10RowCheck 32 = true := by decide
theorem tmFiber10Row_33_ok : tmFiber10RowCheck 33 = true := by decide
theorem tmFiber10Row_34_ok : tmFiber10RowCheck 34 = true := by decide
theorem tmFiber10Row_35_ok : tmFiber10RowCheck 35 = true := by decide
theorem tmFiber10Row_36_ok : tmFiber10RowCheck 36 = true := by decide
theorem tmFiber10Row_37_ok : tmFiber10RowCheck 37 = true := by decide
theorem tmFiber10Row_38_ok : tmFiber10RowCheck 38 = true := by decide
theorem tmFiber10Row_39_ok : tmFiber10RowCheck 39 = true := by decide
theorem tmFiber10Row_40_ok : tmFiber10RowCheck 40 = true := by decide
theorem tmFiber10Row_41_ok : tmFiber10RowCheck 41 = true := by decide
theorem tmFiber10Row_42_ok : tmFiber10RowCheck 42 = true := by decide
theorem tmFiber10Row_43_ok : tmFiber10RowCheck 43 = true := by decide
theorem tmFiber10Row_44_ok : tmFiber10RowCheck 44 = true := by decide
theorem tmFiber10Row_45_ok : tmFiber10RowCheck 45 = true := by decide
theorem tmFiber10Row_46_ok : tmFiber10RowCheck 46 = true := by decide
theorem tmFiber10Row_47_ok : tmFiber10RowCheck 47 = true := by decide
theorem tmFiber10Row_48_ok : tmFiber10RowCheck 48 = true := by decide
theorem tmFiber10Row_49_ok : tmFiber10RowCheck 49 = true := by decide
theorem tmFiber10Row_50_ok : tmFiber10RowCheck 50 = true := by decide
theorem tmFiber10Row_51_ok : tmFiber10RowCheck 51 = true := by decide
theorem tmFiber10Row_52_ok : tmFiber10RowCheck 52 = true := by decide
theorem tmFiber10Row_53_ok : tmFiber10RowCheck 53 = true := by decide
theorem tmFiber10Row_54_ok : tmFiber10RowCheck 54 = true := by decide
theorem tmFiber10Row_55_ok : tmFiber10RowCheck 55 = true := by decide
theorem tmFiber10Row_56_ok : tmFiber10RowCheck 56 = true := by decide
theorem tmFiber10Row_57_ok : tmFiber10RowCheck 57 = true := by decide
theorem tmFiber10Row_58_ok : tmFiber10RowCheck 58 = true := by decide
theorem tmFiber10Row_59_ok : tmFiber10RowCheck 59 = true := by decide
theorem tmFiber10Row_60_ok : tmFiber10RowCheck 60 = true := by decide
theorem tmFiber10Row_61_ok : tmFiber10RowCheck 61 = true := by decide
theorem tmFiber10Row_62_ok : tmFiber10RowCheck 62 = true := by decide
theorem tmFiber10Row_63_ok : tmFiber10RowCheck 63 = true := by decide

def tmFiber10ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber10Rows tmMaxParentDepth (listGetD tmFiber10Expected i 0) == 432

theorem tmFiber10Parent_0_ok : tmFiber10ParentCheck 0 = true := by decide
theorem tmFiber10Parent_1_ok : tmFiber10ParentCheck 1 = true := by decide
theorem tmFiber10Parent_2_ok : tmFiber10ParentCheck 2 = true := by decide
theorem tmFiber10Parent_3_ok : tmFiber10ParentCheck 3 = true := by decide
theorem tmFiber10Parent_4_ok : tmFiber10ParentCheck 4 = true := by decide
theorem tmFiber10Parent_5_ok : tmFiber10ParentCheck 5 = true := by decide
theorem tmFiber10Parent_6_ok : tmFiber10ParentCheck 6 = true := by decide
theorem tmFiber10Parent_7_ok : tmFiber10ParentCheck 7 = true := by decide
theorem tmFiber10Parent_8_ok : tmFiber10ParentCheck 8 = true := by decide
theorem tmFiber10Parent_9_ok : tmFiber10ParentCheck 9 = true := by decide
theorem tmFiber10Parent_10_ok : tmFiber10ParentCheck 10 = true := by decide
theorem tmFiber10Parent_11_ok : tmFiber10ParentCheck 11 = true := by decide
theorem tmFiber10Parent_12_ok : tmFiber10ParentCheck 12 = true := by decide
theorem tmFiber10Parent_13_ok : tmFiber10ParentCheck 13 = true := by decide
theorem tmFiber10Parent_14_ok : tmFiber10ParentCheck 14 = true := by decide
theorem tmFiber10Parent_15_ok : tmFiber10ParentCheck 15 = true := by decide
theorem tmFiber10Parent_16_ok : tmFiber10ParentCheck 16 = true := by decide
theorem tmFiber10Parent_17_ok : tmFiber10ParentCheck 17 = true := by decide
theorem tmFiber10Parent_18_ok : tmFiber10ParentCheck 18 = true := by decide
theorem tmFiber10Parent_19_ok : tmFiber10ParentCheck 19 = true := by decide
theorem tmFiber10Parent_20_ok : tmFiber10ParentCheck 20 = true := by decide
theorem tmFiber10Parent_21_ok : tmFiber10ParentCheck 21 = true := by decide
theorem tmFiber10Parent_22_ok : tmFiber10ParentCheck 22 = true := by decide
theorem tmFiber10Parent_23_ok : tmFiber10ParentCheck 23 = true := by decide
theorem tmFiber10Parent_24_ok : tmFiber10ParentCheck 24 = true := by decide
theorem tmFiber10Parent_25_ok : tmFiber10ParentCheck 25 = true := by decide
theorem tmFiber10Parent_26_ok : tmFiber10ParentCheck 26 = true := by decide
theorem tmFiber10Parent_27_ok : tmFiber10ParentCheck 27 = true := by decide
theorem tmFiber10Parent_28_ok : tmFiber10ParentCheck 28 = true := by decide
theorem tmFiber10Parent_29_ok : tmFiber10ParentCheck 29 = true := by decide
theorem tmFiber10Parent_30_ok : tmFiber10ParentCheck 30 = true := by decide
theorem tmFiber10Parent_31_ok : tmFiber10ParentCheck 31 = true := by decide
theorem tmFiber10Parent_32_ok : tmFiber10ParentCheck 32 = true := by decide
theorem tmFiber10Parent_33_ok : tmFiber10ParentCheck 33 = true := by decide
theorem tmFiber10Parent_34_ok : tmFiber10ParentCheck 34 = true := by decide
theorem tmFiber10Parent_35_ok : tmFiber10ParentCheck 35 = true := by decide
theorem tmFiber10Parent_36_ok : tmFiber10ParentCheck 36 = true := by decide
theorem tmFiber10Parent_37_ok : tmFiber10ParentCheck 37 = true := by decide
theorem tmFiber10Parent_38_ok : tmFiber10ParentCheck 38 = true := by decide
theorem tmFiber10Parent_39_ok : tmFiber10ParentCheck 39 = true := by decide
theorem tmFiber10Parent_40_ok : tmFiber10ParentCheck 40 = true := by decide
theorem tmFiber10Parent_41_ok : tmFiber10ParentCheck 41 = true := by decide
theorem tmFiber10Parent_42_ok : tmFiber10ParentCheck 42 = true := by decide
theorem tmFiber10Parent_43_ok : tmFiber10ParentCheck 43 = true := by decide
theorem tmFiber10Parent_44_ok : tmFiber10ParentCheck 44 = true := by decide
theorem tmFiber10Parent_45_ok : tmFiber10ParentCheck 45 = true := by decide
theorem tmFiber10Parent_46_ok : tmFiber10ParentCheck 46 = true := by decide
theorem tmFiber10Parent_47_ok : tmFiber10ParentCheck 47 = true := by decide
theorem tmFiber10Parent_48_ok : tmFiber10ParentCheck 48 = true := by decide
theorem tmFiber10Parent_49_ok : tmFiber10ParentCheck 49 = true := by decide
theorem tmFiber10Parent_50_ok : tmFiber10ParentCheck 50 = true := by decide
theorem tmFiber10Parent_51_ok : tmFiber10ParentCheck 51 = true := by decide
theorem tmFiber10Parent_52_ok : tmFiber10ParentCheck 52 = true := by decide
theorem tmFiber10Parent_53_ok : tmFiber10ParentCheck 53 = true := by decide
theorem tmFiber10Parent_54_ok : tmFiber10ParentCheck 54 = true := by decide
theorem tmFiber10Parent_55_ok : tmFiber10ParentCheck 55 = true := by decide
theorem tmFiber10Parent_56_ok : tmFiber10ParentCheck 56 = true := by decide
theorem tmFiber10Parent_57_ok : tmFiber10ParentCheck 57 = true := by decide
theorem tmFiber10Parent_58_ok : tmFiber10ParentCheck 58 = true := by decide
theorem tmFiber10Parent_59_ok : tmFiber10ParentCheck 59 = true := by decide
theorem tmFiber10Parent_60_ok : tmFiber10ParentCheck 60 = true := by decide
theorem tmFiber10Parent_61_ok : tmFiber10ParentCheck 61 = true := by decide
theorem tmFiber10Parent_62_ok : tmFiber10ParentCheck 62 = true := by decide
theorem tmFiber10Parent_63_ok : tmFiber10ParentCheck 63 = true := by decide

def tmFiber10CertificateAudit : Bool :=
  tmFiber10SourcesCheck &&
    tmFiber10RowCheck 0 &&
    tmFiber10RowCheck 1 &&
    tmFiber10RowCheck 2 &&
    tmFiber10RowCheck 3 &&
    tmFiber10RowCheck 4 &&
    tmFiber10RowCheck 5 &&
    tmFiber10RowCheck 6 &&
    tmFiber10RowCheck 7 &&
    tmFiber10RowCheck 8 &&
    tmFiber10RowCheck 9 &&
    tmFiber10RowCheck 10 &&
    tmFiber10RowCheck 11 &&
    tmFiber10RowCheck 12 &&
    tmFiber10RowCheck 13 &&
    tmFiber10RowCheck 14 &&
    tmFiber10RowCheck 15 &&
    tmFiber10RowCheck 16 &&
    tmFiber10RowCheck 17 &&
    tmFiber10RowCheck 18 &&
    tmFiber10RowCheck 19 &&
    tmFiber10RowCheck 20 &&
    tmFiber10RowCheck 21 &&
    tmFiber10RowCheck 22 &&
    tmFiber10RowCheck 23 &&
    tmFiber10RowCheck 24 &&
    tmFiber10RowCheck 25 &&
    tmFiber10RowCheck 26 &&
    tmFiber10RowCheck 27 &&
    tmFiber10RowCheck 28 &&
    tmFiber10RowCheck 29 &&
    tmFiber10RowCheck 30 &&
    tmFiber10RowCheck 31 &&
    tmFiber10RowCheck 32 &&
    tmFiber10RowCheck 33 &&
    tmFiber10RowCheck 34 &&
    tmFiber10RowCheck 35 &&
    tmFiber10RowCheck 36 &&
    tmFiber10RowCheck 37 &&
    tmFiber10RowCheck 38 &&
    tmFiber10RowCheck 39 &&
    tmFiber10RowCheck 40 &&
    tmFiber10RowCheck 41 &&
    tmFiber10RowCheck 42 &&
    tmFiber10RowCheck 43 &&
    tmFiber10RowCheck 44 &&
    tmFiber10RowCheck 45 &&
    tmFiber10RowCheck 46 &&
    tmFiber10RowCheck 47 &&
    tmFiber10RowCheck 48 &&
    tmFiber10RowCheck 49 &&
    tmFiber10RowCheck 50 &&
    tmFiber10RowCheck 51 &&
    tmFiber10RowCheck 52 &&
    tmFiber10RowCheck 53 &&
    tmFiber10RowCheck 54 &&
    tmFiber10RowCheck 55 &&
    tmFiber10RowCheck 56 &&
    tmFiber10RowCheck 57 &&
    tmFiber10RowCheck 58 &&
    tmFiber10RowCheck 59 &&
    tmFiber10RowCheck 60 &&
    tmFiber10RowCheck 61 &&
    tmFiber10RowCheck 62 &&
    tmFiber10RowCheck 63 &&
    tmFiber10ParentCheck 0 &&
    tmFiber10ParentCheck 1 &&
    tmFiber10ParentCheck 2 &&
    tmFiber10ParentCheck 3 &&
    tmFiber10ParentCheck 4 &&
    tmFiber10ParentCheck 5 &&
    tmFiber10ParentCheck 6 &&
    tmFiber10ParentCheck 7 &&
    tmFiber10ParentCheck 8 &&
    tmFiber10ParentCheck 9 &&
    tmFiber10ParentCheck 10 &&
    tmFiber10ParentCheck 11 &&
    tmFiber10ParentCheck 12 &&
    tmFiber10ParentCheck 13 &&
    tmFiber10ParentCheck 14 &&
    tmFiber10ParentCheck 15 &&
    tmFiber10ParentCheck 16 &&
    tmFiber10ParentCheck 17 &&
    tmFiber10ParentCheck 18 &&
    tmFiber10ParentCheck 19 &&
    tmFiber10ParentCheck 20 &&
    tmFiber10ParentCheck 21 &&
    tmFiber10ParentCheck 22 &&
    tmFiber10ParentCheck 23 &&
    tmFiber10ParentCheck 24 &&
    tmFiber10ParentCheck 25 &&
    tmFiber10ParentCheck 26 &&
    tmFiber10ParentCheck 27 &&
    tmFiber10ParentCheck 28 &&
    tmFiber10ParentCheck 29 &&
    tmFiber10ParentCheck 30 &&
    tmFiber10ParentCheck 31 &&
    tmFiber10ParentCheck 32 &&
    tmFiber10ParentCheck 33 &&
    tmFiber10ParentCheck 34 &&
    tmFiber10ParentCheck 35 &&
    tmFiber10ParentCheck 36 &&
    tmFiber10ParentCheck 37 &&
    tmFiber10ParentCheck 38 &&
    tmFiber10ParentCheck 39 &&
    tmFiber10ParentCheck 40 &&
    tmFiber10ParentCheck 41 &&
    tmFiber10ParentCheck 42 &&
    tmFiber10ParentCheck 43 &&
    tmFiber10ParentCheck 44 &&
    tmFiber10ParentCheck 45 &&
    tmFiber10ParentCheck 46 &&
    tmFiber10ParentCheck 47 &&
    tmFiber10ParentCheck 48 &&
    tmFiber10ParentCheck 49 &&
    tmFiber10ParentCheck 50 &&
    tmFiber10ParentCheck 51 &&
    tmFiber10ParentCheck 52 &&
    tmFiber10ParentCheck 53 &&
    tmFiber10ParentCheck 54 &&
    tmFiber10ParentCheck 55 &&
    tmFiber10ParentCheck 56 &&
    tmFiber10ParentCheck 57 &&
    tmFiber10ParentCheck 58 &&
    tmFiber10ParentCheck 59 &&
    tmFiber10ParentCheck 60 &&
    tmFiber10ParentCheck 61 &&
    tmFiber10ParentCheck 62 &&
    tmFiber10ParentCheck 63

theorem tmFiber10CertificateAudit_ok :
    tmFiber10CertificateAudit = true := by
  simp [tmFiber10CertificateAudit,
    tmFiber10SourcesCheck_ok,
    tmFiber10Row_0_ok,
    tmFiber10Row_1_ok,
    tmFiber10Row_2_ok,
    tmFiber10Row_3_ok,
    tmFiber10Row_4_ok,
    tmFiber10Row_5_ok,
    tmFiber10Row_6_ok,
    tmFiber10Row_7_ok,
    tmFiber10Row_8_ok,
    tmFiber10Row_9_ok,
    tmFiber10Row_10_ok,
    tmFiber10Row_11_ok,
    tmFiber10Row_12_ok,
    tmFiber10Row_13_ok,
    tmFiber10Row_14_ok,
    tmFiber10Row_15_ok,
    tmFiber10Row_16_ok,
    tmFiber10Row_17_ok,
    tmFiber10Row_18_ok,
    tmFiber10Row_19_ok,
    tmFiber10Row_20_ok,
    tmFiber10Row_21_ok,
    tmFiber10Row_22_ok,
    tmFiber10Row_23_ok,
    tmFiber10Row_24_ok,
    tmFiber10Row_25_ok,
    tmFiber10Row_26_ok,
    tmFiber10Row_27_ok,
    tmFiber10Row_28_ok,
    tmFiber10Row_29_ok,
    tmFiber10Row_30_ok,
    tmFiber10Row_31_ok,
    tmFiber10Row_32_ok,
    tmFiber10Row_33_ok,
    tmFiber10Row_34_ok,
    tmFiber10Row_35_ok,
    tmFiber10Row_36_ok,
    tmFiber10Row_37_ok,
    tmFiber10Row_38_ok,
    tmFiber10Row_39_ok,
    tmFiber10Row_40_ok,
    tmFiber10Row_41_ok,
    tmFiber10Row_42_ok,
    tmFiber10Row_43_ok,
    tmFiber10Row_44_ok,
    tmFiber10Row_45_ok,
    tmFiber10Row_46_ok,
    tmFiber10Row_47_ok,
    tmFiber10Row_48_ok,
    tmFiber10Row_49_ok,
    tmFiber10Row_50_ok,
    tmFiber10Row_51_ok,
    tmFiber10Row_52_ok,
    tmFiber10Row_53_ok,
    tmFiber10Row_54_ok,
    tmFiber10Row_55_ok,
    tmFiber10Row_56_ok,
    tmFiber10Row_57_ok,
    tmFiber10Row_58_ok,
    tmFiber10Row_59_ok,
    tmFiber10Row_60_ok,
    tmFiber10Row_61_ok,
    tmFiber10Row_62_ok,
    tmFiber10Row_63_ok,
    tmFiber10Parent_0_ok,
    tmFiber10Parent_1_ok,
    tmFiber10Parent_2_ok,
    tmFiber10Parent_3_ok,
    tmFiber10Parent_4_ok,
    tmFiber10Parent_5_ok,
    tmFiber10Parent_6_ok,
    tmFiber10Parent_7_ok,
    tmFiber10Parent_8_ok,
    tmFiber10Parent_9_ok,
    tmFiber10Parent_10_ok,
    tmFiber10Parent_11_ok,
    tmFiber10Parent_12_ok,
    tmFiber10Parent_13_ok,
    tmFiber10Parent_14_ok,
    tmFiber10Parent_15_ok,
    tmFiber10Parent_16_ok,
    tmFiber10Parent_17_ok,
    tmFiber10Parent_18_ok,
    tmFiber10Parent_19_ok,
    tmFiber10Parent_20_ok,
    tmFiber10Parent_21_ok,
    tmFiber10Parent_22_ok,
    tmFiber10Parent_23_ok,
    tmFiber10Parent_24_ok,
    tmFiber10Parent_25_ok,
    tmFiber10Parent_26_ok,
    tmFiber10Parent_27_ok,
    tmFiber10Parent_28_ok,
    tmFiber10Parent_29_ok,
    tmFiber10Parent_30_ok,
    tmFiber10Parent_31_ok,
    tmFiber10Parent_32_ok,
    tmFiber10Parent_33_ok,
    tmFiber10Parent_34_ok,
    tmFiber10Parent_35_ok,
    tmFiber10Parent_36_ok,
    tmFiber10Parent_37_ok,
    tmFiber10Parent_38_ok,
    tmFiber10Parent_39_ok,
    tmFiber10Parent_40_ok,
    tmFiber10Parent_41_ok,
    tmFiber10Parent_42_ok,
    tmFiber10Parent_43_ok,
    tmFiber10Parent_44_ok,
    tmFiber10Parent_45_ok,
    tmFiber10Parent_46_ok,
    tmFiber10Parent_47_ok,
    tmFiber10Parent_48_ok,
    tmFiber10Parent_49_ok,
    tmFiber10Parent_50_ok,
    tmFiber10Parent_51_ok,
    tmFiber10Parent_52_ok,
    tmFiber10Parent_53_ok,
    tmFiber10Parent_54_ok,
    tmFiber10Parent_55_ok,
    tmFiber10Parent_56_ok,
    tmFiber10Parent_57_ok,
    tmFiber10Parent_58_ok,
    tmFiber10Parent_59_ok,
    tmFiber10Parent_60_ok,
    tmFiber10Parent_61_ok,
    tmFiber10Parent_62_ok,
    tmFiber10Parent_63_ok]

def tmFiber11Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.p]

def tmFiber11Expected : List Nat :=
  [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]

def tmFiber11Rows : List DirectChainParentRow :=
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

def tmFiber11RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber11Rows i default

def tmFiber11SourcesCheck : Bool :=
  (tmFiber11Rows.map fun row => row.source) == tmFiber11Expected

theorem tmFiber11SourcesCheck_ok :
    tmFiber11SourcesCheck = true := by
  decide

def tmFiber11RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt i)

theorem tmFiber11Row_0_ok : tmFiber11RowCheck 0 = true := by decide
theorem tmFiber11Row_1_ok : tmFiber11RowCheck 1 = true := by decide
theorem tmFiber11Row_2_ok : tmFiber11RowCheck 2 = true := by decide
theorem tmFiber11Row_3_ok : tmFiber11RowCheck 3 = true := by decide
theorem tmFiber11Row_4_ok : tmFiber11RowCheck 4 = true := by decide
theorem tmFiber11Row_5_ok : tmFiber11RowCheck 5 = true := by decide
theorem tmFiber11Row_6_ok : tmFiber11RowCheck 6 = true := by decide
theorem tmFiber11Row_7_ok : tmFiber11RowCheck 7 = true := by decide
theorem tmFiber11Row_8_ok : tmFiber11RowCheck 8 = true := by decide
theorem tmFiber11Row_9_ok : tmFiber11RowCheck 9 = true := by decide
theorem tmFiber11Row_10_ok : tmFiber11RowCheck 10 = true := by decide
theorem tmFiber11Row_11_ok : tmFiber11RowCheck 11 = true := by decide
theorem tmFiber11Row_12_ok : tmFiber11RowCheck 12 = true := by decide
theorem tmFiber11Row_13_ok : tmFiber11RowCheck 13 = true := by decide
theorem tmFiber11Row_14_ok : tmFiber11RowCheck 14 = true := by decide
theorem tmFiber11Row_15_ok : tmFiber11RowCheck 15 = true := by decide

def tmFiber11ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber11Rows tmMaxParentDepth (listGetD tmFiber11Expected i 0) == 464

theorem tmFiber11Parent_0_ok : tmFiber11ParentCheck 0 = true := by decide
theorem tmFiber11Parent_1_ok : tmFiber11ParentCheck 1 = true := by decide
theorem tmFiber11Parent_2_ok : tmFiber11ParentCheck 2 = true := by decide
theorem tmFiber11Parent_3_ok : tmFiber11ParentCheck 3 = true := by decide
theorem tmFiber11Parent_4_ok : tmFiber11ParentCheck 4 = true := by decide
theorem tmFiber11Parent_5_ok : tmFiber11ParentCheck 5 = true := by decide
theorem tmFiber11Parent_6_ok : tmFiber11ParentCheck 6 = true := by decide
theorem tmFiber11Parent_7_ok : tmFiber11ParentCheck 7 = true := by decide
theorem tmFiber11Parent_8_ok : tmFiber11ParentCheck 8 = true := by decide
theorem tmFiber11Parent_9_ok : tmFiber11ParentCheck 9 = true := by decide
theorem tmFiber11Parent_10_ok : tmFiber11ParentCheck 10 = true := by decide
theorem tmFiber11Parent_11_ok : tmFiber11ParentCheck 11 = true := by decide
theorem tmFiber11Parent_12_ok : tmFiber11ParentCheck 12 = true := by decide
theorem tmFiber11Parent_13_ok : tmFiber11ParentCheck 13 = true := by decide
theorem tmFiber11Parent_14_ok : tmFiber11ParentCheck 14 = true := by decide
theorem tmFiber11Parent_15_ok : tmFiber11ParentCheck 15 = true := by decide

def tmFiber11CertificateAudit : Bool :=
  tmFiber11SourcesCheck &&
    tmFiber11RowCheck 0 &&
    tmFiber11RowCheck 1 &&
    tmFiber11RowCheck 2 &&
    tmFiber11RowCheck 3 &&
    tmFiber11RowCheck 4 &&
    tmFiber11RowCheck 5 &&
    tmFiber11RowCheck 6 &&
    tmFiber11RowCheck 7 &&
    tmFiber11RowCheck 8 &&
    tmFiber11RowCheck 9 &&
    tmFiber11RowCheck 10 &&
    tmFiber11RowCheck 11 &&
    tmFiber11RowCheck 12 &&
    tmFiber11RowCheck 13 &&
    tmFiber11RowCheck 14 &&
    tmFiber11RowCheck 15 &&
    tmFiber11ParentCheck 0 &&
    tmFiber11ParentCheck 1 &&
    tmFiber11ParentCheck 2 &&
    tmFiber11ParentCheck 3 &&
    tmFiber11ParentCheck 4 &&
    tmFiber11ParentCheck 5 &&
    tmFiber11ParentCheck 6 &&
    tmFiber11ParentCheck 7 &&
    tmFiber11ParentCheck 8 &&
    tmFiber11ParentCheck 9 &&
    tmFiber11ParentCheck 10 &&
    tmFiber11ParentCheck 11 &&
    tmFiber11ParentCheck 12 &&
    tmFiber11ParentCheck 13 &&
    tmFiber11ParentCheck 14 &&
    tmFiber11ParentCheck 15

theorem tmFiber11CertificateAudit_ok :
    tmFiber11CertificateAudit = true := by
  simp [tmFiber11CertificateAudit,
    tmFiber11SourcesCheck_ok,
    tmFiber11Row_0_ok,
    tmFiber11Row_1_ok,
    tmFiber11Row_2_ok,
    tmFiber11Row_3_ok,
    tmFiber11Row_4_ok,
    tmFiber11Row_5_ok,
    tmFiber11Row_6_ok,
    tmFiber11Row_7_ok,
    tmFiber11Row_8_ok,
    tmFiber11Row_9_ok,
    tmFiber11Row_10_ok,
    tmFiber11Row_11_ok,
    tmFiber11Row_12_ok,
    tmFiber11Row_13_ok,
    tmFiber11Row_14_ok,
    tmFiber11Row_15_ok,
    tmFiber11Parent_0_ok,
    tmFiber11Parent_1_ok,
    tmFiber11Parent_2_ok,
    tmFiber11Parent_3_ok,
    tmFiber11Parent_4_ok,
    tmFiber11Parent_5_ok,
    tmFiber11Parent_6_ok,
    tmFiber11Parent_7_ok,
    tmFiber11Parent_8_ok,
    tmFiber11Parent_9_ok,
    tmFiber11Parent_10_ok,
    tmFiber11Parent_11_ok,
    tmFiber11Parent_12_ok,
    tmFiber11Parent_13_ok,
    tmFiber11Parent_14_ok,
    tmFiber11Parent_15_ok]

def tmFiber12Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.r]

def tmFiber12Expected : List Nat :=
  []

def tmFiber12Rows : List DirectChainParentRow :=
  []

def tmFiber12RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber12Rows i default

def tmFiber12SourcesCheck : Bool :=
  (tmFiber12Rows.map fun row => row.source) == tmFiber12Expected

theorem tmFiber12SourcesCheck_ok :
    tmFiber12SourcesCheck = true := by
  decide

def tmFiber12RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber12Key tmFiber12Expected (tmFiber12RowAt i)

def tmFiber12ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber12Rows tmMaxParentDepth (listGetD tmFiber12Expected i 0) == 0

def tmFiber12CertificateAudit : Bool :=
  tmFiber12SourcesCheck

theorem tmFiber12CertificateAudit_ok :
    tmFiber12CertificateAudit = true := by
  simp [tmFiber12CertificateAudit,
    tmFiber12SourcesCheck_ok]

def tmFiber13Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.b]

def tmFiber13Expected : List Nat :=
  []

def tmFiber13Rows : List DirectChainParentRow :=
  []

def tmFiber13RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber13Rows i default

def tmFiber13SourcesCheck : Bool :=
  (tmFiber13Rows.map fun row => row.source) == tmFiber13Expected

theorem tmFiber13SourcesCheck_ok :
    tmFiber13SourcesCheck = true := by
  decide

def tmFiber13RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber13Key tmFiber13Expected (tmFiber13RowAt i)

def tmFiber13ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber13Rows tmMaxParentDepth (listGetD tmFiber13Expected i 0) == 0

def tmFiber13CertificateAudit : Bool :=
  tmFiber13SourcesCheck

theorem tmFiber13CertificateAudit_ok :
    tmFiber13CertificateAudit = true := by
  simp [tmFiber13CertificateAudit,
    tmFiber13SourcesCheck_ok]

def tmFiber14Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.p]

def tmFiber14Expected : List Nat :=
  []

def tmFiber14Rows : List DirectChainParentRow :=
  []

def tmFiber14RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber14Rows i default

def tmFiber14SourcesCheck : Bool :=
  (tmFiber14Rows.map fun row => row.source) == tmFiber14Expected

theorem tmFiber14SourcesCheck_ok :
    tmFiber14SourcesCheck = true := by
  decide

def tmFiber14RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber14Key tmFiber14Expected (tmFiber14RowAt i)

def tmFiber14ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber14Rows tmMaxParentDepth (listGetD tmFiber14Expected i 0) == 0

def tmFiber14CertificateAudit : Bool :=
  tmFiber14SourcesCheck

theorem tmFiber14CertificateAudit_ok :
    tmFiber14CertificateAudit = true := by
  simp [tmFiber14CertificateAudit,
    tmFiber14SourcesCheck_ok]

def tmFiber15Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.r]

def tmFiber15Expected : List Nat :=
  []

def tmFiber15Rows : List DirectChainParentRow :=
  []

def tmFiber15RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber15Rows i default

def tmFiber15SourcesCheck : Bool :=
  (tmFiber15Rows.map fun row => row.source) == tmFiber15Expected

theorem tmFiber15SourcesCheck_ok :
    tmFiber15SourcesCheck = true := by
  decide

def tmFiber15RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber15Key tmFiber15Expected (tmFiber15RowAt i)

def tmFiber15ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber15Rows tmMaxParentDepth (listGetD tmFiber15Expected i 0) == 0

def tmFiber15CertificateAudit : Bool :=
  tmFiber15SourcesCheck

theorem tmFiber15CertificateAudit_ok :
    tmFiber15CertificateAudit = true := by
  simp [tmFiber15CertificateAudit,
    tmFiber15SourcesCheck_ok]

def tmFiber16Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.b]

def tmFiber16Expected : List Nat :=
  []

def tmFiber16Rows : List DirectChainParentRow :=
  []

def tmFiber16RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber16Rows i default

def tmFiber16SourcesCheck : Bool :=
  (tmFiber16Rows.map fun row => row.source) == tmFiber16Expected

theorem tmFiber16SourcesCheck_ok :
    tmFiber16SourcesCheck = true := by
  decide

def tmFiber16RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber16Key tmFiber16Expected (tmFiber16RowAt i)

def tmFiber16ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber16Rows tmMaxParentDepth (listGetD tmFiber16Expected i 0) == 0

def tmFiber16CertificateAudit : Bool :=
  tmFiber16SourcesCheck

theorem tmFiber16CertificateAudit_ok :
    tmFiber16CertificateAudit = true := by
  simp [tmFiber16CertificateAudit,
    tmFiber16SourcesCheck_ok]

def tmFiber17Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.p]

def tmFiber17Expected : List Nat :=
  []

def tmFiber17Rows : List DirectChainParentRow :=
  []

def tmFiber17RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber17Rows i default

def tmFiber17SourcesCheck : Bool :=
  (tmFiber17Rows.map fun row => row.source) == tmFiber17Expected

theorem tmFiber17SourcesCheck_ok :
    tmFiber17SourcesCheck = true := by
  decide

def tmFiber17RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber17Key tmFiber17Expected (tmFiber17RowAt i)

def tmFiber17ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber17Rows tmMaxParentDepth (listGetD tmFiber17Expected i 0) == 0

def tmFiber17CertificateAudit : Bool :=
  tmFiber17SourcesCheck

theorem tmFiber17CertificateAudit_ok :
    tmFiber17CertificateAudit = true := by
  simp [tmFiber17CertificateAudit,
    tmFiber17SourcesCheck_ok]

def tmFiber18Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.r]

def tmFiber18Expected : List Nat :=
  [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]

def tmFiber18Rows : List DirectChainParentRow :=
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

def tmFiber18RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber18Rows i default

def tmFiber18SourcesCheck : Bool :=
  (tmFiber18Rows.map fun row => row.source) == tmFiber18Expected

theorem tmFiber18SourcesCheck_ok :
    tmFiber18SourcesCheck = true := by
  decide

def tmFiber18RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt i)

theorem tmFiber18Row_0_ok : tmFiber18RowCheck 0 = true := by decide
theorem tmFiber18Row_1_ok : tmFiber18RowCheck 1 = true := by decide
theorem tmFiber18Row_2_ok : tmFiber18RowCheck 2 = true := by decide
theorem tmFiber18Row_3_ok : tmFiber18RowCheck 3 = true := by decide
theorem tmFiber18Row_4_ok : tmFiber18RowCheck 4 = true := by decide
theorem tmFiber18Row_5_ok : tmFiber18RowCheck 5 = true := by decide
theorem tmFiber18Row_6_ok : tmFiber18RowCheck 6 = true := by decide
theorem tmFiber18Row_7_ok : tmFiber18RowCheck 7 = true := by decide
theorem tmFiber18Row_8_ok : tmFiber18RowCheck 8 = true := by decide
theorem tmFiber18Row_9_ok : tmFiber18RowCheck 9 = true := by decide
theorem tmFiber18Row_10_ok : tmFiber18RowCheck 10 = true := by decide
theorem tmFiber18Row_11_ok : tmFiber18RowCheck 11 = true := by decide
theorem tmFiber18Row_12_ok : tmFiber18RowCheck 12 = true := by decide
theorem tmFiber18Row_13_ok : tmFiber18RowCheck 13 = true := by decide
theorem tmFiber18Row_14_ok : tmFiber18RowCheck 14 = true := by decide
theorem tmFiber18Row_15_ok : tmFiber18RowCheck 15 = true := by decide

def tmFiber18ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber18Rows tmMaxParentDepth (listGetD tmFiber18Expected i 0) == 1104

theorem tmFiber18Parent_0_ok : tmFiber18ParentCheck 0 = true := by decide
theorem tmFiber18Parent_1_ok : tmFiber18ParentCheck 1 = true := by decide
theorem tmFiber18Parent_2_ok : tmFiber18ParentCheck 2 = true := by decide
theorem tmFiber18Parent_3_ok : tmFiber18ParentCheck 3 = true := by decide
theorem tmFiber18Parent_4_ok : tmFiber18ParentCheck 4 = true := by decide
theorem tmFiber18Parent_5_ok : tmFiber18ParentCheck 5 = true := by decide
theorem tmFiber18Parent_6_ok : tmFiber18ParentCheck 6 = true := by decide
theorem tmFiber18Parent_7_ok : tmFiber18ParentCheck 7 = true := by decide
theorem tmFiber18Parent_8_ok : tmFiber18ParentCheck 8 = true := by decide
theorem tmFiber18Parent_9_ok : tmFiber18ParentCheck 9 = true := by decide
theorem tmFiber18Parent_10_ok : tmFiber18ParentCheck 10 = true := by decide
theorem tmFiber18Parent_11_ok : tmFiber18ParentCheck 11 = true := by decide
theorem tmFiber18Parent_12_ok : tmFiber18ParentCheck 12 = true := by decide
theorem tmFiber18Parent_13_ok : tmFiber18ParentCheck 13 = true := by decide
theorem tmFiber18Parent_14_ok : tmFiber18ParentCheck 14 = true := by decide
theorem tmFiber18Parent_15_ok : tmFiber18ParentCheck 15 = true := by decide

def tmFiber18CertificateAudit : Bool :=
  tmFiber18SourcesCheck &&
    tmFiber18RowCheck 0 &&
    tmFiber18RowCheck 1 &&
    tmFiber18RowCheck 2 &&
    tmFiber18RowCheck 3 &&
    tmFiber18RowCheck 4 &&
    tmFiber18RowCheck 5 &&
    tmFiber18RowCheck 6 &&
    tmFiber18RowCheck 7 &&
    tmFiber18RowCheck 8 &&
    tmFiber18RowCheck 9 &&
    tmFiber18RowCheck 10 &&
    tmFiber18RowCheck 11 &&
    tmFiber18RowCheck 12 &&
    tmFiber18RowCheck 13 &&
    tmFiber18RowCheck 14 &&
    tmFiber18RowCheck 15 &&
    tmFiber18ParentCheck 0 &&
    tmFiber18ParentCheck 1 &&
    tmFiber18ParentCheck 2 &&
    tmFiber18ParentCheck 3 &&
    tmFiber18ParentCheck 4 &&
    tmFiber18ParentCheck 5 &&
    tmFiber18ParentCheck 6 &&
    tmFiber18ParentCheck 7 &&
    tmFiber18ParentCheck 8 &&
    tmFiber18ParentCheck 9 &&
    tmFiber18ParentCheck 10 &&
    tmFiber18ParentCheck 11 &&
    tmFiber18ParentCheck 12 &&
    tmFiber18ParentCheck 13 &&
    tmFiber18ParentCheck 14 &&
    tmFiber18ParentCheck 15

theorem tmFiber18CertificateAudit_ok :
    tmFiber18CertificateAudit = true := by
  simp [tmFiber18CertificateAudit,
    tmFiber18SourcesCheck_ok,
    tmFiber18Row_0_ok,
    tmFiber18Row_1_ok,
    tmFiber18Row_2_ok,
    tmFiber18Row_3_ok,
    tmFiber18Row_4_ok,
    tmFiber18Row_5_ok,
    tmFiber18Row_6_ok,
    tmFiber18Row_7_ok,
    tmFiber18Row_8_ok,
    tmFiber18Row_9_ok,
    tmFiber18Row_10_ok,
    tmFiber18Row_11_ok,
    tmFiber18Row_12_ok,
    tmFiber18Row_13_ok,
    tmFiber18Row_14_ok,
    tmFiber18Row_15_ok,
    tmFiber18Parent_0_ok,
    tmFiber18Parent_1_ok,
    tmFiber18Parent_2_ok,
    tmFiber18Parent_3_ok,
    tmFiber18Parent_4_ok,
    tmFiber18Parent_5_ok,
    tmFiber18Parent_6_ok,
    tmFiber18Parent_7_ok,
    tmFiber18Parent_8_ok,
    tmFiber18Parent_9_ok,
    tmFiber18Parent_10_ok,
    tmFiber18Parent_11_ok,
    tmFiber18Parent_12_ok,
    tmFiber18Parent_13_ok,
    tmFiber18Parent_14_ok,
    tmFiber18Parent_15_ok]

def tmFiber19Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.b]

def tmFiber19Expected : List Nat :=
  [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]

def tmFiber19Rows : List DirectChainParentRow :=
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

def tmFiber19RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber19Rows i default

def tmFiber19SourcesCheck : Bool :=
  (tmFiber19Rows.map fun row => row.source) == tmFiber19Expected

theorem tmFiber19SourcesCheck_ok :
    tmFiber19SourcesCheck = true := by
  decide

def tmFiber19RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt i)

theorem tmFiber19Row_0_ok : tmFiber19RowCheck 0 = true := by decide
theorem tmFiber19Row_1_ok : tmFiber19RowCheck 1 = true := by decide
theorem tmFiber19Row_2_ok : tmFiber19RowCheck 2 = true := by decide
theorem tmFiber19Row_3_ok : tmFiber19RowCheck 3 = true := by decide
theorem tmFiber19Row_4_ok : tmFiber19RowCheck 4 = true := by decide
theorem tmFiber19Row_5_ok : tmFiber19RowCheck 5 = true := by decide
theorem tmFiber19Row_6_ok : tmFiber19RowCheck 6 = true := by decide
theorem tmFiber19Row_7_ok : tmFiber19RowCheck 7 = true := by decide
theorem tmFiber19Row_8_ok : tmFiber19RowCheck 8 = true := by decide
theorem tmFiber19Row_9_ok : tmFiber19RowCheck 9 = true := by decide
theorem tmFiber19Row_10_ok : tmFiber19RowCheck 10 = true := by decide
theorem tmFiber19Row_11_ok : tmFiber19RowCheck 11 = true := by decide
theorem tmFiber19Row_12_ok : tmFiber19RowCheck 12 = true := by decide
theorem tmFiber19Row_13_ok : tmFiber19RowCheck 13 = true := by decide
theorem tmFiber19Row_14_ok : tmFiber19RowCheck 14 = true := by decide
theorem tmFiber19Row_15_ok : tmFiber19RowCheck 15 = true := by decide

def tmFiber19ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber19Rows tmMaxParentDepth (listGetD tmFiber19Expected i 0) == 816

theorem tmFiber19Parent_0_ok : tmFiber19ParentCheck 0 = true := by decide
theorem tmFiber19Parent_1_ok : tmFiber19ParentCheck 1 = true := by decide
theorem tmFiber19Parent_2_ok : tmFiber19ParentCheck 2 = true := by decide
theorem tmFiber19Parent_3_ok : tmFiber19ParentCheck 3 = true := by decide
theorem tmFiber19Parent_4_ok : tmFiber19ParentCheck 4 = true := by decide
theorem tmFiber19Parent_5_ok : tmFiber19ParentCheck 5 = true := by decide
theorem tmFiber19Parent_6_ok : tmFiber19ParentCheck 6 = true := by decide
theorem tmFiber19Parent_7_ok : tmFiber19ParentCheck 7 = true := by decide
theorem tmFiber19Parent_8_ok : tmFiber19ParentCheck 8 = true := by decide
theorem tmFiber19Parent_9_ok : tmFiber19ParentCheck 9 = true := by decide
theorem tmFiber19Parent_10_ok : tmFiber19ParentCheck 10 = true := by decide
theorem tmFiber19Parent_11_ok : tmFiber19ParentCheck 11 = true := by decide
theorem tmFiber19Parent_12_ok : tmFiber19ParentCheck 12 = true := by decide
theorem tmFiber19Parent_13_ok : tmFiber19ParentCheck 13 = true := by decide
theorem tmFiber19Parent_14_ok : tmFiber19ParentCheck 14 = true := by decide
theorem tmFiber19Parent_15_ok : tmFiber19ParentCheck 15 = true := by decide

def tmFiber19CertificateAudit : Bool :=
  tmFiber19SourcesCheck &&
    tmFiber19RowCheck 0 &&
    tmFiber19RowCheck 1 &&
    tmFiber19RowCheck 2 &&
    tmFiber19RowCheck 3 &&
    tmFiber19RowCheck 4 &&
    tmFiber19RowCheck 5 &&
    tmFiber19RowCheck 6 &&
    tmFiber19RowCheck 7 &&
    tmFiber19RowCheck 8 &&
    tmFiber19RowCheck 9 &&
    tmFiber19RowCheck 10 &&
    tmFiber19RowCheck 11 &&
    tmFiber19RowCheck 12 &&
    tmFiber19RowCheck 13 &&
    tmFiber19RowCheck 14 &&
    tmFiber19RowCheck 15 &&
    tmFiber19ParentCheck 0 &&
    tmFiber19ParentCheck 1 &&
    tmFiber19ParentCheck 2 &&
    tmFiber19ParentCheck 3 &&
    tmFiber19ParentCheck 4 &&
    tmFiber19ParentCheck 5 &&
    tmFiber19ParentCheck 6 &&
    tmFiber19ParentCheck 7 &&
    tmFiber19ParentCheck 8 &&
    tmFiber19ParentCheck 9 &&
    tmFiber19ParentCheck 10 &&
    tmFiber19ParentCheck 11 &&
    tmFiber19ParentCheck 12 &&
    tmFiber19ParentCheck 13 &&
    tmFiber19ParentCheck 14 &&
    tmFiber19ParentCheck 15

theorem tmFiber19CertificateAudit_ok :
    tmFiber19CertificateAudit = true := by
  simp [tmFiber19CertificateAudit,
    tmFiber19SourcesCheck_ok,
    tmFiber19Row_0_ok,
    tmFiber19Row_1_ok,
    tmFiber19Row_2_ok,
    tmFiber19Row_3_ok,
    tmFiber19Row_4_ok,
    tmFiber19Row_5_ok,
    tmFiber19Row_6_ok,
    tmFiber19Row_7_ok,
    tmFiber19Row_8_ok,
    tmFiber19Row_9_ok,
    tmFiber19Row_10_ok,
    tmFiber19Row_11_ok,
    tmFiber19Row_12_ok,
    tmFiber19Row_13_ok,
    tmFiber19Row_14_ok,
    tmFiber19Row_15_ok,
    tmFiber19Parent_0_ok,
    tmFiber19Parent_1_ok,
    tmFiber19Parent_2_ok,
    tmFiber19Parent_3_ok,
    tmFiber19Parent_4_ok,
    tmFiber19Parent_5_ok,
    tmFiber19Parent_6_ok,
    tmFiber19Parent_7_ok,
    tmFiber19Parent_8_ok,
    tmFiber19Parent_9_ok,
    tmFiber19Parent_10_ok,
    tmFiber19Parent_11_ok,
    tmFiber19Parent_12_ok,
    tmFiber19Parent_13_ok,
    tmFiber19Parent_14_ok,
    tmFiber19Parent_15_ok]

def tmFiber20Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.p]

def tmFiber20Expected : List Nat :=
  [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]

def tmFiber20Rows : List DirectChainParentRow :=
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

def tmFiber20RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber20Rows i default

def tmFiber20SourcesCheck : Bool :=
  (tmFiber20Rows.map fun row => row.source) == tmFiber20Expected

theorem tmFiber20SourcesCheck_ok :
    tmFiber20SourcesCheck = true := by
  decide

def tmFiber20RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber20Key tmFiber20Expected (tmFiber20RowAt i)

theorem tmFiber20Row_0_ok : tmFiber20RowCheck 0 = true := by decide
theorem tmFiber20Row_1_ok : tmFiber20RowCheck 1 = true := by decide
theorem tmFiber20Row_2_ok : tmFiber20RowCheck 2 = true := by decide
theorem tmFiber20Row_3_ok : tmFiber20RowCheck 3 = true := by decide
theorem tmFiber20Row_4_ok : tmFiber20RowCheck 4 = true := by decide
theorem tmFiber20Row_5_ok : tmFiber20RowCheck 5 = true := by decide
theorem tmFiber20Row_6_ok : tmFiber20RowCheck 6 = true := by decide
theorem tmFiber20Row_7_ok : tmFiber20RowCheck 7 = true := by decide
theorem tmFiber20Row_8_ok : tmFiber20RowCheck 8 = true := by decide
theorem tmFiber20Row_9_ok : tmFiber20RowCheck 9 = true := by decide
theorem tmFiber20Row_10_ok : tmFiber20RowCheck 10 = true := by decide
theorem tmFiber20Row_11_ok : tmFiber20RowCheck 11 = true := by decide
theorem tmFiber20Row_12_ok : tmFiber20RowCheck 12 = true := by decide
theorem tmFiber20Row_13_ok : tmFiber20RowCheck 13 = true := by decide
theorem tmFiber20Row_14_ok : tmFiber20RowCheck 14 = true := by decide
theorem tmFiber20Row_15_ok : tmFiber20RowCheck 15 = true := by decide
theorem tmFiber20Row_16_ok : tmFiber20RowCheck 16 = true := by decide
theorem tmFiber20Row_17_ok : tmFiber20RowCheck 17 = true := by decide
theorem tmFiber20Row_18_ok : tmFiber20RowCheck 18 = true := by decide
theorem tmFiber20Row_19_ok : tmFiber20RowCheck 19 = true := by decide
theorem tmFiber20Row_20_ok : tmFiber20RowCheck 20 = true := by decide
theorem tmFiber20Row_21_ok : tmFiber20RowCheck 21 = true := by decide
theorem tmFiber20Row_22_ok : tmFiber20RowCheck 22 = true := by decide
theorem tmFiber20Row_23_ok : tmFiber20RowCheck 23 = true := by decide
theorem tmFiber20Row_24_ok : tmFiber20RowCheck 24 = true := by decide
theorem tmFiber20Row_25_ok : tmFiber20RowCheck 25 = true := by decide
theorem tmFiber20Row_26_ok : tmFiber20RowCheck 26 = true := by decide
theorem tmFiber20Row_27_ok : tmFiber20RowCheck 27 = true := by decide
theorem tmFiber20Row_28_ok : tmFiber20RowCheck 28 = true := by decide
theorem tmFiber20Row_29_ok : tmFiber20RowCheck 29 = true := by decide
theorem tmFiber20Row_30_ok : tmFiber20RowCheck 30 = true := by decide
theorem tmFiber20Row_31_ok : tmFiber20RowCheck 31 = true := by decide
theorem tmFiber20Row_32_ok : tmFiber20RowCheck 32 = true := by decide
theorem tmFiber20Row_33_ok : tmFiber20RowCheck 33 = true := by decide
theorem tmFiber20Row_34_ok : tmFiber20RowCheck 34 = true := by decide
theorem tmFiber20Row_35_ok : tmFiber20RowCheck 35 = true := by decide
theorem tmFiber20Row_36_ok : tmFiber20RowCheck 36 = true := by decide
theorem tmFiber20Row_37_ok : tmFiber20RowCheck 37 = true := by decide
theorem tmFiber20Row_38_ok : tmFiber20RowCheck 38 = true := by decide
theorem tmFiber20Row_39_ok : tmFiber20RowCheck 39 = true := by decide
theorem tmFiber20Row_40_ok : tmFiber20RowCheck 40 = true := by decide
theorem tmFiber20Row_41_ok : tmFiber20RowCheck 41 = true := by decide
theorem tmFiber20Row_42_ok : tmFiber20RowCheck 42 = true := by decide
theorem tmFiber20Row_43_ok : tmFiber20RowCheck 43 = true := by decide
theorem tmFiber20Row_44_ok : tmFiber20RowCheck 44 = true := by decide
theorem tmFiber20Row_45_ok : tmFiber20RowCheck 45 = true := by decide
theorem tmFiber20Row_46_ok : tmFiber20RowCheck 46 = true := by decide
theorem tmFiber20Row_47_ok : tmFiber20RowCheck 47 = true := by decide
theorem tmFiber20Row_48_ok : tmFiber20RowCheck 48 = true := by decide
theorem tmFiber20Row_49_ok : tmFiber20RowCheck 49 = true := by decide
theorem tmFiber20Row_50_ok : tmFiber20RowCheck 50 = true := by decide
theorem tmFiber20Row_51_ok : tmFiber20RowCheck 51 = true := by decide
theorem tmFiber20Row_52_ok : tmFiber20RowCheck 52 = true := by decide
theorem tmFiber20Row_53_ok : tmFiber20RowCheck 53 = true := by decide
theorem tmFiber20Row_54_ok : tmFiber20RowCheck 54 = true := by decide
theorem tmFiber20Row_55_ok : tmFiber20RowCheck 55 = true := by decide
theorem tmFiber20Row_56_ok : tmFiber20RowCheck 56 = true := by decide
theorem tmFiber20Row_57_ok : tmFiber20RowCheck 57 = true := by decide
theorem tmFiber20Row_58_ok : tmFiber20RowCheck 58 = true := by decide
theorem tmFiber20Row_59_ok : tmFiber20RowCheck 59 = true := by decide
theorem tmFiber20Row_60_ok : tmFiber20RowCheck 60 = true := by decide
theorem tmFiber20Row_61_ok : tmFiber20RowCheck 61 = true := by decide
theorem tmFiber20Row_62_ok : tmFiber20RowCheck 62 = true := by decide
theorem tmFiber20Row_63_ok : tmFiber20RowCheck 63 = true := by decide

def tmFiber20ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber20Rows tmMaxParentDepth (listGetD tmFiber20Expected i 0) == 832

theorem tmFiber20Parent_0_ok : tmFiber20ParentCheck 0 = true := by decide
theorem tmFiber20Parent_1_ok : tmFiber20ParentCheck 1 = true := by decide
theorem tmFiber20Parent_2_ok : tmFiber20ParentCheck 2 = true := by decide
theorem tmFiber20Parent_3_ok : tmFiber20ParentCheck 3 = true := by decide
theorem tmFiber20Parent_4_ok : tmFiber20ParentCheck 4 = true := by decide
theorem tmFiber20Parent_5_ok : tmFiber20ParentCheck 5 = true := by decide
theorem tmFiber20Parent_6_ok : tmFiber20ParentCheck 6 = true := by decide
theorem tmFiber20Parent_7_ok : tmFiber20ParentCheck 7 = true := by decide
theorem tmFiber20Parent_8_ok : tmFiber20ParentCheck 8 = true := by decide
theorem tmFiber20Parent_9_ok : tmFiber20ParentCheck 9 = true := by decide
theorem tmFiber20Parent_10_ok : tmFiber20ParentCheck 10 = true := by decide
theorem tmFiber20Parent_11_ok : tmFiber20ParentCheck 11 = true := by decide
theorem tmFiber20Parent_12_ok : tmFiber20ParentCheck 12 = true := by decide
theorem tmFiber20Parent_13_ok : tmFiber20ParentCheck 13 = true := by decide
theorem tmFiber20Parent_14_ok : tmFiber20ParentCheck 14 = true := by decide
theorem tmFiber20Parent_15_ok : tmFiber20ParentCheck 15 = true := by decide
theorem tmFiber20Parent_16_ok : tmFiber20ParentCheck 16 = true := by decide
theorem tmFiber20Parent_17_ok : tmFiber20ParentCheck 17 = true := by decide
theorem tmFiber20Parent_18_ok : tmFiber20ParentCheck 18 = true := by decide
theorem tmFiber20Parent_19_ok : tmFiber20ParentCheck 19 = true := by decide
theorem tmFiber20Parent_20_ok : tmFiber20ParentCheck 20 = true := by decide
theorem tmFiber20Parent_21_ok : tmFiber20ParentCheck 21 = true := by decide
theorem tmFiber20Parent_22_ok : tmFiber20ParentCheck 22 = true := by decide
theorem tmFiber20Parent_23_ok : tmFiber20ParentCheck 23 = true := by decide
theorem tmFiber20Parent_24_ok : tmFiber20ParentCheck 24 = true := by decide
theorem tmFiber20Parent_25_ok : tmFiber20ParentCheck 25 = true := by decide
theorem tmFiber20Parent_26_ok : tmFiber20ParentCheck 26 = true := by decide
theorem tmFiber20Parent_27_ok : tmFiber20ParentCheck 27 = true := by decide
theorem tmFiber20Parent_28_ok : tmFiber20ParentCheck 28 = true := by decide
theorem tmFiber20Parent_29_ok : tmFiber20ParentCheck 29 = true := by decide
theorem tmFiber20Parent_30_ok : tmFiber20ParentCheck 30 = true := by decide
theorem tmFiber20Parent_31_ok : tmFiber20ParentCheck 31 = true := by decide
theorem tmFiber20Parent_32_ok : tmFiber20ParentCheck 32 = true := by decide
theorem tmFiber20Parent_33_ok : tmFiber20ParentCheck 33 = true := by decide
theorem tmFiber20Parent_34_ok : tmFiber20ParentCheck 34 = true := by decide
theorem tmFiber20Parent_35_ok : tmFiber20ParentCheck 35 = true := by decide
theorem tmFiber20Parent_36_ok : tmFiber20ParentCheck 36 = true := by decide
theorem tmFiber20Parent_37_ok : tmFiber20ParentCheck 37 = true := by decide
theorem tmFiber20Parent_38_ok : tmFiber20ParentCheck 38 = true := by decide
theorem tmFiber20Parent_39_ok : tmFiber20ParentCheck 39 = true := by decide
theorem tmFiber20Parent_40_ok : tmFiber20ParentCheck 40 = true := by decide
theorem tmFiber20Parent_41_ok : tmFiber20ParentCheck 41 = true := by decide
theorem tmFiber20Parent_42_ok : tmFiber20ParentCheck 42 = true := by decide
theorem tmFiber20Parent_43_ok : tmFiber20ParentCheck 43 = true := by decide
theorem tmFiber20Parent_44_ok : tmFiber20ParentCheck 44 = true := by decide
theorem tmFiber20Parent_45_ok : tmFiber20ParentCheck 45 = true := by decide
theorem tmFiber20Parent_46_ok : tmFiber20ParentCheck 46 = true := by decide
theorem tmFiber20Parent_47_ok : tmFiber20ParentCheck 47 = true := by decide
theorem tmFiber20Parent_48_ok : tmFiber20ParentCheck 48 = true := by decide
theorem tmFiber20Parent_49_ok : tmFiber20ParentCheck 49 = true := by decide
theorem tmFiber20Parent_50_ok : tmFiber20ParentCheck 50 = true := by decide
theorem tmFiber20Parent_51_ok : tmFiber20ParentCheck 51 = true := by decide
theorem tmFiber20Parent_52_ok : tmFiber20ParentCheck 52 = true := by decide
theorem tmFiber20Parent_53_ok : tmFiber20ParentCheck 53 = true := by decide
theorem tmFiber20Parent_54_ok : tmFiber20ParentCheck 54 = true := by decide
theorem tmFiber20Parent_55_ok : tmFiber20ParentCheck 55 = true := by decide
theorem tmFiber20Parent_56_ok : tmFiber20ParentCheck 56 = true := by decide
theorem tmFiber20Parent_57_ok : tmFiber20ParentCheck 57 = true := by decide
theorem tmFiber20Parent_58_ok : tmFiber20ParentCheck 58 = true := by decide
theorem tmFiber20Parent_59_ok : tmFiber20ParentCheck 59 = true := by decide
theorem tmFiber20Parent_60_ok : tmFiber20ParentCheck 60 = true := by decide
theorem tmFiber20Parent_61_ok : tmFiber20ParentCheck 61 = true := by decide
theorem tmFiber20Parent_62_ok : tmFiber20ParentCheck 62 = true := by decide
theorem tmFiber20Parent_63_ok : tmFiber20ParentCheck 63 = true := by decide

def tmFiber20CertificateAudit : Bool :=
  tmFiber20SourcesCheck &&
    tmFiber20RowCheck 0 &&
    tmFiber20RowCheck 1 &&
    tmFiber20RowCheck 2 &&
    tmFiber20RowCheck 3 &&
    tmFiber20RowCheck 4 &&
    tmFiber20RowCheck 5 &&
    tmFiber20RowCheck 6 &&
    tmFiber20RowCheck 7 &&
    tmFiber20RowCheck 8 &&
    tmFiber20RowCheck 9 &&
    tmFiber20RowCheck 10 &&
    tmFiber20RowCheck 11 &&
    tmFiber20RowCheck 12 &&
    tmFiber20RowCheck 13 &&
    tmFiber20RowCheck 14 &&
    tmFiber20RowCheck 15 &&
    tmFiber20RowCheck 16 &&
    tmFiber20RowCheck 17 &&
    tmFiber20RowCheck 18 &&
    tmFiber20RowCheck 19 &&
    tmFiber20RowCheck 20 &&
    tmFiber20RowCheck 21 &&
    tmFiber20RowCheck 22 &&
    tmFiber20RowCheck 23 &&
    tmFiber20RowCheck 24 &&
    tmFiber20RowCheck 25 &&
    tmFiber20RowCheck 26 &&
    tmFiber20RowCheck 27 &&
    tmFiber20RowCheck 28 &&
    tmFiber20RowCheck 29 &&
    tmFiber20RowCheck 30 &&
    tmFiber20RowCheck 31 &&
    tmFiber20RowCheck 32 &&
    tmFiber20RowCheck 33 &&
    tmFiber20RowCheck 34 &&
    tmFiber20RowCheck 35 &&
    tmFiber20RowCheck 36 &&
    tmFiber20RowCheck 37 &&
    tmFiber20RowCheck 38 &&
    tmFiber20RowCheck 39 &&
    tmFiber20RowCheck 40 &&
    tmFiber20RowCheck 41 &&
    tmFiber20RowCheck 42 &&
    tmFiber20RowCheck 43 &&
    tmFiber20RowCheck 44 &&
    tmFiber20RowCheck 45 &&
    tmFiber20RowCheck 46 &&
    tmFiber20RowCheck 47 &&
    tmFiber20RowCheck 48 &&
    tmFiber20RowCheck 49 &&
    tmFiber20RowCheck 50 &&
    tmFiber20RowCheck 51 &&
    tmFiber20RowCheck 52 &&
    tmFiber20RowCheck 53 &&
    tmFiber20RowCheck 54 &&
    tmFiber20RowCheck 55 &&
    tmFiber20RowCheck 56 &&
    tmFiber20RowCheck 57 &&
    tmFiber20RowCheck 58 &&
    tmFiber20RowCheck 59 &&
    tmFiber20RowCheck 60 &&
    tmFiber20RowCheck 61 &&
    tmFiber20RowCheck 62 &&
    tmFiber20RowCheck 63 &&
    tmFiber20ParentCheck 0 &&
    tmFiber20ParentCheck 1 &&
    tmFiber20ParentCheck 2 &&
    tmFiber20ParentCheck 3 &&
    tmFiber20ParentCheck 4 &&
    tmFiber20ParentCheck 5 &&
    tmFiber20ParentCheck 6 &&
    tmFiber20ParentCheck 7 &&
    tmFiber20ParentCheck 8 &&
    tmFiber20ParentCheck 9 &&
    tmFiber20ParentCheck 10 &&
    tmFiber20ParentCheck 11 &&
    tmFiber20ParentCheck 12 &&
    tmFiber20ParentCheck 13 &&
    tmFiber20ParentCheck 14 &&
    tmFiber20ParentCheck 15 &&
    tmFiber20ParentCheck 16 &&
    tmFiber20ParentCheck 17 &&
    tmFiber20ParentCheck 18 &&
    tmFiber20ParentCheck 19 &&
    tmFiber20ParentCheck 20 &&
    tmFiber20ParentCheck 21 &&
    tmFiber20ParentCheck 22 &&
    tmFiber20ParentCheck 23 &&
    tmFiber20ParentCheck 24 &&
    tmFiber20ParentCheck 25 &&
    tmFiber20ParentCheck 26 &&
    tmFiber20ParentCheck 27 &&
    tmFiber20ParentCheck 28 &&
    tmFiber20ParentCheck 29 &&
    tmFiber20ParentCheck 30 &&
    tmFiber20ParentCheck 31 &&
    tmFiber20ParentCheck 32 &&
    tmFiber20ParentCheck 33 &&
    tmFiber20ParentCheck 34 &&
    tmFiber20ParentCheck 35 &&
    tmFiber20ParentCheck 36 &&
    tmFiber20ParentCheck 37 &&
    tmFiber20ParentCheck 38 &&
    tmFiber20ParentCheck 39 &&
    tmFiber20ParentCheck 40 &&
    tmFiber20ParentCheck 41 &&
    tmFiber20ParentCheck 42 &&
    tmFiber20ParentCheck 43 &&
    tmFiber20ParentCheck 44 &&
    tmFiber20ParentCheck 45 &&
    tmFiber20ParentCheck 46 &&
    tmFiber20ParentCheck 47 &&
    tmFiber20ParentCheck 48 &&
    tmFiber20ParentCheck 49 &&
    tmFiber20ParentCheck 50 &&
    tmFiber20ParentCheck 51 &&
    tmFiber20ParentCheck 52 &&
    tmFiber20ParentCheck 53 &&
    tmFiber20ParentCheck 54 &&
    tmFiber20ParentCheck 55 &&
    tmFiber20ParentCheck 56 &&
    tmFiber20ParentCheck 57 &&
    tmFiber20ParentCheck 58 &&
    tmFiber20ParentCheck 59 &&
    tmFiber20ParentCheck 60 &&
    tmFiber20ParentCheck 61 &&
    tmFiber20ParentCheck 62 &&
    tmFiber20ParentCheck 63

theorem tmFiber20CertificateAudit_ok :
    tmFiber20CertificateAudit = true := by
  simp [tmFiber20CertificateAudit,
    tmFiber20SourcesCheck_ok,
    tmFiber20Row_0_ok,
    tmFiber20Row_1_ok,
    tmFiber20Row_2_ok,
    tmFiber20Row_3_ok,
    tmFiber20Row_4_ok,
    tmFiber20Row_5_ok,
    tmFiber20Row_6_ok,
    tmFiber20Row_7_ok,
    tmFiber20Row_8_ok,
    tmFiber20Row_9_ok,
    tmFiber20Row_10_ok,
    tmFiber20Row_11_ok,
    tmFiber20Row_12_ok,
    tmFiber20Row_13_ok,
    tmFiber20Row_14_ok,
    tmFiber20Row_15_ok,
    tmFiber20Row_16_ok,
    tmFiber20Row_17_ok,
    tmFiber20Row_18_ok,
    tmFiber20Row_19_ok,
    tmFiber20Row_20_ok,
    tmFiber20Row_21_ok,
    tmFiber20Row_22_ok,
    tmFiber20Row_23_ok,
    tmFiber20Row_24_ok,
    tmFiber20Row_25_ok,
    tmFiber20Row_26_ok,
    tmFiber20Row_27_ok,
    tmFiber20Row_28_ok,
    tmFiber20Row_29_ok,
    tmFiber20Row_30_ok,
    tmFiber20Row_31_ok,
    tmFiber20Row_32_ok,
    tmFiber20Row_33_ok,
    tmFiber20Row_34_ok,
    tmFiber20Row_35_ok,
    tmFiber20Row_36_ok,
    tmFiber20Row_37_ok,
    tmFiber20Row_38_ok,
    tmFiber20Row_39_ok,
    tmFiber20Row_40_ok,
    tmFiber20Row_41_ok,
    tmFiber20Row_42_ok,
    tmFiber20Row_43_ok,
    tmFiber20Row_44_ok,
    tmFiber20Row_45_ok,
    tmFiber20Row_46_ok,
    tmFiber20Row_47_ok,
    tmFiber20Row_48_ok,
    tmFiber20Row_49_ok,
    tmFiber20Row_50_ok,
    tmFiber20Row_51_ok,
    tmFiber20Row_52_ok,
    tmFiber20Row_53_ok,
    tmFiber20Row_54_ok,
    tmFiber20Row_55_ok,
    tmFiber20Row_56_ok,
    tmFiber20Row_57_ok,
    tmFiber20Row_58_ok,
    tmFiber20Row_59_ok,
    tmFiber20Row_60_ok,
    tmFiber20Row_61_ok,
    tmFiber20Row_62_ok,
    tmFiber20Row_63_ok,
    tmFiber20Parent_0_ok,
    tmFiber20Parent_1_ok,
    tmFiber20Parent_2_ok,
    tmFiber20Parent_3_ok,
    tmFiber20Parent_4_ok,
    tmFiber20Parent_5_ok,
    tmFiber20Parent_6_ok,
    tmFiber20Parent_7_ok,
    tmFiber20Parent_8_ok,
    tmFiber20Parent_9_ok,
    tmFiber20Parent_10_ok,
    tmFiber20Parent_11_ok,
    tmFiber20Parent_12_ok,
    tmFiber20Parent_13_ok,
    tmFiber20Parent_14_ok,
    tmFiber20Parent_15_ok,
    tmFiber20Parent_16_ok,
    tmFiber20Parent_17_ok,
    tmFiber20Parent_18_ok,
    tmFiber20Parent_19_ok,
    tmFiber20Parent_20_ok,
    tmFiber20Parent_21_ok,
    tmFiber20Parent_22_ok,
    tmFiber20Parent_23_ok,
    tmFiber20Parent_24_ok,
    tmFiber20Parent_25_ok,
    tmFiber20Parent_26_ok,
    tmFiber20Parent_27_ok,
    tmFiber20Parent_28_ok,
    tmFiber20Parent_29_ok,
    tmFiber20Parent_30_ok,
    tmFiber20Parent_31_ok,
    tmFiber20Parent_32_ok,
    tmFiber20Parent_33_ok,
    tmFiber20Parent_34_ok,
    tmFiber20Parent_35_ok,
    tmFiber20Parent_36_ok,
    tmFiber20Parent_37_ok,
    tmFiber20Parent_38_ok,
    tmFiber20Parent_39_ok,
    tmFiber20Parent_40_ok,
    tmFiber20Parent_41_ok,
    tmFiber20Parent_42_ok,
    tmFiber20Parent_43_ok,
    tmFiber20Parent_44_ok,
    tmFiber20Parent_45_ok,
    tmFiber20Parent_46_ok,
    tmFiber20Parent_47_ok,
    tmFiber20Parent_48_ok,
    tmFiber20Parent_49_ok,
    tmFiber20Parent_50_ok,
    tmFiber20Parent_51_ok,
    tmFiber20Parent_52_ok,
    tmFiber20Parent_53_ok,
    tmFiber20Parent_54_ok,
    tmFiber20Parent_55_ok,
    tmFiber20Parent_56_ok,
    tmFiber20Parent_57_ok,
    tmFiber20Parent_58_ok,
    tmFiber20Parent_59_ok,
    tmFiber20Parent_60_ok,
    tmFiber20Parent_61_ok,
    tmFiber20Parent_62_ok,
    tmFiber20Parent_63_ok]

def tmFiber21Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.r]

def tmFiber21Expected : List Nat :=
  []

def tmFiber21Rows : List DirectChainParentRow :=
  []

def tmFiber21RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber21Rows i default

def tmFiber21SourcesCheck : Bool :=
  (tmFiber21Rows.map fun row => row.source) == tmFiber21Expected

theorem tmFiber21SourcesCheck_ok :
    tmFiber21SourcesCheck = true := by
  decide

def tmFiber21RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber21Key tmFiber21Expected (tmFiber21RowAt i)

def tmFiber21ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber21Rows tmMaxParentDepth (listGetD tmFiber21Expected i 0) == 0

def tmFiber21CertificateAudit : Bool :=
  tmFiber21SourcesCheck

theorem tmFiber21CertificateAudit_ok :
    tmFiber21CertificateAudit = true := by
  simp [tmFiber21CertificateAudit,
    tmFiber21SourcesCheck_ok]

def tmFiber22Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.b]

def tmFiber22Expected : List Nat :=
  []

def tmFiber22Rows : List DirectChainParentRow :=
  []

def tmFiber22RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber22Rows i default

def tmFiber22SourcesCheck : Bool :=
  (tmFiber22Rows.map fun row => row.source) == tmFiber22Expected

theorem tmFiber22SourcesCheck_ok :
    tmFiber22SourcesCheck = true := by
  decide

def tmFiber22RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber22Key tmFiber22Expected (tmFiber22RowAt i)

def tmFiber22ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber22Rows tmMaxParentDepth (listGetD tmFiber22Expected i 0) == 0

def tmFiber22CertificateAudit : Bool :=
  tmFiber22SourcesCheck

theorem tmFiber22CertificateAudit_ok :
    tmFiber22CertificateAudit = true := by
  simp [tmFiber22CertificateAudit,
    tmFiber22SourcesCheck_ok]

def tmFiber23Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.p]

def tmFiber23Expected : List Nat :=
  []

def tmFiber23Rows : List DirectChainParentRow :=
  []

def tmFiber23RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber23Rows i default

def tmFiber23SourcesCheck : Bool :=
  (tmFiber23Rows.map fun row => row.source) == tmFiber23Expected

theorem tmFiber23SourcesCheck_ok :
    tmFiber23SourcesCheck = true := by
  decide

def tmFiber23RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber23Key tmFiber23Expected (tmFiber23RowAt i)

def tmFiber23ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber23Rows tmMaxParentDepth (listGetD tmFiber23Expected i 0) == 0

def tmFiber23CertificateAudit : Bool :=
  tmFiber23SourcesCheck

theorem tmFiber23CertificateAudit_ok :
    tmFiber23CertificateAudit = true := by
  simp [tmFiber23CertificateAudit,
    tmFiber23SourcesCheck_ok]

def tmFiber24Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.r]

def tmFiber24Expected : List Nat :=
  []

def tmFiber24Rows : List DirectChainParentRow :=
  []

def tmFiber24RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber24Rows i default

def tmFiber24SourcesCheck : Bool :=
  (tmFiber24Rows.map fun row => row.source) == tmFiber24Expected

theorem tmFiber24SourcesCheck_ok :
    tmFiber24SourcesCheck = true := by
  decide

def tmFiber24RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber24Key tmFiber24Expected (tmFiber24RowAt i)

def tmFiber24ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber24Rows tmMaxParentDepth (listGetD tmFiber24Expected i 0) == 0

def tmFiber24CertificateAudit : Bool :=
  tmFiber24SourcesCheck

theorem tmFiber24CertificateAudit_ok :
    tmFiber24CertificateAudit = true := by
  simp [tmFiber24CertificateAudit,
    tmFiber24SourcesCheck_ok]

def tmFiber25Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.b]

def tmFiber25Expected : List Nat :=
  []

def tmFiber25Rows : List DirectChainParentRow :=
  []

def tmFiber25RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber25Rows i default

def tmFiber25SourcesCheck : Bool :=
  (tmFiber25Rows.map fun row => row.source) == tmFiber25Expected

theorem tmFiber25SourcesCheck_ok :
    tmFiber25SourcesCheck = true := by
  decide

def tmFiber25RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber25Key tmFiber25Expected (tmFiber25RowAt i)

def tmFiber25ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber25Rows tmMaxParentDepth (listGetD tmFiber25Expected i 0) == 0

def tmFiber25CertificateAudit : Bool :=
  tmFiber25SourcesCheck

theorem tmFiber25CertificateAudit_ok :
    tmFiber25CertificateAudit = true := by
  simp [tmFiber25CertificateAudit,
    tmFiber25SourcesCheck_ok]

def tmFiber26Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.p]

def tmFiber26Expected : List Nat :=
  []

def tmFiber26Rows : List DirectChainParentRow :=
  []

def tmFiber26RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber26Rows i default

def tmFiber26SourcesCheck : Bool :=
  (tmFiber26Rows.map fun row => row.source) == tmFiber26Expected

theorem tmFiber26SourcesCheck_ok :
    tmFiber26SourcesCheck = true := by
  decide

def tmFiber26RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber26Key tmFiber26Expected (tmFiber26RowAt i)

def tmFiber26ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber26Rows tmMaxParentDepth (listGetD tmFiber26Expected i 0) == 0

def tmFiber26CertificateAudit : Bool :=
  tmFiber26SourcesCheck

theorem tmFiber26CertificateAudit_ok :
    tmFiber26CertificateAudit = true := by
  simp [tmFiber26CertificateAudit,
    tmFiber26SourcesCheck_ok]

def tmFiber27Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.r]

def tmFiber27Expected : List Nat :=
  []

def tmFiber27Rows : List DirectChainParentRow :=
  []

def tmFiber27RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber27Rows i default

def tmFiber27SourcesCheck : Bool :=
  (tmFiber27Rows.map fun row => row.source) == tmFiber27Expected

theorem tmFiber27SourcesCheck_ok :
    tmFiber27SourcesCheck = true := by
  decide

def tmFiber27RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber27Key tmFiber27Expected (tmFiber27RowAt i)

def tmFiber27ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber27Rows tmMaxParentDepth (listGetD tmFiber27Expected i 0) == 0

def tmFiber27CertificateAudit : Bool :=
  tmFiber27SourcesCheck

theorem tmFiber27CertificateAudit_ok :
    tmFiber27CertificateAudit = true := by
  simp [tmFiber27CertificateAudit,
    tmFiber27SourcesCheck_ok]

def tmFiber28Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.b]

def tmFiber28Expected : List Nat :=
  []

def tmFiber28Rows : List DirectChainParentRow :=
  []

def tmFiber28RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber28Rows i default

def tmFiber28SourcesCheck : Bool :=
  (tmFiber28Rows.map fun row => row.source) == tmFiber28Expected

theorem tmFiber28SourcesCheck_ok :
    tmFiber28SourcesCheck = true := by
  decide

def tmFiber28RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber28Key tmFiber28Expected (tmFiber28RowAt i)

def tmFiber28ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber28Rows tmMaxParentDepth (listGetD tmFiber28Expected i 0) == 0

def tmFiber28CertificateAudit : Bool :=
  tmFiber28SourcesCheck

theorem tmFiber28CertificateAudit_ok :
    tmFiber28CertificateAudit = true := by
  simp [tmFiber28CertificateAudit,
    tmFiber28SourcesCheck_ok]

def tmFiber29Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.p]

def tmFiber29Expected : List Nat :=
  []

def tmFiber29Rows : List DirectChainParentRow :=
  []

def tmFiber29RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber29Rows i default

def tmFiber29SourcesCheck : Bool :=
  (tmFiber29Rows.map fun row => row.source) == tmFiber29Expected

theorem tmFiber29SourcesCheck_ok :
    tmFiber29SourcesCheck = true := by
  decide

def tmFiber29RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber29Key tmFiber29Expected (tmFiber29RowAt i)

def tmFiber29ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber29Rows tmMaxParentDepth (listGetD tmFiber29Expected i 0) == 0

def tmFiber29CertificateAudit : Bool :=
  tmFiber29SourcesCheck

theorem tmFiber29CertificateAudit_ok :
    tmFiber29CertificateAudit = true := by
  simp [tmFiber29CertificateAudit,
    tmFiber29SourcesCheck_ok]

def tmFiber30Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.r]

def tmFiber30Expected : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]

def tmFiber30Rows : List DirectChainParentRow :=
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

def tmFiber30RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber30Rows i default

def tmFiber30SourcesCheck : Bool :=
  (tmFiber30Rows.map fun row => row.source) == tmFiber30Expected

theorem tmFiber30SourcesCheck_ok :
    tmFiber30SourcesCheck = true := by
  decide

def tmFiber30RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber30Key tmFiber30Expected (tmFiber30RowAt i)

theorem tmFiber30Row_0_ok : tmFiber30RowCheck 0 = true := by decide
theorem tmFiber30Row_1_ok : tmFiber30RowCheck 1 = true := by decide
theorem tmFiber30Row_2_ok : tmFiber30RowCheck 2 = true := by decide
theorem tmFiber30Row_3_ok : tmFiber30RowCheck 3 = true := by decide
theorem tmFiber30Row_4_ok : tmFiber30RowCheck 4 = true := by decide
theorem tmFiber30Row_5_ok : tmFiber30RowCheck 5 = true := by decide
theorem tmFiber30Row_6_ok : tmFiber30RowCheck 6 = true := by decide
theorem tmFiber30Row_7_ok : tmFiber30RowCheck 7 = true := by decide
theorem tmFiber30Row_8_ok : tmFiber30RowCheck 8 = true := by decide
theorem tmFiber30Row_9_ok : tmFiber30RowCheck 9 = true := by decide
theorem tmFiber30Row_10_ok : tmFiber30RowCheck 10 = true := by decide
theorem tmFiber30Row_11_ok : tmFiber30RowCheck 11 = true := by decide
theorem tmFiber30Row_12_ok : tmFiber30RowCheck 12 = true := by decide
theorem tmFiber30Row_13_ok : tmFiber30RowCheck 13 = true := by decide
theorem tmFiber30Row_14_ok : tmFiber30RowCheck 14 = true := by decide
theorem tmFiber30Row_15_ok : tmFiber30RowCheck 15 = true := by decide
theorem tmFiber30Row_16_ok : tmFiber30RowCheck 16 = true := by decide
theorem tmFiber30Row_17_ok : tmFiber30RowCheck 17 = true := by decide
theorem tmFiber30Row_18_ok : tmFiber30RowCheck 18 = true := by decide
theorem tmFiber30Row_19_ok : tmFiber30RowCheck 19 = true := by decide
theorem tmFiber30Row_20_ok : tmFiber30RowCheck 20 = true := by decide
theorem tmFiber30Row_21_ok : tmFiber30RowCheck 21 = true := by decide
theorem tmFiber30Row_22_ok : tmFiber30RowCheck 22 = true := by decide
theorem tmFiber30Row_23_ok : tmFiber30RowCheck 23 = true := by decide
theorem tmFiber30Row_24_ok : tmFiber30RowCheck 24 = true := by decide
theorem tmFiber30Row_25_ok : tmFiber30RowCheck 25 = true := by decide
theorem tmFiber30Row_26_ok : tmFiber30RowCheck 26 = true := by decide
theorem tmFiber30Row_27_ok : tmFiber30RowCheck 27 = true := by decide
theorem tmFiber30Row_28_ok : tmFiber30RowCheck 28 = true := by decide
theorem tmFiber30Row_29_ok : tmFiber30RowCheck 29 = true := by decide
theorem tmFiber30Row_30_ok : tmFiber30RowCheck 30 = true := by decide
theorem tmFiber30Row_31_ok : tmFiber30RowCheck 31 = true := by decide
theorem tmFiber30Row_32_ok : tmFiber30RowCheck 32 = true := by decide
theorem tmFiber30Row_33_ok : tmFiber30RowCheck 33 = true := by decide
theorem tmFiber30Row_34_ok : tmFiber30RowCheck 34 = true := by decide
theorem tmFiber30Row_35_ok : tmFiber30RowCheck 35 = true := by decide
theorem tmFiber30Row_36_ok : tmFiber30RowCheck 36 = true := by decide
theorem tmFiber30Row_37_ok : tmFiber30RowCheck 37 = true := by decide
theorem tmFiber30Row_38_ok : tmFiber30RowCheck 38 = true := by decide
theorem tmFiber30Row_39_ok : tmFiber30RowCheck 39 = true := by decide
theorem tmFiber30Row_40_ok : tmFiber30RowCheck 40 = true := by decide
theorem tmFiber30Row_41_ok : tmFiber30RowCheck 41 = true := by decide
theorem tmFiber30Row_42_ok : tmFiber30RowCheck 42 = true := by decide
theorem tmFiber30Row_43_ok : tmFiber30RowCheck 43 = true := by decide
theorem tmFiber30Row_44_ok : tmFiber30RowCheck 44 = true := by decide
theorem tmFiber30Row_45_ok : tmFiber30RowCheck 45 = true := by decide
theorem tmFiber30Row_46_ok : tmFiber30RowCheck 46 = true := by decide
theorem tmFiber30Row_47_ok : tmFiber30RowCheck 47 = true := by decide
theorem tmFiber30Row_48_ok : tmFiber30RowCheck 48 = true := by decide
theorem tmFiber30Row_49_ok : tmFiber30RowCheck 49 = true := by decide
theorem tmFiber30Row_50_ok : tmFiber30RowCheck 50 = true := by decide
theorem tmFiber30Row_51_ok : tmFiber30RowCheck 51 = true := by decide
theorem tmFiber30Row_52_ok : tmFiber30RowCheck 52 = true := by decide
theorem tmFiber30Row_53_ok : tmFiber30RowCheck 53 = true := by decide
theorem tmFiber30Row_54_ok : tmFiber30RowCheck 54 = true := by decide
theorem tmFiber30Row_55_ok : tmFiber30RowCheck 55 = true := by decide
theorem tmFiber30Row_56_ok : tmFiber30RowCheck 56 = true := by decide
theorem tmFiber30Row_57_ok : tmFiber30RowCheck 57 = true := by decide
theorem tmFiber30Row_58_ok : tmFiber30RowCheck 58 = true := by decide
theorem tmFiber30Row_59_ok : tmFiber30RowCheck 59 = true := by decide
theorem tmFiber30Row_60_ok : tmFiber30RowCheck 60 = true := by decide
theorem tmFiber30Row_61_ok : tmFiber30RowCheck 61 = true := by decide
theorem tmFiber30Row_62_ok : tmFiber30RowCheck 62 = true := by decide
theorem tmFiber30Row_63_ok : tmFiber30RowCheck 63 = true := by decide

def tmFiber30ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber30Rows tmMaxParentDepth (listGetD tmFiber30Expected i 0) == 0

theorem tmFiber30Parent_0_ok : tmFiber30ParentCheck 0 = true := by decide
theorem tmFiber30Parent_1_ok : tmFiber30ParentCheck 1 = true := by decide
theorem tmFiber30Parent_2_ok : tmFiber30ParentCheck 2 = true := by decide
theorem tmFiber30Parent_3_ok : tmFiber30ParentCheck 3 = true := by decide
theorem tmFiber30Parent_4_ok : tmFiber30ParentCheck 4 = true := by decide
theorem tmFiber30Parent_5_ok : tmFiber30ParentCheck 5 = true := by decide
theorem tmFiber30Parent_6_ok : tmFiber30ParentCheck 6 = true := by decide
theorem tmFiber30Parent_7_ok : tmFiber30ParentCheck 7 = true := by decide
theorem tmFiber30Parent_8_ok : tmFiber30ParentCheck 8 = true := by decide
theorem tmFiber30Parent_9_ok : tmFiber30ParentCheck 9 = true := by decide
theorem tmFiber30Parent_10_ok : tmFiber30ParentCheck 10 = true := by decide
theorem tmFiber30Parent_11_ok : tmFiber30ParentCheck 11 = true := by decide
theorem tmFiber30Parent_12_ok : tmFiber30ParentCheck 12 = true := by decide
theorem tmFiber30Parent_13_ok : tmFiber30ParentCheck 13 = true := by decide
theorem tmFiber30Parent_14_ok : tmFiber30ParentCheck 14 = true := by decide
theorem tmFiber30Parent_15_ok : tmFiber30ParentCheck 15 = true := by decide
theorem tmFiber30Parent_16_ok : tmFiber30ParentCheck 16 = true := by decide
theorem tmFiber30Parent_17_ok : tmFiber30ParentCheck 17 = true := by decide
theorem tmFiber30Parent_18_ok : tmFiber30ParentCheck 18 = true := by decide
theorem tmFiber30Parent_19_ok : tmFiber30ParentCheck 19 = true := by decide
theorem tmFiber30Parent_20_ok : tmFiber30ParentCheck 20 = true := by decide
theorem tmFiber30Parent_21_ok : tmFiber30ParentCheck 21 = true := by decide
theorem tmFiber30Parent_22_ok : tmFiber30ParentCheck 22 = true := by decide
theorem tmFiber30Parent_23_ok : tmFiber30ParentCheck 23 = true := by decide
theorem tmFiber30Parent_24_ok : tmFiber30ParentCheck 24 = true := by decide
theorem tmFiber30Parent_25_ok : tmFiber30ParentCheck 25 = true := by decide
theorem tmFiber30Parent_26_ok : tmFiber30ParentCheck 26 = true := by decide
theorem tmFiber30Parent_27_ok : tmFiber30ParentCheck 27 = true := by decide
theorem tmFiber30Parent_28_ok : tmFiber30ParentCheck 28 = true := by decide
theorem tmFiber30Parent_29_ok : tmFiber30ParentCheck 29 = true := by decide
theorem tmFiber30Parent_30_ok : tmFiber30ParentCheck 30 = true := by decide
theorem tmFiber30Parent_31_ok : tmFiber30ParentCheck 31 = true := by decide
theorem tmFiber30Parent_32_ok : tmFiber30ParentCheck 32 = true := by decide
theorem tmFiber30Parent_33_ok : tmFiber30ParentCheck 33 = true := by decide
theorem tmFiber30Parent_34_ok : tmFiber30ParentCheck 34 = true := by decide
theorem tmFiber30Parent_35_ok : tmFiber30ParentCheck 35 = true := by decide
theorem tmFiber30Parent_36_ok : tmFiber30ParentCheck 36 = true := by decide
theorem tmFiber30Parent_37_ok : tmFiber30ParentCheck 37 = true := by decide
theorem tmFiber30Parent_38_ok : tmFiber30ParentCheck 38 = true := by decide
theorem tmFiber30Parent_39_ok : tmFiber30ParentCheck 39 = true := by decide
theorem tmFiber30Parent_40_ok : tmFiber30ParentCheck 40 = true := by decide
theorem tmFiber30Parent_41_ok : tmFiber30ParentCheck 41 = true := by decide
theorem tmFiber30Parent_42_ok : tmFiber30ParentCheck 42 = true := by decide
theorem tmFiber30Parent_43_ok : tmFiber30ParentCheck 43 = true := by decide
theorem tmFiber30Parent_44_ok : tmFiber30ParentCheck 44 = true := by decide
theorem tmFiber30Parent_45_ok : tmFiber30ParentCheck 45 = true := by decide
theorem tmFiber30Parent_46_ok : tmFiber30ParentCheck 46 = true := by decide
theorem tmFiber30Parent_47_ok : tmFiber30ParentCheck 47 = true := by decide
theorem tmFiber30Parent_48_ok : tmFiber30ParentCheck 48 = true := by decide
theorem tmFiber30Parent_49_ok : tmFiber30ParentCheck 49 = true := by decide
theorem tmFiber30Parent_50_ok : tmFiber30ParentCheck 50 = true := by decide
theorem tmFiber30Parent_51_ok : tmFiber30ParentCheck 51 = true := by decide
theorem tmFiber30Parent_52_ok : tmFiber30ParentCheck 52 = true := by decide
theorem tmFiber30Parent_53_ok : tmFiber30ParentCheck 53 = true := by decide
theorem tmFiber30Parent_54_ok : tmFiber30ParentCheck 54 = true := by decide
theorem tmFiber30Parent_55_ok : tmFiber30ParentCheck 55 = true := by decide
theorem tmFiber30Parent_56_ok : tmFiber30ParentCheck 56 = true := by decide
theorem tmFiber30Parent_57_ok : tmFiber30ParentCheck 57 = true := by decide
theorem tmFiber30Parent_58_ok : tmFiber30ParentCheck 58 = true := by decide
theorem tmFiber30Parent_59_ok : tmFiber30ParentCheck 59 = true := by decide
theorem tmFiber30Parent_60_ok : tmFiber30ParentCheck 60 = true := by decide
theorem tmFiber30Parent_61_ok : tmFiber30ParentCheck 61 = true := by decide
theorem tmFiber30Parent_62_ok : tmFiber30ParentCheck 62 = true := by decide
theorem tmFiber30Parent_63_ok : tmFiber30ParentCheck 63 = true := by decide

def tmFiber30CertificateAudit : Bool :=
  tmFiber30SourcesCheck &&
    tmFiber30RowCheck 0 &&
    tmFiber30RowCheck 1 &&
    tmFiber30RowCheck 2 &&
    tmFiber30RowCheck 3 &&
    tmFiber30RowCheck 4 &&
    tmFiber30RowCheck 5 &&
    tmFiber30RowCheck 6 &&
    tmFiber30RowCheck 7 &&
    tmFiber30RowCheck 8 &&
    tmFiber30RowCheck 9 &&
    tmFiber30RowCheck 10 &&
    tmFiber30RowCheck 11 &&
    tmFiber30RowCheck 12 &&
    tmFiber30RowCheck 13 &&
    tmFiber30RowCheck 14 &&
    tmFiber30RowCheck 15 &&
    tmFiber30RowCheck 16 &&
    tmFiber30RowCheck 17 &&
    tmFiber30RowCheck 18 &&
    tmFiber30RowCheck 19 &&
    tmFiber30RowCheck 20 &&
    tmFiber30RowCheck 21 &&
    tmFiber30RowCheck 22 &&
    tmFiber30RowCheck 23 &&
    tmFiber30RowCheck 24 &&
    tmFiber30RowCheck 25 &&
    tmFiber30RowCheck 26 &&
    tmFiber30RowCheck 27 &&
    tmFiber30RowCheck 28 &&
    tmFiber30RowCheck 29 &&
    tmFiber30RowCheck 30 &&
    tmFiber30RowCheck 31 &&
    tmFiber30RowCheck 32 &&
    tmFiber30RowCheck 33 &&
    tmFiber30RowCheck 34 &&
    tmFiber30RowCheck 35 &&
    tmFiber30RowCheck 36 &&
    tmFiber30RowCheck 37 &&
    tmFiber30RowCheck 38 &&
    tmFiber30RowCheck 39 &&
    tmFiber30RowCheck 40 &&
    tmFiber30RowCheck 41 &&
    tmFiber30RowCheck 42 &&
    tmFiber30RowCheck 43 &&
    tmFiber30RowCheck 44 &&
    tmFiber30RowCheck 45 &&
    tmFiber30RowCheck 46 &&
    tmFiber30RowCheck 47 &&
    tmFiber30RowCheck 48 &&
    tmFiber30RowCheck 49 &&
    tmFiber30RowCheck 50 &&
    tmFiber30RowCheck 51 &&
    tmFiber30RowCheck 52 &&
    tmFiber30RowCheck 53 &&
    tmFiber30RowCheck 54 &&
    tmFiber30RowCheck 55 &&
    tmFiber30RowCheck 56 &&
    tmFiber30RowCheck 57 &&
    tmFiber30RowCheck 58 &&
    tmFiber30RowCheck 59 &&
    tmFiber30RowCheck 60 &&
    tmFiber30RowCheck 61 &&
    tmFiber30RowCheck 62 &&
    tmFiber30RowCheck 63 &&
    tmFiber30ParentCheck 0 &&
    tmFiber30ParentCheck 1 &&
    tmFiber30ParentCheck 2 &&
    tmFiber30ParentCheck 3 &&
    tmFiber30ParentCheck 4 &&
    tmFiber30ParentCheck 5 &&
    tmFiber30ParentCheck 6 &&
    tmFiber30ParentCheck 7 &&
    tmFiber30ParentCheck 8 &&
    tmFiber30ParentCheck 9 &&
    tmFiber30ParentCheck 10 &&
    tmFiber30ParentCheck 11 &&
    tmFiber30ParentCheck 12 &&
    tmFiber30ParentCheck 13 &&
    tmFiber30ParentCheck 14 &&
    tmFiber30ParentCheck 15 &&
    tmFiber30ParentCheck 16 &&
    tmFiber30ParentCheck 17 &&
    tmFiber30ParentCheck 18 &&
    tmFiber30ParentCheck 19 &&
    tmFiber30ParentCheck 20 &&
    tmFiber30ParentCheck 21 &&
    tmFiber30ParentCheck 22 &&
    tmFiber30ParentCheck 23 &&
    tmFiber30ParentCheck 24 &&
    tmFiber30ParentCheck 25 &&
    tmFiber30ParentCheck 26 &&
    tmFiber30ParentCheck 27 &&
    tmFiber30ParentCheck 28 &&
    tmFiber30ParentCheck 29 &&
    tmFiber30ParentCheck 30 &&
    tmFiber30ParentCheck 31 &&
    tmFiber30ParentCheck 32 &&
    tmFiber30ParentCheck 33 &&
    tmFiber30ParentCheck 34 &&
    tmFiber30ParentCheck 35 &&
    tmFiber30ParentCheck 36 &&
    tmFiber30ParentCheck 37 &&
    tmFiber30ParentCheck 38 &&
    tmFiber30ParentCheck 39 &&
    tmFiber30ParentCheck 40 &&
    tmFiber30ParentCheck 41 &&
    tmFiber30ParentCheck 42 &&
    tmFiber30ParentCheck 43 &&
    tmFiber30ParentCheck 44 &&
    tmFiber30ParentCheck 45 &&
    tmFiber30ParentCheck 46 &&
    tmFiber30ParentCheck 47 &&
    tmFiber30ParentCheck 48 &&
    tmFiber30ParentCheck 49 &&
    tmFiber30ParentCheck 50 &&
    tmFiber30ParentCheck 51 &&
    tmFiber30ParentCheck 52 &&
    tmFiber30ParentCheck 53 &&
    tmFiber30ParentCheck 54 &&
    tmFiber30ParentCheck 55 &&
    tmFiber30ParentCheck 56 &&
    tmFiber30ParentCheck 57 &&
    tmFiber30ParentCheck 58 &&
    tmFiber30ParentCheck 59 &&
    tmFiber30ParentCheck 60 &&
    tmFiber30ParentCheck 61 &&
    tmFiber30ParentCheck 62 &&
    tmFiber30ParentCheck 63

theorem tmFiber30CertificateAudit_ok :
    tmFiber30CertificateAudit = true := by
  simp [tmFiber30CertificateAudit,
    tmFiber30SourcesCheck_ok,
    tmFiber30Row_0_ok,
    tmFiber30Row_1_ok,
    tmFiber30Row_2_ok,
    tmFiber30Row_3_ok,
    tmFiber30Row_4_ok,
    tmFiber30Row_5_ok,
    tmFiber30Row_6_ok,
    tmFiber30Row_7_ok,
    tmFiber30Row_8_ok,
    tmFiber30Row_9_ok,
    tmFiber30Row_10_ok,
    tmFiber30Row_11_ok,
    tmFiber30Row_12_ok,
    tmFiber30Row_13_ok,
    tmFiber30Row_14_ok,
    tmFiber30Row_15_ok,
    tmFiber30Row_16_ok,
    tmFiber30Row_17_ok,
    tmFiber30Row_18_ok,
    tmFiber30Row_19_ok,
    tmFiber30Row_20_ok,
    tmFiber30Row_21_ok,
    tmFiber30Row_22_ok,
    tmFiber30Row_23_ok,
    tmFiber30Row_24_ok,
    tmFiber30Row_25_ok,
    tmFiber30Row_26_ok,
    tmFiber30Row_27_ok,
    tmFiber30Row_28_ok,
    tmFiber30Row_29_ok,
    tmFiber30Row_30_ok,
    tmFiber30Row_31_ok,
    tmFiber30Row_32_ok,
    tmFiber30Row_33_ok,
    tmFiber30Row_34_ok,
    tmFiber30Row_35_ok,
    tmFiber30Row_36_ok,
    tmFiber30Row_37_ok,
    tmFiber30Row_38_ok,
    tmFiber30Row_39_ok,
    tmFiber30Row_40_ok,
    tmFiber30Row_41_ok,
    tmFiber30Row_42_ok,
    tmFiber30Row_43_ok,
    tmFiber30Row_44_ok,
    tmFiber30Row_45_ok,
    tmFiber30Row_46_ok,
    tmFiber30Row_47_ok,
    tmFiber30Row_48_ok,
    tmFiber30Row_49_ok,
    tmFiber30Row_50_ok,
    tmFiber30Row_51_ok,
    tmFiber30Row_52_ok,
    tmFiber30Row_53_ok,
    tmFiber30Row_54_ok,
    tmFiber30Row_55_ok,
    tmFiber30Row_56_ok,
    tmFiber30Row_57_ok,
    tmFiber30Row_58_ok,
    tmFiber30Row_59_ok,
    tmFiber30Row_60_ok,
    tmFiber30Row_61_ok,
    tmFiber30Row_62_ok,
    tmFiber30Row_63_ok,
    tmFiber30Parent_0_ok,
    tmFiber30Parent_1_ok,
    tmFiber30Parent_2_ok,
    tmFiber30Parent_3_ok,
    tmFiber30Parent_4_ok,
    tmFiber30Parent_5_ok,
    tmFiber30Parent_6_ok,
    tmFiber30Parent_7_ok,
    tmFiber30Parent_8_ok,
    tmFiber30Parent_9_ok,
    tmFiber30Parent_10_ok,
    tmFiber30Parent_11_ok,
    tmFiber30Parent_12_ok,
    tmFiber30Parent_13_ok,
    tmFiber30Parent_14_ok,
    tmFiber30Parent_15_ok,
    tmFiber30Parent_16_ok,
    tmFiber30Parent_17_ok,
    tmFiber30Parent_18_ok,
    tmFiber30Parent_19_ok,
    tmFiber30Parent_20_ok,
    tmFiber30Parent_21_ok,
    tmFiber30Parent_22_ok,
    tmFiber30Parent_23_ok,
    tmFiber30Parent_24_ok,
    tmFiber30Parent_25_ok,
    tmFiber30Parent_26_ok,
    tmFiber30Parent_27_ok,
    tmFiber30Parent_28_ok,
    tmFiber30Parent_29_ok,
    tmFiber30Parent_30_ok,
    tmFiber30Parent_31_ok,
    tmFiber30Parent_32_ok,
    tmFiber30Parent_33_ok,
    tmFiber30Parent_34_ok,
    tmFiber30Parent_35_ok,
    tmFiber30Parent_36_ok,
    tmFiber30Parent_37_ok,
    tmFiber30Parent_38_ok,
    tmFiber30Parent_39_ok,
    tmFiber30Parent_40_ok,
    tmFiber30Parent_41_ok,
    tmFiber30Parent_42_ok,
    tmFiber30Parent_43_ok,
    tmFiber30Parent_44_ok,
    tmFiber30Parent_45_ok,
    tmFiber30Parent_46_ok,
    tmFiber30Parent_47_ok,
    tmFiber30Parent_48_ok,
    tmFiber30Parent_49_ok,
    tmFiber30Parent_50_ok,
    tmFiber30Parent_51_ok,
    tmFiber30Parent_52_ok,
    tmFiber30Parent_53_ok,
    tmFiber30Parent_54_ok,
    tmFiber30Parent_55_ok,
    tmFiber30Parent_56_ok,
    tmFiber30Parent_57_ok,
    tmFiber30Parent_58_ok,
    tmFiber30Parent_59_ok,
    tmFiber30Parent_60_ok,
    tmFiber30Parent_61_ok,
    tmFiber30Parent_62_ok,
    tmFiber30Parent_63_ok]

def tmFiber31Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.b]

def tmFiber31Expected : List Nat :=
  [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]

def tmFiber31Rows : List DirectChainParentRow :=
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

def tmFiber31RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber31Rows i default

def tmFiber31SourcesCheck : Bool :=
  (tmFiber31Rows.map fun row => row.source) == tmFiber31Expected

theorem tmFiber31SourcesCheck_ok :
    tmFiber31SourcesCheck = true := by
  decide

def tmFiber31RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt i)

theorem tmFiber31Row_0_ok : tmFiber31RowCheck 0 = true := by decide
theorem tmFiber31Row_1_ok : tmFiber31RowCheck 1 = true := by decide
theorem tmFiber31Row_2_ok : tmFiber31RowCheck 2 = true := by decide
theorem tmFiber31Row_3_ok : tmFiber31RowCheck 3 = true := by decide
theorem tmFiber31Row_4_ok : tmFiber31RowCheck 4 = true := by decide
theorem tmFiber31Row_5_ok : tmFiber31RowCheck 5 = true := by decide
theorem tmFiber31Row_6_ok : tmFiber31RowCheck 6 = true := by decide
theorem tmFiber31Row_7_ok : tmFiber31RowCheck 7 = true := by decide
theorem tmFiber31Row_8_ok : tmFiber31RowCheck 8 = true := by decide
theorem tmFiber31Row_9_ok : tmFiber31RowCheck 9 = true := by decide
theorem tmFiber31Row_10_ok : tmFiber31RowCheck 10 = true := by decide
theorem tmFiber31Row_11_ok : tmFiber31RowCheck 11 = true := by decide
theorem tmFiber31Row_12_ok : tmFiber31RowCheck 12 = true := by decide
theorem tmFiber31Row_13_ok : tmFiber31RowCheck 13 = true := by decide
theorem tmFiber31Row_14_ok : tmFiber31RowCheck 14 = true := by decide
theorem tmFiber31Row_15_ok : tmFiber31RowCheck 15 = true := by decide

def tmFiber31ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber31Rows tmMaxParentDepth (listGetD tmFiber31Expected i 0) == 320

theorem tmFiber31Parent_0_ok : tmFiber31ParentCheck 0 = true := by decide
theorem tmFiber31Parent_1_ok : tmFiber31ParentCheck 1 = true := by decide
theorem tmFiber31Parent_2_ok : tmFiber31ParentCheck 2 = true := by decide
theorem tmFiber31Parent_3_ok : tmFiber31ParentCheck 3 = true := by decide
theorem tmFiber31Parent_4_ok : tmFiber31ParentCheck 4 = true := by decide
theorem tmFiber31Parent_5_ok : tmFiber31ParentCheck 5 = true := by decide
theorem tmFiber31Parent_6_ok : tmFiber31ParentCheck 6 = true := by decide
theorem tmFiber31Parent_7_ok : tmFiber31ParentCheck 7 = true := by decide
theorem tmFiber31Parent_8_ok : tmFiber31ParentCheck 8 = true := by decide
theorem tmFiber31Parent_9_ok : tmFiber31ParentCheck 9 = true := by decide
theorem tmFiber31Parent_10_ok : tmFiber31ParentCheck 10 = true := by decide
theorem tmFiber31Parent_11_ok : tmFiber31ParentCheck 11 = true := by decide
theorem tmFiber31Parent_12_ok : tmFiber31ParentCheck 12 = true := by decide
theorem tmFiber31Parent_13_ok : tmFiber31ParentCheck 13 = true := by decide
theorem tmFiber31Parent_14_ok : tmFiber31ParentCheck 14 = true := by decide
theorem tmFiber31Parent_15_ok : tmFiber31ParentCheck 15 = true := by decide

def tmFiber31CertificateAudit : Bool :=
  tmFiber31SourcesCheck &&
    tmFiber31RowCheck 0 &&
    tmFiber31RowCheck 1 &&
    tmFiber31RowCheck 2 &&
    tmFiber31RowCheck 3 &&
    tmFiber31RowCheck 4 &&
    tmFiber31RowCheck 5 &&
    tmFiber31RowCheck 6 &&
    tmFiber31RowCheck 7 &&
    tmFiber31RowCheck 8 &&
    tmFiber31RowCheck 9 &&
    tmFiber31RowCheck 10 &&
    tmFiber31RowCheck 11 &&
    tmFiber31RowCheck 12 &&
    tmFiber31RowCheck 13 &&
    tmFiber31RowCheck 14 &&
    tmFiber31RowCheck 15 &&
    tmFiber31ParentCheck 0 &&
    tmFiber31ParentCheck 1 &&
    tmFiber31ParentCheck 2 &&
    tmFiber31ParentCheck 3 &&
    tmFiber31ParentCheck 4 &&
    tmFiber31ParentCheck 5 &&
    tmFiber31ParentCheck 6 &&
    tmFiber31ParentCheck 7 &&
    tmFiber31ParentCheck 8 &&
    tmFiber31ParentCheck 9 &&
    tmFiber31ParentCheck 10 &&
    tmFiber31ParentCheck 11 &&
    tmFiber31ParentCheck 12 &&
    tmFiber31ParentCheck 13 &&
    tmFiber31ParentCheck 14 &&
    tmFiber31ParentCheck 15

theorem tmFiber31CertificateAudit_ok :
    tmFiber31CertificateAudit = true := by
  simp [tmFiber31CertificateAudit,
    tmFiber31SourcesCheck_ok,
    tmFiber31Row_0_ok,
    tmFiber31Row_1_ok,
    tmFiber31Row_2_ok,
    tmFiber31Row_3_ok,
    tmFiber31Row_4_ok,
    tmFiber31Row_5_ok,
    tmFiber31Row_6_ok,
    tmFiber31Row_7_ok,
    tmFiber31Row_8_ok,
    tmFiber31Row_9_ok,
    tmFiber31Row_10_ok,
    tmFiber31Row_11_ok,
    tmFiber31Row_12_ok,
    tmFiber31Row_13_ok,
    tmFiber31Row_14_ok,
    tmFiber31Row_15_ok,
    tmFiber31Parent_0_ok,
    tmFiber31Parent_1_ok,
    tmFiber31Parent_2_ok,
    tmFiber31Parent_3_ok,
    tmFiber31Parent_4_ok,
    tmFiber31Parent_5_ok,
    tmFiber31Parent_6_ok,
    tmFiber31Parent_7_ok,
    tmFiber31Parent_8_ok,
    tmFiber31Parent_9_ok,
    tmFiber31Parent_10_ok,
    tmFiber31Parent_11_ok,
    tmFiber31Parent_12_ok,
    tmFiber31Parent_13_ok,
    tmFiber31Parent_14_ok,
    tmFiber31Parent_15_ok]

def tmFiber32Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.p]

def tmFiber32Expected : List Nat :=
  [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

def tmFiber32Rows : List DirectChainParentRow :=
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

def tmFiber32RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber32Rows i default

def tmFiber32SourcesCheck : Bool :=
  (tmFiber32Rows.map fun row => row.source) == tmFiber32Expected

theorem tmFiber32SourcesCheck_ok :
    tmFiber32SourcesCheck = true := by
  decide

def tmFiber32RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt i)

theorem tmFiber32Row_0_ok : tmFiber32RowCheck 0 = true := by decide
theorem tmFiber32Row_1_ok : tmFiber32RowCheck 1 = true := by decide
theorem tmFiber32Row_2_ok : tmFiber32RowCheck 2 = true := by decide
theorem tmFiber32Row_3_ok : tmFiber32RowCheck 3 = true := by decide
theorem tmFiber32Row_4_ok : tmFiber32RowCheck 4 = true := by decide
theorem tmFiber32Row_5_ok : tmFiber32RowCheck 5 = true := by decide
theorem tmFiber32Row_6_ok : tmFiber32RowCheck 6 = true := by decide
theorem tmFiber32Row_7_ok : tmFiber32RowCheck 7 = true := by decide
theorem tmFiber32Row_8_ok : tmFiber32RowCheck 8 = true := by decide
theorem tmFiber32Row_9_ok : tmFiber32RowCheck 9 = true := by decide
theorem tmFiber32Row_10_ok : tmFiber32RowCheck 10 = true := by decide
theorem tmFiber32Row_11_ok : tmFiber32RowCheck 11 = true := by decide
theorem tmFiber32Row_12_ok : tmFiber32RowCheck 12 = true := by decide
theorem tmFiber32Row_13_ok : tmFiber32RowCheck 13 = true := by decide
theorem tmFiber32Row_14_ok : tmFiber32RowCheck 14 = true := by decide
theorem tmFiber32Row_15_ok : tmFiber32RowCheck 15 = true := by decide

def tmFiber32ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber32Rows tmMaxParentDepth (listGetD tmFiber32Expected i 0) == 32

theorem tmFiber32Parent_0_ok : tmFiber32ParentCheck 0 = true := by decide
theorem tmFiber32Parent_1_ok : tmFiber32ParentCheck 1 = true := by decide
theorem tmFiber32Parent_2_ok : tmFiber32ParentCheck 2 = true := by decide
theorem tmFiber32Parent_3_ok : tmFiber32ParentCheck 3 = true := by decide
theorem tmFiber32Parent_4_ok : tmFiber32ParentCheck 4 = true := by decide
theorem tmFiber32Parent_5_ok : tmFiber32ParentCheck 5 = true := by decide
theorem tmFiber32Parent_6_ok : tmFiber32ParentCheck 6 = true := by decide
theorem tmFiber32Parent_7_ok : tmFiber32ParentCheck 7 = true := by decide
theorem tmFiber32Parent_8_ok : tmFiber32ParentCheck 8 = true := by decide
theorem tmFiber32Parent_9_ok : tmFiber32ParentCheck 9 = true := by decide
theorem tmFiber32Parent_10_ok : tmFiber32ParentCheck 10 = true := by decide
theorem tmFiber32Parent_11_ok : tmFiber32ParentCheck 11 = true := by decide
theorem tmFiber32Parent_12_ok : tmFiber32ParentCheck 12 = true := by decide
theorem tmFiber32Parent_13_ok : tmFiber32ParentCheck 13 = true := by decide
theorem tmFiber32Parent_14_ok : tmFiber32ParentCheck 14 = true := by decide
theorem tmFiber32Parent_15_ok : tmFiber32ParentCheck 15 = true := by decide

def tmFiber32CertificateAudit : Bool :=
  tmFiber32SourcesCheck &&
    tmFiber32RowCheck 0 &&
    tmFiber32RowCheck 1 &&
    tmFiber32RowCheck 2 &&
    tmFiber32RowCheck 3 &&
    tmFiber32RowCheck 4 &&
    tmFiber32RowCheck 5 &&
    tmFiber32RowCheck 6 &&
    tmFiber32RowCheck 7 &&
    tmFiber32RowCheck 8 &&
    tmFiber32RowCheck 9 &&
    tmFiber32RowCheck 10 &&
    tmFiber32RowCheck 11 &&
    tmFiber32RowCheck 12 &&
    tmFiber32RowCheck 13 &&
    tmFiber32RowCheck 14 &&
    tmFiber32RowCheck 15 &&
    tmFiber32ParentCheck 0 &&
    tmFiber32ParentCheck 1 &&
    tmFiber32ParentCheck 2 &&
    tmFiber32ParentCheck 3 &&
    tmFiber32ParentCheck 4 &&
    tmFiber32ParentCheck 5 &&
    tmFiber32ParentCheck 6 &&
    tmFiber32ParentCheck 7 &&
    tmFiber32ParentCheck 8 &&
    tmFiber32ParentCheck 9 &&
    tmFiber32ParentCheck 10 &&
    tmFiber32ParentCheck 11 &&
    tmFiber32ParentCheck 12 &&
    tmFiber32ParentCheck 13 &&
    tmFiber32ParentCheck 14 &&
    tmFiber32ParentCheck 15

theorem tmFiber32CertificateAudit_ok :
    tmFiber32CertificateAudit = true := by
  simp [tmFiber32CertificateAudit,
    tmFiber32SourcesCheck_ok,
    tmFiber32Row_0_ok,
    tmFiber32Row_1_ok,
    tmFiber32Row_2_ok,
    tmFiber32Row_3_ok,
    tmFiber32Row_4_ok,
    tmFiber32Row_5_ok,
    tmFiber32Row_6_ok,
    tmFiber32Row_7_ok,
    tmFiber32Row_8_ok,
    tmFiber32Row_9_ok,
    tmFiber32Row_10_ok,
    tmFiber32Row_11_ok,
    tmFiber32Row_12_ok,
    tmFiber32Row_13_ok,
    tmFiber32Row_14_ok,
    tmFiber32Row_15_ok,
    tmFiber32Parent_0_ok,
    tmFiber32Parent_1_ok,
    tmFiber32Parent_2_ok,
    tmFiber32Parent_3_ok,
    tmFiber32Parent_4_ok,
    tmFiber32Parent_5_ok,
    tmFiber32Parent_6_ok,
    tmFiber32Parent_7_ok,
    tmFiber32Parent_8_ok,
    tmFiber32Parent_9_ok,
    tmFiber32Parent_10_ok,
    tmFiber32Parent_11_ok,
    tmFiber32Parent_12_ok,
    tmFiber32Parent_13_ok,
    tmFiber32Parent_14_ok,
    tmFiber32Parent_15_ok]

def tmFiber33Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.r]

def tmFiber33Expected : List Nat :=
  []

def tmFiber33Rows : List DirectChainParentRow :=
  []

def tmFiber33RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber33Rows i default

def tmFiber33SourcesCheck : Bool :=
  (tmFiber33Rows.map fun row => row.source) == tmFiber33Expected

theorem tmFiber33SourcesCheck_ok :
    tmFiber33SourcesCheck = true := by
  decide

def tmFiber33RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber33Key tmFiber33Expected (tmFiber33RowAt i)

def tmFiber33ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber33Rows tmMaxParentDepth (listGetD tmFiber33Expected i 0) == 0

def tmFiber33CertificateAudit : Bool :=
  tmFiber33SourcesCheck

theorem tmFiber33CertificateAudit_ok :
    tmFiber33CertificateAudit = true := by
  simp [tmFiber33CertificateAudit,
    tmFiber33SourcesCheck_ok]

def tmFiber34Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.b]

def tmFiber34Expected : List Nat :=
  []

def tmFiber34Rows : List DirectChainParentRow :=
  []

def tmFiber34RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber34Rows i default

def tmFiber34SourcesCheck : Bool :=
  (tmFiber34Rows.map fun row => row.source) == tmFiber34Expected

theorem tmFiber34SourcesCheck_ok :
    tmFiber34SourcesCheck = true := by
  decide

def tmFiber34RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber34Key tmFiber34Expected (tmFiber34RowAt i)

def tmFiber34ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber34Rows tmMaxParentDepth (listGetD tmFiber34Expected i 0) == 0

def tmFiber34CertificateAudit : Bool :=
  tmFiber34SourcesCheck

theorem tmFiber34CertificateAudit_ok :
    tmFiber34CertificateAudit = true := by
  simp [tmFiber34CertificateAudit,
    tmFiber34SourcesCheck_ok]

def tmFiber35Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.p]

def tmFiber35Expected : List Nat :=
  []

def tmFiber35Rows : List DirectChainParentRow :=
  []

def tmFiber35RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber35Rows i default

def tmFiber35SourcesCheck : Bool :=
  (tmFiber35Rows.map fun row => row.source) == tmFiber35Expected

theorem tmFiber35SourcesCheck_ok :
    tmFiber35SourcesCheck = true := by
  decide

def tmFiber35RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber35Key tmFiber35Expected (tmFiber35RowAt i)

def tmFiber35ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber35Rows tmMaxParentDepth (listGetD tmFiber35Expected i 0) == 0

def tmFiber35CertificateAudit : Bool :=
  tmFiber35SourcesCheck

theorem tmFiber35CertificateAudit_ok :
    tmFiber35CertificateAudit = true := by
  simp [tmFiber35CertificateAudit,
    tmFiber35SourcesCheck_ok]

def tmFiber36Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.r]

def tmFiber36Expected : List Nat :=
  [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]

def tmFiber36Rows : List DirectChainParentRow :=
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

def tmFiber36RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber36Rows i default

def tmFiber36SourcesCheck : Bool :=
  (tmFiber36Rows.map fun row => row.source) == tmFiber36Expected

theorem tmFiber36SourcesCheck_ok :
    tmFiber36SourcesCheck = true := by
  decide

def tmFiber36RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber36Key tmFiber36Expected (tmFiber36RowAt i)

theorem tmFiber36Row_0_ok : tmFiber36RowCheck 0 = true := by decide
theorem tmFiber36Row_1_ok : tmFiber36RowCheck 1 = true := by decide
theorem tmFiber36Row_2_ok : tmFiber36RowCheck 2 = true := by decide
theorem tmFiber36Row_3_ok : tmFiber36RowCheck 3 = true := by decide
theorem tmFiber36Row_4_ok : tmFiber36RowCheck 4 = true := by decide
theorem tmFiber36Row_5_ok : tmFiber36RowCheck 5 = true := by decide
theorem tmFiber36Row_6_ok : tmFiber36RowCheck 6 = true := by decide
theorem tmFiber36Row_7_ok : tmFiber36RowCheck 7 = true := by decide
theorem tmFiber36Row_8_ok : tmFiber36RowCheck 8 = true := by decide
theorem tmFiber36Row_9_ok : tmFiber36RowCheck 9 = true := by decide
theorem tmFiber36Row_10_ok : tmFiber36RowCheck 10 = true := by decide
theorem tmFiber36Row_11_ok : tmFiber36RowCheck 11 = true := by decide
theorem tmFiber36Row_12_ok : tmFiber36RowCheck 12 = true := by decide
theorem tmFiber36Row_13_ok : tmFiber36RowCheck 13 = true := by decide
theorem tmFiber36Row_14_ok : tmFiber36RowCheck 14 = true := by decide
theorem tmFiber36Row_15_ok : tmFiber36RowCheck 15 = true := by decide
theorem tmFiber36Row_16_ok : tmFiber36RowCheck 16 = true := by decide
theorem tmFiber36Row_17_ok : tmFiber36RowCheck 17 = true := by decide
theorem tmFiber36Row_18_ok : tmFiber36RowCheck 18 = true := by decide
theorem tmFiber36Row_19_ok : tmFiber36RowCheck 19 = true := by decide
theorem tmFiber36Row_20_ok : tmFiber36RowCheck 20 = true := by decide
theorem tmFiber36Row_21_ok : tmFiber36RowCheck 21 = true := by decide
theorem tmFiber36Row_22_ok : tmFiber36RowCheck 22 = true := by decide
theorem tmFiber36Row_23_ok : tmFiber36RowCheck 23 = true := by decide
theorem tmFiber36Row_24_ok : tmFiber36RowCheck 24 = true := by decide
theorem tmFiber36Row_25_ok : tmFiber36RowCheck 25 = true := by decide
theorem tmFiber36Row_26_ok : tmFiber36RowCheck 26 = true := by decide
theorem tmFiber36Row_27_ok : tmFiber36RowCheck 27 = true := by decide
theorem tmFiber36Row_28_ok : tmFiber36RowCheck 28 = true := by decide
theorem tmFiber36Row_29_ok : tmFiber36RowCheck 29 = true := by decide
theorem tmFiber36Row_30_ok : tmFiber36RowCheck 30 = true := by decide
theorem tmFiber36Row_31_ok : tmFiber36RowCheck 31 = true := by decide
theorem tmFiber36Row_32_ok : tmFiber36RowCheck 32 = true := by decide
theorem tmFiber36Row_33_ok : tmFiber36RowCheck 33 = true := by decide
theorem tmFiber36Row_34_ok : tmFiber36RowCheck 34 = true := by decide
theorem tmFiber36Row_35_ok : tmFiber36RowCheck 35 = true := by decide
theorem tmFiber36Row_36_ok : tmFiber36RowCheck 36 = true := by decide
theorem tmFiber36Row_37_ok : tmFiber36RowCheck 37 = true := by decide
theorem tmFiber36Row_38_ok : tmFiber36RowCheck 38 = true := by decide
theorem tmFiber36Row_39_ok : tmFiber36RowCheck 39 = true := by decide
theorem tmFiber36Row_40_ok : tmFiber36RowCheck 40 = true := by decide
theorem tmFiber36Row_41_ok : tmFiber36RowCheck 41 = true := by decide
theorem tmFiber36Row_42_ok : tmFiber36RowCheck 42 = true := by decide
theorem tmFiber36Row_43_ok : tmFiber36RowCheck 43 = true := by decide
theorem tmFiber36Row_44_ok : tmFiber36RowCheck 44 = true := by decide
theorem tmFiber36Row_45_ok : tmFiber36RowCheck 45 = true := by decide
theorem tmFiber36Row_46_ok : tmFiber36RowCheck 46 = true := by decide
theorem tmFiber36Row_47_ok : tmFiber36RowCheck 47 = true := by decide
theorem tmFiber36Row_48_ok : tmFiber36RowCheck 48 = true := by decide
theorem tmFiber36Row_49_ok : tmFiber36RowCheck 49 = true := by decide
theorem tmFiber36Row_50_ok : tmFiber36RowCheck 50 = true := by decide
theorem tmFiber36Row_51_ok : tmFiber36RowCheck 51 = true := by decide
theorem tmFiber36Row_52_ok : tmFiber36RowCheck 52 = true := by decide
theorem tmFiber36Row_53_ok : tmFiber36RowCheck 53 = true := by decide
theorem tmFiber36Row_54_ok : tmFiber36RowCheck 54 = true := by decide
theorem tmFiber36Row_55_ok : tmFiber36RowCheck 55 = true := by decide
theorem tmFiber36Row_56_ok : tmFiber36RowCheck 56 = true := by decide
theorem tmFiber36Row_57_ok : tmFiber36RowCheck 57 = true := by decide
theorem tmFiber36Row_58_ok : tmFiber36RowCheck 58 = true := by decide
theorem tmFiber36Row_59_ok : tmFiber36RowCheck 59 = true := by decide
theorem tmFiber36Row_60_ok : tmFiber36RowCheck 60 = true := by decide
theorem tmFiber36Row_61_ok : tmFiber36RowCheck 61 = true := by decide
theorem tmFiber36Row_62_ok : tmFiber36RowCheck 62 = true := by decide
theorem tmFiber36Row_63_ok : tmFiber36RowCheck 63 = true := by decide

def tmFiber36ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber36Rows tmMaxParentDepth (listGetD tmFiber36Expected i 0) == 48

theorem tmFiber36Parent_0_ok : tmFiber36ParentCheck 0 = true := by decide
theorem tmFiber36Parent_1_ok : tmFiber36ParentCheck 1 = true := by decide
theorem tmFiber36Parent_2_ok : tmFiber36ParentCheck 2 = true := by decide
theorem tmFiber36Parent_3_ok : tmFiber36ParentCheck 3 = true := by decide
theorem tmFiber36Parent_4_ok : tmFiber36ParentCheck 4 = true := by decide
theorem tmFiber36Parent_5_ok : tmFiber36ParentCheck 5 = true := by decide
theorem tmFiber36Parent_6_ok : tmFiber36ParentCheck 6 = true := by decide
theorem tmFiber36Parent_7_ok : tmFiber36ParentCheck 7 = true := by decide
theorem tmFiber36Parent_8_ok : tmFiber36ParentCheck 8 = true := by decide
theorem tmFiber36Parent_9_ok : tmFiber36ParentCheck 9 = true := by decide
theorem tmFiber36Parent_10_ok : tmFiber36ParentCheck 10 = true := by decide
theorem tmFiber36Parent_11_ok : tmFiber36ParentCheck 11 = true := by decide
theorem tmFiber36Parent_12_ok : tmFiber36ParentCheck 12 = true := by decide
theorem tmFiber36Parent_13_ok : tmFiber36ParentCheck 13 = true := by decide
theorem tmFiber36Parent_14_ok : tmFiber36ParentCheck 14 = true := by decide
theorem tmFiber36Parent_15_ok : tmFiber36ParentCheck 15 = true := by decide
theorem tmFiber36Parent_16_ok : tmFiber36ParentCheck 16 = true := by decide
theorem tmFiber36Parent_17_ok : tmFiber36ParentCheck 17 = true := by decide
theorem tmFiber36Parent_18_ok : tmFiber36ParentCheck 18 = true := by decide
theorem tmFiber36Parent_19_ok : tmFiber36ParentCheck 19 = true := by decide
theorem tmFiber36Parent_20_ok : tmFiber36ParentCheck 20 = true := by decide
theorem tmFiber36Parent_21_ok : tmFiber36ParentCheck 21 = true := by decide
theorem tmFiber36Parent_22_ok : tmFiber36ParentCheck 22 = true := by decide
theorem tmFiber36Parent_23_ok : tmFiber36ParentCheck 23 = true := by decide
theorem tmFiber36Parent_24_ok : tmFiber36ParentCheck 24 = true := by decide
theorem tmFiber36Parent_25_ok : tmFiber36ParentCheck 25 = true := by decide
theorem tmFiber36Parent_26_ok : tmFiber36ParentCheck 26 = true := by decide
theorem tmFiber36Parent_27_ok : tmFiber36ParentCheck 27 = true := by decide
theorem tmFiber36Parent_28_ok : tmFiber36ParentCheck 28 = true := by decide
theorem tmFiber36Parent_29_ok : tmFiber36ParentCheck 29 = true := by decide
theorem tmFiber36Parent_30_ok : tmFiber36ParentCheck 30 = true := by decide
theorem tmFiber36Parent_31_ok : tmFiber36ParentCheck 31 = true := by decide
theorem tmFiber36Parent_32_ok : tmFiber36ParentCheck 32 = true := by decide
theorem tmFiber36Parent_33_ok : tmFiber36ParentCheck 33 = true := by decide
theorem tmFiber36Parent_34_ok : tmFiber36ParentCheck 34 = true := by decide
theorem tmFiber36Parent_35_ok : tmFiber36ParentCheck 35 = true := by decide
theorem tmFiber36Parent_36_ok : tmFiber36ParentCheck 36 = true := by decide
theorem tmFiber36Parent_37_ok : tmFiber36ParentCheck 37 = true := by decide
theorem tmFiber36Parent_38_ok : tmFiber36ParentCheck 38 = true := by decide
theorem tmFiber36Parent_39_ok : tmFiber36ParentCheck 39 = true := by decide
theorem tmFiber36Parent_40_ok : tmFiber36ParentCheck 40 = true := by decide
theorem tmFiber36Parent_41_ok : tmFiber36ParentCheck 41 = true := by decide
theorem tmFiber36Parent_42_ok : tmFiber36ParentCheck 42 = true := by decide
theorem tmFiber36Parent_43_ok : tmFiber36ParentCheck 43 = true := by decide
theorem tmFiber36Parent_44_ok : tmFiber36ParentCheck 44 = true := by decide
theorem tmFiber36Parent_45_ok : tmFiber36ParentCheck 45 = true := by decide
theorem tmFiber36Parent_46_ok : tmFiber36ParentCheck 46 = true := by decide
theorem tmFiber36Parent_47_ok : tmFiber36ParentCheck 47 = true := by decide
theorem tmFiber36Parent_48_ok : tmFiber36ParentCheck 48 = true := by decide
theorem tmFiber36Parent_49_ok : tmFiber36ParentCheck 49 = true := by decide
theorem tmFiber36Parent_50_ok : tmFiber36ParentCheck 50 = true := by decide
theorem tmFiber36Parent_51_ok : tmFiber36ParentCheck 51 = true := by decide
theorem tmFiber36Parent_52_ok : tmFiber36ParentCheck 52 = true := by decide
theorem tmFiber36Parent_53_ok : tmFiber36ParentCheck 53 = true := by decide
theorem tmFiber36Parent_54_ok : tmFiber36ParentCheck 54 = true := by decide
theorem tmFiber36Parent_55_ok : tmFiber36ParentCheck 55 = true := by decide
theorem tmFiber36Parent_56_ok : tmFiber36ParentCheck 56 = true := by decide
theorem tmFiber36Parent_57_ok : tmFiber36ParentCheck 57 = true := by decide
theorem tmFiber36Parent_58_ok : tmFiber36ParentCheck 58 = true := by decide
theorem tmFiber36Parent_59_ok : tmFiber36ParentCheck 59 = true := by decide
theorem tmFiber36Parent_60_ok : tmFiber36ParentCheck 60 = true := by decide
theorem tmFiber36Parent_61_ok : tmFiber36ParentCheck 61 = true := by decide
theorem tmFiber36Parent_62_ok : tmFiber36ParentCheck 62 = true := by decide
theorem tmFiber36Parent_63_ok : tmFiber36ParentCheck 63 = true := by decide

def tmFiber36CertificateAudit : Bool :=
  tmFiber36SourcesCheck &&
    tmFiber36RowCheck 0 &&
    tmFiber36RowCheck 1 &&
    tmFiber36RowCheck 2 &&
    tmFiber36RowCheck 3 &&
    tmFiber36RowCheck 4 &&
    tmFiber36RowCheck 5 &&
    tmFiber36RowCheck 6 &&
    tmFiber36RowCheck 7 &&
    tmFiber36RowCheck 8 &&
    tmFiber36RowCheck 9 &&
    tmFiber36RowCheck 10 &&
    tmFiber36RowCheck 11 &&
    tmFiber36RowCheck 12 &&
    tmFiber36RowCheck 13 &&
    tmFiber36RowCheck 14 &&
    tmFiber36RowCheck 15 &&
    tmFiber36RowCheck 16 &&
    tmFiber36RowCheck 17 &&
    tmFiber36RowCheck 18 &&
    tmFiber36RowCheck 19 &&
    tmFiber36RowCheck 20 &&
    tmFiber36RowCheck 21 &&
    tmFiber36RowCheck 22 &&
    tmFiber36RowCheck 23 &&
    tmFiber36RowCheck 24 &&
    tmFiber36RowCheck 25 &&
    tmFiber36RowCheck 26 &&
    tmFiber36RowCheck 27 &&
    tmFiber36RowCheck 28 &&
    tmFiber36RowCheck 29 &&
    tmFiber36RowCheck 30 &&
    tmFiber36RowCheck 31 &&
    tmFiber36RowCheck 32 &&
    tmFiber36RowCheck 33 &&
    tmFiber36RowCheck 34 &&
    tmFiber36RowCheck 35 &&
    tmFiber36RowCheck 36 &&
    tmFiber36RowCheck 37 &&
    tmFiber36RowCheck 38 &&
    tmFiber36RowCheck 39 &&
    tmFiber36RowCheck 40 &&
    tmFiber36RowCheck 41 &&
    tmFiber36RowCheck 42 &&
    tmFiber36RowCheck 43 &&
    tmFiber36RowCheck 44 &&
    tmFiber36RowCheck 45 &&
    tmFiber36RowCheck 46 &&
    tmFiber36RowCheck 47 &&
    tmFiber36RowCheck 48 &&
    tmFiber36RowCheck 49 &&
    tmFiber36RowCheck 50 &&
    tmFiber36RowCheck 51 &&
    tmFiber36RowCheck 52 &&
    tmFiber36RowCheck 53 &&
    tmFiber36RowCheck 54 &&
    tmFiber36RowCheck 55 &&
    tmFiber36RowCheck 56 &&
    tmFiber36RowCheck 57 &&
    tmFiber36RowCheck 58 &&
    tmFiber36RowCheck 59 &&
    tmFiber36RowCheck 60 &&
    tmFiber36RowCheck 61 &&
    tmFiber36RowCheck 62 &&
    tmFiber36RowCheck 63 &&
    tmFiber36ParentCheck 0 &&
    tmFiber36ParentCheck 1 &&
    tmFiber36ParentCheck 2 &&
    tmFiber36ParentCheck 3 &&
    tmFiber36ParentCheck 4 &&
    tmFiber36ParentCheck 5 &&
    tmFiber36ParentCheck 6 &&
    tmFiber36ParentCheck 7 &&
    tmFiber36ParentCheck 8 &&
    tmFiber36ParentCheck 9 &&
    tmFiber36ParentCheck 10 &&
    tmFiber36ParentCheck 11 &&
    tmFiber36ParentCheck 12 &&
    tmFiber36ParentCheck 13 &&
    tmFiber36ParentCheck 14 &&
    tmFiber36ParentCheck 15 &&
    tmFiber36ParentCheck 16 &&
    tmFiber36ParentCheck 17 &&
    tmFiber36ParentCheck 18 &&
    tmFiber36ParentCheck 19 &&
    tmFiber36ParentCheck 20 &&
    tmFiber36ParentCheck 21 &&
    tmFiber36ParentCheck 22 &&
    tmFiber36ParentCheck 23 &&
    tmFiber36ParentCheck 24 &&
    tmFiber36ParentCheck 25 &&
    tmFiber36ParentCheck 26 &&
    tmFiber36ParentCheck 27 &&
    tmFiber36ParentCheck 28 &&
    tmFiber36ParentCheck 29 &&
    tmFiber36ParentCheck 30 &&
    tmFiber36ParentCheck 31 &&
    tmFiber36ParentCheck 32 &&
    tmFiber36ParentCheck 33 &&
    tmFiber36ParentCheck 34 &&
    tmFiber36ParentCheck 35 &&
    tmFiber36ParentCheck 36 &&
    tmFiber36ParentCheck 37 &&
    tmFiber36ParentCheck 38 &&
    tmFiber36ParentCheck 39 &&
    tmFiber36ParentCheck 40 &&
    tmFiber36ParentCheck 41 &&
    tmFiber36ParentCheck 42 &&
    tmFiber36ParentCheck 43 &&
    tmFiber36ParentCheck 44 &&
    tmFiber36ParentCheck 45 &&
    tmFiber36ParentCheck 46 &&
    tmFiber36ParentCheck 47 &&
    tmFiber36ParentCheck 48 &&
    tmFiber36ParentCheck 49 &&
    tmFiber36ParentCheck 50 &&
    tmFiber36ParentCheck 51 &&
    tmFiber36ParentCheck 52 &&
    tmFiber36ParentCheck 53 &&
    tmFiber36ParentCheck 54 &&
    tmFiber36ParentCheck 55 &&
    tmFiber36ParentCheck 56 &&
    tmFiber36ParentCheck 57 &&
    tmFiber36ParentCheck 58 &&
    tmFiber36ParentCheck 59 &&
    tmFiber36ParentCheck 60 &&
    tmFiber36ParentCheck 61 &&
    tmFiber36ParentCheck 62 &&
    tmFiber36ParentCheck 63

theorem tmFiber36CertificateAudit_ok :
    tmFiber36CertificateAudit = true := by
  simp [tmFiber36CertificateAudit,
    tmFiber36SourcesCheck_ok,
    tmFiber36Row_0_ok,
    tmFiber36Row_1_ok,
    tmFiber36Row_2_ok,
    tmFiber36Row_3_ok,
    tmFiber36Row_4_ok,
    tmFiber36Row_5_ok,
    tmFiber36Row_6_ok,
    tmFiber36Row_7_ok,
    tmFiber36Row_8_ok,
    tmFiber36Row_9_ok,
    tmFiber36Row_10_ok,
    tmFiber36Row_11_ok,
    tmFiber36Row_12_ok,
    tmFiber36Row_13_ok,
    tmFiber36Row_14_ok,
    tmFiber36Row_15_ok,
    tmFiber36Row_16_ok,
    tmFiber36Row_17_ok,
    tmFiber36Row_18_ok,
    tmFiber36Row_19_ok,
    tmFiber36Row_20_ok,
    tmFiber36Row_21_ok,
    tmFiber36Row_22_ok,
    tmFiber36Row_23_ok,
    tmFiber36Row_24_ok,
    tmFiber36Row_25_ok,
    tmFiber36Row_26_ok,
    tmFiber36Row_27_ok,
    tmFiber36Row_28_ok,
    tmFiber36Row_29_ok,
    tmFiber36Row_30_ok,
    tmFiber36Row_31_ok,
    tmFiber36Row_32_ok,
    tmFiber36Row_33_ok,
    tmFiber36Row_34_ok,
    tmFiber36Row_35_ok,
    tmFiber36Row_36_ok,
    tmFiber36Row_37_ok,
    tmFiber36Row_38_ok,
    tmFiber36Row_39_ok,
    tmFiber36Row_40_ok,
    tmFiber36Row_41_ok,
    tmFiber36Row_42_ok,
    tmFiber36Row_43_ok,
    tmFiber36Row_44_ok,
    tmFiber36Row_45_ok,
    tmFiber36Row_46_ok,
    tmFiber36Row_47_ok,
    tmFiber36Row_48_ok,
    tmFiber36Row_49_ok,
    tmFiber36Row_50_ok,
    tmFiber36Row_51_ok,
    tmFiber36Row_52_ok,
    tmFiber36Row_53_ok,
    tmFiber36Row_54_ok,
    tmFiber36Row_55_ok,
    tmFiber36Row_56_ok,
    tmFiber36Row_57_ok,
    tmFiber36Row_58_ok,
    tmFiber36Row_59_ok,
    tmFiber36Row_60_ok,
    tmFiber36Row_61_ok,
    tmFiber36Row_62_ok,
    tmFiber36Row_63_ok,
    tmFiber36Parent_0_ok,
    tmFiber36Parent_1_ok,
    tmFiber36Parent_2_ok,
    tmFiber36Parent_3_ok,
    tmFiber36Parent_4_ok,
    tmFiber36Parent_5_ok,
    tmFiber36Parent_6_ok,
    tmFiber36Parent_7_ok,
    tmFiber36Parent_8_ok,
    tmFiber36Parent_9_ok,
    tmFiber36Parent_10_ok,
    tmFiber36Parent_11_ok,
    tmFiber36Parent_12_ok,
    tmFiber36Parent_13_ok,
    tmFiber36Parent_14_ok,
    tmFiber36Parent_15_ok,
    tmFiber36Parent_16_ok,
    tmFiber36Parent_17_ok,
    tmFiber36Parent_18_ok,
    tmFiber36Parent_19_ok,
    tmFiber36Parent_20_ok,
    tmFiber36Parent_21_ok,
    tmFiber36Parent_22_ok,
    tmFiber36Parent_23_ok,
    tmFiber36Parent_24_ok,
    tmFiber36Parent_25_ok,
    tmFiber36Parent_26_ok,
    tmFiber36Parent_27_ok,
    tmFiber36Parent_28_ok,
    tmFiber36Parent_29_ok,
    tmFiber36Parent_30_ok,
    tmFiber36Parent_31_ok,
    tmFiber36Parent_32_ok,
    tmFiber36Parent_33_ok,
    tmFiber36Parent_34_ok,
    tmFiber36Parent_35_ok,
    tmFiber36Parent_36_ok,
    tmFiber36Parent_37_ok,
    tmFiber36Parent_38_ok,
    tmFiber36Parent_39_ok,
    tmFiber36Parent_40_ok,
    tmFiber36Parent_41_ok,
    tmFiber36Parent_42_ok,
    tmFiber36Parent_43_ok,
    tmFiber36Parent_44_ok,
    tmFiber36Parent_45_ok,
    tmFiber36Parent_46_ok,
    tmFiber36Parent_47_ok,
    tmFiber36Parent_48_ok,
    tmFiber36Parent_49_ok,
    tmFiber36Parent_50_ok,
    tmFiber36Parent_51_ok,
    tmFiber36Parent_52_ok,
    tmFiber36Parent_53_ok,
    tmFiber36Parent_54_ok,
    tmFiber36Parent_55_ok,
    tmFiber36Parent_56_ok,
    tmFiber36Parent_57_ok,
    tmFiber36Parent_58_ok,
    tmFiber36Parent_59_ok,
    tmFiber36Parent_60_ok,
    tmFiber36Parent_61_ok,
    tmFiber36Parent_62_ok,
    tmFiber36Parent_63_ok]

def tmFiber37Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.b]

def tmFiber37Expected : List Nat :=
  [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]

def tmFiber37Rows : List DirectChainParentRow :=
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

def tmFiber37RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber37Rows i default

def tmFiber37SourcesCheck : Bool :=
  (tmFiber37Rows.map fun row => row.source) == tmFiber37Expected

theorem tmFiber37SourcesCheck_ok :
    tmFiber37SourcesCheck = true := by
  decide

def tmFiber37RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt i)

theorem tmFiber37Row_0_ok : tmFiber37RowCheck 0 = true := by decide
theorem tmFiber37Row_1_ok : tmFiber37RowCheck 1 = true := by decide
theorem tmFiber37Row_2_ok : tmFiber37RowCheck 2 = true := by decide
theorem tmFiber37Row_3_ok : tmFiber37RowCheck 3 = true := by decide
theorem tmFiber37Row_4_ok : tmFiber37RowCheck 4 = true := by decide
theorem tmFiber37Row_5_ok : tmFiber37RowCheck 5 = true := by decide
theorem tmFiber37Row_6_ok : tmFiber37RowCheck 6 = true := by decide
theorem tmFiber37Row_7_ok : tmFiber37RowCheck 7 = true := by decide
theorem tmFiber37Row_8_ok : tmFiber37RowCheck 8 = true := by decide
theorem tmFiber37Row_9_ok : tmFiber37RowCheck 9 = true := by decide
theorem tmFiber37Row_10_ok : tmFiber37RowCheck 10 = true := by decide
theorem tmFiber37Row_11_ok : tmFiber37RowCheck 11 = true := by decide
theorem tmFiber37Row_12_ok : tmFiber37RowCheck 12 = true := by decide
theorem tmFiber37Row_13_ok : tmFiber37RowCheck 13 = true := by decide
theorem tmFiber37Row_14_ok : tmFiber37RowCheck 14 = true := by decide
theorem tmFiber37Row_15_ok : tmFiber37RowCheck 15 = true := by decide

def tmFiber37ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber37Rows tmMaxParentDepth (listGetD tmFiber37Expected i 0) == 368

theorem tmFiber37Parent_0_ok : tmFiber37ParentCheck 0 = true := by decide
theorem tmFiber37Parent_1_ok : tmFiber37ParentCheck 1 = true := by decide
theorem tmFiber37Parent_2_ok : tmFiber37ParentCheck 2 = true := by decide
theorem tmFiber37Parent_3_ok : tmFiber37ParentCheck 3 = true := by decide
theorem tmFiber37Parent_4_ok : tmFiber37ParentCheck 4 = true := by decide
theorem tmFiber37Parent_5_ok : tmFiber37ParentCheck 5 = true := by decide
theorem tmFiber37Parent_6_ok : tmFiber37ParentCheck 6 = true := by decide
theorem tmFiber37Parent_7_ok : tmFiber37ParentCheck 7 = true := by decide
theorem tmFiber37Parent_8_ok : tmFiber37ParentCheck 8 = true := by decide
theorem tmFiber37Parent_9_ok : tmFiber37ParentCheck 9 = true := by decide
theorem tmFiber37Parent_10_ok : tmFiber37ParentCheck 10 = true := by decide
theorem tmFiber37Parent_11_ok : tmFiber37ParentCheck 11 = true := by decide
theorem tmFiber37Parent_12_ok : tmFiber37ParentCheck 12 = true := by decide
theorem tmFiber37Parent_13_ok : tmFiber37ParentCheck 13 = true := by decide
theorem tmFiber37Parent_14_ok : tmFiber37ParentCheck 14 = true := by decide
theorem tmFiber37Parent_15_ok : tmFiber37ParentCheck 15 = true := by decide

def tmFiber37CertificateAudit : Bool :=
  tmFiber37SourcesCheck &&
    tmFiber37RowCheck 0 &&
    tmFiber37RowCheck 1 &&
    tmFiber37RowCheck 2 &&
    tmFiber37RowCheck 3 &&
    tmFiber37RowCheck 4 &&
    tmFiber37RowCheck 5 &&
    tmFiber37RowCheck 6 &&
    tmFiber37RowCheck 7 &&
    tmFiber37RowCheck 8 &&
    tmFiber37RowCheck 9 &&
    tmFiber37RowCheck 10 &&
    tmFiber37RowCheck 11 &&
    tmFiber37RowCheck 12 &&
    tmFiber37RowCheck 13 &&
    tmFiber37RowCheck 14 &&
    tmFiber37RowCheck 15 &&
    tmFiber37ParentCheck 0 &&
    tmFiber37ParentCheck 1 &&
    tmFiber37ParentCheck 2 &&
    tmFiber37ParentCheck 3 &&
    tmFiber37ParentCheck 4 &&
    tmFiber37ParentCheck 5 &&
    tmFiber37ParentCheck 6 &&
    tmFiber37ParentCheck 7 &&
    tmFiber37ParentCheck 8 &&
    tmFiber37ParentCheck 9 &&
    tmFiber37ParentCheck 10 &&
    tmFiber37ParentCheck 11 &&
    tmFiber37ParentCheck 12 &&
    tmFiber37ParentCheck 13 &&
    tmFiber37ParentCheck 14 &&
    tmFiber37ParentCheck 15

theorem tmFiber37CertificateAudit_ok :
    tmFiber37CertificateAudit = true := by
  simp [tmFiber37CertificateAudit,
    tmFiber37SourcesCheck_ok,
    tmFiber37Row_0_ok,
    tmFiber37Row_1_ok,
    tmFiber37Row_2_ok,
    tmFiber37Row_3_ok,
    tmFiber37Row_4_ok,
    tmFiber37Row_5_ok,
    tmFiber37Row_6_ok,
    tmFiber37Row_7_ok,
    tmFiber37Row_8_ok,
    tmFiber37Row_9_ok,
    tmFiber37Row_10_ok,
    tmFiber37Row_11_ok,
    tmFiber37Row_12_ok,
    tmFiber37Row_13_ok,
    tmFiber37Row_14_ok,
    tmFiber37Row_15_ok,
    tmFiber37Parent_0_ok,
    tmFiber37Parent_1_ok,
    tmFiber37Parent_2_ok,
    tmFiber37Parent_3_ok,
    tmFiber37Parent_4_ok,
    tmFiber37Parent_5_ok,
    tmFiber37Parent_6_ok,
    tmFiber37Parent_7_ok,
    tmFiber37Parent_8_ok,
    tmFiber37Parent_9_ok,
    tmFiber37Parent_10_ok,
    tmFiber37Parent_11_ok,
    tmFiber37Parent_12_ok,
    tmFiber37Parent_13_ok,
    tmFiber37Parent_14_ok,
    tmFiber37Parent_15_ok]

def tmFiber38Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.p]

def tmFiber38Expected : List Nat :=
  [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

def tmFiber38Rows : List DirectChainParentRow :=
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

def tmFiber38RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber38Rows i default

def tmFiber38SourcesCheck : Bool :=
  (tmFiber38Rows.map fun row => row.source) == tmFiber38Expected

theorem tmFiber38SourcesCheck_ok :
    tmFiber38SourcesCheck = true := by
  decide

def tmFiber38RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt i)

theorem tmFiber38Row_0_ok : tmFiber38RowCheck 0 = true := by decide
theorem tmFiber38Row_1_ok : tmFiber38RowCheck 1 = true := by decide
theorem tmFiber38Row_2_ok : tmFiber38RowCheck 2 = true := by decide
theorem tmFiber38Row_3_ok : tmFiber38RowCheck 3 = true := by decide
theorem tmFiber38Row_4_ok : tmFiber38RowCheck 4 = true := by decide
theorem tmFiber38Row_5_ok : tmFiber38RowCheck 5 = true := by decide
theorem tmFiber38Row_6_ok : tmFiber38RowCheck 6 = true := by decide
theorem tmFiber38Row_7_ok : tmFiber38RowCheck 7 = true := by decide
theorem tmFiber38Row_8_ok : tmFiber38RowCheck 8 = true := by decide
theorem tmFiber38Row_9_ok : tmFiber38RowCheck 9 = true := by decide
theorem tmFiber38Row_10_ok : tmFiber38RowCheck 10 = true := by decide
theorem tmFiber38Row_11_ok : tmFiber38RowCheck 11 = true := by decide
theorem tmFiber38Row_12_ok : tmFiber38RowCheck 12 = true := by decide
theorem tmFiber38Row_13_ok : tmFiber38RowCheck 13 = true := by decide
theorem tmFiber38Row_14_ok : tmFiber38RowCheck 14 = true := by decide
theorem tmFiber38Row_15_ok : tmFiber38RowCheck 15 = true := by decide

def tmFiber38ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber38Rows tmMaxParentDepth (listGetD tmFiber38Expected i 0) == 80

theorem tmFiber38Parent_0_ok : tmFiber38ParentCheck 0 = true := by decide
theorem tmFiber38Parent_1_ok : tmFiber38ParentCheck 1 = true := by decide
theorem tmFiber38Parent_2_ok : tmFiber38ParentCheck 2 = true := by decide
theorem tmFiber38Parent_3_ok : tmFiber38ParentCheck 3 = true := by decide
theorem tmFiber38Parent_4_ok : tmFiber38ParentCheck 4 = true := by decide
theorem tmFiber38Parent_5_ok : tmFiber38ParentCheck 5 = true := by decide
theorem tmFiber38Parent_6_ok : tmFiber38ParentCheck 6 = true := by decide
theorem tmFiber38Parent_7_ok : tmFiber38ParentCheck 7 = true := by decide
theorem tmFiber38Parent_8_ok : tmFiber38ParentCheck 8 = true := by decide
theorem tmFiber38Parent_9_ok : tmFiber38ParentCheck 9 = true := by decide
theorem tmFiber38Parent_10_ok : tmFiber38ParentCheck 10 = true := by decide
theorem tmFiber38Parent_11_ok : tmFiber38ParentCheck 11 = true := by decide
theorem tmFiber38Parent_12_ok : tmFiber38ParentCheck 12 = true := by decide
theorem tmFiber38Parent_13_ok : tmFiber38ParentCheck 13 = true := by decide
theorem tmFiber38Parent_14_ok : tmFiber38ParentCheck 14 = true := by decide
theorem tmFiber38Parent_15_ok : tmFiber38ParentCheck 15 = true := by decide

def tmFiber38CertificateAudit : Bool :=
  tmFiber38SourcesCheck &&
    tmFiber38RowCheck 0 &&
    tmFiber38RowCheck 1 &&
    tmFiber38RowCheck 2 &&
    tmFiber38RowCheck 3 &&
    tmFiber38RowCheck 4 &&
    tmFiber38RowCheck 5 &&
    tmFiber38RowCheck 6 &&
    tmFiber38RowCheck 7 &&
    tmFiber38RowCheck 8 &&
    tmFiber38RowCheck 9 &&
    tmFiber38RowCheck 10 &&
    tmFiber38RowCheck 11 &&
    tmFiber38RowCheck 12 &&
    tmFiber38RowCheck 13 &&
    tmFiber38RowCheck 14 &&
    tmFiber38RowCheck 15 &&
    tmFiber38ParentCheck 0 &&
    tmFiber38ParentCheck 1 &&
    tmFiber38ParentCheck 2 &&
    tmFiber38ParentCheck 3 &&
    tmFiber38ParentCheck 4 &&
    tmFiber38ParentCheck 5 &&
    tmFiber38ParentCheck 6 &&
    tmFiber38ParentCheck 7 &&
    tmFiber38ParentCheck 8 &&
    tmFiber38ParentCheck 9 &&
    tmFiber38ParentCheck 10 &&
    tmFiber38ParentCheck 11 &&
    tmFiber38ParentCheck 12 &&
    tmFiber38ParentCheck 13 &&
    tmFiber38ParentCheck 14 &&
    tmFiber38ParentCheck 15

theorem tmFiber38CertificateAudit_ok :
    tmFiber38CertificateAudit = true := by
  simp [tmFiber38CertificateAudit,
    tmFiber38SourcesCheck_ok,
    tmFiber38Row_0_ok,
    tmFiber38Row_1_ok,
    tmFiber38Row_2_ok,
    tmFiber38Row_3_ok,
    tmFiber38Row_4_ok,
    tmFiber38Row_5_ok,
    tmFiber38Row_6_ok,
    tmFiber38Row_7_ok,
    tmFiber38Row_8_ok,
    tmFiber38Row_9_ok,
    tmFiber38Row_10_ok,
    tmFiber38Row_11_ok,
    tmFiber38Row_12_ok,
    tmFiber38Row_13_ok,
    tmFiber38Row_14_ok,
    tmFiber38Row_15_ok,
    tmFiber38Parent_0_ok,
    tmFiber38Parent_1_ok,
    tmFiber38Parent_2_ok,
    tmFiber38Parent_3_ok,
    tmFiber38Parent_4_ok,
    tmFiber38Parent_5_ok,
    tmFiber38Parent_6_ok,
    tmFiber38Parent_7_ok,
    tmFiber38Parent_8_ok,
    tmFiber38Parent_9_ok,
    tmFiber38Parent_10_ok,
    tmFiber38Parent_11_ok,
    tmFiber38Parent_12_ok,
    tmFiber38Parent_13_ok,
    tmFiber38Parent_14_ok,
    tmFiber38Parent_15_ok]

def tmFiber39Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.r]

def tmFiber39Expected : List Nat :=
  []

def tmFiber39Rows : List DirectChainParentRow :=
  []

def tmFiber39RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber39Rows i default

def tmFiber39SourcesCheck : Bool :=
  (tmFiber39Rows.map fun row => row.source) == tmFiber39Expected

theorem tmFiber39SourcesCheck_ok :
    tmFiber39SourcesCheck = true := by
  decide

def tmFiber39RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber39Key tmFiber39Expected (tmFiber39RowAt i)

def tmFiber39ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber39Rows tmMaxParentDepth (listGetD tmFiber39Expected i 0) == 0

def tmFiber39CertificateAudit : Bool :=
  tmFiber39SourcesCheck

theorem tmFiber39CertificateAudit_ok :
    tmFiber39CertificateAudit = true := by
  simp [tmFiber39CertificateAudit,
    tmFiber39SourcesCheck_ok]

def tmFiber40Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.b]

def tmFiber40Expected : List Nat :=
  []

def tmFiber40Rows : List DirectChainParentRow :=
  []

def tmFiber40RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber40Rows i default

def tmFiber40SourcesCheck : Bool :=
  (tmFiber40Rows.map fun row => row.source) == tmFiber40Expected

theorem tmFiber40SourcesCheck_ok :
    tmFiber40SourcesCheck = true := by
  decide

def tmFiber40RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber40Key tmFiber40Expected (tmFiber40RowAt i)

def tmFiber40ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber40Rows tmMaxParentDepth (listGetD tmFiber40Expected i 0) == 0

def tmFiber40CertificateAudit : Bool :=
  tmFiber40SourcesCheck

theorem tmFiber40CertificateAudit_ok :
    tmFiber40CertificateAudit = true := by
  simp [tmFiber40CertificateAudit,
    tmFiber40SourcesCheck_ok]

def tmFiber41Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.p]

def tmFiber41Expected : List Nat :=
  []

def tmFiber41Rows : List DirectChainParentRow :=
  []

def tmFiber41RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber41Rows i default

def tmFiber41SourcesCheck : Bool :=
  (tmFiber41Rows.map fun row => row.source) == tmFiber41Expected

theorem tmFiber41SourcesCheck_ok :
    tmFiber41SourcesCheck = true := by
  decide

def tmFiber41RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber41Key tmFiber41Expected (tmFiber41RowAt i)

def tmFiber41ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber41Rows tmMaxParentDepth (listGetD tmFiber41Expected i 0) == 0

def tmFiber41CertificateAudit : Bool :=
  tmFiber41SourcesCheck

theorem tmFiber41CertificateAudit_ok :
    tmFiber41CertificateAudit = true := by
  simp [tmFiber41CertificateAudit,
    tmFiber41SourcesCheck_ok]

def tmFiber42Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.r]

def tmFiber42Expected : List Nat :=
  [960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]

def tmFiber42Rows : List DirectChainParentRow :=
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

def tmFiber42RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber42Rows i default

def tmFiber42SourcesCheck : Bool :=
  (tmFiber42Rows.map fun row => row.source) == tmFiber42Expected

theorem tmFiber42SourcesCheck_ok :
    tmFiber42SourcesCheck = true := by
  decide

def tmFiber42RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt i)

theorem tmFiber42Row_0_ok : tmFiber42RowCheck 0 = true := by decide
theorem tmFiber42Row_1_ok : tmFiber42RowCheck 1 = true := by decide
theorem tmFiber42Row_2_ok : tmFiber42RowCheck 2 = true := by decide
theorem tmFiber42Row_3_ok : tmFiber42RowCheck 3 = true := by decide
theorem tmFiber42Row_4_ok : tmFiber42RowCheck 4 = true := by decide
theorem tmFiber42Row_5_ok : tmFiber42RowCheck 5 = true := by decide
theorem tmFiber42Row_6_ok : tmFiber42RowCheck 6 = true := by decide
theorem tmFiber42Row_7_ok : tmFiber42RowCheck 7 = true := by decide
theorem tmFiber42Row_8_ok : tmFiber42RowCheck 8 = true := by decide
theorem tmFiber42Row_9_ok : tmFiber42RowCheck 9 = true := by decide
theorem tmFiber42Row_10_ok : tmFiber42RowCheck 10 = true := by decide
theorem tmFiber42Row_11_ok : tmFiber42RowCheck 11 = true := by decide
theorem tmFiber42Row_12_ok : tmFiber42RowCheck 12 = true := by decide
theorem tmFiber42Row_13_ok : tmFiber42RowCheck 13 = true := by decide
theorem tmFiber42Row_14_ok : tmFiber42RowCheck 14 = true := by decide
theorem tmFiber42Row_15_ok : tmFiber42RowCheck 15 = true := by decide

def tmFiber42ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber42Rows tmMaxParentDepth (listGetD tmFiber42Expected i 0) == 960

theorem tmFiber42Parent_0_ok : tmFiber42ParentCheck 0 = true := by decide
theorem tmFiber42Parent_1_ok : tmFiber42ParentCheck 1 = true := by decide
theorem tmFiber42Parent_2_ok : tmFiber42ParentCheck 2 = true := by decide
theorem tmFiber42Parent_3_ok : tmFiber42ParentCheck 3 = true := by decide
theorem tmFiber42Parent_4_ok : tmFiber42ParentCheck 4 = true := by decide
theorem tmFiber42Parent_5_ok : tmFiber42ParentCheck 5 = true := by decide
theorem tmFiber42Parent_6_ok : tmFiber42ParentCheck 6 = true := by decide
theorem tmFiber42Parent_7_ok : tmFiber42ParentCheck 7 = true := by decide
theorem tmFiber42Parent_8_ok : tmFiber42ParentCheck 8 = true := by decide
theorem tmFiber42Parent_9_ok : tmFiber42ParentCheck 9 = true := by decide
theorem tmFiber42Parent_10_ok : tmFiber42ParentCheck 10 = true := by decide
theorem tmFiber42Parent_11_ok : tmFiber42ParentCheck 11 = true := by decide
theorem tmFiber42Parent_12_ok : tmFiber42ParentCheck 12 = true := by decide
theorem tmFiber42Parent_13_ok : tmFiber42ParentCheck 13 = true := by decide
theorem tmFiber42Parent_14_ok : tmFiber42ParentCheck 14 = true := by decide
theorem tmFiber42Parent_15_ok : tmFiber42ParentCheck 15 = true := by decide

def tmFiber42CertificateAudit : Bool :=
  tmFiber42SourcesCheck &&
    tmFiber42RowCheck 0 &&
    tmFiber42RowCheck 1 &&
    tmFiber42RowCheck 2 &&
    tmFiber42RowCheck 3 &&
    tmFiber42RowCheck 4 &&
    tmFiber42RowCheck 5 &&
    tmFiber42RowCheck 6 &&
    tmFiber42RowCheck 7 &&
    tmFiber42RowCheck 8 &&
    tmFiber42RowCheck 9 &&
    tmFiber42RowCheck 10 &&
    tmFiber42RowCheck 11 &&
    tmFiber42RowCheck 12 &&
    tmFiber42RowCheck 13 &&
    tmFiber42RowCheck 14 &&
    tmFiber42RowCheck 15 &&
    tmFiber42ParentCheck 0 &&
    tmFiber42ParentCheck 1 &&
    tmFiber42ParentCheck 2 &&
    tmFiber42ParentCheck 3 &&
    tmFiber42ParentCheck 4 &&
    tmFiber42ParentCheck 5 &&
    tmFiber42ParentCheck 6 &&
    tmFiber42ParentCheck 7 &&
    tmFiber42ParentCheck 8 &&
    tmFiber42ParentCheck 9 &&
    tmFiber42ParentCheck 10 &&
    tmFiber42ParentCheck 11 &&
    tmFiber42ParentCheck 12 &&
    tmFiber42ParentCheck 13 &&
    tmFiber42ParentCheck 14 &&
    tmFiber42ParentCheck 15

theorem tmFiber42CertificateAudit_ok :
    tmFiber42CertificateAudit = true := by
  simp [tmFiber42CertificateAudit,
    tmFiber42SourcesCheck_ok,
    tmFiber42Row_0_ok,
    tmFiber42Row_1_ok,
    tmFiber42Row_2_ok,
    tmFiber42Row_3_ok,
    tmFiber42Row_4_ok,
    tmFiber42Row_5_ok,
    tmFiber42Row_6_ok,
    tmFiber42Row_7_ok,
    tmFiber42Row_8_ok,
    tmFiber42Row_9_ok,
    tmFiber42Row_10_ok,
    tmFiber42Row_11_ok,
    tmFiber42Row_12_ok,
    tmFiber42Row_13_ok,
    tmFiber42Row_14_ok,
    tmFiber42Row_15_ok,
    tmFiber42Parent_0_ok,
    tmFiber42Parent_1_ok,
    tmFiber42Parent_2_ok,
    tmFiber42Parent_3_ok,
    tmFiber42Parent_4_ok,
    tmFiber42Parent_5_ok,
    tmFiber42Parent_6_ok,
    tmFiber42Parent_7_ok,
    tmFiber42Parent_8_ok,
    tmFiber42Parent_9_ok,
    tmFiber42Parent_10_ok,
    tmFiber42Parent_11_ok,
    tmFiber42Parent_12_ok,
    tmFiber42Parent_13_ok,
    tmFiber42Parent_14_ok,
    tmFiber42Parent_15_ok]

def tmFiber43Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.b]

def tmFiber43Expected : List Nat :=
  [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]

def tmFiber43Rows : List DirectChainParentRow :=
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

def tmFiber43RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber43Rows i default

def tmFiber43SourcesCheck : Bool :=
  (tmFiber43Rows.map fun row => row.source) == tmFiber43Expected

theorem tmFiber43SourcesCheck_ok :
    tmFiber43SourcesCheck = true := by
  decide

def tmFiber43RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt i)

theorem tmFiber43Row_0_ok : tmFiber43RowCheck 0 = true := by decide
theorem tmFiber43Row_1_ok : tmFiber43RowCheck 1 = true := by decide
theorem tmFiber43Row_2_ok : tmFiber43RowCheck 2 = true := by decide
theorem tmFiber43Row_3_ok : tmFiber43RowCheck 3 = true := by decide
theorem tmFiber43Row_4_ok : tmFiber43RowCheck 4 = true := by decide
theorem tmFiber43Row_5_ok : tmFiber43RowCheck 5 = true := by decide
theorem tmFiber43Row_6_ok : tmFiber43RowCheck 6 = true := by decide
theorem tmFiber43Row_7_ok : tmFiber43RowCheck 7 = true := by decide
theorem tmFiber43Row_8_ok : tmFiber43RowCheck 8 = true := by decide
theorem tmFiber43Row_9_ok : tmFiber43RowCheck 9 = true := by decide
theorem tmFiber43Row_10_ok : tmFiber43RowCheck 10 = true := by decide
theorem tmFiber43Row_11_ok : tmFiber43RowCheck 11 = true := by decide
theorem tmFiber43Row_12_ok : tmFiber43RowCheck 12 = true := by decide
theorem tmFiber43Row_13_ok : tmFiber43RowCheck 13 = true := by decide
theorem tmFiber43Row_14_ok : tmFiber43RowCheck 14 = true := by decide
theorem tmFiber43Row_15_ok : tmFiber43RowCheck 15 = true := by decide

def tmFiber43ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber43Rows tmMaxParentDepth (listGetD tmFiber43Expected i 0) == 864

theorem tmFiber43Parent_0_ok : tmFiber43ParentCheck 0 = true := by decide
theorem tmFiber43Parent_1_ok : tmFiber43ParentCheck 1 = true := by decide
theorem tmFiber43Parent_2_ok : tmFiber43ParentCheck 2 = true := by decide
theorem tmFiber43Parent_3_ok : tmFiber43ParentCheck 3 = true := by decide
theorem tmFiber43Parent_4_ok : tmFiber43ParentCheck 4 = true := by decide
theorem tmFiber43Parent_5_ok : tmFiber43ParentCheck 5 = true := by decide
theorem tmFiber43Parent_6_ok : tmFiber43ParentCheck 6 = true := by decide
theorem tmFiber43Parent_7_ok : tmFiber43ParentCheck 7 = true := by decide
theorem tmFiber43Parent_8_ok : tmFiber43ParentCheck 8 = true := by decide
theorem tmFiber43Parent_9_ok : tmFiber43ParentCheck 9 = true := by decide
theorem tmFiber43Parent_10_ok : tmFiber43ParentCheck 10 = true := by decide
theorem tmFiber43Parent_11_ok : tmFiber43ParentCheck 11 = true := by decide
theorem tmFiber43Parent_12_ok : tmFiber43ParentCheck 12 = true := by decide
theorem tmFiber43Parent_13_ok : tmFiber43ParentCheck 13 = true := by decide
theorem tmFiber43Parent_14_ok : tmFiber43ParentCheck 14 = true := by decide
theorem tmFiber43Parent_15_ok : tmFiber43ParentCheck 15 = true := by decide

def tmFiber43CertificateAudit : Bool :=
  tmFiber43SourcesCheck &&
    tmFiber43RowCheck 0 &&
    tmFiber43RowCheck 1 &&
    tmFiber43RowCheck 2 &&
    tmFiber43RowCheck 3 &&
    tmFiber43RowCheck 4 &&
    tmFiber43RowCheck 5 &&
    tmFiber43RowCheck 6 &&
    tmFiber43RowCheck 7 &&
    tmFiber43RowCheck 8 &&
    tmFiber43RowCheck 9 &&
    tmFiber43RowCheck 10 &&
    tmFiber43RowCheck 11 &&
    tmFiber43RowCheck 12 &&
    tmFiber43RowCheck 13 &&
    tmFiber43RowCheck 14 &&
    tmFiber43RowCheck 15 &&
    tmFiber43ParentCheck 0 &&
    tmFiber43ParentCheck 1 &&
    tmFiber43ParentCheck 2 &&
    tmFiber43ParentCheck 3 &&
    tmFiber43ParentCheck 4 &&
    tmFiber43ParentCheck 5 &&
    tmFiber43ParentCheck 6 &&
    tmFiber43ParentCheck 7 &&
    tmFiber43ParentCheck 8 &&
    tmFiber43ParentCheck 9 &&
    tmFiber43ParentCheck 10 &&
    tmFiber43ParentCheck 11 &&
    tmFiber43ParentCheck 12 &&
    tmFiber43ParentCheck 13 &&
    tmFiber43ParentCheck 14 &&
    tmFiber43ParentCheck 15

theorem tmFiber43CertificateAudit_ok :
    tmFiber43CertificateAudit = true := by
  simp [tmFiber43CertificateAudit,
    tmFiber43SourcesCheck_ok,
    tmFiber43Row_0_ok,
    tmFiber43Row_1_ok,
    tmFiber43Row_2_ok,
    tmFiber43Row_3_ok,
    tmFiber43Row_4_ok,
    tmFiber43Row_5_ok,
    tmFiber43Row_6_ok,
    tmFiber43Row_7_ok,
    tmFiber43Row_8_ok,
    tmFiber43Row_9_ok,
    tmFiber43Row_10_ok,
    tmFiber43Row_11_ok,
    tmFiber43Row_12_ok,
    tmFiber43Row_13_ok,
    tmFiber43Row_14_ok,
    tmFiber43Row_15_ok,
    tmFiber43Parent_0_ok,
    tmFiber43Parent_1_ok,
    tmFiber43Parent_2_ok,
    tmFiber43Parent_3_ok,
    tmFiber43Parent_4_ok,
    tmFiber43Parent_5_ok,
    tmFiber43Parent_6_ok,
    tmFiber43Parent_7_ok,
    tmFiber43Parent_8_ok,
    tmFiber43Parent_9_ok,
    tmFiber43Parent_10_ok,
    tmFiber43Parent_11_ok,
    tmFiber43Parent_12_ok,
    tmFiber43Parent_13_ok,
    tmFiber43Parent_14_ok,
    tmFiber43Parent_15_ok]

def tmFiber44Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.p]

def tmFiber44Expected : List Nat :=
  [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]

def tmFiber44Rows : List DirectChainParentRow :=
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

def tmFiber44RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber44Rows i default

def tmFiber44SourcesCheck : Bool :=
  (tmFiber44Rows.map fun row => row.source) == tmFiber44Expected

theorem tmFiber44SourcesCheck_ok :
    tmFiber44SourcesCheck = true := by
  decide

def tmFiber44RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber44Key tmFiber44Expected (tmFiber44RowAt i)

theorem tmFiber44Row_0_ok : tmFiber44RowCheck 0 = true := by decide
theorem tmFiber44Row_1_ok : tmFiber44RowCheck 1 = true := by decide
theorem tmFiber44Row_2_ok : tmFiber44RowCheck 2 = true := by decide
theorem tmFiber44Row_3_ok : tmFiber44RowCheck 3 = true := by decide
theorem tmFiber44Row_4_ok : tmFiber44RowCheck 4 = true := by decide
theorem tmFiber44Row_5_ok : tmFiber44RowCheck 5 = true := by decide
theorem tmFiber44Row_6_ok : tmFiber44RowCheck 6 = true := by decide
theorem tmFiber44Row_7_ok : tmFiber44RowCheck 7 = true := by decide
theorem tmFiber44Row_8_ok : tmFiber44RowCheck 8 = true := by decide
theorem tmFiber44Row_9_ok : tmFiber44RowCheck 9 = true := by decide
theorem tmFiber44Row_10_ok : tmFiber44RowCheck 10 = true := by decide
theorem tmFiber44Row_11_ok : tmFiber44RowCheck 11 = true := by decide
theorem tmFiber44Row_12_ok : tmFiber44RowCheck 12 = true := by decide
theorem tmFiber44Row_13_ok : tmFiber44RowCheck 13 = true := by decide
theorem tmFiber44Row_14_ok : tmFiber44RowCheck 14 = true := by decide
theorem tmFiber44Row_15_ok : tmFiber44RowCheck 15 = true := by decide
theorem tmFiber44Row_16_ok : tmFiber44RowCheck 16 = true := by decide
theorem tmFiber44Row_17_ok : tmFiber44RowCheck 17 = true := by decide
theorem tmFiber44Row_18_ok : tmFiber44RowCheck 18 = true := by decide
theorem tmFiber44Row_19_ok : tmFiber44RowCheck 19 = true := by decide
theorem tmFiber44Row_20_ok : tmFiber44RowCheck 20 = true := by decide
theorem tmFiber44Row_21_ok : tmFiber44RowCheck 21 = true := by decide
theorem tmFiber44Row_22_ok : tmFiber44RowCheck 22 = true := by decide
theorem tmFiber44Row_23_ok : tmFiber44RowCheck 23 = true := by decide
theorem tmFiber44Row_24_ok : tmFiber44RowCheck 24 = true := by decide
theorem tmFiber44Row_25_ok : tmFiber44RowCheck 25 = true := by decide
theorem tmFiber44Row_26_ok : tmFiber44RowCheck 26 = true := by decide
theorem tmFiber44Row_27_ok : tmFiber44RowCheck 27 = true := by decide
theorem tmFiber44Row_28_ok : tmFiber44RowCheck 28 = true := by decide
theorem tmFiber44Row_29_ok : tmFiber44RowCheck 29 = true := by decide
theorem tmFiber44Row_30_ok : tmFiber44RowCheck 30 = true := by decide
theorem tmFiber44Row_31_ok : tmFiber44RowCheck 31 = true := by decide
theorem tmFiber44Row_32_ok : tmFiber44RowCheck 32 = true := by decide
theorem tmFiber44Row_33_ok : tmFiber44RowCheck 33 = true := by decide
theorem tmFiber44Row_34_ok : tmFiber44RowCheck 34 = true := by decide
theorem tmFiber44Row_35_ok : tmFiber44RowCheck 35 = true := by decide
theorem tmFiber44Row_36_ok : tmFiber44RowCheck 36 = true := by decide
theorem tmFiber44Row_37_ok : tmFiber44RowCheck 37 = true := by decide
theorem tmFiber44Row_38_ok : tmFiber44RowCheck 38 = true := by decide
theorem tmFiber44Row_39_ok : tmFiber44RowCheck 39 = true := by decide
theorem tmFiber44Row_40_ok : tmFiber44RowCheck 40 = true := by decide
theorem tmFiber44Row_41_ok : tmFiber44RowCheck 41 = true := by decide
theorem tmFiber44Row_42_ok : tmFiber44RowCheck 42 = true := by decide
theorem tmFiber44Row_43_ok : tmFiber44RowCheck 43 = true := by decide
theorem tmFiber44Row_44_ok : tmFiber44RowCheck 44 = true := by decide
theorem tmFiber44Row_45_ok : tmFiber44RowCheck 45 = true := by decide
theorem tmFiber44Row_46_ok : tmFiber44RowCheck 46 = true := by decide
theorem tmFiber44Row_47_ok : tmFiber44RowCheck 47 = true := by decide
theorem tmFiber44Row_48_ok : tmFiber44RowCheck 48 = true := by decide
theorem tmFiber44Row_49_ok : tmFiber44RowCheck 49 = true := by decide
theorem tmFiber44Row_50_ok : tmFiber44RowCheck 50 = true := by decide
theorem tmFiber44Row_51_ok : tmFiber44RowCheck 51 = true := by decide
theorem tmFiber44Row_52_ok : tmFiber44RowCheck 52 = true := by decide
theorem tmFiber44Row_53_ok : tmFiber44RowCheck 53 = true := by decide
theorem tmFiber44Row_54_ok : tmFiber44RowCheck 54 = true := by decide
theorem tmFiber44Row_55_ok : tmFiber44RowCheck 55 = true := by decide
theorem tmFiber44Row_56_ok : tmFiber44RowCheck 56 = true := by decide
theorem tmFiber44Row_57_ok : tmFiber44RowCheck 57 = true := by decide
theorem tmFiber44Row_58_ok : tmFiber44RowCheck 58 = true := by decide
theorem tmFiber44Row_59_ok : tmFiber44RowCheck 59 = true := by decide
theorem tmFiber44Row_60_ok : tmFiber44RowCheck 60 = true := by decide
theorem tmFiber44Row_61_ok : tmFiber44RowCheck 61 = true := by decide
theorem tmFiber44Row_62_ok : tmFiber44RowCheck 62 = true := by decide
theorem tmFiber44Row_63_ok : tmFiber44RowCheck 63 = true := by decide

def tmFiber44ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber44Rows tmMaxParentDepth (listGetD tmFiber44Expected i 0) == 880

theorem tmFiber44Parent_0_ok : tmFiber44ParentCheck 0 = true := by decide
theorem tmFiber44Parent_1_ok : tmFiber44ParentCheck 1 = true := by decide
theorem tmFiber44Parent_2_ok : tmFiber44ParentCheck 2 = true := by decide
theorem tmFiber44Parent_3_ok : tmFiber44ParentCheck 3 = true := by decide
theorem tmFiber44Parent_4_ok : tmFiber44ParentCheck 4 = true := by decide
theorem tmFiber44Parent_5_ok : tmFiber44ParentCheck 5 = true := by decide
theorem tmFiber44Parent_6_ok : tmFiber44ParentCheck 6 = true := by decide
theorem tmFiber44Parent_7_ok : tmFiber44ParentCheck 7 = true := by decide
theorem tmFiber44Parent_8_ok : tmFiber44ParentCheck 8 = true := by decide
theorem tmFiber44Parent_9_ok : tmFiber44ParentCheck 9 = true := by decide
theorem tmFiber44Parent_10_ok : tmFiber44ParentCheck 10 = true := by decide
theorem tmFiber44Parent_11_ok : tmFiber44ParentCheck 11 = true := by decide
theorem tmFiber44Parent_12_ok : tmFiber44ParentCheck 12 = true := by decide
theorem tmFiber44Parent_13_ok : tmFiber44ParentCheck 13 = true := by decide
theorem tmFiber44Parent_14_ok : tmFiber44ParentCheck 14 = true := by decide
theorem tmFiber44Parent_15_ok : tmFiber44ParentCheck 15 = true := by decide
theorem tmFiber44Parent_16_ok : tmFiber44ParentCheck 16 = true := by decide
theorem tmFiber44Parent_17_ok : tmFiber44ParentCheck 17 = true := by decide
theorem tmFiber44Parent_18_ok : tmFiber44ParentCheck 18 = true := by decide
theorem tmFiber44Parent_19_ok : tmFiber44ParentCheck 19 = true := by decide
theorem tmFiber44Parent_20_ok : tmFiber44ParentCheck 20 = true := by decide
theorem tmFiber44Parent_21_ok : tmFiber44ParentCheck 21 = true := by decide
theorem tmFiber44Parent_22_ok : tmFiber44ParentCheck 22 = true := by decide
theorem tmFiber44Parent_23_ok : tmFiber44ParentCheck 23 = true := by decide
theorem tmFiber44Parent_24_ok : tmFiber44ParentCheck 24 = true := by decide
theorem tmFiber44Parent_25_ok : tmFiber44ParentCheck 25 = true := by decide
theorem tmFiber44Parent_26_ok : tmFiber44ParentCheck 26 = true := by decide
theorem tmFiber44Parent_27_ok : tmFiber44ParentCheck 27 = true := by decide
theorem tmFiber44Parent_28_ok : tmFiber44ParentCheck 28 = true := by decide
theorem tmFiber44Parent_29_ok : tmFiber44ParentCheck 29 = true := by decide
theorem tmFiber44Parent_30_ok : tmFiber44ParentCheck 30 = true := by decide
theorem tmFiber44Parent_31_ok : tmFiber44ParentCheck 31 = true := by decide
theorem tmFiber44Parent_32_ok : tmFiber44ParentCheck 32 = true := by decide
theorem tmFiber44Parent_33_ok : tmFiber44ParentCheck 33 = true := by decide
theorem tmFiber44Parent_34_ok : tmFiber44ParentCheck 34 = true := by decide
theorem tmFiber44Parent_35_ok : tmFiber44ParentCheck 35 = true := by decide
theorem tmFiber44Parent_36_ok : tmFiber44ParentCheck 36 = true := by decide
theorem tmFiber44Parent_37_ok : tmFiber44ParentCheck 37 = true := by decide
theorem tmFiber44Parent_38_ok : tmFiber44ParentCheck 38 = true := by decide
theorem tmFiber44Parent_39_ok : tmFiber44ParentCheck 39 = true := by decide
theorem tmFiber44Parent_40_ok : tmFiber44ParentCheck 40 = true := by decide
theorem tmFiber44Parent_41_ok : tmFiber44ParentCheck 41 = true := by decide
theorem tmFiber44Parent_42_ok : tmFiber44ParentCheck 42 = true := by decide
theorem tmFiber44Parent_43_ok : tmFiber44ParentCheck 43 = true := by decide
theorem tmFiber44Parent_44_ok : tmFiber44ParentCheck 44 = true := by decide
theorem tmFiber44Parent_45_ok : tmFiber44ParentCheck 45 = true := by decide
theorem tmFiber44Parent_46_ok : tmFiber44ParentCheck 46 = true := by decide
theorem tmFiber44Parent_47_ok : tmFiber44ParentCheck 47 = true := by decide
theorem tmFiber44Parent_48_ok : tmFiber44ParentCheck 48 = true := by decide
theorem tmFiber44Parent_49_ok : tmFiber44ParentCheck 49 = true := by decide
theorem tmFiber44Parent_50_ok : tmFiber44ParentCheck 50 = true := by decide
theorem tmFiber44Parent_51_ok : tmFiber44ParentCheck 51 = true := by decide
theorem tmFiber44Parent_52_ok : tmFiber44ParentCheck 52 = true := by decide
theorem tmFiber44Parent_53_ok : tmFiber44ParentCheck 53 = true := by decide
theorem tmFiber44Parent_54_ok : tmFiber44ParentCheck 54 = true := by decide
theorem tmFiber44Parent_55_ok : tmFiber44ParentCheck 55 = true := by decide
theorem tmFiber44Parent_56_ok : tmFiber44ParentCheck 56 = true := by decide
theorem tmFiber44Parent_57_ok : tmFiber44ParentCheck 57 = true := by decide
theorem tmFiber44Parent_58_ok : tmFiber44ParentCheck 58 = true := by decide
theorem tmFiber44Parent_59_ok : tmFiber44ParentCheck 59 = true := by decide
theorem tmFiber44Parent_60_ok : tmFiber44ParentCheck 60 = true := by decide
theorem tmFiber44Parent_61_ok : tmFiber44ParentCheck 61 = true := by decide
theorem tmFiber44Parent_62_ok : tmFiber44ParentCheck 62 = true := by decide
theorem tmFiber44Parent_63_ok : tmFiber44ParentCheck 63 = true := by decide

def tmFiber44CertificateAudit : Bool :=
  tmFiber44SourcesCheck &&
    tmFiber44RowCheck 0 &&
    tmFiber44RowCheck 1 &&
    tmFiber44RowCheck 2 &&
    tmFiber44RowCheck 3 &&
    tmFiber44RowCheck 4 &&
    tmFiber44RowCheck 5 &&
    tmFiber44RowCheck 6 &&
    tmFiber44RowCheck 7 &&
    tmFiber44RowCheck 8 &&
    tmFiber44RowCheck 9 &&
    tmFiber44RowCheck 10 &&
    tmFiber44RowCheck 11 &&
    tmFiber44RowCheck 12 &&
    tmFiber44RowCheck 13 &&
    tmFiber44RowCheck 14 &&
    tmFiber44RowCheck 15 &&
    tmFiber44RowCheck 16 &&
    tmFiber44RowCheck 17 &&
    tmFiber44RowCheck 18 &&
    tmFiber44RowCheck 19 &&
    tmFiber44RowCheck 20 &&
    tmFiber44RowCheck 21 &&
    tmFiber44RowCheck 22 &&
    tmFiber44RowCheck 23 &&
    tmFiber44RowCheck 24 &&
    tmFiber44RowCheck 25 &&
    tmFiber44RowCheck 26 &&
    tmFiber44RowCheck 27 &&
    tmFiber44RowCheck 28 &&
    tmFiber44RowCheck 29 &&
    tmFiber44RowCheck 30 &&
    tmFiber44RowCheck 31 &&
    tmFiber44RowCheck 32 &&
    tmFiber44RowCheck 33 &&
    tmFiber44RowCheck 34 &&
    tmFiber44RowCheck 35 &&
    tmFiber44RowCheck 36 &&
    tmFiber44RowCheck 37 &&
    tmFiber44RowCheck 38 &&
    tmFiber44RowCheck 39 &&
    tmFiber44RowCheck 40 &&
    tmFiber44RowCheck 41 &&
    tmFiber44RowCheck 42 &&
    tmFiber44RowCheck 43 &&
    tmFiber44RowCheck 44 &&
    tmFiber44RowCheck 45 &&
    tmFiber44RowCheck 46 &&
    tmFiber44RowCheck 47 &&
    tmFiber44RowCheck 48 &&
    tmFiber44RowCheck 49 &&
    tmFiber44RowCheck 50 &&
    tmFiber44RowCheck 51 &&
    tmFiber44RowCheck 52 &&
    tmFiber44RowCheck 53 &&
    tmFiber44RowCheck 54 &&
    tmFiber44RowCheck 55 &&
    tmFiber44RowCheck 56 &&
    tmFiber44RowCheck 57 &&
    tmFiber44RowCheck 58 &&
    tmFiber44RowCheck 59 &&
    tmFiber44RowCheck 60 &&
    tmFiber44RowCheck 61 &&
    tmFiber44RowCheck 62 &&
    tmFiber44RowCheck 63 &&
    tmFiber44ParentCheck 0 &&
    tmFiber44ParentCheck 1 &&
    tmFiber44ParentCheck 2 &&
    tmFiber44ParentCheck 3 &&
    tmFiber44ParentCheck 4 &&
    tmFiber44ParentCheck 5 &&
    tmFiber44ParentCheck 6 &&
    tmFiber44ParentCheck 7 &&
    tmFiber44ParentCheck 8 &&
    tmFiber44ParentCheck 9 &&
    tmFiber44ParentCheck 10 &&
    tmFiber44ParentCheck 11 &&
    tmFiber44ParentCheck 12 &&
    tmFiber44ParentCheck 13 &&
    tmFiber44ParentCheck 14 &&
    tmFiber44ParentCheck 15 &&
    tmFiber44ParentCheck 16 &&
    tmFiber44ParentCheck 17 &&
    tmFiber44ParentCheck 18 &&
    tmFiber44ParentCheck 19 &&
    tmFiber44ParentCheck 20 &&
    tmFiber44ParentCheck 21 &&
    tmFiber44ParentCheck 22 &&
    tmFiber44ParentCheck 23 &&
    tmFiber44ParentCheck 24 &&
    tmFiber44ParentCheck 25 &&
    tmFiber44ParentCheck 26 &&
    tmFiber44ParentCheck 27 &&
    tmFiber44ParentCheck 28 &&
    tmFiber44ParentCheck 29 &&
    tmFiber44ParentCheck 30 &&
    tmFiber44ParentCheck 31 &&
    tmFiber44ParentCheck 32 &&
    tmFiber44ParentCheck 33 &&
    tmFiber44ParentCheck 34 &&
    tmFiber44ParentCheck 35 &&
    tmFiber44ParentCheck 36 &&
    tmFiber44ParentCheck 37 &&
    tmFiber44ParentCheck 38 &&
    tmFiber44ParentCheck 39 &&
    tmFiber44ParentCheck 40 &&
    tmFiber44ParentCheck 41 &&
    tmFiber44ParentCheck 42 &&
    tmFiber44ParentCheck 43 &&
    tmFiber44ParentCheck 44 &&
    tmFiber44ParentCheck 45 &&
    tmFiber44ParentCheck 46 &&
    tmFiber44ParentCheck 47 &&
    tmFiber44ParentCheck 48 &&
    tmFiber44ParentCheck 49 &&
    tmFiber44ParentCheck 50 &&
    tmFiber44ParentCheck 51 &&
    tmFiber44ParentCheck 52 &&
    tmFiber44ParentCheck 53 &&
    tmFiber44ParentCheck 54 &&
    tmFiber44ParentCheck 55 &&
    tmFiber44ParentCheck 56 &&
    tmFiber44ParentCheck 57 &&
    tmFiber44ParentCheck 58 &&
    tmFiber44ParentCheck 59 &&
    tmFiber44ParentCheck 60 &&
    tmFiber44ParentCheck 61 &&
    tmFiber44ParentCheck 62 &&
    tmFiber44ParentCheck 63

theorem tmFiber44CertificateAudit_ok :
    tmFiber44CertificateAudit = true := by
  simp [tmFiber44CertificateAudit,
    tmFiber44SourcesCheck_ok,
    tmFiber44Row_0_ok,
    tmFiber44Row_1_ok,
    tmFiber44Row_2_ok,
    tmFiber44Row_3_ok,
    tmFiber44Row_4_ok,
    tmFiber44Row_5_ok,
    tmFiber44Row_6_ok,
    tmFiber44Row_7_ok,
    tmFiber44Row_8_ok,
    tmFiber44Row_9_ok,
    tmFiber44Row_10_ok,
    tmFiber44Row_11_ok,
    tmFiber44Row_12_ok,
    tmFiber44Row_13_ok,
    tmFiber44Row_14_ok,
    tmFiber44Row_15_ok,
    tmFiber44Row_16_ok,
    tmFiber44Row_17_ok,
    tmFiber44Row_18_ok,
    tmFiber44Row_19_ok,
    tmFiber44Row_20_ok,
    tmFiber44Row_21_ok,
    tmFiber44Row_22_ok,
    tmFiber44Row_23_ok,
    tmFiber44Row_24_ok,
    tmFiber44Row_25_ok,
    tmFiber44Row_26_ok,
    tmFiber44Row_27_ok,
    tmFiber44Row_28_ok,
    tmFiber44Row_29_ok,
    tmFiber44Row_30_ok,
    tmFiber44Row_31_ok,
    tmFiber44Row_32_ok,
    tmFiber44Row_33_ok,
    tmFiber44Row_34_ok,
    tmFiber44Row_35_ok,
    tmFiber44Row_36_ok,
    tmFiber44Row_37_ok,
    tmFiber44Row_38_ok,
    tmFiber44Row_39_ok,
    tmFiber44Row_40_ok,
    tmFiber44Row_41_ok,
    tmFiber44Row_42_ok,
    tmFiber44Row_43_ok,
    tmFiber44Row_44_ok,
    tmFiber44Row_45_ok,
    tmFiber44Row_46_ok,
    tmFiber44Row_47_ok,
    tmFiber44Row_48_ok,
    tmFiber44Row_49_ok,
    tmFiber44Row_50_ok,
    tmFiber44Row_51_ok,
    tmFiber44Row_52_ok,
    tmFiber44Row_53_ok,
    tmFiber44Row_54_ok,
    tmFiber44Row_55_ok,
    tmFiber44Row_56_ok,
    tmFiber44Row_57_ok,
    tmFiber44Row_58_ok,
    tmFiber44Row_59_ok,
    tmFiber44Row_60_ok,
    tmFiber44Row_61_ok,
    tmFiber44Row_62_ok,
    tmFiber44Row_63_ok,
    tmFiber44Parent_0_ok,
    tmFiber44Parent_1_ok,
    tmFiber44Parent_2_ok,
    tmFiber44Parent_3_ok,
    tmFiber44Parent_4_ok,
    tmFiber44Parent_5_ok,
    tmFiber44Parent_6_ok,
    tmFiber44Parent_7_ok,
    tmFiber44Parent_8_ok,
    tmFiber44Parent_9_ok,
    tmFiber44Parent_10_ok,
    tmFiber44Parent_11_ok,
    tmFiber44Parent_12_ok,
    tmFiber44Parent_13_ok,
    tmFiber44Parent_14_ok,
    tmFiber44Parent_15_ok,
    tmFiber44Parent_16_ok,
    tmFiber44Parent_17_ok,
    tmFiber44Parent_18_ok,
    tmFiber44Parent_19_ok,
    tmFiber44Parent_20_ok,
    tmFiber44Parent_21_ok,
    tmFiber44Parent_22_ok,
    tmFiber44Parent_23_ok,
    tmFiber44Parent_24_ok,
    tmFiber44Parent_25_ok,
    tmFiber44Parent_26_ok,
    tmFiber44Parent_27_ok,
    tmFiber44Parent_28_ok,
    tmFiber44Parent_29_ok,
    tmFiber44Parent_30_ok,
    tmFiber44Parent_31_ok,
    tmFiber44Parent_32_ok,
    tmFiber44Parent_33_ok,
    tmFiber44Parent_34_ok,
    tmFiber44Parent_35_ok,
    tmFiber44Parent_36_ok,
    tmFiber44Parent_37_ok,
    tmFiber44Parent_38_ok,
    tmFiber44Parent_39_ok,
    tmFiber44Parent_40_ok,
    tmFiber44Parent_41_ok,
    tmFiber44Parent_42_ok,
    tmFiber44Parent_43_ok,
    tmFiber44Parent_44_ok,
    tmFiber44Parent_45_ok,
    tmFiber44Parent_46_ok,
    tmFiber44Parent_47_ok,
    tmFiber44Parent_48_ok,
    tmFiber44Parent_49_ok,
    tmFiber44Parent_50_ok,
    tmFiber44Parent_51_ok,
    tmFiber44Parent_52_ok,
    tmFiber44Parent_53_ok,
    tmFiber44Parent_54_ok,
    tmFiber44Parent_55_ok,
    tmFiber44Parent_56_ok,
    tmFiber44Parent_57_ok,
    tmFiber44Parent_58_ok,
    tmFiber44Parent_59_ok,
    tmFiber44Parent_60_ok,
    tmFiber44Parent_61_ok,
    tmFiber44Parent_62_ok,
    tmFiber44Parent_63_ok]

def tmFiber45Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.r]

def tmFiber45Expected : List Nat :=
  []

def tmFiber45Rows : List DirectChainParentRow :=
  []

def tmFiber45RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber45Rows i default

def tmFiber45SourcesCheck : Bool :=
  (tmFiber45Rows.map fun row => row.source) == tmFiber45Expected

theorem tmFiber45SourcesCheck_ok :
    tmFiber45SourcesCheck = true := by
  decide

def tmFiber45RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber45Key tmFiber45Expected (tmFiber45RowAt i)

def tmFiber45ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber45Rows tmMaxParentDepth (listGetD tmFiber45Expected i 0) == 0

def tmFiber45CertificateAudit : Bool :=
  tmFiber45SourcesCheck

theorem tmFiber45CertificateAudit_ok :
    tmFiber45CertificateAudit = true := by
  simp [tmFiber45CertificateAudit,
    tmFiber45SourcesCheck_ok]

def tmFiber46Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.b]

def tmFiber46Expected : List Nat :=
  []

def tmFiber46Rows : List DirectChainParentRow :=
  []

def tmFiber46RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber46Rows i default

def tmFiber46SourcesCheck : Bool :=
  (tmFiber46Rows.map fun row => row.source) == tmFiber46Expected

theorem tmFiber46SourcesCheck_ok :
    tmFiber46SourcesCheck = true := by
  decide

def tmFiber46RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber46Key tmFiber46Expected (tmFiber46RowAt i)

def tmFiber46ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber46Rows tmMaxParentDepth (listGetD tmFiber46Expected i 0) == 0

def tmFiber46CertificateAudit : Bool :=
  tmFiber46SourcesCheck

theorem tmFiber46CertificateAudit_ok :
    tmFiber46CertificateAudit = true := by
  simp [tmFiber46CertificateAudit,
    tmFiber46SourcesCheck_ok]

def tmFiber47Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.p]

def tmFiber47Expected : List Nat :=
  []

def tmFiber47Rows : List DirectChainParentRow :=
  []

def tmFiber47RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber47Rows i default

def tmFiber47SourcesCheck : Bool :=
  (tmFiber47Rows.map fun row => row.source) == tmFiber47Expected

theorem tmFiber47SourcesCheck_ok :
    tmFiber47SourcesCheck = true := by
  decide

def tmFiber47RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber47Key tmFiber47Expected (tmFiber47RowAt i)

def tmFiber47ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber47Rows tmMaxParentDepth (listGetD tmFiber47Expected i 0) == 0

def tmFiber47CertificateAudit : Bool :=
  tmFiber47SourcesCheck

theorem tmFiber47CertificateAudit_ok :
    tmFiber47CertificateAudit = true := by
  simp [tmFiber47CertificateAudit,
    tmFiber47SourcesCheck_ok]

def tmFiber48Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.r]

def tmFiber48Expected : List Nat :=
  [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]

def tmFiber48Rows : List DirectChainParentRow :=
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

def tmFiber48RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber48Rows i default

def tmFiber48SourcesCheck : Bool :=
  (tmFiber48Rows.map fun row => row.source) == tmFiber48Expected

theorem tmFiber48SourcesCheck_ok :
    tmFiber48SourcesCheck = true := by
  decide

def tmFiber48RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt i)

theorem tmFiber48Row_0_ok : tmFiber48RowCheck 0 = true := by decide
theorem tmFiber48Row_1_ok : tmFiber48RowCheck 1 = true := by decide
theorem tmFiber48Row_2_ok : tmFiber48RowCheck 2 = true := by decide
theorem tmFiber48Row_3_ok : tmFiber48RowCheck 3 = true := by decide
theorem tmFiber48Row_4_ok : tmFiber48RowCheck 4 = true := by decide
theorem tmFiber48Row_5_ok : tmFiber48RowCheck 5 = true := by decide
theorem tmFiber48Row_6_ok : tmFiber48RowCheck 6 = true := by decide
theorem tmFiber48Row_7_ok : tmFiber48RowCheck 7 = true := by decide
theorem tmFiber48Row_8_ok : tmFiber48RowCheck 8 = true := by decide
theorem tmFiber48Row_9_ok : tmFiber48RowCheck 9 = true := by decide
theorem tmFiber48Row_10_ok : tmFiber48RowCheck 10 = true := by decide
theorem tmFiber48Row_11_ok : tmFiber48RowCheck 11 = true := by decide
theorem tmFiber48Row_12_ok : tmFiber48RowCheck 12 = true := by decide
theorem tmFiber48Row_13_ok : tmFiber48RowCheck 13 = true := by decide
theorem tmFiber48Row_14_ok : tmFiber48RowCheck 14 = true := by decide
theorem tmFiber48Row_15_ok : tmFiber48RowCheck 15 = true := by decide

def tmFiber48ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber48Rows tmMaxParentDepth (listGetD tmFiber48Expected i 0) == 1008

theorem tmFiber48Parent_0_ok : tmFiber48ParentCheck 0 = true := by decide
theorem tmFiber48Parent_1_ok : tmFiber48ParentCheck 1 = true := by decide
theorem tmFiber48Parent_2_ok : tmFiber48ParentCheck 2 = true := by decide
theorem tmFiber48Parent_3_ok : tmFiber48ParentCheck 3 = true := by decide
theorem tmFiber48Parent_4_ok : tmFiber48ParentCheck 4 = true := by decide
theorem tmFiber48Parent_5_ok : tmFiber48ParentCheck 5 = true := by decide
theorem tmFiber48Parent_6_ok : tmFiber48ParentCheck 6 = true := by decide
theorem tmFiber48Parent_7_ok : tmFiber48ParentCheck 7 = true := by decide
theorem tmFiber48Parent_8_ok : tmFiber48ParentCheck 8 = true := by decide
theorem tmFiber48Parent_9_ok : tmFiber48ParentCheck 9 = true := by decide
theorem tmFiber48Parent_10_ok : tmFiber48ParentCheck 10 = true := by decide
theorem tmFiber48Parent_11_ok : tmFiber48ParentCheck 11 = true := by decide
theorem tmFiber48Parent_12_ok : tmFiber48ParentCheck 12 = true := by decide
theorem tmFiber48Parent_13_ok : tmFiber48ParentCheck 13 = true := by decide
theorem tmFiber48Parent_14_ok : tmFiber48ParentCheck 14 = true := by decide
theorem tmFiber48Parent_15_ok : tmFiber48ParentCheck 15 = true := by decide

def tmFiber48CertificateAudit : Bool :=
  tmFiber48SourcesCheck &&
    tmFiber48RowCheck 0 &&
    tmFiber48RowCheck 1 &&
    tmFiber48RowCheck 2 &&
    tmFiber48RowCheck 3 &&
    tmFiber48RowCheck 4 &&
    tmFiber48RowCheck 5 &&
    tmFiber48RowCheck 6 &&
    tmFiber48RowCheck 7 &&
    tmFiber48RowCheck 8 &&
    tmFiber48RowCheck 9 &&
    tmFiber48RowCheck 10 &&
    tmFiber48RowCheck 11 &&
    tmFiber48RowCheck 12 &&
    tmFiber48RowCheck 13 &&
    tmFiber48RowCheck 14 &&
    tmFiber48RowCheck 15 &&
    tmFiber48ParentCheck 0 &&
    tmFiber48ParentCheck 1 &&
    tmFiber48ParentCheck 2 &&
    tmFiber48ParentCheck 3 &&
    tmFiber48ParentCheck 4 &&
    tmFiber48ParentCheck 5 &&
    tmFiber48ParentCheck 6 &&
    tmFiber48ParentCheck 7 &&
    tmFiber48ParentCheck 8 &&
    tmFiber48ParentCheck 9 &&
    tmFiber48ParentCheck 10 &&
    tmFiber48ParentCheck 11 &&
    tmFiber48ParentCheck 12 &&
    tmFiber48ParentCheck 13 &&
    tmFiber48ParentCheck 14 &&
    tmFiber48ParentCheck 15

theorem tmFiber48CertificateAudit_ok :
    tmFiber48CertificateAudit = true := by
  simp [tmFiber48CertificateAudit,
    tmFiber48SourcesCheck_ok,
    tmFiber48Row_0_ok,
    tmFiber48Row_1_ok,
    tmFiber48Row_2_ok,
    tmFiber48Row_3_ok,
    tmFiber48Row_4_ok,
    tmFiber48Row_5_ok,
    tmFiber48Row_6_ok,
    tmFiber48Row_7_ok,
    tmFiber48Row_8_ok,
    tmFiber48Row_9_ok,
    tmFiber48Row_10_ok,
    tmFiber48Row_11_ok,
    tmFiber48Row_12_ok,
    tmFiber48Row_13_ok,
    tmFiber48Row_14_ok,
    tmFiber48Row_15_ok,
    tmFiber48Parent_0_ok,
    tmFiber48Parent_1_ok,
    tmFiber48Parent_2_ok,
    tmFiber48Parent_3_ok,
    tmFiber48Parent_4_ok,
    tmFiber48Parent_5_ok,
    tmFiber48Parent_6_ok,
    tmFiber48Parent_7_ok,
    tmFiber48Parent_8_ok,
    tmFiber48Parent_9_ok,
    tmFiber48Parent_10_ok,
    tmFiber48Parent_11_ok,
    tmFiber48Parent_12_ok,
    tmFiber48Parent_13_ok,
    tmFiber48Parent_14_ok,
    tmFiber48Parent_15_ok]

def tmFiber49Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.b]

def tmFiber49Expected : List Nat :=
  [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]

def tmFiber49Rows : List DirectChainParentRow :=
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

def tmFiber49RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber49Rows i default

def tmFiber49SourcesCheck : Bool :=
  (tmFiber49Rows.map fun row => row.source) == tmFiber49Expected

theorem tmFiber49SourcesCheck_ok :
    tmFiber49SourcesCheck = true := by
  decide

def tmFiber49RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt i)

theorem tmFiber49Row_0_ok : tmFiber49RowCheck 0 = true := by decide
theorem tmFiber49Row_1_ok : tmFiber49RowCheck 1 = true := by decide
theorem tmFiber49Row_2_ok : tmFiber49RowCheck 2 = true := by decide
theorem tmFiber49Row_3_ok : tmFiber49RowCheck 3 = true := by decide
theorem tmFiber49Row_4_ok : tmFiber49RowCheck 4 = true := by decide
theorem tmFiber49Row_5_ok : tmFiber49RowCheck 5 = true := by decide
theorem tmFiber49Row_6_ok : tmFiber49RowCheck 6 = true := by decide
theorem tmFiber49Row_7_ok : tmFiber49RowCheck 7 = true := by decide
theorem tmFiber49Row_8_ok : tmFiber49RowCheck 8 = true := by decide
theorem tmFiber49Row_9_ok : tmFiber49RowCheck 9 = true := by decide
theorem tmFiber49Row_10_ok : tmFiber49RowCheck 10 = true := by decide
theorem tmFiber49Row_11_ok : tmFiber49RowCheck 11 = true := by decide
theorem tmFiber49Row_12_ok : tmFiber49RowCheck 12 = true := by decide
theorem tmFiber49Row_13_ok : tmFiber49RowCheck 13 = true := by decide
theorem tmFiber49Row_14_ok : tmFiber49RowCheck 14 = true := by decide
theorem tmFiber49Row_15_ok : tmFiber49RowCheck 15 = true := by decide

def tmFiber49ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber49Rows tmMaxParentDepth (listGetD tmFiber49Expected i 0) == 912

theorem tmFiber49Parent_0_ok : tmFiber49ParentCheck 0 = true := by decide
theorem tmFiber49Parent_1_ok : tmFiber49ParentCheck 1 = true := by decide
theorem tmFiber49Parent_2_ok : tmFiber49ParentCheck 2 = true := by decide
theorem tmFiber49Parent_3_ok : tmFiber49ParentCheck 3 = true := by decide
theorem tmFiber49Parent_4_ok : tmFiber49ParentCheck 4 = true := by decide
theorem tmFiber49Parent_5_ok : tmFiber49ParentCheck 5 = true := by decide
theorem tmFiber49Parent_6_ok : tmFiber49ParentCheck 6 = true := by decide
theorem tmFiber49Parent_7_ok : tmFiber49ParentCheck 7 = true := by decide
theorem tmFiber49Parent_8_ok : tmFiber49ParentCheck 8 = true := by decide
theorem tmFiber49Parent_9_ok : tmFiber49ParentCheck 9 = true := by decide
theorem tmFiber49Parent_10_ok : tmFiber49ParentCheck 10 = true := by decide
theorem tmFiber49Parent_11_ok : tmFiber49ParentCheck 11 = true := by decide
theorem tmFiber49Parent_12_ok : tmFiber49ParentCheck 12 = true := by decide
theorem tmFiber49Parent_13_ok : tmFiber49ParentCheck 13 = true := by decide
theorem tmFiber49Parent_14_ok : tmFiber49ParentCheck 14 = true := by decide
theorem tmFiber49Parent_15_ok : tmFiber49ParentCheck 15 = true := by decide

def tmFiber49CertificateAudit : Bool :=
  tmFiber49SourcesCheck &&
    tmFiber49RowCheck 0 &&
    tmFiber49RowCheck 1 &&
    tmFiber49RowCheck 2 &&
    tmFiber49RowCheck 3 &&
    tmFiber49RowCheck 4 &&
    tmFiber49RowCheck 5 &&
    tmFiber49RowCheck 6 &&
    tmFiber49RowCheck 7 &&
    tmFiber49RowCheck 8 &&
    tmFiber49RowCheck 9 &&
    tmFiber49RowCheck 10 &&
    tmFiber49RowCheck 11 &&
    tmFiber49RowCheck 12 &&
    tmFiber49RowCheck 13 &&
    tmFiber49RowCheck 14 &&
    tmFiber49RowCheck 15 &&
    tmFiber49ParentCheck 0 &&
    tmFiber49ParentCheck 1 &&
    tmFiber49ParentCheck 2 &&
    tmFiber49ParentCheck 3 &&
    tmFiber49ParentCheck 4 &&
    tmFiber49ParentCheck 5 &&
    tmFiber49ParentCheck 6 &&
    tmFiber49ParentCheck 7 &&
    tmFiber49ParentCheck 8 &&
    tmFiber49ParentCheck 9 &&
    tmFiber49ParentCheck 10 &&
    tmFiber49ParentCheck 11 &&
    tmFiber49ParentCheck 12 &&
    tmFiber49ParentCheck 13 &&
    tmFiber49ParentCheck 14 &&
    tmFiber49ParentCheck 15

theorem tmFiber49CertificateAudit_ok :
    tmFiber49CertificateAudit = true := by
  simp [tmFiber49CertificateAudit,
    tmFiber49SourcesCheck_ok,
    tmFiber49Row_0_ok,
    tmFiber49Row_1_ok,
    tmFiber49Row_2_ok,
    tmFiber49Row_3_ok,
    tmFiber49Row_4_ok,
    tmFiber49Row_5_ok,
    tmFiber49Row_6_ok,
    tmFiber49Row_7_ok,
    tmFiber49Row_8_ok,
    tmFiber49Row_9_ok,
    tmFiber49Row_10_ok,
    tmFiber49Row_11_ok,
    tmFiber49Row_12_ok,
    tmFiber49Row_13_ok,
    tmFiber49Row_14_ok,
    tmFiber49Row_15_ok,
    tmFiber49Parent_0_ok,
    tmFiber49Parent_1_ok,
    tmFiber49Parent_2_ok,
    tmFiber49Parent_3_ok,
    tmFiber49Parent_4_ok,
    tmFiber49Parent_5_ok,
    tmFiber49Parent_6_ok,
    tmFiber49Parent_7_ok,
    tmFiber49Parent_8_ok,
    tmFiber49Parent_9_ok,
    tmFiber49Parent_10_ok,
    tmFiber49Parent_11_ok,
    tmFiber49Parent_12_ok,
    tmFiber49Parent_13_ok,
    tmFiber49Parent_14_ok,
    tmFiber49Parent_15_ok]

def tmFiber50Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.p]

def tmFiber50Expected : List Nat :=
  [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]

def tmFiber50Rows : List DirectChainParentRow :=
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

def tmFiber50RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber50Rows i default

def tmFiber50SourcesCheck : Bool :=
  (tmFiber50Rows.map fun row => row.source) == tmFiber50Expected

theorem tmFiber50SourcesCheck_ok :
    tmFiber50SourcesCheck = true := by
  decide

def tmFiber50RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber50Key tmFiber50Expected (tmFiber50RowAt i)

theorem tmFiber50Row_0_ok : tmFiber50RowCheck 0 = true := by decide
theorem tmFiber50Row_1_ok : tmFiber50RowCheck 1 = true := by decide
theorem tmFiber50Row_2_ok : tmFiber50RowCheck 2 = true := by decide
theorem tmFiber50Row_3_ok : tmFiber50RowCheck 3 = true := by decide
theorem tmFiber50Row_4_ok : tmFiber50RowCheck 4 = true := by decide
theorem tmFiber50Row_5_ok : tmFiber50RowCheck 5 = true := by decide
theorem tmFiber50Row_6_ok : tmFiber50RowCheck 6 = true := by decide
theorem tmFiber50Row_7_ok : tmFiber50RowCheck 7 = true := by decide
theorem tmFiber50Row_8_ok : tmFiber50RowCheck 8 = true := by decide
theorem tmFiber50Row_9_ok : tmFiber50RowCheck 9 = true := by decide
theorem tmFiber50Row_10_ok : tmFiber50RowCheck 10 = true := by decide
theorem tmFiber50Row_11_ok : tmFiber50RowCheck 11 = true := by decide
theorem tmFiber50Row_12_ok : tmFiber50RowCheck 12 = true := by decide
theorem tmFiber50Row_13_ok : tmFiber50RowCheck 13 = true := by decide
theorem tmFiber50Row_14_ok : tmFiber50RowCheck 14 = true := by decide
theorem tmFiber50Row_15_ok : tmFiber50RowCheck 15 = true := by decide
theorem tmFiber50Row_16_ok : tmFiber50RowCheck 16 = true := by decide
theorem tmFiber50Row_17_ok : tmFiber50RowCheck 17 = true := by decide
theorem tmFiber50Row_18_ok : tmFiber50RowCheck 18 = true := by decide
theorem tmFiber50Row_19_ok : tmFiber50RowCheck 19 = true := by decide
theorem tmFiber50Row_20_ok : tmFiber50RowCheck 20 = true := by decide
theorem tmFiber50Row_21_ok : tmFiber50RowCheck 21 = true := by decide
theorem tmFiber50Row_22_ok : tmFiber50RowCheck 22 = true := by decide
theorem tmFiber50Row_23_ok : tmFiber50RowCheck 23 = true := by decide
theorem tmFiber50Row_24_ok : tmFiber50RowCheck 24 = true := by decide
theorem tmFiber50Row_25_ok : tmFiber50RowCheck 25 = true := by decide
theorem tmFiber50Row_26_ok : tmFiber50RowCheck 26 = true := by decide
theorem tmFiber50Row_27_ok : tmFiber50RowCheck 27 = true := by decide
theorem tmFiber50Row_28_ok : tmFiber50RowCheck 28 = true := by decide
theorem tmFiber50Row_29_ok : tmFiber50RowCheck 29 = true := by decide
theorem tmFiber50Row_30_ok : tmFiber50RowCheck 30 = true := by decide
theorem tmFiber50Row_31_ok : tmFiber50RowCheck 31 = true := by decide
theorem tmFiber50Row_32_ok : tmFiber50RowCheck 32 = true := by decide
theorem tmFiber50Row_33_ok : tmFiber50RowCheck 33 = true := by decide
theorem tmFiber50Row_34_ok : tmFiber50RowCheck 34 = true := by decide
theorem tmFiber50Row_35_ok : tmFiber50RowCheck 35 = true := by decide
theorem tmFiber50Row_36_ok : tmFiber50RowCheck 36 = true := by decide
theorem tmFiber50Row_37_ok : tmFiber50RowCheck 37 = true := by decide
theorem tmFiber50Row_38_ok : tmFiber50RowCheck 38 = true := by decide
theorem tmFiber50Row_39_ok : tmFiber50RowCheck 39 = true := by decide
theorem tmFiber50Row_40_ok : tmFiber50RowCheck 40 = true := by decide
theorem tmFiber50Row_41_ok : tmFiber50RowCheck 41 = true := by decide
theorem tmFiber50Row_42_ok : tmFiber50RowCheck 42 = true := by decide
theorem tmFiber50Row_43_ok : tmFiber50RowCheck 43 = true := by decide
theorem tmFiber50Row_44_ok : tmFiber50RowCheck 44 = true := by decide
theorem tmFiber50Row_45_ok : tmFiber50RowCheck 45 = true := by decide
theorem tmFiber50Row_46_ok : tmFiber50RowCheck 46 = true := by decide
theorem tmFiber50Row_47_ok : tmFiber50RowCheck 47 = true := by decide
theorem tmFiber50Row_48_ok : tmFiber50RowCheck 48 = true := by decide
theorem tmFiber50Row_49_ok : tmFiber50RowCheck 49 = true := by decide
theorem tmFiber50Row_50_ok : tmFiber50RowCheck 50 = true := by decide
theorem tmFiber50Row_51_ok : tmFiber50RowCheck 51 = true := by decide
theorem tmFiber50Row_52_ok : tmFiber50RowCheck 52 = true := by decide
theorem tmFiber50Row_53_ok : tmFiber50RowCheck 53 = true := by decide
theorem tmFiber50Row_54_ok : tmFiber50RowCheck 54 = true := by decide
theorem tmFiber50Row_55_ok : tmFiber50RowCheck 55 = true := by decide
theorem tmFiber50Row_56_ok : tmFiber50RowCheck 56 = true := by decide
theorem tmFiber50Row_57_ok : tmFiber50RowCheck 57 = true := by decide
theorem tmFiber50Row_58_ok : tmFiber50RowCheck 58 = true := by decide
theorem tmFiber50Row_59_ok : tmFiber50RowCheck 59 = true := by decide
theorem tmFiber50Row_60_ok : tmFiber50RowCheck 60 = true := by decide
theorem tmFiber50Row_61_ok : tmFiber50RowCheck 61 = true := by decide
theorem tmFiber50Row_62_ok : tmFiber50RowCheck 62 = true := by decide
theorem tmFiber50Row_63_ok : tmFiber50RowCheck 63 = true := by decide

def tmFiber50ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber50Rows tmMaxParentDepth (listGetD tmFiber50Expected i 0) == 928

theorem tmFiber50Parent_0_ok : tmFiber50ParentCheck 0 = true := by decide
theorem tmFiber50Parent_1_ok : tmFiber50ParentCheck 1 = true := by decide
theorem tmFiber50Parent_2_ok : tmFiber50ParentCheck 2 = true := by decide
theorem tmFiber50Parent_3_ok : tmFiber50ParentCheck 3 = true := by decide
theorem tmFiber50Parent_4_ok : tmFiber50ParentCheck 4 = true := by decide
theorem tmFiber50Parent_5_ok : tmFiber50ParentCheck 5 = true := by decide
theorem tmFiber50Parent_6_ok : tmFiber50ParentCheck 6 = true := by decide
theorem tmFiber50Parent_7_ok : tmFiber50ParentCheck 7 = true := by decide
theorem tmFiber50Parent_8_ok : tmFiber50ParentCheck 8 = true := by decide
theorem tmFiber50Parent_9_ok : tmFiber50ParentCheck 9 = true := by decide
theorem tmFiber50Parent_10_ok : tmFiber50ParentCheck 10 = true := by decide
theorem tmFiber50Parent_11_ok : tmFiber50ParentCheck 11 = true := by decide
theorem tmFiber50Parent_12_ok : tmFiber50ParentCheck 12 = true := by decide
theorem tmFiber50Parent_13_ok : tmFiber50ParentCheck 13 = true := by decide
theorem tmFiber50Parent_14_ok : tmFiber50ParentCheck 14 = true := by decide
theorem tmFiber50Parent_15_ok : tmFiber50ParentCheck 15 = true := by decide
theorem tmFiber50Parent_16_ok : tmFiber50ParentCheck 16 = true := by decide
theorem tmFiber50Parent_17_ok : tmFiber50ParentCheck 17 = true := by decide
theorem tmFiber50Parent_18_ok : tmFiber50ParentCheck 18 = true := by decide
theorem tmFiber50Parent_19_ok : tmFiber50ParentCheck 19 = true := by decide
theorem tmFiber50Parent_20_ok : tmFiber50ParentCheck 20 = true := by decide
theorem tmFiber50Parent_21_ok : tmFiber50ParentCheck 21 = true := by decide
theorem tmFiber50Parent_22_ok : tmFiber50ParentCheck 22 = true := by decide
theorem tmFiber50Parent_23_ok : tmFiber50ParentCheck 23 = true := by decide
theorem tmFiber50Parent_24_ok : tmFiber50ParentCheck 24 = true := by decide
theorem tmFiber50Parent_25_ok : tmFiber50ParentCheck 25 = true := by decide
theorem tmFiber50Parent_26_ok : tmFiber50ParentCheck 26 = true := by decide
theorem tmFiber50Parent_27_ok : tmFiber50ParentCheck 27 = true := by decide
theorem tmFiber50Parent_28_ok : tmFiber50ParentCheck 28 = true := by decide
theorem tmFiber50Parent_29_ok : tmFiber50ParentCheck 29 = true := by decide
theorem tmFiber50Parent_30_ok : tmFiber50ParentCheck 30 = true := by decide
theorem tmFiber50Parent_31_ok : tmFiber50ParentCheck 31 = true := by decide
theorem tmFiber50Parent_32_ok : tmFiber50ParentCheck 32 = true := by decide
theorem tmFiber50Parent_33_ok : tmFiber50ParentCheck 33 = true := by decide
theorem tmFiber50Parent_34_ok : tmFiber50ParentCheck 34 = true := by decide
theorem tmFiber50Parent_35_ok : tmFiber50ParentCheck 35 = true := by decide
theorem tmFiber50Parent_36_ok : tmFiber50ParentCheck 36 = true := by decide
theorem tmFiber50Parent_37_ok : tmFiber50ParentCheck 37 = true := by decide
theorem tmFiber50Parent_38_ok : tmFiber50ParentCheck 38 = true := by decide
theorem tmFiber50Parent_39_ok : tmFiber50ParentCheck 39 = true := by decide
theorem tmFiber50Parent_40_ok : tmFiber50ParentCheck 40 = true := by decide
theorem tmFiber50Parent_41_ok : tmFiber50ParentCheck 41 = true := by decide
theorem tmFiber50Parent_42_ok : tmFiber50ParentCheck 42 = true := by decide
theorem tmFiber50Parent_43_ok : tmFiber50ParentCheck 43 = true := by decide
theorem tmFiber50Parent_44_ok : tmFiber50ParentCheck 44 = true := by decide
theorem tmFiber50Parent_45_ok : tmFiber50ParentCheck 45 = true := by decide
theorem tmFiber50Parent_46_ok : tmFiber50ParentCheck 46 = true := by decide
theorem tmFiber50Parent_47_ok : tmFiber50ParentCheck 47 = true := by decide
theorem tmFiber50Parent_48_ok : tmFiber50ParentCheck 48 = true := by decide
theorem tmFiber50Parent_49_ok : tmFiber50ParentCheck 49 = true := by decide
theorem tmFiber50Parent_50_ok : tmFiber50ParentCheck 50 = true := by decide
theorem tmFiber50Parent_51_ok : tmFiber50ParentCheck 51 = true := by decide
theorem tmFiber50Parent_52_ok : tmFiber50ParentCheck 52 = true := by decide
theorem tmFiber50Parent_53_ok : tmFiber50ParentCheck 53 = true := by decide
theorem tmFiber50Parent_54_ok : tmFiber50ParentCheck 54 = true := by decide
theorem tmFiber50Parent_55_ok : tmFiber50ParentCheck 55 = true := by decide
theorem tmFiber50Parent_56_ok : tmFiber50ParentCheck 56 = true := by decide
theorem tmFiber50Parent_57_ok : tmFiber50ParentCheck 57 = true := by decide
theorem tmFiber50Parent_58_ok : tmFiber50ParentCheck 58 = true := by decide
theorem tmFiber50Parent_59_ok : tmFiber50ParentCheck 59 = true := by decide
theorem tmFiber50Parent_60_ok : tmFiber50ParentCheck 60 = true := by decide
theorem tmFiber50Parent_61_ok : tmFiber50ParentCheck 61 = true := by decide
theorem tmFiber50Parent_62_ok : tmFiber50ParentCheck 62 = true := by decide
theorem tmFiber50Parent_63_ok : tmFiber50ParentCheck 63 = true := by decide

def tmFiber50CertificateAudit : Bool :=
  tmFiber50SourcesCheck &&
    tmFiber50RowCheck 0 &&
    tmFiber50RowCheck 1 &&
    tmFiber50RowCheck 2 &&
    tmFiber50RowCheck 3 &&
    tmFiber50RowCheck 4 &&
    tmFiber50RowCheck 5 &&
    tmFiber50RowCheck 6 &&
    tmFiber50RowCheck 7 &&
    tmFiber50RowCheck 8 &&
    tmFiber50RowCheck 9 &&
    tmFiber50RowCheck 10 &&
    tmFiber50RowCheck 11 &&
    tmFiber50RowCheck 12 &&
    tmFiber50RowCheck 13 &&
    tmFiber50RowCheck 14 &&
    tmFiber50RowCheck 15 &&
    tmFiber50RowCheck 16 &&
    tmFiber50RowCheck 17 &&
    tmFiber50RowCheck 18 &&
    tmFiber50RowCheck 19 &&
    tmFiber50RowCheck 20 &&
    tmFiber50RowCheck 21 &&
    tmFiber50RowCheck 22 &&
    tmFiber50RowCheck 23 &&
    tmFiber50RowCheck 24 &&
    tmFiber50RowCheck 25 &&
    tmFiber50RowCheck 26 &&
    tmFiber50RowCheck 27 &&
    tmFiber50RowCheck 28 &&
    tmFiber50RowCheck 29 &&
    tmFiber50RowCheck 30 &&
    tmFiber50RowCheck 31 &&
    tmFiber50RowCheck 32 &&
    tmFiber50RowCheck 33 &&
    tmFiber50RowCheck 34 &&
    tmFiber50RowCheck 35 &&
    tmFiber50RowCheck 36 &&
    tmFiber50RowCheck 37 &&
    tmFiber50RowCheck 38 &&
    tmFiber50RowCheck 39 &&
    tmFiber50RowCheck 40 &&
    tmFiber50RowCheck 41 &&
    tmFiber50RowCheck 42 &&
    tmFiber50RowCheck 43 &&
    tmFiber50RowCheck 44 &&
    tmFiber50RowCheck 45 &&
    tmFiber50RowCheck 46 &&
    tmFiber50RowCheck 47 &&
    tmFiber50RowCheck 48 &&
    tmFiber50RowCheck 49 &&
    tmFiber50RowCheck 50 &&
    tmFiber50RowCheck 51 &&
    tmFiber50RowCheck 52 &&
    tmFiber50RowCheck 53 &&
    tmFiber50RowCheck 54 &&
    tmFiber50RowCheck 55 &&
    tmFiber50RowCheck 56 &&
    tmFiber50RowCheck 57 &&
    tmFiber50RowCheck 58 &&
    tmFiber50RowCheck 59 &&
    tmFiber50RowCheck 60 &&
    tmFiber50RowCheck 61 &&
    tmFiber50RowCheck 62 &&
    tmFiber50RowCheck 63 &&
    tmFiber50ParentCheck 0 &&
    tmFiber50ParentCheck 1 &&
    tmFiber50ParentCheck 2 &&
    tmFiber50ParentCheck 3 &&
    tmFiber50ParentCheck 4 &&
    tmFiber50ParentCheck 5 &&
    tmFiber50ParentCheck 6 &&
    tmFiber50ParentCheck 7 &&
    tmFiber50ParentCheck 8 &&
    tmFiber50ParentCheck 9 &&
    tmFiber50ParentCheck 10 &&
    tmFiber50ParentCheck 11 &&
    tmFiber50ParentCheck 12 &&
    tmFiber50ParentCheck 13 &&
    tmFiber50ParentCheck 14 &&
    tmFiber50ParentCheck 15 &&
    tmFiber50ParentCheck 16 &&
    tmFiber50ParentCheck 17 &&
    tmFiber50ParentCheck 18 &&
    tmFiber50ParentCheck 19 &&
    tmFiber50ParentCheck 20 &&
    tmFiber50ParentCheck 21 &&
    tmFiber50ParentCheck 22 &&
    tmFiber50ParentCheck 23 &&
    tmFiber50ParentCheck 24 &&
    tmFiber50ParentCheck 25 &&
    tmFiber50ParentCheck 26 &&
    tmFiber50ParentCheck 27 &&
    tmFiber50ParentCheck 28 &&
    tmFiber50ParentCheck 29 &&
    tmFiber50ParentCheck 30 &&
    tmFiber50ParentCheck 31 &&
    tmFiber50ParentCheck 32 &&
    tmFiber50ParentCheck 33 &&
    tmFiber50ParentCheck 34 &&
    tmFiber50ParentCheck 35 &&
    tmFiber50ParentCheck 36 &&
    tmFiber50ParentCheck 37 &&
    tmFiber50ParentCheck 38 &&
    tmFiber50ParentCheck 39 &&
    tmFiber50ParentCheck 40 &&
    tmFiber50ParentCheck 41 &&
    tmFiber50ParentCheck 42 &&
    tmFiber50ParentCheck 43 &&
    tmFiber50ParentCheck 44 &&
    tmFiber50ParentCheck 45 &&
    tmFiber50ParentCheck 46 &&
    tmFiber50ParentCheck 47 &&
    tmFiber50ParentCheck 48 &&
    tmFiber50ParentCheck 49 &&
    tmFiber50ParentCheck 50 &&
    tmFiber50ParentCheck 51 &&
    tmFiber50ParentCheck 52 &&
    tmFiber50ParentCheck 53 &&
    tmFiber50ParentCheck 54 &&
    tmFiber50ParentCheck 55 &&
    tmFiber50ParentCheck 56 &&
    tmFiber50ParentCheck 57 &&
    tmFiber50ParentCheck 58 &&
    tmFiber50ParentCheck 59 &&
    tmFiber50ParentCheck 60 &&
    tmFiber50ParentCheck 61 &&
    tmFiber50ParentCheck 62 &&
    tmFiber50ParentCheck 63

theorem tmFiber50CertificateAudit_ok :
    tmFiber50CertificateAudit = true := by
  simp [tmFiber50CertificateAudit,
    tmFiber50SourcesCheck_ok,
    tmFiber50Row_0_ok,
    tmFiber50Row_1_ok,
    tmFiber50Row_2_ok,
    tmFiber50Row_3_ok,
    tmFiber50Row_4_ok,
    tmFiber50Row_5_ok,
    tmFiber50Row_6_ok,
    tmFiber50Row_7_ok,
    tmFiber50Row_8_ok,
    tmFiber50Row_9_ok,
    tmFiber50Row_10_ok,
    tmFiber50Row_11_ok,
    tmFiber50Row_12_ok,
    tmFiber50Row_13_ok,
    tmFiber50Row_14_ok,
    tmFiber50Row_15_ok,
    tmFiber50Row_16_ok,
    tmFiber50Row_17_ok,
    tmFiber50Row_18_ok,
    tmFiber50Row_19_ok,
    tmFiber50Row_20_ok,
    tmFiber50Row_21_ok,
    tmFiber50Row_22_ok,
    tmFiber50Row_23_ok,
    tmFiber50Row_24_ok,
    tmFiber50Row_25_ok,
    tmFiber50Row_26_ok,
    tmFiber50Row_27_ok,
    tmFiber50Row_28_ok,
    tmFiber50Row_29_ok,
    tmFiber50Row_30_ok,
    tmFiber50Row_31_ok,
    tmFiber50Row_32_ok,
    tmFiber50Row_33_ok,
    tmFiber50Row_34_ok,
    tmFiber50Row_35_ok,
    tmFiber50Row_36_ok,
    tmFiber50Row_37_ok,
    tmFiber50Row_38_ok,
    tmFiber50Row_39_ok,
    tmFiber50Row_40_ok,
    tmFiber50Row_41_ok,
    tmFiber50Row_42_ok,
    tmFiber50Row_43_ok,
    tmFiber50Row_44_ok,
    tmFiber50Row_45_ok,
    tmFiber50Row_46_ok,
    tmFiber50Row_47_ok,
    tmFiber50Row_48_ok,
    tmFiber50Row_49_ok,
    tmFiber50Row_50_ok,
    tmFiber50Row_51_ok,
    tmFiber50Row_52_ok,
    tmFiber50Row_53_ok,
    tmFiber50Row_54_ok,
    tmFiber50Row_55_ok,
    tmFiber50Row_56_ok,
    tmFiber50Row_57_ok,
    tmFiber50Row_58_ok,
    tmFiber50Row_59_ok,
    tmFiber50Row_60_ok,
    tmFiber50Row_61_ok,
    tmFiber50Row_62_ok,
    tmFiber50Row_63_ok,
    tmFiber50Parent_0_ok,
    tmFiber50Parent_1_ok,
    tmFiber50Parent_2_ok,
    tmFiber50Parent_3_ok,
    tmFiber50Parent_4_ok,
    tmFiber50Parent_5_ok,
    tmFiber50Parent_6_ok,
    tmFiber50Parent_7_ok,
    tmFiber50Parent_8_ok,
    tmFiber50Parent_9_ok,
    tmFiber50Parent_10_ok,
    tmFiber50Parent_11_ok,
    tmFiber50Parent_12_ok,
    tmFiber50Parent_13_ok,
    tmFiber50Parent_14_ok,
    tmFiber50Parent_15_ok,
    tmFiber50Parent_16_ok,
    tmFiber50Parent_17_ok,
    tmFiber50Parent_18_ok,
    tmFiber50Parent_19_ok,
    tmFiber50Parent_20_ok,
    tmFiber50Parent_21_ok,
    tmFiber50Parent_22_ok,
    tmFiber50Parent_23_ok,
    tmFiber50Parent_24_ok,
    tmFiber50Parent_25_ok,
    tmFiber50Parent_26_ok,
    tmFiber50Parent_27_ok,
    tmFiber50Parent_28_ok,
    tmFiber50Parent_29_ok,
    tmFiber50Parent_30_ok,
    tmFiber50Parent_31_ok,
    tmFiber50Parent_32_ok,
    tmFiber50Parent_33_ok,
    tmFiber50Parent_34_ok,
    tmFiber50Parent_35_ok,
    tmFiber50Parent_36_ok,
    tmFiber50Parent_37_ok,
    tmFiber50Parent_38_ok,
    tmFiber50Parent_39_ok,
    tmFiber50Parent_40_ok,
    tmFiber50Parent_41_ok,
    tmFiber50Parent_42_ok,
    tmFiber50Parent_43_ok,
    tmFiber50Parent_44_ok,
    tmFiber50Parent_45_ok,
    tmFiber50Parent_46_ok,
    tmFiber50Parent_47_ok,
    tmFiber50Parent_48_ok,
    tmFiber50Parent_49_ok,
    tmFiber50Parent_50_ok,
    tmFiber50Parent_51_ok,
    tmFiber50Parent_52_ok,
    tmFiber50Parent_53_ok,
    tmFiber50Parent_54_ok,
    tmFiber50Parent_55_ok,
    tmFiber50Parent_56_ok,
    tmFiber50Parent_57_ok,
    tmFiber50Parent_58_ok,
    tmFiber50Parent_59_ok,
    tmFiber50Parent_60_ok,
    tmFiber50Parent_61_ok,
    tmFiber50Parent_62_ok,
    tmFiber50Parent_63_ok]

def tmFiber51Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.r]

def tmFiber51Expected : List Nat :=
  []

def tmFiber51Rows : List DirectChainParentRow :=
  []

def tmFiber51RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber51Rows i default

def tmFiber51SourcesCheck : Bool :=
  (tmFiber51Rows.map fun row => row.source) == tmFiber51Expected

theorem tmFiber51SourcesCheck_ok :
    tmFiber51SourcesCheck = true := by
  decide

def tmFiber51RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber51Key tmFiber51Expected (tmFiber51RowAt i)

def tmFiber51ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber51Rows tmMaxParentDepth (listGetD tmFiber51Expected i 0) == 0

def tmFiber51CertificateAudit : Bool :=
  tmFiber51SourcesCheck

theorem tmFiber51CertificateAudit_ok :
    tmFiber51CertificateAudit = true := by
  simp [tmFiber51CertificateAudit,
    tmFiber51SourcesCheck_ok]

def tmFiber52Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.b]

def tmFiber52Expected : List Nat :=
  []

def tmFiber52Rows : List DirectChainParentRow :=
  []

def tmFiber52RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber52Rows i default

def tmFiber52SourcesCheck : Bool :=
  (tmFiber52Rows.map fun row => row.source) == tmFiber52Expected

theorem tmFiber52SourcesCheck_ok :
    tmFiber52SourcesCheck = true := by
  decide

def tmFiber52RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber52Key tmFiber52Expected (tmFiber52RowAt i)

def tmFiber52ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber52Rows tmMaxParentDepth (listGetD tmFiber52Expected i 0) == 0

def tmFiber52CertificateAudit : Bool :=
  tmFiber52SourcesCheck

theorem tmFiber52CertificateAudit_ok :
    tmFiber52CertificateAudit = true := by
  simp [tmFiber52CertificateAudit,
    tmFiber52SourcesCheck_ok]

def tmFiber53Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.p]

def tmFiber53Expected : List Nat :=
  []

def tmFiber53Rows : List DirectChainParentRow :=
  []

def tmFiber53RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber53Rows i default

def tmFiber53SourcesCheck : Bool :=
  (tmFiber53Rows.map fun row => row.source) == tmFiber53Expected

theorem tmFiber53SourcesCheck_ok :
    tmFiber53SourcesCheck = true := by
  decide

def tmFiber53RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber53Key tmFiber53Expected (tmFiber53RowAt i)

def tmFiber53ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber53Rows tmMaxParentDepth (listGetD tmFiber53Expected i 0) == 0

def tmFiber53CertificateAudit : Bool :=
  tmFiber53SourcesCheck

theorem tmFiber53CertificateAudit_ok :
    tmFiber53CertificateAudit = true := by
  simp [tmFiber53CertificateAudit,
    tmFiber53SourcesCheck_ok]

def tmFiber54Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.r]

def tmFiber54Expected : List Nat :=
  []

def tmFiber54Rows : List DirectChainParentRow :=
  []

def tmFiber54RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber54Rows i default

def tmFiber54SourcesCheck : Bool :=
  (tmFiber54Rows.map fun row => row.source) == tmFiber54Expected

theorem tmFiber54SourcesCheck_ok :
    tmFiber54SourcesCheck = true := by
  decide

def tmFiber54RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber54Key tmFiber54Expected (tmFiber54RowAt i)

def tmFiber54ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber54Rows tmMaxParentDepth (listGetD tmFiber54Expected i 0) == 0

def tmFiber54CertificateAudit : Bool :=
  tmFiber54SourcesCheck

theorem tmFiber54CertificateAudit_ok :
    tmFiber54CertificateAudit = true := by
  simp [tmFiber54CertificateAudit,
    tmFiber54SourcesCheck_ok]

def tmFiber55Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.b]

def tmFiber55Expected : List Nat :=
  []

def tmFiber55Rows : List DirectChainParentRow :=
  []

def tmFiber55RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber55Rows i default

def tmFiber55SourcesCheck : Bool :=
  (tmFiber55Rows.map fun row => row.source) == tmFiber55Expected

theorem tmFiber55SourcesCheck_ok :
    tmFiber55SourcesCheck = true := by
  decide

def tmFiber55RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber55Key tmFiber55Expected (tmFiber55RowAt i)

def tmFiber55ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber55Rows tmMaxParentDepth (listGetD tmFiber55Expected i 0) == 0

def tmFiber55CertificateAudit : Bool :=
  tmFiber55SourcesCheck

theorem tmFiber55CertificateAudit_ok :
    tmFiber55CertificateAudit = true := by
  simp [tmFiber55CertificateAudit,
    tmFiber55SourcesCheck_ok]

def tmFiber56Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.p]

def tmFiber56Expected : List Nat :=
  []

def tmFiber56Rows : List DirectChainParentRow :=
  []

def tmFiber56RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber56Rows i default

def tmFiber56SourcesCheck : Bool :=
  (tmFiber56Rows.map fun row => row.source) == tmFiber56Expected

theorem tmFiber56SourcesCheck_ok :
    tmFiber56SourcesCheck = true := by
  decide

def tmFiber56RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber56Key tmFiber56Expected (tmFiber56RowAt i)

def tmFiber56ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber56Rows tmMaxParentDepth (listGetD tmFiber56Expected i 0) == 0

def tmFiber56CertificateAudit : Bool :=
  tmFiber56SourcesCheck

theorem tmFiber56CertificateAudit_ok :
    tmFiber56CertificateAudit = true := by
  simp [tmFiber56CertificateAudit,
    tmFiber56SourcesCheck_ok]

def tmFiber57Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.r]

def tmFiber57Expected : List Nat :=
  []

def tmFiber57Rows : List DirectChainParentRow :=
  []

def tmFiber57RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber57Rows i default

def tmFiber57SourcesCheck : Bool :=
  (tmFiber57Rows.map fun row => row.source) == tmFiber57Expected

theorem tmFiber57SourcesCheck_ok :
    tmFiber57SourcesCheck = true := by
  decide

def tmFiber57RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber57Key tmFiber57Expected (tmFiber57RowAt i)

def tmFiber57ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber57Rows tmMaxParentDepth (listGetD tmFiber57Expected i 0) == 0

def tmFiber57CertificateAudit : Bool :=
  tmFiber57SourcesCheck

theorem tmFiber57CertificateAudit_ok :
    tmFiber57CertificateAudit = true := by
  simp [tmFiber57CertificateAudit,
    tmFiber57SourcesCheck_ok]

def tmFiber58Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.b]

def tmFiber58Expected : List Nat :=
  []

def tmFiber58Rows : List DirectChainParentRow :=
  []

def tmFiber58RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber58Rows i default

def tmFiber58SourcesCheck : Bool :=
  (tmFiber58Rows.map fun row => row.source) == tmFiber58Expected

theorem tmFiber58SourcesCheck_ok :
    tmFiber58SourcesCheck = true := by
  decide

def tmFiber58RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber58Key tmFiber58Expected (tmFiber58RowAt i)

def tmFiber58ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber58Rows tmMaxParentDepth (listGetD tmFiber58Expected i 0) == 0

def tmFiber58CertificateAudit : Bool :=
  tmFiber58SourcesCheck

theorem tmFiber58CertificateAudit_ok :
    tmFiber58CertificateAudit = true := by
  simp [tmFiber58CertificateAudit,
    tmFiber58SourcesCheck_ok]

def tmFiber59Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.p]

def tmFiber59Expected : List Nat :=
  []

def tmFiber59Rows : List DirectChainParentRow :=
  []

def tmFiber59RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber59Rows i default

def tmFiber59SourcesCheck : Bool :=
  (tmFiber59Rows.map fun row => row.source) == tmFiber59Expected

theorem tmFiber59SourcesCheck_ok :
    tmFiber59SourcesCheck = true := by
  decide

def tmFiber59RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber59Key tmFiber59Expected (tmFiber59RowAt i)

def tmFiber59ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber59Rows tmMaxParentDepth (listGetD tmFiber59Expected i 0) == 0

def tmFiber59CertificateAudit : Bool :=
  tmFiber59SourcesCheck

theorem tmFiber59CertificateAudit_ok :
    tmFiber59CertificateAudit = true := by
  simp [tmFiber59CertificateAudit,
    tmFiber59SourcesCheck_ok]

def tmFiber60Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.r]

def tmFiber60Expected : List Nat :=
  [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]

def tmFiber60Rows : List DirectChainParentRow :=
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

def tmFiber60RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber60Rows i default

def tmFiber60SourcesCheck : Bool :=
  (tmFiber60Rows.map fun row => row.source) == tmFiber60Expected

theorem tmFiber60SourcesCheck_ok :
    tmFiber60SourcesCheck = true := by
  decide

def tmFiber60RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber60Key tmFiber60Expected (tmFiber60RowAt i)

theorem tmFiber60Row_0_ok : tmFiber60RowCheck 0 = true := by decide
theorem tmFiber60Row_1_ok : tmFiber60RowCheck 1 = true := by decide
theorem tmFiber60Row_2_ok : tmFiber60RowCheck 2 = true := by decide
theorem tmFiber60Row_3_ok : tmFiber60RowCheck 3 = true := by decide
theorem tmFiber60Row_4_ok : tmFiber60RowCheck 4 = true := by decide
theorem tmFiber60Row_5_ok : tmFiber60RowCheck 5 = true := by decide
theorem tmFiber60Row_6_ok : tmFiber60RowCheck 6 = true := by decide
theorem tmFiber60Row_7_ok : tmFiber60RowCheck 7 = true := by decide
theorem tmFiber60Row_8_ok : tmFiber60RowCheck 8 = true := by decide
theorem tmFiber60Row_9_ok : tmFiber60RowCheck 9 = true := by decide
theorem tmFiber60Row_10_ok : tmFiber60RowCheck 10 = true := by decide
theorem tmFiber60Row_11_ok : tmFiber60RowCheck 11 = true := by decide
theorem tmFiber60Row_12_ok : tmFiber60RowCheck 12 = true := by decide
theorem tmFiber60Row_13_ok : tmFiber60RowCheck 13 = true := by decide
theorem tmFiber60Row_14_ok : tmFiber60RowCheck 14 = true := by decide
theorem tmFiber60Row_15_ok : tmFiber60RowCheck 15 = true := by decide
theorem tmFiber60Row_16_ok : tmFiber60RowCheck 16 = true := by decide
theorem tmFiber60Row_17_ok : tmFiber60RowCheck 17 = true := by decide
theorem tmFiber60Row_18_ok : tmFiber60RowCheck 18 = true := by decide
theorem tmFiber60Row_19_ok : tmFiber60RowCheck 19 = true := by decide
theorem tmFiber60Row_20_ok : tmFiber60RowCheck 20 = true := by decide
theorem tmFiber60Row_21_ok : tmFiber60RowCheck 21 = true := by decide
theorem tmFiber60Row_22_ok : tmFiber60RowCheck 22 = true := by decide
theorem tmFiber60Row_23_ok : tmFiber60RowCheck 23 = true := by decide
theorem tmFiber60Row_24_ok : tmFiber60RowCheck 24 = true := by decide
theorem tmFiber60Row_25_ok : tmFiber60RowCheck 25 = true := by decide
theorem tmFiber60Row_26_ok : tmFiber60RowCheck 26 = true := by decide
theorem tmFiber60Row_27_ok : tmFiber60RowCheck 27 = true := by decide
theorem tmFiber60Row_28_ok : tmFiber60RowCheck 28 = true := by decide
theorem tmFiber60Row_29_ok : tmFiber60RowCheck 29 = true := by decide
theorem tmFiber60Row_30_ok : tmFiber60RowCheck 30 = true := by decide
theorem tmFiber60Row_31_ok : tmFiber60RowCheck 31 = true := by decide
theorem tmFiber60Row_32_ok : tmFiber60RowCheck 32 = true := by decide
theorem tmFiber60Row_33_ok : tmFiber60RowCheck 33 = true := by decide
theorem tmFiber60Row_34_ok : tmFiber60RowCheck 34 = true := by decide
theorem tmFiber60Row_35_ok : tmFiber60RowCheck 35 = true := by decide
theorem tmFiber60Row_36_ok : tmFiber60RowCheck 36 = true := by decide
theorem tmFiber60Row_37_ok : tmFiber60RowCheck 37 = true := by decide
theorem tmFiber60Row_38_ok : tmFiber60RowCheck 38 = true := by decide
theorem tmFiber60Row_39_ok : tmFiber60RowCheck 39 = true := by decide
theorem tmFiber60Row_40_ok : tmFiber60RowCheck 40 = true := by decide
theorem tmFiber60Row_41_ok : tmFiber60RowCheck 41 = true := by decide
theorem tmFiber60Row_42_ok : tmFiber60RowCheck 42 = true := by decide
theorem tmFiber60Row_43_ok : tmFiber60RowCheck 43 = true := by decide
theorem tmFiber60Row_44_ok : tmFiber60RowCheck 44 = true := by decide
theorem tmFiber60Row_45_ok : tmFiber60RowCheck 45 = true := by decide
theorem tmFiber60Row_46_ok : tmFiber60RowCheck 46 = true := by decide
theorem tmFiber60Row_47_ok : tmFiber60RowCheck 47 = true := by decide
theorem tmFiber60Row_48_ok : tmFiber60RowCheck 48 = true := by decide
theorem tmFiber60Row_49_ok : tmFiber60RowCheck 49 = true := by decide
theorem tmFiber60Row_50_ok : tmFiber60RowCheck 50 = true := by decide
theorem tmFiber60Row_51_ok : tmFiber60RowCheck 51 = true := by decide
theorem tmFiber60Row_52_ok : tmFiber60RowCheck 52 = true := by decide
theorem tmFiber60Row_53_ok : tmFiber60RowCheck 53 = true := by decide
theorem tmFiber60Row_54_ok : tmFiber60RowCheck 54 = true := by decide
theorem tmFiber60Row_55_ok : tmFiber60RowCheck 55 = true := by decide
theorem tmFiber60Row_56_ok : tmFiber60RowCheck 56 = true := by decide
theorem tmFiber60Row_57_ok : tmFiber60RowCheck 57 = true := by decide
theorem tmFiber60Row_58_ok : tmFiber60RowCheck 58 = true := by decide
theorem tmFiber60Row_59_ok : tmFiber60RowCheck 59 = true := by decide
theorem tmFiber60Row_60_ok : tmFiber60RowCheck 60 = true := by decide
theorem tmFiber60Row_61_ok : tmFiber60RowCheck 61 = true := by decide
theorem tmFiber60Row_62_ok : tmFiber60RowCheck 62 = true := by decide
theorem tmFiber60Row_63_ok : tmFiber60RowCheck 63 = true := by decide

def tmFiber60ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber60Rows tmMaxParentDepth (listGetD tmFiber60Expected i 0) == 96

theorem tmFiber60Parent_0_ok : tmFiber60ParentCheck 0 = true := by decide
theorem tmFiber60Parent_1_ok : tmFiber60ParentCheck 1 = true := by decide
theorem tmFiber60Parent_2_ok : tmFiber60ParentCheck 2 = true := by decide
theorem tmFiber60Parent_3_ok : tmFiber60ParentCheck 3 = true := by decide
theorem tmFiber60Parent_4_ok : tmFiber60ParentCheck 4 = true := by decide
theorem tmFiber60Parent_5_ok : tmFiber60ParentCheck 5 = true := by decide
theorem tmFiber60Parent_6_ok : tmFiber60ParentCheck 6 = true := by decide
theorem tmFiber60Parent_7_ok : tmFiber60ParentCheck 7 = true := by decide
theorem tmFiber60Parent_8_ok : tmFiber60ParentCheck 8 = true := by decide
theorem tmFiber60Parent_9_ok : tmFiber60ParentCheck 9 = true := by decide
theorem tmFiber60Parent_10_ok : tmFiber60ParentCheck 10 = true := by decide
theorem tmFiber60Parent_11_ok : tmFiber60ParentCheck 11 = true := by decide
theorem tmFiber60Parent_12_ok : tmFiber60ParentCheck 12 = true := by decide
theorem tmFiber60Parent_13_ok : tmFiber60ParentCheck 13 = true := by decide
theorem tmFiber60Parent_14_ok : tmFiber60ParentCheck 14 = true := by decide
theorem tmFiber60Parent_15_ok : tmFiber60ParentCheck 15 = true := by decide
theorem tmFiber60Parent_16_ok : tmFiber60ParentCheck 16 = true := by decide
theorem tmFiber60Parent_17_ok : tmFiber60ParentCheck 17 = true := by decide
theorem tmFiber60Parent_18_ok : tmFiber60ParentCheck 18 = true := by decide
theorem tmFiber60Parent_19_ok : tmFiber60ParentCheck 19 = true := by decide
theorem tmFiber60Parent_20_ok : tmFiber60ParentCheck 20 = true := by decide
theorem tmFiber60Parent_21_ok : tmFiber60ParentCheck 21 = true := by decide
theorem tmFiber60Parent_22_ok : tmFiber60ParentCheck 22 = true := by decide
theorem tmFiber60Parent_23_ok : tmFiber60ParentCheck 23 = true := by decide
theorem tmFiber60Parent_24_ok : tmFiber60ParentCheck 24 = true := by decide
theorem tmFiber60Parent_25_ok : tmFiber60ParentCheck 25 = true := by decide
theorem tmFiber60Parent_26_ok : tmFiber60ParentCheck 26 = true := by decide
theorem tmFiber60Parent_27_ok : tmFiber60ParentCheck 27 = true := by decide
theorem tmFiber60Parent_28_ok : tmFiber60ParentCheck 28 = true := by decide
theorem tmFiber60Parent_29_ok : tmFiber60ParentCheck 29 = true := by decide
theorem tmFiber60Parent_30_ok : tmFiber60ParentCheck 30 = true := by decide
theorem tmFiber60Parent_31_ok : tmFiber60ParentCheck 31 = true := by decide
theorem tmFiber60Parent_32_ok : tmFiber60ParentCheck 32 = true := by decide
theorem tmFiber60Parent_33_ok : tmFiber60ParentCheck 33 = true := by decide
theorem tmFiber60Parent_34_ok : tmFiber60ParentCheck 34 = true := by decide
theorem tmFiber60Parent_35_ok : tmFiber60ParentCheck 35 = true := by decide
theorem tmFiber60Parent_36_ok : tmFiber60ParentCheck 36 = true := by decide
theorem tmFiber60Parent_37_ok : tmFiber60ParentCheck 37 = true := by decide
theorem tmFiber60Parent_38_ok : tmFiber60ParentCheck 38 = true := by decide
theorem tmFiber60Parent_39_ok : tmFiber60ParentCheck 39 = true := by decide
theorem tmFiber60Parent_40_ok : tmFiber60ParentCheck 40 = true := by decide
theorem tmFiber60Parent_41_ok : tmFiber60ParentCheck 41 = true := by decide
theorem tmFiber60Parent_42_ok : tmFiber60ParentCheck 42 = true := by decide
theorem tmFiber60Parent_43_ok : tmFiber60ParentCheck 43 = true := by decide
theorem tmFiber60Parent_44_ok : tmFiber60ParentCheck 44 = true := by decide
theorem tmFiber60Parent_45_ok : tmFiber60ParentCheck 45 = true := by decide
theorem tmFiber60Parent_46_ok : tmFiber60ParentCheck 46 = true := by decide
theorem tmFiber60Parent_47_ok : tmFiber60ParentCheck 47 = true := by decide
theorem tmFiber60Parent_48_ok : tmFiber60ParentCheck 48 = true := by decide
theorem tmFiber60Parent_49_ok : tmFiber60ParentCheck 49 = true := by decide
theorem tmFiber60Parent_50_ok : tmFiber60ParentCheck 50 = true := by decide
theorem tmFiber60Parent_51_ok : tmFiber60ParentCheck 51 = true := by decide
theorem tmFiber60Parent_52_ok : tmFiber60ParentCheck 52 = true := by decide
theorem tmFiber60Parent_53_ok : tmFiber60ParentCheck 53 = true := by decide
theorem tmFiber60Parent_54_ok : tmFiber60ParentCheck 54 = true := by decide
theorem tmFiber60Parent_55_ok : tmFiber60ParentCheck 55 = true := by decide
theorem tmFiber60Parent_56_ok : tmFiber60ParentCheck 56 = true := by decide
theorem tmFiber60Parent_57_ok : tmFiber60ParentCheck 57 = true := by decide
theorem tmFiber60Parent_58_ok : tmFiber60ParentCheck 58 = true := by decide
theorem tmFiber60Parent_59_ok : tmFiber60ParentCheck 59 = true := by decide
theorem tmFiber60Parent_60_ok : tmFiber60ParentCheck 60 = true := by decide
theorem tmFiber60Parent_61_ok : tmFiber60ParentCheck 61 = true := by decide
theorem tmFiber60Parent_62_ok : tmFiber60ParentCheck 62 = true := by decide
theorem tmFiber60Parent_63_ok : tmFiber60ParentCheck 63 = true := by decide

def tmFiber60CertificateAudit : Bool :=
  tmFiber60SourcesCheck &&
    tmFiber60RowCheck 0 &&
    tmFiber60RowCheck 1 &&
    tmFiber60RowCheck 2 &&
    tmFiber60RowCheck 3 &&
    tmFiber60RowCheck 4 &&
    tmFiber60RowCheck 5 &&
    tmFiber60RowCheck 6 &&
    tmFiber60RowCheck 7 &&
    tmFiber60RowCheck 8 &&
    tmFiber60RowCheck 9 &&
    tmFiber60RowCheck 10 &&
    tmFiber60RowCheck 11 &&
    tmFiber60RowCheck 12 &&
    tmFiber60RowCheck 13 &&
    tmFiber60RowCheck 14 &&
    tmFiber60RowCheck 15 &&
    tmFiber60RowCheck 16 &&
    tmFiber60RowCheck 17 &&
    tmFiber60RowCheck 18 &&
    tmFiber60RowCheck 19 &&
    tmFiber60RowCheck 20 &&
    tmFiber60RowCheck 21 &&
    tmFiber60RowCheck 22 &&
    tmFiber60RowCheck 23 &&
    tmFiber60RowCheck 24 &&
    tmFiber60RowCheck 25 &&
    tmFiber60RowCheck 26 &&
    tmFiber60RowCheck 27 &&
    tmFiber60RowCheck 28 &&
    tmFiber60RowCheck 29 &&
    tmFiber60RowCheck 30 &&
    tmFiber60RowCheck 31 &&
    tmFiber60RowCheck 32 &&
    tmFiber60RowCheck 33 &&
    tmFiber60RowCheck 34 &&
    tmFiber60RowCheck 35 &&
    tmFiber60RowCheck 36 &&
    tmFiber60RowCheck 37 &&
    tmFiber60RowCheck 38 &&
    tmFiber60RowCheck 39 &&
    tmFiber60RowCheck 40 &&
    tmFiber60RowCheck 41 &&
    tmFiber60RowCheck 42 &&
    tmFiber60RowCheck 43 &&
    tmFiber60RowCheck 44 &&
    tmFiber60RowCheck 45 &&
    tmFiber60RowCheck 46 &&
    tmFiber60RowCheck 47 &&
    tmFiber60RowCheck 48 &&
    tmFiber60RowCheck 49 &&
    tmFiber60RowCheck 50 &&
    tmFiber60RowCheck 51 &&
    tmFiber60RowCheck 52 &&
    tmFiber60RowCheck 53 &&
    tmFiber60RowCheck 54 &&
    tmFiber60RowCheck 55 &&
    tmFiber60RowCheck 56 &&
    tmFiber60RowCheck 57 &&
    tmFiber60RowCheck 58 &&
    tmFiber60RowCheck 59 &&
    tmFiber60RowCheck 60 &&
    tmFiber60RowCheck 61 &&
    tmFiber60RowCheck 62 &&
    tmFiber60RowCheck 63 &&
    tmFiber60ParentCheck 0 &&
    tmFiber60ParentCheck 1 &&
    tmFiber60ParentCheck 2 &&
    tmFiber60ParentCheck 3 &&
    tmFiber60ParentCheck 4 &&
    tmFiber60ParentCheck 5 &&
    tmFiber60ParentCheck 6 &&
    tmFiber60ParentCheck 7 &&
    tmFiber60ParentCheck 8 &&
    tmFiber60ParentCheck 9 &&
    tmFiber60ParentCheck 10 &&
    tmFiber60ParentCheck 11 &&
    tmFiber60ParentCheck 12 &&
    tmFiber60ParentCheck 13 &&
    tmFiber60ParentCheck 14 &&
    tmFiber60ParentCheck 15 &&
    tmFiber60ParentCheck 16 &&
    tmFiber60ParentCheck 17 &&
    tmFiber60ParentCheck 18 &&
    tmFiber60ParentCheck 19 &&
    tmFiber60ParentCheck 20 &&
    tmFiber60ParentCheck 21 &&
    tmFiber60ParentCheck 22 &&
    tmFiber60ParentCheck 23 &&
    tmFiber60ParentCheck 24 &&
    tmFiber60ParentCheck 25 &&
    tmFiber60ParentCheck 26 &&
    tmFiber60ParentCheck 27 &&
    tmFiber60ParentCheck 28 &&
    tmFiber60ParentCheck 29 &&
    tmFiber60ParentCheck 30 &&
    tmFiber60ParentCheck 31 &&
    tmFiber60ParentCheck 32 &&
    tmFiber60ParentCheck 33 &&
    tmFiber60ParentCheck 34 &&
    tmFiber60ParentCheck 35 &&
    tmFiber60ParentCheck 36 &&
    tmFiber60ParentCheck 37 &&
    tmFiber60ParentCheck 38 &&
    tmFiber60ParentCheck 39 &&
    tmFiber60ParentCheck 40 &&
    tmFiber60ParentCheck 41 &&
    tmFiber60ParentCheck 42 &&
    tmFiber60ParentCheck 43 &&
    tmFiber60ParentCheck 44 &&
    tmFiber60ParentCheck 45 &&
    tmFiber60ParentCheck 46 &&
    tmFiber60ParentCheck 47 &&
    tmFiber60ParentCheck 48 &&
    tmFiber60ParentCheck 49 &&
    tmFiber60ParentCheck 50 &&
    tmFiber60ParentCheck 51 &&
    tmFiber60ParentCheck 52 &&
    tmFiber60ParentCheck 53 &&
    tmFiber60ParentCheck 54 &&
    tmFiber60ParentCheck 55 &&
    tmFiber60ParentCheck 56 &&
    tmFiber60ParentCheck 57 &&
    tmFiber60ParentCheck 58 &&
    tmFiber60ParentCheck 59 &&
    tmFiber60ParentCheck 60 &&
    tmFiber60ParentCheck 61 &&
    tmFiber60ParentCheck 62 &&
    tmFiber60ParentCheck 63

theorem tmFiber60CertificateAudit_ok :
    tmFiber60CertificateAudit = true := by
  simp [tmFiber60CertificateAudit,
    tmFiber60SourcesCheck_ok,
    tmFiber60Row_0_ok,
    tmFiber60Row_1_ok,
    tmFiber60Row_2_ok,
    tmFiber60Row_3_ok,
    tmFiber60Row_4_ok,
    tmFiber60Row_5_ok,
    tmFiber60Row_6_ok,
    tmFiber60Row_7_ok,
    tmFiber60Row_8_ok,
    tmFiber60Row_9_ok,
    tmFiber60Row_10_ok,
    tmFiber60Row_11_ok,
    tmFiber60Row_12_ok,
    tmFiber60Row_13_ok,
    tmFiber60Row_14_ok,
    tmFiber60Row_15_ok,
    tmFiber60Row_16_ok,
    tmFiber60Row_17_ok,
    tmFiber60Row_18_ok,
    tmFiber60Row_19_ok,
    tmFiber60Row_20_ok,
    tmFiber60Row_21_ok,
    tmFiber60Row_22_ok,
    tmFiber60Row_23_ok,
    tmFiber60Row_24_ok,
    tmFiber60Row_25_ok,
    tmFiber60Row_26_ok,
    tmFiber60Row_27_ok,
    tmFiber60Row_28_ok,
    tmFiber60Row_29_ok,
    tmFiber60Row_30_ok,
    tmFiber60Row_31_ok,
    tmFiber60Row_32_ok,
    tmFiber60Row_33_ok,
    tmFiber60Row_34_ok,
    tmFiber60Row_35_ok,
    tmFiber60Row_36_ok,
    tmFiber60Row_37_ok,
    tmFiber60Row_38_ok,
    tmFiber60Row_39_ok,
    tmFiber60Row_40_ok,
    tmFiber60Row_41_ok,
    tmFiber60Row_42_ok,
    tmFiber60Row_43_ok,
    tmFiber60Row_44_ok,
    tmFiber60Row_45_ok,
    tmFiber60Row_46_ok,
    tmFiber60Row_47_ok,
    tmFiber60Row_48_ok,
    tmFiber60Row_49_ok,
    tmFiber60Row_50_ok,
    tmFiber60Row_51_ok,
    tmFiber60Row_52_ok,
    tmFiber60Row_53_ok,
    tmFiber60Row_54_ok,
    tmFiber60Row_55_ok,
    tmFiber60Row_56_ok,
    tmFiber60Row_57_ok,
    tmFiber60Row_58_ok,
    tmFiber60Row_59_ok,
    tmFiber60Row_60_ok,
    tmFiber60Row_61_ok,
    tmFiber60Row_62_ok,
    tmFiber60Row_63_ok,
    tmFiber60Parent_0_ok,
    tmFiber60Parent_1_ok,
    tmFiber60Parent_2_ok,
    tmFiber60Parent_3_ok,
    tmFiber60Parent_4_ok,
    tmFiber60Parent_5_ok,
    tmFiber60Parent_6_ok,
    tmFiber60Parent_7_ok,
    tmFiber60Parent_8_ok,
    tmFiber60Parent_9_ok,
    tmFiber60Parent_10_ok,
    tmFiber60Parent_11_ok,
    tmFiber60Parent_12_ok,
    tmFiber60Parent_13_ok,
    tmFiber60Parent_14_ok,
    tmFiber60Parent_15_ok,
    tmFiber60Parent_16_ok,
    tmFiber60Parent_17_ok,
    tmFiber60Parent_18_ok,
    tmFiber60Parent_19_ok,
    tmFiber60Parent_20_ok,
    tmFiber60Parent_21_ok,
    tmFiber60Parent_22_ok,
    tmFiber60Parent_23_ok,
    tmFiber60Parent_24_ok,
    tmFiber60Parent_25_ok,
    tmFiber60Parent_26_ok,
    tmFiber60Parent_27_ok,
    tmFiber60Parent_28_ok,
    tmFiber60Parent_29_ok,
    tmFiber60Parent_30_ok,
    tmFiber60Parent_31_ok,
    tmFiber60Parent_32_ok,
    tmFiber60Parent_33_ok,
    tmFiber60Parent_34_ok,
    tmFiber60Parent_35_ok,
    tmFiber60Parent_36_ok,
    tmFiber60Parent_37_ok,
    tmFiber60Parent_38_ok,
    tmFiber60Parent_39_ok,
    tmFiber60Parent_40_ok,
    tmFiber60Parent_41_ok,
    tmFiber60Parent_42_ok,
    tmFiber60Parent_43_ok,
    tmFiber60Parent_44_ok,
    tmFiber60Parent_45_ok,
    tmFiber60Parent_46_ok,
    tmFiber60Parent_47_ok,
    tmFiber60Parent_48_ok,
    tmFiber60Parent_49_ok,
    tmFiber60Parent_50_ok,
    tmFiber60Parent_51_ok,
    tmFiber60Parent_52_ok,
    tmFiber60Parent_53_ok,
    tmFiber60Parent_54_ok,
    tmFiber60Parent_55_ok,
    tmFiber60Parent_56_ok,
    tmFiber60Parent_57_ok,
    tmFiber60Parent_58_ok,
    tmFiber60Parent_59_ok,
    tmFiber60Parent_60_ok,
    tmFiber60Parent_61_ok,
    tmFiber60Parent_62_ok,
    tmFiber60Parent_63_ok]

def tmFiber61Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.b]

def tmFiber61Expected : List Nat :=
  [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]

def tmFiber61Rows : List DirectChainParentRow :=
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

def tmFiber61RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber61Rows i default

def tmFiber61SourcesCheck : Bool :=
  (tmFiber61Rows.map fun row => row.source) == tmFiber61Expected

theorem tmFiber61SourcesCheck_ok :
    tmFiber61SourcesCheck = true := by
  decide

def tmFiber61RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt i)

theorem tmFiber61Row_0_ok : tmFiber61RowCheck 0 = true := by decide
theorem tmFiber61Row_1_ok : tmFiber61RowCheck 1 = true := by decide
theorem tmFiber61Row_2_ok : tmFiber61RowCheck 2 = true := by decide
theorem tmFiber61Row_3_ok : tmFiber61RowCheck 3 = true := by decide
theorem tmFiber61Row_4_ok : tmFiber61RowCheck 4 = true := by decide
theorem tmFiber61Row_5_ok : tmFiber61RowCheck 5 = true := by decide
theorem tmFiber61Row_6_ok : tmFiber61RowCheck 6 = true := by decide
theorem tmFiber61Row_7_ok : tmFiber61RowCheck 7 = true := by decide
theorem tmFiber61Row_8_ok : tmFiber61RowCheck 8 = true := by decide
theorem tmFiber61Row_9_ok : tmFiber61RowCheck 9 = true := by decide
theorem tmFiber61Row_10_ok : tmFiber61RowCheck 10 = true := by decide
theorem tmFiber61Row_11_ok : tmFiber61RowCheck 11 = true := by decide
theorem tmFiber61Row_12_ok : tmFiber61RowCheck 12 = true := by decide
theorem tmFiber61Row_13_ok : tmFiber61RowCheck 13 = true := by decide
theorem tmFiber61Row_14_ok : tmFiber61RowCheck 14 = true := by decide
theorem tmFiber61Row_15_ok : tmFiber61RowCheck 15 = true := by decide

def tmFiber61ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber61Rows tmMaxParentDepth (listGetD tmFiber61Expected i 0) == 224

theorem tmFiber61Parent_0_ok : tmFiber61ParentCheck 0 = true := by decide
theorem tmFiber61Parent_1_ok : tmFiber61ParentCheck 1 = true := by decide
theorem tmFiber61Parent_2_ok : tmFiber61ParentCheck 2 = true := by decide
theorem tmFiber61Parent_3_ok : tmFiber61ParentCheck 3 = true := by decide
theorem tmFiber61Parent_4_ok : tmFiber61ParentCheck 4 = true := by decide
theorem tmFiber61Parent_5_ok : tmFiber61ParentCheck 5 = true := by decide
theorem tmFiber61Parent_6_ok : tmFiber61ParentCheck 6 = true := by decide
theorem tmFiber61Parent_7_ok : tmFiber61ParentCheck 7 = true := by decide
theorem tmFiber61Parent_8_ok : tmFiber61ParentCheck 8 = true := by decide
theorem tmFiber61Parent_9_ok : tmFiber61ParentCheck 9 = true := by decide
theorem tmFiber61Parent_10_ok : tmFiber61ParentCheck 10 = true := by decide
theorem tmFiber61Parent_11_ok : tmFiber61ParentCheck 11 = true := by decide
theorem tmFiber61Parent_12_ok : tmFiber61ParentCheck 12 = true := by decide
theorem tmFiber61Parent_13_ok : tmFiber61ParentCheck 13 = true := by decide
theorem tmFiber61Parent_14_ok : tmFiber61ParentCheck 14 = true := by decide
theorem tmFiber61Parent_15_ok : tmFiber61ParentCheck 15 = true := by decide

def tmFiber61CertificateAudit : Bool :=
  tmFiber61SourcesCheck &&
    tmFiber61RowCheck 0 &&
    tmFiber61RowCheck 1 &&
    tmFiber61RowCheck 2 &&
    tmFiber61RowCheck 3 &&
    tmFiber61RowCheck 4 &&
    tmFiber61RowCheck 5 &&
    tmFiber61RowCheck 6 &&
    tmFiber61RowCheck 7 &&
    tmFiber61RowCheck 8 &&
    tmFiber61RowCheck 9 &&
    tmFiber61RowCheck 10 &&
    tmFiber61RowCheck 11 &&
    tmFiber61RowCheck 12 &&
    tmFiber61RowCheck 13 &&
    tmFiber61RowCheck 14 &&
    tmFiber61RowCheck 15 &&
    tmFiber61ParentCheck 0 &&
    tmFiber61ParentCheck 1 &&
    tmFiber61ParentCheck 2 &&
    tmFiber61ParentCheck 3 &&
    tmFiber61ParentCheck 4 &&
    tmFiber61ParentCheck 5 &&
    tmFiber61ParentCheck 6 &&
    tmFiber61ParentCheck 7 &&
    tmFiber61ParentCheck 8 &&
    tmFiber61ParentCheck 9 &&
    tmFiber61ParentCheck 10 &&
    tmFiber61ParentCheck 11 &&
    tmFiber61ParentCheck 12 &&
    tmFiber61ParentCheck 13 &&
    tmFiber61ParentCheck 14 &&
    tmFiber61ParentCheck 15

theorem tmFiber61CertificateAudit_ok :
    tmFiber61CertificateAudit = true := by
  simp [tmFiber61CertificateAudit,
    tmFiber61SourcesCheck_ok,
    tmFiber61Row_0_ok,
    tmFiber61Row_1_ok,
    tmFiber61Row_2_ok,
    tmFiber61Row_3_ok,
    tmFiber61Row_4_ok,
    tmFiber61Row_5_ok,
    tmFiber61Row_6_ok,
    tmFiber61Row_7_ok,
    tmFiber61Row_8_ok,
    tmFiber61Row_9_ok,
    tmFiber61Row_10_ok,
    tmFiber61Row_11_ok,
    tmFiber61Row_12_ok,
    tmFiber61Row_13_ok,
    tmFiber61Row_14_ok,
    tmFiber61Row_15_ok,
    tmFiber61Parent_0_ok,
    tmFiber61Parent_1_ok,
    tmFiber61Parent_2_ok,
    tmFiber61Parent_3_ok,
    tmFiber61Parent_4_ok,
    tmFiber61Parent_5_ok,
    tmFiber61Parent_6_ok,
    tmFiber61Parent_7_ok,
    tmFiber61Parent_8_ok,
    tmFiber61Parent_9_ok,
    tmFiber61Parent_10_ok,
    tmFiber61Parent_11_ok,
    tmFiber61Parent_12_ok,
    tmFiber61Parent_13_ok,
    tmFiber61Parent_14_ok,
    tmFiber61Parent_15_ok]

def tmFiber62Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.p]

def tmFiber62Expected : List Nat :=
  [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]

def tmFiber62Rows : List DirectChainParentRow :=
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

def tmFiber62RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber62Rows i default

def tmFiber62SourcesCheck : Bool :=
  (tmFiber62Rows.map fun row => row.source) == tmFiber62Expected

theorem tmFiber62SourcesCheck_ok :
    tmFiber62SourcesCheck = true := by
  decide

def tmFiber62RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt i)

theorem tmFiber62Row_0_ok : tmFiber62RowCheck 0 = true := by decide
theorem tmFiber62Row_1_ok : tmFiber62RowCheck 1 = true := by decide
theorem tmFiber62Row_2_ok : tmFiber62RowCheck 2 = true := by decide
theorem tmFiber62Row_3_ok : tmFiber62RowCheck 3 = true := by decide
theorem tmFiber62Row_4_ok : tmFiber62RowCheck 4 = true := by decide
theorem tmFiber62Row_5_ok : tmFiber62RowCheck 5 = true := by decide
theorem tmFiber62Row_6_ok : tmFiber62RowCheck 6 = true := by decide
theorem tmFiber62Row_7_ok : tmFiber62RowCheck 7 = true := by decide
theorem tmFiber62Row_8_ok : tmFiber62RowCheck 8 = true := by decide
theorem tmFiber62Row_9_ok : tmFiber62RowCheck 9 = true := by decide
theorem tmFiber62Row_10_ok : tmFiber62RowCheck 10 = true := by decide
theorem tmFiber62Row_11_ok : tmFiber62RowCheck 11 = true := by decide
theorem tmFiber62Row_12_ok : tmFiber62RowCheck 12 = true := by decide
theorem tmFiber62Row_13_ok : tmFiber62RowCheck 13 = true := by decide
theorem tmFiber62Row_14_ok : tmFiber62RowCheck 14 = true := by decide
theorem tmFiber62Row_15_ok : tmFiber62RowCheck 15 = true := by decide

def tmFiber62ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber62Rows tmMaxParentDepth (listGetD tmFiber62Expected i 0) == 128

theorem tmFiber62Parent_0_ok : tmFiber62ParentCheck 0 = true := by decide
theorem tmFiber62Parent_1_ok : tmFiber62ParentCheck 1 = true := by decide
theorem tmFiber62Parent_2_ok : tmFiber62ParentCheck 2 = true := by decide
theorem tmFiber62Parent_3_ok : tmFiber62ParentCheck 3 = true := by decide
theorem tmFiber62Parent_4_ok : tmFiber62ParentCheck 4 = true := by decide
theorem tmFiber62Parent_5_ok : tmFiber62ParentCheck 5 = true := by decide
theorem tmFiber62Parent_6_ok : tmFiber62ParentCheck 6 = true := by decide
theorem tmFiber62Parent_7_ok : tmFiber62ParentCheck 7 = true := by decide
theorem tmFiber62Parent_8_ok : tmFiber62ParentCheck 8 = true := by decide
theorem tmFiber62Parent_9_ok : tmFiber62ParentCheck 9 = true := by decide
theorem tmFiber62Parent_10_ok : tmFiber62ParentCheck 10 = true := by decide
theorem tmFiber62Parent_11_ok : tmFiber62ParentCheck 11 = true := by decide
theorem tmFiber62Parent_12_ok : tmFiber62ParentCheck 12 = true := by decide
theorem tmFiber62Parent_13_ok : tmFiber62ParentCheck 13 = true := by decide
theorem tmFiber62Parent_14_ok : tmFiber62ParentCheck 14 = true := by decide
theorem tmFiber62Parent_15_ok : tmFiber62ParentCheck 15 = true := by decide

def tmFiber62CertificateAudit : Bool :=
  tmFiber62SourcesCheck &&
    tmFiber62RowCheck 0 &&
    tmFiber62RowCheck 1 &&
    tmFiber62RowCheck 2 &&
    tmFiber62RowCheck 3 &&
    tmFiber62RowCheck 4 &&
    tmFiber62RowCheck 5 &&
    tmFiber62RowCheck 6 &&
    tmFiber62RowCheck 7 &&
    tmFiber62RowCheck 8 &&
    tmFiber62RowCheck 9 &&
    tmFiber62RowCheck 10 &&
    tmFiber62RowCheck 11 &&
    tmFiber62RowCheck 12 &&
    tmFiber62RowCheck 13 &&
    tmFiber62RowCheck 14 &&
    tmFiber62RowCheck 15 &&
    tmFiber62ParentCheck 0 &&
    tmFiber62ParentCheck 1 &&
    tmFiber62ParentCheck 2 &&
    tmFiber62ParentCheck 3 &&
    tmFiber62ParentCheck 4 &&
    tmFiber62ParentCheck 5 &&
    tmFiber62ParentCheck 6 &&
    tmFiber62ParentCheck 7 &&
    tmFiber62ParentCheck 8 &&
    tmFiber62ParentCheck 9 &&
    tmFiber62ParentCheck 10 &&
    tmFiber62ParentCheck 11 &&
    tmFiber62ParentCheck 12 &&
    tmFiber62ParentCheck 13 &&
    tmFiber62ParentCheck 14 &&
    tmFiber62ParentCheck 15

theorem tmFiber62CertificateAudit_ok :
    tmFiber62CertificateAudit = true := by
  simp [tmFiber62CertificateAudit,
    tmFiber62SourcesCheck_ok,
    tmFiber62Row_0_ok,
    tmFiber62Row_1_ok,
    tmFiber62Row_2_ok,
    tmFiber62Row_3_ok,
    tmFiber62Row_4_ok,
    tmFiber62Row_5_ok,
    tmFiber62Row_6_ok,
    tmFiber62Row_7_ok,
    tmFiber62Row_8_ok,
    tmFiber62Row_9_ok,
    tmFiber62Row_10_ok,
    tmFiber62Row_11_ok,
    tmFiber62Row_12_ok,
    tmFiber62Row_13_ok,
    tmFiber62Row_14_ok,
    tmFiber62Row_15_ok,
    tmFiber62Parent_0_ok,
    tmFiber62Parent_1_ok,
    tmFiber62Parent_2_ok,
    tmFiber62Parent_3_ok,
    tmFiber62Parent_4_ok,
    tmFiber62Parent_5_ok,
    tmFiber62Parent_6_ok,
    tmFiber62Parent_7_ok,
    tmFiber62Parent_8_ok,
    tmFiber62Parent_9_ok,
    tmFiber62Parent_10_ok,
    tmFiber62Parent_11_ok,
    tmFiber62Parent_12_ok,
    tmFiber62Parent_13_ok,
    tmFiber62Parent_14_ok,
    tmFiber62Parent_15_ok]

def tmFiber63Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.r]

def tmFiber63Expected : List Nat :=
  []

def tmFiber63Rows : List DirectChainParentRow :=
  []

def tmFiber63RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber63Rows i default

def tmFiber63SourcesCheck : Bool :=
  (tmFiber63Rows.map fun row => row.source) == tmFiber63Expected

theorem tmFiber63SourcesCheck_ok :
    tmFiber63SourcesCheck = true := by
  decide

def tmFiber63RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber63Key tmFiber63Expected (tmFiber63RowAt i)

def tmFiber63ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber63Rows tmMaxParentDepth (listGetD tmFiber63Expected i 0) == 0

def tmFiber63CertificateAudit : Bool :=
  tmFiber63SourcesCheck

theorem tmFiber63CertificateAudit_ok :
    tmFiber63CertificateAudit = true := by
  simp [tmFiber63CertificateAudit,
    tmFiber63SourcesCheck_ok]

def tmFiber64Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.b]

def tmFiber64Expected : List Nat :=
  []

def tmFiber64Rows : List DirectChainParentRow :=
  []

def tmFiber64RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber64Rows i default

def tmFiber64SourcesCheck : Bool :=
  (tmFiber64Rows.map fun row => row.source) == tmFiber64Expected

theorem tmFiber64SourcesCheck_ok :
    tmFiber64SourcesCheck = true := by
  decide

def tmFiber64RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber64Key tmFiber64Expected (tmFiber64RowAt i)

def tmFiber64ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber64Rows tmMaxParentDepth (listGetD tmFiber64Expected i 0) == 0

def tmFiber64CertificateAudit : Bool :=
  tmFiber64SourcesCheck

theorem tmFiber64CertificateAudit_ok :
    tmFiber64CertificateAudit = true := by
  simp [tmFiber64CertificateAudit,
    tmFiber64SourcesCheck_ok]

def tmFiber65Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.p]

def tmFiber65Expected : List Nat :=
  []

def tmFiber65Rows : List DirectChainParentRow :=
  []

def tmFiber65RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber65Rows i default

def tmFiber65SourcesCheck : Bool :=
  (tmFiber65Rows.map fun row => row.source) == tmFiber65Expected

theorem tmFiber65SourcesCheck_ok :
    tmFiber65SourcesCheck = true := by
  decide

def tmFiber65RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber65Key tmFiber65Expected (tmFiber65RowAt i)

def tmFiber65ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber65Rows tmMaxParentDepth (listGetD tmFiber65Expected i 0) == 0

def tmFiber65CertificateAudit : Bool :=
  tmFiber65SourcesCheck

theorem tmFiber65CertificateAudit_ok :
    tmFiber65CertificateAudit = true := by
  simp [tmFiber65CertificateAudit,
    tmFiber65SourcesCheck_ok]

def tmFiber66Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.r]

def tmFiber66Expected : List Nat :=
  []

def tmFiber66Rows : List DirectChainParentRow :=
  []

def tmFiber66RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber66Rows i default

def tmFiber66SourcesCheck : Bool :=
  (tmFiber66Rows.map fun row => row.source) == tmFiber66Expected

theorem tmFiber66SourcesCheck_ok :
    tmFiber66SourcesCheck = true := by
  decide

def tmFiber66RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber66Key tmFiber66Expected (tmFiber66RowAt i)

def tmFiber66ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber66Rows tmMaxParentDepth (listGetD tmFiber66Expected i 0) == 0

def tmFiber66CertificateAudit : Bool :=
  tmFiber66SourcesCheck

theorem tmFiber66CertificateAudit_ok :
    tmFiber66CertificateAudit = true := by
  simp [tmFiber66CertificateAudit,
    tmFiber66SourcesCheck_ok]

def tmFiber67Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.b]

def tmFiber67Expected : List Nat :=
  []

def tmFiber67Rows : List DirectChainParentRow :=
  []

def tmFiber67RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber67Rows i default

def tmFiber67SourcesCheck : Bool :=
  (tmFiber67Rows.map fun row => row.source) == tmFiber67Expected

theorem tmFiber67SourcesCheck_ok :
    tmFiber67SourcesCheck = true := by
  decide

def tmFiber67RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber67Key tmFiber67Expected (tmFiber67RowAt i)

def tmFiber67ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber67Rows tmMaxParentDepth (listGetD tmFiber67Expected i 0) == 0

def tmFiber67CertificateAudit : Bool :=
  tmFiber67SourcesCheck

theorem tmFiber67CertificateAudit_ok :
    tmFiber67CertificateAudit = true := by
  simp [tmFiber67CertificateAudit,
    tmFiber67SourcesCheck_ok]

def tmFiber68Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.p]

def tmFiber68Expected : List Nat :=
  []

def tmFiber68Rows : List DirectChainParentRow :=
  []

def tmFiber68RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber68Rows i default

def tmFiber68SourcesCheck : Bool :=
  (tmFiber68Rows.map fun row => row.source) == tmFiber68Expected

theorem tmFiber68SourcesCheck_ok :
    tmFiber68SourcesCheck = true := by
  decide

def tmFiber68RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber68Key tmFiber68Expected (tmFiber68RowAt i)

def tmFiber68ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber68Rows tmMaxParentDepth (listGetD tmFiber68Expected i 0) == 0

def tmFiber68CertificateAudit : Bool :=
  tmFiber68SourcesCheck

theorem tmFiber68CertificateAudit_ok :
    tmFiber68CertificateAudit = true := by
  simp [tmFiber68CertificateAudit,
    tmFiber68SourcesCheck_ok]

def tmFiber69Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.r]

def tmFiber69Expected : List Nat :=
  [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]

def tmFiber69Rows : List DirectChainParentRow :=
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

def tmFiber69RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber69Rows i default

def tmFiber69SourcesCheck : Bool :=
  (tmFiber69Rows.map fun row => row.source) == tmFiber69Expected

theorem tmFiber69SourcesCheck_ok :
    tmFiber69SourcesCheck = true := by
  decide

def tmFiber69RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt i)

theorem tmFiber69Row_0_ok : tmFiber69RowCheck 0 = true := by decide
theorem tmFiber69Row_1_ok : tmFiber69RowCheck 1 = true := by decide
theorem tmFiber69Row_2_ok : tmFiber69RowCheck 2 = true := by decide
theorem tmFiber69Row_3_ok : tmFiber69RowCheck 3 = true := by decide
theorem tmFiber69Row_4_ok : tmFiber69RowCheck 4 = true := by decide
theorem tmFiber69Row_5_ok : tmFiber69RowCheck 5 = true := by decide
theorem tmFiber69Row_6_ok : tmFiber69RowCheck 6 = true := by decide
theorem tmFiber69Row_7_ok : tmFiber69RowCheck 7 = true := by decide
theorem tmFiber69Row_8_ok : tmFiber69RowCheck 8 = true := by decide
theorem tmFiber69Row_9_ok : tmFiber69RowCheck 9 = true := by decide
theorem tmFiber69Row_10_ok : tmFiber69RowCheck 10 = true := by decide
theorem tmFiber69Row_11_ok : tmFiber69RowCheck 11 = true := by decide
theorem tmFiber69Row_12_ok : tmFiber69RowCheck 12 = true := by decide
theorem tmFiber69Row_13_ok : tmFiber69RowCheck 13 = true := by decide
theorem tmFiber69Row_14_ok : tmFiber69RowCheck 14 = true := by decide
theorem tmFiber69Row_15_ok : tmFiber69RowCheck 15 = true := by decide

def tmFiber69ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber69Rows tmMaxParentDepth (listGetD tmFiber69Expected i 0) == 576

theorem tmFiber69Parent_0_ok : tmFiber69ParentCheck 0 = true := by decide
theorem tmFiber69Parent_1_ok : tmFiber69ParentCheck 1 = true := by decide
theorem tmFiber69Parent_2_ok : tmFiber69ParentCheck 2 = true := by decide
theorem tmFiber69Parent_3_ok : tmFiber69ParentCheck 3 = true := by decide
theorem tmFiber69Parent_4_ok : tmFiber69ParentCheck 4 = true := by decide
theorem tmFiber69Parent_5_ok : tmFiber69ParentCheck 5 = true := by decide
theorem tmFiber69Parent_6_ok : tmFiber69ParentCheck 6 = true := by decide
theorem tmFiber69Parent_7_ok : tmFiber69ParentCheck 7 = true := by decide
theorem tmFiber69Parent_8_ok : tmFiber69ParentCheck 8 = true := by decide
theorem tmFiber69Parent_9_ok : tmFiber69ParentCheck 9 = true := by decide
theorem tmFiber69Parent_10_ok : tmFiber69ParentCheck 10 = true := by decide
theorem tmFiber69Parent_11_ok : tmFiber69ParentCheck 11 = true := by decide
theorem tmFiber69Parent_12_ok : tmFiber69ParentCheck 12 = true := by decide
theorem tmFiber69Parent_13_ok : tmFiber69ParentCheck 13 = true := by decide
theorem tmFiber69Parent_14_ok : tmFiber69ParentCheck 14 = true := by decide
theorem tmFiber69Parent_15_ok : tmFiber69ParentCheck 15 = true := by decide

def tmFiber69CertificateAudit : Bool :=
  tmFiber69SourcesCheck &&
    tmFiber69RowCheck 0 &&
    tmFiber69RowCheck 1 &&
    tmFiber69RowCheck 2 &&
    tmFiber69RowCheck 3 &&
    tmFiber69RowCheck 4 &&
    tmFiber69RowCheck 5 &&
    tmFiber69RowCheck 6 &&
    tmFiber69RowCheck 7 &&
    tmFiber69RowCheck 8 &&
    tmFiber69RowCheck 9 &&
    tmFiber69RowCheck 10 &&
    tmFiber69RowCheck 11 &&
    tmFiber69RowCheck 12 &&
    tmFiber69RowCheck 13 &&
    tmFiber69RowCheck 14 &&
    tmFiber69RowCheck 15 &&
    tmFiber69ParentCheck 0 &&
    tmFiber69ParentCheck 1 &&
    tmFiber69ParentCheck 2 &&
    tmFiber69ParentCheck 3 &&
    tmFiber69ParentCheck 4 &&
    tmFiber69ParentCheck 5 &&
    tmFiber69ParentCheck 6 &&
    tmFiber69ParentCheck 7 &&
    tmFiber69ParentCheck 8 &&
    tmFiber69ParentCheck 9 &&
    tmFiber69ParentCheck 10 &&
    tmFiber69ParentCheck 11 &&
    tmFiber69ParentCheck 12 &&
    tmFiber69ParentCheck 13 &&
    tmFiber69ParentCheck 14 &&
    tmFiber69ParentCheck 15

theorem tmFiber69CertificateAudit_ok :
    tmFiber69CertificateAudit = true := by
  simp [tmFiber69CertificateAudit,
    tmFiber69SourcesCheck_ok,
    tmFiber69Row_0_ok,
    tmFiber69Row_1_ok,
    tmFiber69Row_2_ok,
    tmFiber69Row_3_ok,
    tmFiber69Row_4_ok,
    tmFiber69Row_5_ok,
    tmFiber69Row_6_ok,
    tmFiber69Row_7_ok,
    tmFiber69Row_8_ok,
    tmFiber69Row_9_ok,
    tmFiber69Row_10_ok,
    tmFiber69Row_11_ok,
    tmFiber69Row_12_ok,
    tmFiber69Row_13_ok,
    tmFiber69Row_14_ok,
    tmFiber69Row_15_ok,
    tmFiber69Parent_0_ok,
    tmFiber69Parent_1_ok,
    tmFiber69Parent_2_ok,
    tmFiber69Parent_3_ok,
    tmFiber69Parent_4_ok,
    tmFiber69Parent_5_ok,
    tmFiber69Parent_6_ok,
    tmFiber69Parent_7_ok,
    tmFiber69Parent_8_ok,
    tmFiber69Parent_9_ok,
    tmFiber69Parent_10_ok,
    tmFiber69Parent_11_ok,
    tmFiber69Parent_12_ok,
    tmFiber69Parent_13_ok,
    tmFiber69Parent_14_ok,
    tmFiber69Parent_15_ok]

def tmFiber70Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.b]

def tmFiber70Expected : List Nat :=
  [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]

def tmFiber70Rows : List DirectChainParentRow :=
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

def tmFiber70RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber70Rows i default

def tmFiber70SourcesCheck : Bool :=
  (tmFiber70Rows.map fun row => row.source) == tmFiber70Expected

theorem tmFiber70SourcesCheck_ok :
    tmFiber70SourcesCheck = true := by
  decide

def tmFiber70RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt i)

theorem tmFiber70Row_0_ok : tmFiber70RowCheck 0 = true := by decide
theorem tmFiber70Row_1_ok : tmFiber70RowCheck 1 = true := by decide
theorem tmFiber70Row_2_ok : tmFiber70RowCheck 2 = true := by decide
theorem tmFiber70Row_3_ok : tmFiber70RowCheck 3 = true := by decide
theorem tmFiber70Row_4_ok : tmFiber70RowCheck 4 = true := by decide
theorem tmFiber70Row_5_ok : tmFiber70RowCheck 5 = true := by decide
theorem tmFiber70Row_6_ok : tmFiber70RowCheck 6 = true := by decide
theorem tmFiber70Row_7_ok : tmFiber70RowCheck 7 = true := by decide
theorem tmFiber70Row_8_ok : tmFiber70RowCheck 8 = true := by decide
theorem tmFiber70Row_9_ok : tmFiber70RowCheck 9 = true := by decide
theorem tmFiber70Row_10_ok : tmFiber70RowCheck 10 = true := by decide
theorem tmFiber70Row_11_ok : tmFiber70RowCheck 11 = true := by decide
theorem tmFiber70Row_12_ok : tmFiber70RowCheck 12 = true := by decide
theorem tmFiber70Row_13_ok : tmFiber70RowCheck 13 = true := by decide
theorem tmFiber70Row_14_ok : tmFiber70RowCheck 14 = true := by decide
theorem tmFiber70Row_15_ok : tmFiber70RowCheck 15 = true := by decide
theorem tmFiber70Row_16_ok : tmFiber70RowCheck 16 = true := by decide
theorem tmFiber70Row_17_ok : tmFiber70RowCheck 17 = true := by decide
theorem tmFiber70Row_18_ok : tmFiber70RowCheck 18 = true := by decide
theorem tmFiber70Row_19_ok : tmFiber70RowCheck 19 = true := by decide
theorem tmFiber70Row_20_ok : tmFiber70RowCheck 20 = true := by decide
theorem tmFiber70Row_21_ok : tmFiber70RowCheck 21 = true := by decide
theorem tmFiber70Row_22_ok : tmFiber70RowCheck 22 = true := by decide
theorem tmFiber70Row_23_ok : tmFiber70RowCheck 23 = true := by decide
theorem tmFiber70Row_24_ok : tmFiber70RowCheck 24 = true := by decide
theorem tmFiber70Row_25_ok : tmFiber70RowCheck 25 = true := by decide
theorem tmFiber70Row_26_ok : tmFiber70RowCheck 26 = true := by decide
theorem tmFiber70Row_27_ok : tmFiber70RowCheck 27 = true := by decide
theorem tmFiber70Row_28_ok : tmFiber70RowCheck 28 = true := by decide
theorem tmFiber70Row_29_ok : tmFiber70RowCheck 29 = true := by decide
theorem tmFiber70Row_30_ok : tmFiber70RowCheck 30 = true := by decide
theorem tmFiber70Row_31_ok : tmFiber70RowCheck 31 = true := by decide
theorem tmFiber70Row_32_ok : tmFiber70RowCheck 32 = true := by decide
theorem tmFiber70Row_33_ok : tmFiber70RowCheck 33 = true := by decide
theorem tmFiber70Row_34_ok : tmFiber70RowCheck 34 = true := by decide
theorem tmFiber70Row_35_ok : tmFiber70RowCheck 35 = true := by decide
theorem tmFiber70Row_36_ok : tmFiber70RowCheck 36 = true := by decide
theorem tmFiber70Row_37_ok : tmFiber70RowCheck 37 = true := by decide
theorem tmFiber70Row_38_ok : tmFiber70RowCheck 38 = true := by decide
theorem tmFiber70Row_39_ok : tmFiber70RowCheck 39 = true := by decide
theorem tmFiber70Row_40_ok : tmFiber70RowCheck 40 = true := by decide
theorem tmFiber70Row_41_ok : tmFiber70RowCheck 41 = true := by decide
theorem tmFiber70Row_42_ok : tmFiber70RowCheck 42 = true := by decide
theorem tmFiber70Row_43_ok : tmFiber70RowCheck 43 = true := by decide
theorem tmFiber70Row_44_ok : tmFiber70RowCheck 44 = true := by decide
theorem tmFiber70Row_45_ok : tmFiber70RowCheck 45 = true := by decide
theorem tmFiber70Row_46_ok : tmFiber70RowCheck 46 = true := by decide
theorem tmFiber70Row_47_ok : tmFiber70RowCheck 47 = true := by decide
theorem tmFiber70Row_48_ok : tmFiber70RowCheck 48 = true := by decide
theorem tmFiber70Row_49_ok : tmFiber70RowCheck 49 = true := by decide
theorem tmFiber70Row_50_ok : tmFiber70RowCheck 50 = true := by decide
theorem tmFiber70Row_51_ok : tmFiber70RowCheck 51 = true := by decide
theorem tmFiber70Row_52_ok : tmFiber70RowCheck 52 = true := by decide
theorem tmFiber70Row_53_ok : tmFiber70RowCheck 53 = true := by decide
theorem tmFiber70Row_54_ok : tmFiber70RowCheck 54 = true := by decide
theorem tmFiber70Row_55_ok : tmFiber70RowCheck 55 = true := by decide
theorem tmFiber70Row_56_ok : tmFiber70RowCheck 56 = true := by decide
theorem tmFiber70Row_57_ok : tmFiber70RowCheck 57 = true := by decide
theorem tmFiber70Row_58_ok : tmFiber70RowCheck 58 = true := by decide
theorem tmFiber70Row_59_ok : tmFiber70RowCheck 59 = true := by decide
theorem tmFiber70Row_60_ok : tmFiber70RowCheck 60 = true := by decide
theorem tmFiber70Row_61_ok : tmFiber70RowCheck 61 = true := by decide
theorem tmFiber70Row_62_ok : tmFiber70RowCheck 62 = true := by decide
theorem tmFiber70Row_63_ok : tmFiber70RowCheck 63 = true := by decide

def tmFiber70ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber70Rows tmMaxParentDepth (listGetD tmFiber70Expected i 0) == 480

theorem tmFiber70Parent_0_ok : tmFiber70ParentCheck 0 = true := by decide
theorem tmFiber70Parent_1_ok : tmFiber70ParentCheck 1 = true := by decide
theorem tmFiber70Parent_2_ok : tmFiber70ParentCheck 2 = true := by decide
theorem tmFiber70Parent_3_ok : tmFiber70ParentCheck 3 = true := by decide
theorem tmFiber70Parent_4_ok : tmFiber70ParentCheck 4 = true := by decide
theorem tmFiber70Parent_5_ok : tmFiber70ParentCheck 5 = true := by decide
theorem tmFiber70Parent_6_ok : tmFiber70ParentCheck 6 = true := by decide
theorem tmFiber70Parent_7_ok : tmFiber70ParentCheck 7 = true := by decide
theorem tmFiber70Parent_8_ok : tmFiber70ParentCheck 8 = true := by decide
theorem tmFiber70Parent_9_ok : tmFiber70ParentCheck 9 = true := by decide
theorem tmFiber70Parent_10_ok : tmFiber70ParentCheck 10 = true := by decide
theorem tmFiber70Parent_11_ok : tmFiber70ParentCheck 11 = true := by decide
theorem tmFiber70Parent_12_ok : tmFiber70ParentCheck 12 = true := by decide
theorem tmFiber70Parent_13_ok : tmFiber70ParentCheck 13 = true := by decide
theorem tmFiber70Parent_14_ok : tmFiber70ParentCheck 14 = true := by decide
theorem tmFiber70Parent_15_ok : tmFiber70ParentCheck 15 = true := by decide
theorem tmFiber70Parent_16_ok : tmFiber70ParentCheck 16 = true := by decide
theorem tmFiber70Parent_17_ok : tmFiber70ParentCheck 17 = true := by decide
theorem tmFiber70Parent_18_ok : tmFiber70ParentCheck 18 = true := by decide
theorem tmFiber70Parent_19_ok : tmFiber70ParentCheck 19 = true := by decide
theorem tmFiber70Parent_20_ok : tmFiber70ParentCheck 20 = true := by decide
theorem tmFiber70Parent_21_ok : tmFiber70ParentCheck 21 = true := by decide
theorem tmFiber70Parent_22_ok : tmFiber70ParentCheck 22 = true := by decide
theorem tmFiber70Parent_23_ok : tmFiber70ParentCheck 23 = true := by decide
theorem tmFiber70Parent_24_ok : tmFiber70ParentCheck 24 = true := by decide
theorem tmFiber70Parent_25_ok : tmFiber70ParentCheck 25 = true := by decide
theorem tmFiber70Parent_26_ok : tmFiber70ParentCheck 26 = true := by decide
theorem tmFiber70Parent_27_ok : tmFiber70ParentCheck 27 = true := by decide
theorem tmFiber70Parent_28_ok : tmFiber70ParentCheck 28 = true := by decide
theorem tmFiber70Parent_29_ok : tmFiber70ParentCheck 29 = true := by decide
theorem tmFiber70Parent_30_ok : tmFiber70ParentCheck 30 = true := by decide
theorem tmFiber70Parent_31_ok : tmFiber70ParentCheck 31 = true := by decide
theorem tmFiber70Parent_32_ok : tmFiber70ParentCheck 32 = true := by decide
theorem tmFiber70Parent_33_ok : tmFiber70ParentCheck 33 = true := by decide
theorem tmFiber70Parent_34_ok : tmFiber70ParentCheck 34 = true := by decide
theorem tmFiber70Parent_35_ok : tmFiber70ParentCheck 35 = true := by decide
theorem tmFiber70Parent_36_ok : tmFiber70ParentCheck 36 = true := by decide
theorem tmFiber70Parent_37_ok : tmFiber70ParentCheck 37 = true := by decide
theorem tmFiber70Parent_38_ok : tmFiber70ParentCheck 38 = true := by decide
theorem tmFiber70Parent_39_ok : tmFiber70ParentCheck 39 = true := by decide
theorem tmFiber70Parent_40_ok : tmFiber70ParentCheck 40 = true := by decide
theorem tmFiber70Parent_41_ok : tmFiber70ParentCheck 41 = true := by decide
theorem tmFiber70Parent_42_ok : tmFiber70ParentCheck 42 = true := by decide
theorem tmFiber70Parent_43_ok : tmFiber70ParentCheck 43 = true := by decide
theorem tmFiber70Parent_44_ok : tmFiber70ParentCheck 44 = true := by decide
theorem tmFiber70Parent_45_ok : tmFiber70ParentCheck 45 = true := by decide
theorem tmFiber70Parent_46_ok : tmFiber70ParentCheck 46 = true := by decide
theorem tmFiber70Parent_47_ok : tmFiber70ParentCheck 47 = true := by decide
theorem tmFiber70Parent_48_ok : tmFiber70ParentCheck 48 = true := by decide
theorem tmFiber70Parent_49_ok : tmFiber70ParentCheck 49 = true := by decide
theorem tmFiber70Parent_50_ok : tmFiber70ParentCheck 50 = true := by decide
theorem tmFiber70Parent_51_ok : tmFiber70ParentCheck 51 = true := by decide
theorem tmFiber70Parent_52_ok : tmFiber70ParentCheck 52 = true := by decide
theorem tmFiber70Parent_53_ok : tmFiber70ParentCheck 53 = true := by decide
theorem tmFiber70Parent_54_ok : tmFiber70ParentCheck 54 = true := by decide
theorem tmFiber70Parent_55_ok : tmFiber70ParentCheck 55 = true := by decide
theorem tmFiber70Parent_56_ok : tmFiber70ParentCheck 56 = true := by decide
theorem tmFiber70Parent_57_ok : tmFiber70ParentCheck 57 = true := by decide
theorem tmFiber70Parent_58_ok : tmFiber70ParentCheck 58 = true := by decide
theorem tmFiber70Parent_59_ok : tmFiber70ParentCheck 59 = true := by decide
theorem tmFiber70Parent_60_ok : tmFiber70ParentCheck 60 = true := by decide
theorem tmFiber70Parent_61_ok : tmFiber70ParentCheck 61 = true := by decide
theorem tmFiber70Parent_62_ok : tmFiber70ParentCheck 62 = true := by decide
theorem tmFiber70Parent_63_ok : tmFiber70ParentCheck 63 = true := by decide

def tmFiber70CertificateAudit : Bool :=
  tmFiber70SourcesCheck &&
    tmFiber70RowCheck 0 &&
    tmFiber70RowCheck 1 &&
    tmFiber70RowCheck 2 &&
    tmFiber70RowCheck 3 &&
    tmFiber70RowCheck 4 &&
    tmFiber70RowCheck 5 &&
    tmFiber70RowCheck 6 &&
    tmFiber70RowCheck 7 &&
    tmFiber70RowCheck 8 &&
    tmFiber70RowCheck 9 &&
    tmFiber70RowCheck 10 &&
    tmFiber70RowCheck 11 &&
    tmFiber70RowCheck 12 &&
    tmFiber70RowCheck 13 &&
    tmFiber70RowCheck 14 &&
    tmFiber70RowCheck 15 &&
    tmFiber70RowCheck 16 &&
    tmFiber70RowCheck 17 &&
    tmFiber70RowCheck 18 &&
    tmFiber70RowCheck 19 &&
    tmFiber70RowCheck 20 &&
    tmFiber70RowCheck 21 &&
    tmFiber70RowCheck 22 &&
    tmFiber70RowCheck 23 &&
    tmFiber70RowCheck 24 &&
    tmFiber70RowCheck 25 &&
    tmFiber70RowCheck 26 &&
    tmFiber70RowCheck 27 &&
    tmFiber70RowCheck 28 &&
    tmFiber70RowCheck 29 &&
    tmFiber70RowCheck 30 &&
    tmFiber70RowCheck 31 &&
    tmFiber70RowCheck 32 &&
    tmFiber70RowCheck 33 &&
    tmFiber70RowCheck 34 &&
    tmFiber70RowCheck 35 &&
    tmFiber70RowCheck 36 &&
    tmFiber70RowCheck 37 &&
    tmFiber70RowCheck 38 &&
    tmFiber70RowCheck 39 &&
    tmFiber70RowCheck 40 &&
    tmFiber70RowCheck 41 &&
    tmFiber70RowCheck 42 &&
    tmFiber70RowCheck 43 &&
    tmFiber70RowCheck 44 &&
    tmFiber70RowCheck 45 &&
    tmFiber70RowCheck 46 &&
    tmFiber70RowCheck 47 &&
    tmFiber70RowCheck 48 &&
    tmFiber70RowCheck 49 &&
    tmFiber70RowCheck 50 &&
    tmFiber70RowCheck 51 &&
    tmFiber70RowCheck 52 &&
    tmFiber70RowCheck 53 &&
    tmFiber70RowCheck 54 &&
    tmFiber70RowCheck 55 &&
    tmFiber70RowCheck 56 &&
    tmFiber70RowCheck 57 &&
    tmFiber70RowCheck 58 &&
    tmFiber70RowCheck 59 &&
    tmFiber70RowCheck 60 &&
    tmFiber70RowCheck 61 &&
    tmFiber70RowCheck 62 &&
    tmFiber70RowCheck 63 &&
    tmFiber70ParentCheck 0 &&
    tmFiber70ParentCheck 1 &&
    tmFiber70ParentCheck 2 &&
    tmFiber70ParentCheck 3 &&
    tmFiber70ParentCheck 4 &&
    tmFiber70ParentCheck 5 &&
    tmFiber70ParentCheck 6 &&
    tmFiber70ParentCheck 7 &&
    tmFiber70ParentCheck 8 &&
    tmFiber70ParentCheck 9 &&
    tmFiber70ParentCheck 10 &&
    tmFiber70ParentCheck 11 &&
    tmFiber70ParentCheck 12 &&
    tmFiber70ParentCheck 13 &&
    tmFiber70ParentCheck 14 &&
    tmFiber70ParentCheck 15 &&
    tmFiber70ParentCheck 16 &&
    tmFiber70ParentCheck 17 &&
    tmFiber70ParentCheck 18 &&
    tmFiber70ParentCheck 19 &&
    tmFiber70ParentCheck 20 &&
    tmFiber70ParentCheck 21 &&
    tmFiber70ParentCheck 22 &&
    tmFiber70ParentCheck 23 &&
    tmFiber70ParentCheck 24 &&
    tmFiber70ParentCheck 25 &&
    tmFiber70ParentCheck 26 &&
    tmFiber70ParentCheck 27 &&
    tmFiber70ParentCheck 28 &&
    tmFiber70ParentCheck 29 &&
    tmFiber70ParentCheck 30 &&
    tmFiber70ParentCheck 31 &&
    tmFiber70ParentCheck 32 &&
    tmFiber70ParentCheck 33 &&
    tmFiber70ParentCheck 34 &&
    tmFiber70ParentCheck 35 &&
    tmFiber70ParentCheck 36 &&
    tmFiber70ParentCheck 37 &&
    tmFiber70ParentCheck 38 &&
    tmFiber70ParentCheck 39 &&
    tmFiber70ParentCheck 40 &&
    tmFiber70ParentCheck 41 &&
    tmFiber70ParentCheck 42 &&
    tmFiber70ParentCheck 43 &&
    tmFiber70ParentCheck 44 &&
    tmFiber70ParentCheck 45 &&
    tmFiber70ParentCheck 46 &&
    tmFiber70ParentCheck 47 &&
    tmFiber70ParentCheck 48 &&
    tmFiber70ParentCheck 49 &&
    tmFiber70ParentCheck 50 &&
    tmFiber70ParentCheck 51 &&
    tmFiber70ParentCheck 52 &&
    tmFiber70ParentCheck 53 &&
    tmFiber70ParentCheck 54 &&
    tmFiber70ParentCheck 55 &&
    tmFiber70ParentCheck 56 &&
    tmFiber70ParentCheck 57 &&
    tmFiber70ParentCheck 58 &&
    tmFiber70ParentCheck 59 &&
    tmFiber70ParentCheck 60 &&
    tmFiber70ParentCheck 61 &&
    tmFiber70ParentCheck 62 &&
    tmFiber70ParentCheck 63

theorem tmFiber70CertificateAudit_ok :
    tmFiber70CertificateAudit = true := by
  simp [tmFiber70CertificateAudit,
    tmFiber70SourcesCheck_ok,
    tmFiber70Row_0_ok,
    tmFiber70Row_1_ok,
    tmFiber70Row_2_ok,
    tmFiber70Row_3_ok,
    tmFiber70Row_4_ok,
    tmFiber70Row_5_ok,
    tmFiber70Row_6_ok,
    tmFiber70Row_7_ok,
    tmFiber70Row_8_ok,
    tmFiber70Row_9_ok,
    tmFiber70Row_10_ok,
    tmFiber70Row_11_ok,
    tmFiber70Row_12_ok,
    tmFiber70Row_13_ok,
    tmFiber70Row_14_ok,
    tmFiber70Row_15_ok,
    tmFiber70Row_16_ok,
    tmFiber70Row_17_ok,
    tmFiber70Row_18_ok,
    tmFiber70Row_19_ok,
    tmFiber70Row_20_ok,
    tmFiber70Row_21_ok,
    tmFiber70Row_22_ok,
    tmFiber70Row_23_ok,
    tmFiber70Row_24_ok,
    tmFiber70Row_25_ok,
    tmFiber70Row_26_ok,
    tmFiber70Row_27_ok,
    tmFiber70Row_28_ok,
    tmFiber70Row_29_ok,
    tmFiber70Row_30_ok,
    tmFiber70Row_31_ok,
    tmFiber70Row_32_ok,
    tmFiber70Row_33_ok,
    tmFiber70Row_34_ok,
    tmFiber70Row_35_ok,
    tmFiber70Row_36_ok,
    tmFiber70Row_37_ok,
    tmFiber70Row_38_ok,
    tmFiber70Row_39_ok,
    tmFiber70Row_40_ok,
    tmFiber70Row_41_ok,
    tmFiber70Row_42_ok,
    tmFiber70Row_43_ok,
    tmFiber70Row_44_ok,
    tmFiber70Row_45_ok,
    tmFiber70Row_46_ok,
    tmFiber70Row_47_ok,
    tmFiber70Row_48_ok,
    tmFiber70Row_49_ok,
    tmFiber70Row_50_ok,
    tmFiber70Row_51_ok,
    tmFiber70Row_52_ok,
    tmFiber70Row_53_ok,
    tmFiber70Row_54_ok,
    tmFiber70Row_55_ok,
    tmFiber70Row_56_ok,
    tmFiber70Row_57_ok,
    tmFiber70Row_58_ok,
    tmFiber70Row_59_ok,
    tmFiber70Row_60_ok,
    tmFiber70Row_61_ok,
    tmFiber70Row_62_ok,
    tmFiber70Row_63_ok,
    tmFiber70Parent_0_ok,
    tmFiber70Parent_1_ok,
    tmFiber70Parent_2_ok,
    tmFiber70Parent_3_ok,
    tmFiber70Parent_4_ok,
    tmFiber70Parent_5_ok,
    tmFiber70Parent_6_ok,
    tmFiber70Parent_7_ok,
    tmFiber70Parent_8_ok,
    tmFiber70Parent_9_ok,
    tmFiber70Parent_10_ok,
    tmFiber70Parent_11_ok,
    tmFiber70Parent_12_ok,
    tmFiber70Parent_13_ok,
    tmFiber70Parent_14_ok,
    tmFiber70Parent_15_ok,
    tmFiber70Parent_16_ok,
    tmFiber70Parent_17_ok,
    tmFiber70Parent_18_ok,
    tmFiber70Parent_19_ok,
    tmFiber70Parent_20_ok,
    tmFiber70Parent_21_ok,
    tmFiber70Parent_22_ok,
    tmFiber70Parent_23_ok,
    tmFiber70Parent_24_ok,
    tmFiber70Parent_25_ok,
    tmFiber70Parent_26_ok,
    tmFiber70Parent_27_ok,
    tmFiber70Parent_28_ok,
    tmFiber70Parent_29_ok,
    tmFiber70Parent_30_ok,
    tmFiber70Parent_31_ok,
    tmFiber70Parent_32_ok,
    tmFiber70Parent_33_ok,
    tmFiber70Parent_34_ok,
    tmFiber70Parent_35_ok,
    tmFiber70Parent_36_ok,
    tmFiber70Parent_37_ok,
    tmFiber70Parent_38_ok,
    tmFiber70Parent_39_ok,
    tmFiber70Parent_40_ok,
    tmFiber70Parent_41_ok,
    tmFiber70Parent_42_ok,
    tmFiber70Parent_43_ok,
    tmFiber70Parent_44_ok,
    tmFiber70Parent_45_ok,
    tmFiber70Parent_46_ok,
    tmFiber70Parent_47_ok,
    tmFiber70Parent_48_ok,
    tmFiber70Parent_49_ok,
    tmFiber70Parent_50_ok,
    tmFiber70Parent_51_ok,
    tmFiber70Parent_52_ok,
    tmFiber70Parent_53_ok,
    tmFiber70Parent_54_ok,
    tmFiber70Parent_55_ok,
    tmFiber70Parent_56_ok,
    tmFiber70Parent_57_ok,
    tmFiber70Parent_58_ok,
    tmFiber70Parent_59_ok,
    tmFiber70Parent_60_ok,
    tmFiber70Parent_61_ok,
    tmFiber70Parent_62_ok,
    tmFiber70Parent_63_ok]

def tmFiber71Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.p]

def tmFiber71Expected : List Nat :=
  [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]

def tmFiber71Rows : List DirectChainParentRow :=
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

def tmFiber71RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber71Rows i default

def tmFiber71SourcesCheck : Bool :=
  (tmFiber71Rows.map fun row => row.source) == tmFiber71Expected

theorem tmFiber71SourcesCheck_ok :
    tmFiber71SourcesCheck = true := by
  decide

def tmFiber71RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt i)

theorem tmFiber71Row_0_ok : tmFiber71RowCheck 0 = true := by decide
theorem tmFiber71Row_1_ok : tmFiber71RowCheck 1 = true := by decide
theorem tmFiber71Row_2_ok : tmFiber71RowCheck 2 = true := by decide
theorem tmFiber71Row_3_ok : tmFiber71RowCheck 3 = true := by decide
theorem tmFiber71Row_4_ok : tmFiber71RowCheck 4 = true := by decide
theorem tmFiber71Row_5_ok : tmFiber71RowCheck 5 = true := by decide
theorem tmFiber71Row_6_ok : tmFiber71RowCheck 6 = true := by decide
theorem tmFiber71Row_7_ok : tmFiber71RowCheck 7 = true := by decide
theorem tmFiber71Row_8_ok : tmFiber71RowCheck 8 = true := by decide
theorem tmFiber71Row_9_ok : tmFiber71RowCheck 9 = true := by decide
theorem tmFiber71Row_10_ok : tmFiber71RowCheck 10 = true := by decide
theorem tmFiber71Row_11_ok : tmFiber71RowCheck 11 = true := by decide
theorem tmFiber71Row_12_ok : tmFiber71RowCheck 12 = true := by decide
theorem tmFiber71Row_13_ok : tmFiber71RowCheck 13 = true := by decide
theorem tmFiber71Row_14_ok : tmFiber71RowCheck 14 = true := by decide
theorem tmFiber71Row_15_ok : tmFiber71RowCheck 15 = true := by decide

def tmFiber71ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber71Rows tmMaxParentDepth (listGetD tmFiber71Expected i 0) == 512

theorem tmFiber71Parent_0_ok : tmFiber71ParentCheck 0 = true := by decide
theorem tmFiber71Parent_1_ok : tmFiber71ParentCheck 1 = true := by decide
theorem tmFiber71Parent_2_ok : tmFiber71ParentCheck 2 = true := by decide
theorem tmFiber71Parent_3_ok : tmFiber71ParentCheck 3 = true := by decide
theorem tmFiber71Parent_4_ok : tmFiber71ParentCheck 4 = true := by decide
theorem tmFiber71Parent_5_ok : tmFiber71ParentCheck 5 = true := by decide
theorem tmFiber71Parent_6_ok : tmFiber71ParentCheck 6 = true := by decide
theorem tmFiber71Parent_7_ok : tmFiber71ParentCheck 7 = true := by decide
theorem tmFiber71Parent_8_ok : tmFiber71ParentCheck 8 = true := by decide
theorem tmFiber71Parent_9_ok : tmFiber71ParentCheck 9 = true := by decide
theorem tmFiber71Parent_10_ok : tmFiber71ParentCheck 10 = true := by decide
theorem tmFiber71Parent_11_ok : tmFiber71ParentCheck 11 = true := by decide
theorem tmFiber71Parent_12_ok : tmFiber71ParentCheck 12 = true := by decide
theorem tmFiber71Parent_13_ok : tmFiber71ParentCheck 13 = true := by decide
theorem tmFiber71Parent_14_ok : tmFiber71ParentCheck 14 = true := by decide
theorem tmFiber71Parent_15_ok : tmFiber71ParentCheck 15 = true := by decide

def tmFiber71CertificateAudit : Bool :=
  tmFiber71SourcesCheck &&
    tmFiber71RowCheck 0 &&
    tmFiber71RowCheck 1 &&
    tmFiber71RowCheck 2 &&
    tmFiber71RowCheck 3 &&
    tmFiber71RowCheck 4 &&
    tmFiber71RowCheck 5 &&
    tmFiber71RowCheck 6 &&
    tmFiber71RowCheck 7 &&
    tmFiber71RowCheck 8 &&
    tmFiber71RowCheck 9 &&
    tmFiber71RowCheck 10 &&
    tmFiber71RowCheck 11 &&
    tmFiber71RowCheck 12 &&
    tmFiber71RowCheck 13 &&
    tmFiber71RowCheck 14 &&
    tmFiber71RowCheck 15 &&
    tmFiber71ParentCheck 0 &&
    tmFiber71ParentCheck 1 &&
    tmFiber71ParentCheck 2 &&
    tmFiber71ParentCheck 3 &&
    tmFiber71ParentCheck 4 &&
    tmFiber71ParentCheck 5 &&
    tmFiber71ParentCheck 6 &&
    tmFiber71ParentCheck 7 &&
    tmFiber71ParentCheck 8 &&
    tmFiber71ParentCheck 9 &&
    tmFiber71ParentCheck 10 &&
    tmFiber71ParentCheck 11 &&
    tmFiber71ParentCheck 12 &&
    tmFiber71ParentCheck 13 &&
    tmFiber71ParentCheck 14 &&
    tmFiber71ParentCheck 15

theorem tmFiber71CertificateAudit_ok :
    tmFiber71CertificateAudit = true := by
  simp [tmFiber71CertificateAudit,
    tmFiber71SourcesCheck_ok,
    tmFiber71Row_0_ok,
    tmFiber71Row_1_ok,
    tmFiber71Row_2_ok,
    tmFiber71Row_3_ok,
    tmFiber71Row_4_ok,
    tmFiber71Row_5_ok,
    tmFiber71Row_6_ok,
    tmFiber71Row_7_ok,
    tmFiber71Row_8_ok,
    tmFiber71Row_9_ok,
    tmFiber71Row_10_ok,
    tmFiber71Row_11_ok,
    tmFiber71Row_12_ok,
    tmFiber71Row_13_ok,
    tmFiber71Row_14_ok,
    tmFiber71Row_15_ok,
    tmFiber71Parent_0_ok,
    tmFiber71Parent_1_ok,
    tmFiber71Parent_2_ok,
    tmFiber71Parent_3_ok,
    tmFiber71Parent_4_ok,
    tmFiber71Parent_5_ok,
    tmFiber71Parent_6_ok,
    tmFiber71Parent_7_ok,
    tmFiber71Parent_8_ok,
    tmFiber71Parent_9_ok,
    tmFiber71Parent_10_ok,
    tmFiber71Parent_11_ok,
    tmFiber71Parent_12_ok,
    tmFiber71Parent_13_ok,
    tmFiber71Parent_14_ok,
    tmFiber71Parent_15_ok]

def tmFiber72Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.r]

def tmFiber72Expected : List Nat :=
  [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]

def tmFiber72Rows : List DirectChainParentRow :=
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

def tmFiber72RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber72Rows i default

def tmFiber72SourcesCheck : Bool :=
  (tmFiber72Rows.map fun row => row.source) == tmFiber72Expected

theorem tmFiber72SourcesCheck_ok :
    tmFiber72SourcesCheck = true := by
  decide

def tmFiber72RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber72Key tmFiber72Expected (tmFiber72RowAt i)

theorem tmFiber72Row_0_ok : tmFiber72RowCheck 0 = true := by decide
theorem tmFiber72Row_1_ok : tmFiber72RowCheck 1 = true := by decide
theorem tmFiber72Row_2_ok : tmFiber72RowCheck 2 = true := by decide
theorem tmFiber72Row_3_ok : tmFiber72RowCheck 3 = true := by decide
theorem tmFiber72Row_4_ok : tmFiber72RowCheck 4 = true := by decide
theorem tmFiber72Row_5_ok : tmFiber72RowCheck 5 = true := by decide
theorem tmFiber72Row_6_ok : tmFiber72RowCheck 6 = true := by decide
theorem tmFiber72Row_7_ok : tmFiber72RowCheck 7 = true := by decide
theorem tmFiber72Row_8_ok : tmFiber72RowCheck 8 = true := by decide
theorem tmFiber72Row_9_ok : tmFiber72RowCheck 9 = true := by decide
theorem tmFiber72Row_10_ok : tmFiber72RowCheck 10 = true := by decide
theorem tmFiber72Row_11_ok : tmFiber72RowCheck 11 = true := by decide
theorem tmFiber72Row_12_ok : tmFiber72RowCheck 12 = true := by decide
theorem tmFiber72Row_13_ok : tmFiber72RowCheck 13 = true := by decide
theorem tmFiber72Row_14_ok : tmFiber72RowCheck 14 = true := by decide
theorem tmFiber72Row_15_ok : tmFiber72RowCheck 15 = true := by decide
theorem tmFiber72Row_16_ok : tmFiber72RowCheck 16 = true := by decide
theorem tmFiber72Row_17_ok : tmFiber72RowCheck 17 = true := by decide
theorem tmFiber72Row_18_ok : tmFiber72RowCheck 18 = true := by decide
theorem tmFiber72Row_19_ok : tmFiber72RowCheck 19 = true := by decide
theorem tmFiber72Row_20_ok : tmFiber72RowCheck 20 = true := by decide
theorem tmFiber72Row_21_ok : tmFiber72RowCheck 21 = true := by decide
theorem tmFiber72Row_22_ok : tmFiber72RowCheck 22 = true := by decide
theorem tmFiber72Row_23_ok : tmFiber72RowCheck 23 = true := by decide
theorem tmFiber72Row_24_ok : tmFiber72RowCheck 24 = true := by decide
theorem tmFiber72Row_25_ok : tmFiber72RowCheck 25 = true := by decide
theorem tmFiber72Row_26_ok : tmFiber72RowCheck 26 = true := by decide
theorem tmFiber72Row_27_ok : tmFiber72RowCheck 27 = true := by decide
theorem tmFiber72Row_28_ok : tmFiber72RowCheck 28 = true := by decide
theorem tmFiber72Row_29_ok : tmFiber72RowCheck 29 = true := by decide
theorem tmFiber72Row_30_ok : tmFiber72RowCheck 30 = true := by decide
theorem tmFiber72Row_31_ok : tmFiber72RowCheck 31 = true := by decide
theorem tmFiber72Row_32_ok : tmFiber72RowCheck 32 = true := by decide
theorem tmFiber72Row_33_ok : tmFiber72RowCheck 33 = true := by decide
theorem tmFiber72Row_34_ok : tmFiber72RowCheck 34 = true := by decide
theorem tmFiber72Row_35_ok : tmFiber72RowCheck 35 = true := by decide
theorem tmFiber72Row_36_ok : tmFiber72RowCheck 36 = true := by decide
theorem tmFiber72Row_37_ok : tmFiber72RowCheck 37 = true := by decide
theorem tmFiber72Row_38_ok : tmFiber72RowCheck 38 = true := by decide
theorem tmFiber72Row_39_ok : tmFiber72RowCheck 39 = true := by decide
theorem tmFiber72Row_40_ok : tmFiber72RowCheck 40 = true := by decide
theorem tmFiber72Row_41_ok : tmFiber72RowCheck 41 = true := by decide
theorem tmFiber72Row_42_ok : tmFiber72RowCheck 42 = true := by decide
theorem tmFiber72Row_43_ok : tmFiber72RowCheck 43 = true := by decide
theorem tmFiber72Row_44_ok : tmFiber72RowCheck 44 = true := by decide
theorem tmFiber72Row_45_ok : tmFiber72RowCheck 45 = true := by decide
theorem tmFiber72Row_46_ok : tmFiber72RowCheck 46 = true := by decide
theorem tmFiber72Row_47_ok : tmFiber72RowCheck 47 = true := by decide
theorem tmFiber72Row_48_ok : tmFiber72RowCheck 48 = true := by decide
theorem tmFiber72Row_49_ok : tmFiber72RowCheck 49 = true := by decide
theorem tmFiber72Row_50_ok : tmFiber72RowCheck 50 = true := by decide
theorem tmFiber72Row_51_ok : tmFiber72RowCheck 51 = true := by decide
theorem tmFiber72Row_52_ok : tmFiber72RowCheck 52 = true := by decide
theorem tmFiber72Row_53_ok : tmFiber72RowCheck 53 = true := by decide
theorem tmFiber72Row_54_ok : tmFiber72RowCheck 54 = true := by decide
theorem tmFiber72Row_55_ok : tmFiber72RowCheck 55 = true := by decide
theorem tmFiber72Row_56_ok : tmFiber72RowCheck 56 = true := by decide
theorem tmFiber72Row_57_ok : tmFiber72RowCheck 57 = true := by decide
theorem tmFiber72Row_58_ok : tmFiber72RowCheck 58 = true := by decide
theorem tmFiber72Row_59_ok : tmFiber72RowCheck 59 = true := by decide
theorem tmFiber72Row_60_ok : tmFiber72RowCheck 60 = true := by decide
theorem tmFiber72Row_61_ok : tmFiber72RowCheck 61 = true := by decide
theorem tmFiber72Row_62_ok : tmFiber72RowCheck 62 = true := by decide
theorem tmFiber72Row_63_ok : tmFiber72RowCheck 63 = true := by decide

def tmFiber72ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber72Rows tmMaxParentDepth (listGetD tmFiber72Expected i 0) == 144

theorem tmFiber72Parent_0_ok : tmFiber72ParentCheck 0 = true := by decide
theorem tmFiber72Parent_1_ok : tmFiber72ParentCheck 1 = true := by decide
theorem tmFiber72Parent_2_ok : tmFiber72ParentCheck 2 = true := by decide
theorem tmFiber72Parent_3_ok : tmFiber72ParentCheck 3 = true := by decide
theorem tmFiber72Parent_4_ok : tmFiber72ParentCheck 4 = true := by decide
theorem tmFiber72Parent_5_ok : tmFiber72ParentCheck 5 = true := by decide
theorem tmFiber72Parent_6_ok : tmFiber72ParentCheck 6 = true := by decide
theorem tmFiber72Parent_7_ok : tmFiber72ParentCheck 7 = true := by decide
theorem tmFiber72Parent_8_ok : tmFiber72ParentCheck 8 = true := by decide
theorem tmFiber72Parent_9_ok : tmFiber72ParentCheck 9 = true := by decide
theorem tmFiber72Parent_10_ok : tmFiber72ParentCheck 10 = true := by decide
theorem tmFiber72Parent_11_ok : tmFiber72ParentCheck 11 = true := by decide
theorem tmFiber72Parent_12_ok : tmFiber72ParentCheck 12 = true := by decide
theorem tmFiber72Parent_13_ok : tmFiber72ParentCheck 13 = true := by decide
theorem tmFiber72Parent_14_ok : tmFiber72ParentCheck 14 = true := by decide
theorem tmFiber72Parent_15_ok : tmFiber72ParentCheck 15 = true := by decide
theorem tmFiber72Parent_16_ok : tmFiber72ParentCheck 16 = true := by decide
theorem tmFiber72Parent_17_ok : tmFiber72ParentCheck 17 = true := by decide
theorem tmFiber72Parent_18_ok : tmFiber72ParentCheck 18 = true := by decide
theorem tmFiber72Parent_19_ok : tmFiber72ParentCheck 19 = true := by decide
theorem tmFiber72Parent_20_ok : tmFiber72ParentCheck 20 = true := by decide
theorem tmFiber72Parent_21_ok : tmFiber72ParentCheck 21 = true := by decide
theorem tmFiber72Parent_22_ok : tmFiber72ParentCheck 22 = true := by decide
theorem tmFiber72Parent_23_ok : tmFiber72ParentCheck 23 = true := by decide
theorem tmFiber72Parent_24_ok : tmFiber72ParentCheck 24 = true := by decide
theorem tmFiber72Parent_25_ok : tmFiber72ParentCheck 25 = true := by decide
theorem tmFiber72Parent_26_ok : tmFiber72ParentCheck 26 = true := by decide
theorem tmFiber72Parent_27_ok : tmFiber72ParentCheck 27 = true := by decide
theorem tmFiber72Parent_28_ok : tmFiber72ParentCheck 28 = true := by decide
theorem tmFiber72Parent_29_ok : tmFiber72ParentCheck 29 = true := by decide
theorem tmFiber72Parent_30_ok : tmFiber72ParentCheck 30 = true := by decide
theorem tmFiber72Parent_31_ok : tmFiber72ParentCheck 31 = true := by decide
theorem tmFiber72Parent_32_ok : tmFiber72ParentCheck 32 = true := by decide
theorem tmFiber72Parent_33_ok : tmFiber72ParentCheck 33 = true := by decide
theorem tmFiber72Parent_34_ok : tmFiber72ParentCheck 34 = true := by decide
theorem tmFiber72Parent_35_ok : tmFiber72ParentCheck 35 = true := by decide
theorem tmFiber72Parent_36_ok : tmFiber72ParentCheck 36 = true := by decide
theorem tmFiber72Parent_37_ok : tmFiber72ParentCheck 37 = true := by decide
theorem tmFiber72Parent_38_ok : tmFiber72ParentCheck 38 = true := by decide
theorem tmFiber72Parent_39_ok : tmFiber72ParentCheck 39 = true := by decide
theorem tmFiber72Parent_40_ok : tmFiber72ParentCheck 40 = true := by decide
theorem tmFiber72Parent_41_ok : tmFiber72ParentCheck 41 = true := by decide
theorem tmFiber72Parent_42_ok : tmFiber72ParentCheck 42 = true := by decide
theorem tmFiber72Parent_43_ok : tmFiber72ParentCheck 43 = true := by decide
theorem tmFiber72Parent_44_ok : tmFiber72ParentCheck 44 = true := by decide
theorem tmFiber72Parent_45_ok : tmFiber72ParentCheck 45 = true := by decide
theorem tmFiber72Parent_46_ok : tmFiber72ParentCheck 46 = true := by decide
theorem tmFiber72Parent_47_ok : tmFiber72ParentCheck 47 = true := by decide
theorem tmFiber72Parent_48_ok : tmFiber72ParentCheck 48 = true := by decide
theorem tmFiber72Parent_49_ok : tmFiber72ParentCheck 49 = true := by decide
theorem tmFiber72Parent_50_ok : tmFiber72ParentCheck 50 = true := by decide
theorem tmFiber72Parent_51_ok : tmFiber72ParentCheck 51 = true := by decide
theorem tmFiber72Parent_52_ok : tmFiber72ParentCheck 52 = true := by decide
theorem tmFiber72Parent_53_ok : tmFiber72ParentCheck 53 = true := by decide
theorem tmFiber72Parent_54_ok : tmFiber72ParentCheck 54 = true := by decide
theorem tmFiber72Parent_55_ok : tmFiber72ParentCheck 55 = true := by decide
theorem tmFiber72Parent_56_ok : tmFiber72ParentCheck 56 = true := by decide
theorem tmFiber72Parent_57_ok : tmFiber72ParentCheck 57 = true := by decide
theorem tmFiber72Parent_58_ok : tmFiber72ParentCheck 58 = true := by decide
theorem tmFiber72Parent_59_ok : tmFiber72ParentCheck 59 = true := by decide
theorem tmFiber72Parent_60_ok : tmFiber72ParentCheck 60 = true := by decide
theorem tmFiber72Parent_61_ok : tmFiber72ParentCheck 61 = true := by decide
theorem tmFiber72Parent_62_ok : tmFiber72ParentCheck 62 = true := by decide
theorem tmFiber72Parent_63_ok : tmFiber72ParentCheck 63 = true := by decide

def tmFiber72CertificateAudit : Bool :=
  tmFiber72SourcesCheck &&
    tmFiber72RowCheck 0 &&
    tmFiber72RowCheck 1 &&
    tmFiber72RowCheck 2 &&
    tmFiber72RowCheck 3 &&
    tmFiber72RowCheck 4 &&
    tmFiber72RowCheck 5 &&
    tmFiber72RowCheck 6 &&
    tmFiber72RowCheck 7 &&
    tmFiber72RowCheck 8 &&
    tmFiber72RowCheck 9 &&
    tmFiber72RowCheck 10 &&
    tmFiber72RowCheck 11 &&
    tmFiber72RowCheck 12 &&
    tmFiber72RowCheck 13 &&
    tmFiber72RowCheck 14 &&
    tmFiber72RowCheck 15 &&
    tmFiber72RowCheck 16 &&
    tmFiber72RowCheck 17 &&
    tmFiber72RowCheck 18 &&
    tmFiber72RowCheck 19 &&
    tmFiber72RowCheck 20 &&
    tmFiber72RowCheck 21 &&
    tmFiber72RowCheck 22 &&
    tmFiber72RowCheck 23 &&
    tmFiber72RowCheck 24 &&
    tmFiber72RowCheck 25 &&
    tmFiber72RowCheck 26 &&
    tmFiber72RowCheck 27 &&
    tmFiber72RowCheck 28 &&
    tmFiber72RowCheck 29 &&
    tmFiber72RowCheck 30 &&
    tmFiber72RowCheck 31 &&
    tmFiber72RowCheck 32 &&
    tmFiber72RowCheck 33 &&
    tmFiber72RowCheck 34 &&
    tmFiber72RowCheck 35 &&
    tmFiber72RowCheck 36 &&
    tmFiber72RowCheck 37 &&
    tmFiber72RowCheck 38 &&
    tmFiber72RowCheck 39 &&
    tmFiber72RowCheck 40 &&
    tmFiber72RowCheck 41 &&
    tmFiber72RowCheck 42 &&
    tmFiber72RowCheck 43 &&
    tmFiber72RowCheck 44 &&
    tmFiber72RowCheck 45 &&
    tmFiber72RowCheck 46 &&
    tmFiber72RowCheck 47 &&
    tmFiber72RowCheck 48 &&
    tmFiber72RowCheck 49 &&
    tmFiber72RowCheck 50 &&
    tmFiber72RowCheck 51 &&
    tmFiber72RowCheck 52 &&
    tmFiber72RowCheck 53 &&
    tmFiber72RowCheck 54 &&
    tmFiber72RowCheck 55 &&
    tmFiber72RowCheck 56 &&
    tmFiber72RowCheck 57 &&
    tmFiber72RowCheck 58 &&
    tmFiber72RowCheck 59 &&
    tmFiber72RowCheck 60 &&
    tmFiber72RowCheck 61 &&
    tmFiber72RowCheck 62 &&
    tmFiber72RowCheck 63 &&
    tmFiber72ParentCheck 0 &&
    tmFiber72ParentCheck 1 &&
    tmFiber72ParentCheck 2 &&
    tmFiber72ParentCheck 3 &&
    tmFiber72ParentCheck 4 &&
    tmFiber72ParentCheck 5 &&
    tmFiber72ParentCheck 6 &&
    tmFiber72ParentCheck 7 &&
    tmFiber72ParentCheck 8 &&
    tmFiber72ParentCheck 9 &&
    tmFiber72ParentCheck 10 &&
    tmFiber72ParentCheck 11 &&
    tmFiber72ParentCheck 12 &&
    tmFiber72ParentCheck 13 &&
    tmFiber72ParentCheck 14 &&
    tmFiber72ParentCheck 15 &&
    tmFiber72ParentCheck 16 &&
    tmFiber72ParentCheck 17 &&
    tmFiber72ParentCheck 18 &&
    tmFiber72ParentCheck 19 &&
    tmFiber72ParentCheck 20 &&
    tmFiber72ParentCheck 21 &&
    tmFiber72ParentCheck 22 &&
    tmFiber72ParentCheck 23 &&
    tmFiber72ParentCheck 24 &&
    tmFiber72ParentCheck 25 &&
    tmFiber72ParentCheck 26 &&
    tmFiber72ParentCheck 27 &&
    tmFiber72ParentCheck 28 &&
    tmFiber72ParentCheck 29 &&
    tmFiber72ParentCheck 30 &&
    tmFiber72ParentCheck 31 &&
    tmFiber72ParentCheck 32 &&
    tmFiber72ParentCheck 33 &&
    tmFiber72ParentCheck 34 &&
    tmFiber72ParentCheck 35 &&
    tmFiber72ParentCheck 36 &&
    tmFiber72ParentCheck 37 &&
    tmFiber72ParentCheck 38 &&
    tmFiber72ParentCheck 39 &&
    tmFiber72ParentCheck 40 &&
    tmFiber72ParentCheck 41 &&
    tmFiber72ParentCheck 42 &&
    tmFiber72ParentCheck 43 &&
    tmFiber72ParentCheck 44 &&
    tmFiber72ParentCheck 45 &&
    tmFiber72ParentCheck 46 &&
    tmFiber72ParentCheck 47 &&
    tmFiber72ParentCheck 48 &&
    tmFiber72ParentCheck 49 &&
    tmFiber72ParentCheck 50 &&
    tmFiber72ParentCheck 51 &&
    tmFiber72ParentCheck 52 &&
    tmFiber72ParentCheck 53 &&
    tmFiber72ParentCheck 54 &&
    tmFiber72ParentCheck 55 &&
    tmFiber72ParentCheck 56 &&
    tmFiber72ParentCheck 57 &&
    tmFiber72ParentCheck 58 &&
    tmFiber72ParentCheck 59 &&
    tmFiber72ParentCheck 60 &&
    tmFiber72ParentCheck 61 &&
    tmFiber72ParentCheck 62 &&
    tmFiber72ParentCheck 63

theorem tmFiber72CertificateAudit_ok :
    tmFiber72CertificateAudit = true := by
  simp [tmFiber72CertificateAudit,
    tmFiber72SourcesCheck_ok,
    tmFiber72Row_0_ok,
    tmFiber72Row_1_ok,
    tmFiber72Row_2_ok,
    tmFiber72Row_3_ok,
    tmFiber72Row_4_ok,
    tmFiber72Row_5_ok,
    tmFiber72Row_6_ok,
    tmFiber72Row_7_ok,
    tmFiber72Row_8_ok,
    tmFiber72Row_9_ok,
    tmFiber72Row_10_ok,
    tmFiber72Row_11_ok,
    tmFiber72Row_12_ok,
    tmFiber72Row_13_ok,
    tmFiber72Row_14_ok,
    tmFiber72Row_15_ok,
    tmFiber72Row_16_ok,
    tmFiber72Row_17_ok,
    tmFiber72Row_18_ok,
    tmFiber72Row_19_ok,
    tmFiber72Row_20_ok,
    tmFiber72Row_21_ok,
    tmFiber72Row_22_ok,
    tmFiber72Row_23_ok,
    tmFiber72Row_24_ok,
    tmFiber72Row_25_ok,
    tmFiber72Row_26_ok,
    tmFiber72Row_27_ok,
    tmFiber72Row_28_ok,
    tmFiber72Row_29_ok,
    tmFiber72Row_30_ok,
    tmFiber72Row_31_ok,
    tmFiber72Row_32_ok,
    tmFiber72Row_33_ok,
    tmFiber72Row_34_ok,
    tmFiber72Row_35_ok,
    tmFiber72Row_36_ok,
    tmFiber72Row_37_ok,
    tmFiber72Row_38_ok,
    tmFiber72Row_39_ok,
    tmFiber72Row_40_ok,
    tmFiber72Row_41_ok,
    tmFiber72Row_42_ok,
    tmFiber72Row_43_ok,
    tmFiber72Row_44_ok,
    tmFiber72Row_45_ok,
    tmFiber72Row_46_ok,
    tmFiber72Row_47_ok,
    tmFiber72Row_48_ok,
    tmFiber72Row_49_ok,
    tmFiber72Row_50_ok,
    tmFiber72Row_51_ok,
    tmFiber72Row_52_ok,
    tmFiber72Row_53_ok,
    tmFiber72Row_54_ok,
    tmFiber72Row_55_ok,
    tmFiber72Row_56_ok,
    tmFiber72Row_57_ok,
    tmFiber72Row_58_ok,
    tmFiber72Row_59_ok,
    tmFiber72Row_60_ok,
    tmFiber72Row_61_ok,
    tmFiber72Row_62_ok,
    tmFiber72Row_63_ok,
    tmFiber72Parent_0_ok,
    tmFiber72Parent_1_ok,
    tmFiber72Parent_2_ok,
    tmFiber72Parent_3_ok,
    tmFiber72Parent_4_ok,
    tmFiber72Parent_5_ok,
    tmFiber72Parent_6_ok,
    tmFiber72Parent_7_ok,
    tmFiber72Parent_8_ok,
    tmFiber72Parent_9_ok,
    tmFiber72Parent_10_ok,
    tmFiber72Parent_11_ok,
    tmFiber72Parent_12_ok,
    tmFiber72Parent_13_ok,
    tmFiber72Parent_14_ok,
    tmFiber72Parent_15_ok,
    tmFiber72Parent_16_ok,
    tmFiber72Parent_17_ok,
    tmFiber72Parent_18_ok,
    tmFiber72Parent_19_ok,
    tmFiber72Parent_20_ok,
    tmFiber72Parent_21_ok,
    tmFiber72Parent_22_ok,
    tmFiber72Parent_23_ok,
    tmFiber72Parent_24_ok,
    tmFiber72Parent_25_ok,
    tmFiber72Parent_26_ok,
    tmFiber72Parent_27_ok,
    tmFiber72Parent_28_ok,
    tmFiber72Parent_29_ok,
    tmFiber72Parent_30_ok,
    tmFiber72Parent_31_ok,
    tmFiber72Parent_32_ok,
    tmFiber72Parent_33_ok,
    tmFiber72Parent_34_ok,
    tmFiber72Parent_35_ok,
    tmFiber72Parent_36_ok,
    tmFiber72Parent_37_ok,
    tmFiber72Parent_38_ok,
    tmFiber72Parent_39_ok,
    tmFiber72Parent_40_ok,
    tmFiber72Parent_41_ok,
    tmFiber72Parent_42_ok,
    tmFiber72Parent_43_ok,
    tmFiber72Parent_44_ok,
    tmFiber72Parent_45_ok,
    tmFiber72Parent_46_ok,
    tmFiber72Parent_47_ok,
    tmFiber72Parent_48_ok,
    tmFiber72Parent_49_ok,
    tmFiber72Parent_50_ok,
    tmFiber72Parent_51_ok,
    tmFiber72Parent_52_ok,
    tmFiber72Parent_53_ok,
    tmFiber72Parent_54_ok,
    tmFiber72Parent_55_ok,
    tmFiber72Parent_56_ok,
    tmFiber72Parent_57_ok,
    tmFiber72Parent_58_ok,
    tmFiber72Parent_59_ok,
    tmFiber72Parent_60_ok,
    tmFiber72Parent_61_ok,
    tmFiber72Parent_62_ok,
    tmFiber72Parent_63_ok]

def tmFiber73Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.b]

def tmFiber73Expected : List Nat :=
  [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]

def tmFiber73Rows : List DirectChainParentRow :=
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

def tmFiber73RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber73Rows i default

def tmFiber73SourcesCheck : Bool :=
  (tmFiber73Rows.map fun row => row.source) == tmFiber73Expected

theorem tmFiber73SourcesCheck_ok :
    tmFiber73SourcesCheck = true := by
  decide

def tmFiber73RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt i)

theorem tmFiber73Row_0_ok : tmFiber73RowCheck 0 = true := by decide
theorem tmFiber73Row_1_ok : tmFiber73RowCheck 1 = true := by decide
theorem tmFiber73Row_2_ok : tmFiber73RowCheck 2 = true := by decide
theorem tmFiber73Row_3_ok : tmFiber73RowCheck 3 = true := by decide
theorem tmFiber73Row_4_ok : tmFiber73RowCheck 4 = true := by decide
theorem tmFiber73Row_5_ok : tmFiber73RowCheck 5 = true := by decide
theorem tmFiber73Row_6_ok : tmFiber73RowCheck 6 = true := by decide
theorem tmFiber73Row_7_ok : tmFiber73RowCheck 7 = true := by decide
theorem tmFiber73Row_8_ok : tmFiber73RowCheck 8 = true := by decide
theorem tmFiber73Row_9_ok : tmFiber73RowCheck 9 = true := by decide
theorem tmFiber73Row_10_ok : tmFiber73RowCheck 10 = true := by decide
theorem tmFiber73Row_11_ok : tmFiber73RowCheck 11 = true := by decide
theorem tmFiber73Row_12_ok : tmFiber73RowCheck 12 = true := by decide
theorem tmFiber73Row_13_ok : tmFiber73RowCheck 13 = true := by decide
theorem tmFiber73Row_14_ok : tmFiber73RowCheck 14 = true := by decide
theorem tmFiber73Row_15_ok : tmFiber73RowCheck 15 = true := by decide

def tmFiber73ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber73Rows tmMaxParentDepth (listGetD tmFiber73Expected i 0) == 272

theorem tmFiber73Parent_0_ok : tmFiber73ParentCheck 0 = true := by decide
theorem tmFiber73Parent_1_ok : tmFiber73ParentCheck 1 = true := by decide
theorem tmFiber73Parent_2_ok : tmFiber73ParentCheck 2 = true := by decide
theorem tmFiber73Parent_3_ok : tmFiber73ParentCheck 3 = true := by decide
theorem tmFiber73Parent_4_ok : tmFiber73ParentCheck 4 = true := by decide
theorem tmFiber73Parent_5_ok : tmFiber73ParentCheck 5 = true := by decide
theorem tmFiber73Parent_6_ok : tmFiber73ParentCheck 6 = true := by decide
theorem tmFiber73Parent_7_ok : tmFiber73ParentCheck 7 = true := by decide
theorem tmFiber73Parent_8_ok : tmFiber73ParentCheck 8 = true := by decide
theorem tmFiber73Parent_9_ok : tmFiber73ParentCheck 9 = true := by decide
theorem tmFiber73Parent_10_ok : tmFiber73ParentCheck 10 = true := by decide
theorem tmFiber73Parent_11_ok : tmFiber73ParentCheck 11 = true := by decide
theorem tmFiber73Parent_12_ok : tmFiber73ParentCheck 12 = true := by decide
theorem tmFiber73Parent_13_ok : tmFiber73ParentCheck 13 = true := by decide
theorem tmFiber73Parent_14_ok : tmFiber73ParentCheck 14 = true := by decide
theorem tmFiber73Parent_15_ok : tmFiber73ParentCheck 15 = true := by decide

def tmFiber73CertificateAudit : Bool :=
  tmFiber73SourcesCheck &&
    tmFiber73RowCheck 0 &&
    tmFiber73RowCheck 1 &&
    tmFiber73RowCheck 2 &&
    tmFiber73RowCheck 3 &&
    tmFiber73RowCheck 4 &&
    tmFiber73RowCheck 5 &&
    tmFiber73RowCheck 6 &&
    tmFiber73RowCheck 7 &&
    tmFiber73RowCheck 8 &&
    tmFiber73RowCheck 9 &&
    tmFiber73RowCheck 10 &&
    tmFiber73RowCheck 11 &&
    tmFiber73RowCheck 12 &&
    tmFiber73RowCheck 13 &&
    tmFiber73RowCheck 14 &&
    tmFiber73RowCheck 15 &&
    tmFiber73ParentCheck 0 &&
    tmFiber73ParentCheck 1 &&
    tmFiber73ParentCheck 2 &&
    tmFiber73ParentCheck 3 &&
    tmFiber73ParentCheck 4 &&
    tmFiber73ParentCheck 5 &&
    tmFiber73ParentCheck 6 &&
    tmFiber73ParentCheck 7 &&
    tmFiber73ParentCheck 8 &&
    tmFiber73ParentCheck 9 &&
    tmFiber73ParentCheck 10 &&
    tmFiber73ParentCheck 11 &&
    tmFiber73ParentCheck 12 &&
    tmFiber73ParentCheck 13 &&
    tmFiber73ParentCheck 14 &&
    tmFiber73ParentCheck 15

theorem tmFiber73CertificateAudit_ok :
    tmFiber73CertificateAudit = true := by
  simp [tmFiber73CertificateAudit,
    tmFiber73SourcesCheck_ok,
    tmFiber73Row_0_ok,
    tmFiber73Row_1_ok,
    tmFiber73Row_2_ok,
    tmFiber73Row_3_ok,
    tmFiber73Row_4_ok,
    tmFiber73Row_5_ok,
    tmFiber73Row_6_ok,
    tmFiber73Row_7_ok,
    tmFiber73Row_8_ok,
    tmFiber73Row_9_ok,
    tmFiber73Row_10_ok,
    tmFiber73Row_11_ok,
    tmFiber73Row_12_ok,
    tmFiber73Row_13_ok,
    tmFiber73Row_14_ok,
    tmFiber73Row_15_ok,
    tmFiber73Parent_0_ok,
    tmFiber73Parent_1_ok,
    tmFiber73Parent_2_ok,
    tmFiber73Parent_3_ok,
    tmFiber73Parent_4_ok,
    tmFiber73Parent_5_ok,
    tmFiber73Parent_6_ok,
    tmFiber73Parent_7_ok,
    tmFiber73Parent_8_ok,
    tmFiber73Parent_9_ok,
    tmFiber73Parent_10_ok,
    tmFiber73Parent_11_ok,
    tmFiber73Parent_12_ok,
    tmFiber73Parent_13_ok,
    tmFiber73Parent_14_ok,
    tmFiber73Parent_15_ok]

def tmFiber74Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.p]

def tmFiber74Expected : List Nat :=
  [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]

def tmFiber74Rows : List DirectChainParentRow :=
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

def tmFiber74RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber74Rows i default

def tmFiber74SourcesCheck : Bool :=
  (tmFiber74Rows.map fun row => row.source) == tmFiber74Expected

theorem tmFiber74SourcesCheck_ok :
    tmFiber74SourcesCheck = true := by
  decide

def tmFiber74RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt i)

theorem tmFiber74Row_0_ok : tmFiber74RowCheck 0 = true := by decide
theorem tmFiber74Row_1_ok : tmFiber74RowCheck 1 = true := by decide
theorem tmFiber74Row_2_ok : tmFiber74RowCheck 2 = true := by decide
theorem tmFiber74Row_3_ok : tmFiber74RowCheck 3 = true := by decide
theorem tmFiber74Row_4_ok : tmFiber74RowCheck 4 = true := by decide
theorem tmFiber74Row_5_ok : tmFiber74RowCheck 5 = true := by decide
theorem tmFiber74Row_6_ok : tmFiber74RowCheck 6 = true := by decide
theorem tmFiber74Row_7_ok : tmFiber74RowCheck 7 = true := by decide
theorem tmFiber74Row_8_ok : tmFiber74RowCheck 8 = true := by decide
theorem tmFiber74Row_9_ok : tmFiber74RowCheck 9 = true := by decide
theorem tmFiber74Row_10_ok : tmFiber74RowCheck 10 = true := by decide
theorem tmFiber74Row_11_ok : tmFiber74RowCheck 11 = true := by decide
theorem tmFiber74Row_12_ok : tmFiber74RowCheck 12 = true := by decide
theorem tmFiber74Row_13_ok : tmFiber74RowCheck 13 = true := by decide
theorem tmFiber74Row_14_ok : tmFiber74RowCheck 14 = true := by decide
theorem tmFiber74Row_15_ok : tmFiber74RowCheck 15 = true := by decide

def tmFiber74ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber74Rows tmMaxParentDepth (listGetD tmFiber74Expected i 0) == 176

theorem tmFiber74Parent_0_ok : tmFiber74ParentCheck 0 = true := by decide
theorem tmFiber74Parent_1_ok : tmFiber74ParentCheck 1 = true := by decide
theorem tmFiber74Parent_2_ok : tmFiber74ParentCheck 2 = true := by decide
theorem tmFiber74Parent_3_ok : tmFiber74ParentCheck 3 = true := by decide
theorem tmFiber74Parent_4_ok : tmFiber74ParentCheck 4 = true := by decide
theorem tmFiber74Parent_5_ok : tmFiber74ParentCheck 5 = true := by decide
theorem tmFiber74Parent_6_ok : tmFiber74ParentCheck 6 = true := by decide
theorem tmFiber74Parent_7_ok : tmFiber74ParentCheck 7 = true := by decide
theorem tmFiber74Parent_8_ok : tmFiber74ParentCheck 8 = true := by decide
theorem tmFiber74Parent_9_ok : tmFiber74ParentCheck 9 = true := by decide
theorem tmFiber74Parent_10_ok : tmFiber74ParentCheck 10 = true := by decide
theorem tmFiber74Parent_11_ok : tmFiber74ParentCheck 11 = true := by decide
theorem tmFiber74Parent_12_ok : tmFiber74ParentCheck 12 = true := by decide
theorem tmFiber74Parent_13_ok : tmFiber74ParentCheck 13 = true := by decide
theorem tmFiber74Parent_14_ok : tmFiber74ParentCheck 14 = true := by decide
theorem tmFiber74Parent_15_ok : tmFiber74ParentCheck 15 = true := by decide

def tmFiber74CertificateAudit : Bool :=
  tmFiber74SourcesCheck &&
    tmFiber74RowCheck 0 &&
    tmFiber74RowCheck 1 &&
    tmFiber74RowCheck 2 &&
    tmFiber74RowCheck 3 &&
    tmFiber74RowCheck 4 &&
    tmFiber74RowCheck 5 &&
    tmFiber74RowCheck 6 &&
    tmFiber74RowCheck 7 &&
    tmFiber74RowCheck 8 &&
    tmFiber74RowCheck 9 &&
    tmFiber74RowCheck 10 &&
    tmFiber74RowCheck 11 &&
    tmFiber74RowCheck 12 &&
    tmFiber74RowCheck 13 &&
    tmFiber74RowCheck 14 &&
    tmFiber74RowCheck 15 &&
    tmFiber74ParentCheck 0 &&
    tmFiber74ParentCheck 1 &&
    tmFiber74ParentCheck 2 &&
    tmFiber74ParentCheck 3 &&
    tmFiber74ParentCheck 4 &&
    tmFiber74ParentCheck 5 &&
    tmFiber74ParentCheck 6 &&
    tmFiber74ParentCheck 7 &&
    tmFiber74ParentCheck 8 &&
    tmFiber74ParentCheck 9 &&
    tmFiber74ParentCheck 10 &&
    tmFiber74ParentCheck 11 &&
    tmFiber74ParentCheck 12 &&
    tmFiber74ParentCheck 13 &&
    tmFiber74ParentCheck 14 &&
    tmFiber74ParentCheck 15

theorem tmFiber74CertificateAudit_ok :
    tmFiber74CertificateAudit = true := by
  simp [tmFiber74CertificateAudit,
    tmFiber74SourcesCheck_ok,
    tmFiber74Row_0_ok,
    tmFiber74Row_1_ok,
    tmFiber74Row_2_ok,
    tmFiber74Row_3_ok,
    tmFiber74Row_4_ok,
    tmFiber74Row_5_ok,
    tmFiber74Row_6_ok,
    tmFiber74Row_7_ok,
    tmFiber74Row_8_ok,
    tmFiber74Row_9_ok,
    tmFiber74Row_10_ok,
    tmFiber74Row_11_ok,
    tmFiber74Row_12_ok,
    tmFiber74Row_13_ok,
    tmFiber74Row_14_ok,
    tmFiber74Row_15_ok,
    tmFiber74Parent_0_ok,
    tmFiber74Parent_1_ok,
    tmFiber74Parent_2_ok,
    tmFiber74Parent_3_ok,
    tmFiber74Parent_4_ok,
    tmFiber74Parent_5_ok,
    tmFiber74Parent_6_ok,
    tmFiber74Parent_7_ok,
    tmFiber74Parent_8_ok,
    tmFiber74Parent_9_ok,
    tmFiber74Parent_10_ok,
    tmFiber74Parent_11_ok,
    tmFiber74Parent_12_ok,
    tmFiber74Parent_13_ok,
    tmFiber74Parent_14_ok,
    tmFiber74Parent_15_ok]

def tmFiber75Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.r]

def tmFiber75Expected : List Nat :=
  [624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]

def tmFiber75Rows : List DirectChainParentRow :=
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

def tmFiber75RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber75Rows i default

def tmFiber75SourcesCheck : Bool :=
  (tmFiber75Rows.map fun row => row.source) == tmFiber75Expected

theorem tmFiber75SourcesCheck_ok :
    tmFiber75SourcesCheck = true := by
  decide

def tmFiber75RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt i)

theorem tmFiber75Row_0_ok : tmFiber75RowCheck 0 = true := by decide
theorem tmFiber75Row_1_ok : tmFiber75RowCheck 1 = true := by decide
theorem tmFiber75Row_2_ok : tmFiber75RowCheck 2 = true := by decide
theorem tmFiber75Row_3_ok : tmFiber75RowCheck 3 = true := by decide
theorem tmFiber75Row_4_ok : tmFiber75RowCheck 4 = true := by decide
theorem tmFiber75Row_5_ok : tmFiber75RowCheck 5 = true := by decide
theorem tmFiber75Row_6_ok : tmFiber75RowCheck 6 = true := by decide
theorem tmFiber75Row_7_ok : tmFiber75RowCheck 7 = true := by decide
theorem tmFiber75Row_8_ok : tmFiber75RowCheck 8 = true := by decide
theorem tmFiber75Row_9_ok : tmFiber75RowCheck 9 = true := by decide
theorem tmFiber75Row_10_ok : tmFiber75RowCheck 10 = true := by decide
theorem tmFiber75Row_11_ok : tmFiber75RowCheck 11 = true := by decide
theorem tmFiber75Row_12_ok : tmFiber75RowCheck 12 = true := by decide
theorem tmFiber75Row_13_ok : tmFiber75RowCheck 13 = true := by decide
theorem tmFiber75Row_14_ok : tmFiber75RowCheck 14 = true := by decide
theorem tmFiber75Row_15_ok : tmFiber75RowCheck 15 = true := by decide

def tmFiber75ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber75Rows tmMaxParentDepth (listGetD tmFiber75Expected i 0) == 624

theorem tmFiber75Parent_0_ok : tmFiber75ParentCheck 0 = true := by decide
theorem tmFiber75Parent_1_ok : tmFiber75ParentCheck 1 = true := by decide
theorem tmFiber75Parent_2_ok : tmFiber75ParentCheck 2 = true := by decide
theorem tmFiber75Parent_3_ok : tmFiber75ParentCheck 3 = true := by decide
theorem tmFiber75Parent_4_ok : tmFiber75ParentCheck 4 = true := by decide
theorem tmFiber75Parent_5_ok : tmFiber75ParentCheck 5 = true := by decide
theorem tmFiber75Parent_6_ok : tmFiber75ParentCheck 6 = true := by decide
theorem tmFiber75Parent_7_ok : tmFiber75ParentCheck 7 = true := by decide
theorem tmFiber75Parent_8_ok : tmFiber75ParentCheck 8 = true := by decide
theorem tmFiber75Parent_9_ok : tmFiber75ParentCheck 9 = true := by decide
theorem tmFiber75Parent_10_ok : tmFiber75ParentCheck 10 = true := by decide
theorem tmFiber75Parent_11_ok : tmFiber75ParentCheck 11 = true := by decide
theorem tmFiber75Parent_12_ok : tmFiber75ParentCheck 12 = true := by decide
theorem tmFiber75Parent_13_ok : tmFiber75ParentCheck 13 = true := by decide
theorem tmFiber75Parent_14_ok : tmFiber75ParentCheck 14 = true := by decide
theorem tmFiber75Parent_15_ok : tmFiber75ParentCheck 15 = true := by decide

def tmFiber75CertificateAudit : Bool :=
  tmFiber75SourcesCheck &&
    tmFiber75RowCheck 0 &&
    tmFiber75RowCheck 1 &&
    tmFiber75RowCheck 2 &&
    tmFiber75RowCheck 3 &&
    tmFiber75RowCheck 4 &&
    tmFiber75RowCheck 5 &&
    tmFiber75RowCheck 6 &&
    tmFiber75RowCheck 7 &&
    tmFiber75RowCheck 8 &&
    tmFiber75RowCheck 9 &&
    tmFiber75RowCheck 10 &&
    tmFiber75RowCheck 11 &&
    tmFiber75RowCheck 12 &&
    tmFiber75RowCheck 13 &&
    tmFiber75RowCheck 14 &&
    tmFiber75RowCheck 15 &&
    tmFiber75ParentCheck 0 &&
    tmFiber75ParentCheck 1 &&
    tmFiber75ParentCheck 2 &&
    tmFiber75ParentCheck 3 &&
    tmFiber75ParentCheck 4 &&
    tmFiber75ParentCheck 5 &&
    tmFiber75ParentCheck 6 &&
    tmFiber75ParentCheck 7 &&
    tmFiber75ParentCheck 8 &&
    tmFiber75ParentCheck 9 &&
    tmFiber75ParentCheck 10 &&
    tmFiber75ParentCheck 11 &&
    tmFiber75ParentCheck 12 &&
    tmFiber75ParentCheck 13 &&
    tmFiber75ParentCheck 14 &&
    tmFiber75ParentCheck 15

theorem tmFiber75CertificateAudit_ok :
    tmFiber75CertificateAudit = true := by
  simp [tmFiber75CertificateAudit,
    tmFiber75SourcesCheck_ok,
    tmFiber75Row_0_ok,
    tmFiber75Row_1_ok,
    tmFiber75Row_2_ok,
    tmFiber75Row_3_ok,
    tmFiber75Row_4_ok,
    tmFiber75Row_5_ok,
    tmFiber75Row_6_ok,
    tmFiber75Row_7_ok,
    tmFiber75Row_8_ok,
    tmFiber75Row_9_ok,
    tmFiber75Row_10_ok,
    tmFiber75Row_11_ok,
    tmFiber75Row_12_ok,
    tmFiber75Row_13_ok,
    tmFiber75Row_14_ok,
    tmFiber75Row_15_ok,
    tmFiber75Parent_0_ok,
    tmFiber75Parent_1_ok,
    tmFiber75Parent_2_ok,
    tmFiber75Parent_3_ok,
    tmFiber75Parent_4_ok,
    tmFiber75Parent_5_ok,
    tmFiber75Parent_6_ok,
    tmFiber75Parent_7_ok,
    tmFiber75Parent_8_ok,
    tmFiber75Parent_9_ok,
    tmFiber75Parent_10_ok,
    tmFiber75Parent_11_ok,
    tmFiber75Parent_12_ok,
    tmFiber75Parent_13_ok,
    tmFiber75Parent_14_ok,
    tmFiber75Parent_15_ok]

def tmFiber76Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.b]

def tmFiber76Expected : List Nat :=
  [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]

def tmFiber76Rows : List DirectChainParentRow :=
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

def tmFiber76RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber76Rows i default

def tmFiber76SourcesCheck : Bool :=
  (tmFiber76Rows.map fun row => row.source) == tmFiber76Expected

theorem tmFiber76SourcesCheck_ok :
    tmFiber76SourcesCheck = true := by
  decide

def tmFiber76RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber76Key tmFiber76Expected (tmFiber76RowAt i)

theorem tmFiber76Row_0_ok : tmFiber76RowCheck 0 = true := by decide
theorem tmFiber76Row_1_ok : tmFiber76RowCheck 1 = true := by decide
theorem tmFiber76Row_2_ok : tmFiber76RowCheck 2 = true := by decide
theorem tmFiber76Row_3_ok : tmFiber76RowCheck 3 = true := by decide
theorem tmFiber76Row_4_ok : tmFiber76RowCheck 4 = true := by decide
theorem tmFiber76Row_5_ok : tmFiber76RowCheck 5 = true := by decide
theorem tmFiber76Row_6_ok : tmFiber76RowCheck 6 = true := by decide
theorem tmFiber76Row_7_ok : tmFiber76RowCheck 7 = true := by decide
theorem tmFiber76Row_8_ok : tmFiber76RowCheck 8 = true := by decide
theorem tmFiber76Row_9_ok : tmFiber76RowCheck 9 = true := by decide
theorem tmFiber76Row_10_ok : tmFiber76RowCheck 10 = true := by decide
theorem tmFiber76Row_11_ok : tmFiber76RowCheck 11 = true := by decide
theorem tmFiber76Row_12_ok : tmFiber76RowCheck 12 = true := by decide
theorem tmFiber76Row_13_ok : tmFiber76RowCheck 13 = true := by decide
theorem tmFiber76Row_14_ok : tmFiber76RowCheck 14 = true := by decide
theorem tmFiber76Row_15_ok : tmFiber76RowCheck 15 = true := by decide
theorem tmFiber76Row_16_ok : tmFiber76RowCheck 16 = true := by decide
theorem tmFiber76Row_17_ok : tmFiber76RowCheck 17 = true := by decide
theorem tmFiber76Row_18_ok : tmFiber76RowCheck 18 = true := by decide
theorem tmFiber76Row_19_ok : tmFiber76RowCheck 19 = true := by decide
theorem tmFiber76Row_20_ok : tmFiber76RowCheck 20 = true := by decide
theorem tmFiber76Row_21_ok : tmFiber76RowCheck 21 = true := by decide
theorem tmFiber76Row_22_ok : tmFiber76RowCheck 22 = true := by decide
theorem tmFiber76Row_23_ok : tmFiber76RowCheck 23 = true := by decide
theorem tmFiber76Row_24_ok : tmFiber76RowCheck 24 = true := by decide
theorem tmFiber76Row_25_ok : tmFiber76RowCheck 25 = true := by decide
theorem tmFiber76Row_26_ok : tmFiber76RowCheck 26 = true := by decide
theorem tmFiber76Row_27_ok : tmFiber76RowCheck 27 = true := by decide
theorem tmFiber76Row_28_ok : tmFiber76RowCheck 28 = true := by decide
theorem tmFiber76Row_29_ok : tmFiber76RowCheck 29 = true := by decide
theorem tmFiber76Row_30_ok : tmFiber76RowCheck 30 = true := by decide
theorem tmFiber76Row_31_ok : tmFiber76RowCheck 31 = true := by decide
theorem tmFiber76Row_32_ok : tmFiber76RowCheck 32 = true := by decide
theorem tmFiber76Row_33_ok : tmFiber76RowCheck 33 = true := by decide
theorem tmFiber76Row_34_ok : tmFiber76RowCheck 34 = true := by decide
theorem tmFiber76Row_35_ok : tmFiber76RowCheck 35 = true := by decide
theorem tmFiber76Row_36_ok : tmFiber76RowCheck 36 = true := by decide
theorem tmFiber76Row_37_ok : tmFiber76RowCheck 37 = true := by decide
theorem tmFiber76Row_38_ok : tmFiber76RowCheck 38 = true := by decide
theorem tmFiber76Row_39_ok : tmFiber76RowCheck 39 = true := by decide
theorem tmFiber76Row_40_ok : tmFiber76RowCheck 40 = true := by decide
theorem tmFiber76Row_41_ok : tmFiber76RowCheck 41 = true := by decide
theorem tmFiber76Row_42_ok : tmFiber76RowCheck 42 = true := by decide
theorem tmFiber76Row_43_ok : tmFiber76RowCheck 43 = true := by decide
theorem tmFiber76Row_44_ok : tmFiber76RowCheck 44 = true := by decide
theorem tmFiber76Row_45_ok : tmFiber76RowCheck 45 = true := by decide
theorem tmFiber76Row_46_ok : tmFiber76RowCheck 46 = true := by decide
theorem tmFiber76Row_47_ok : tmFiber76RowCheck 47 = true := by decide
theorem tmFiber76Row_48_ok : tmFiber76RowCheck 48 = true := by decide
theorem tmFiber76Row_49_ok : tmFiber76RowCheck 49 = true := by decide
theorem tmFiber76Row_50_ok : tmFiber76RowCheck 50 = true := by decide
theorem tmFiber76Row_51_ok : tmFiber76RowCheck 51 = true := by decide
theorem tmFiber76Row_52_ok : tmFiber76RowCheck 52 = true := by decide
theorem tmFiber76Row_53_ok : tmFiber76RowCheck 53 = true := by decide
theorem tmFiber76Row_54_ok : tmFiber76RowCheck 54 = true := by decide
theorem tmFiber76Row_55_ok : tmFiber76RowCheck 55 = true := by decide
theorem tmFiber76Row_56_ok : tmFiber76RowCheck 56 = true := by decide
theorem tmFiber76Row_57_ok : tmFiber76RowCheck 57 = true := by decide
theorem tmFiber76Row_58_ok : tmFiber76RowCheck 58 = true := by decide
theorem tmFiber76Row_59_ok : tmFiber76RowCheck 59 = true := by decide
theorem tmFiber76Row_60_ok : tmFiber76RowCheck 60 = true := by decide
theorem tmFiber76Row_61_ok : tmFiber76RowCheck 61 = true := by decide
theorem tmFiber76Row_62_ok : tmFiber76RowCheck 62 = true := by decide
theorem tmFiber76Row_63_ok : tmFiber76RowCheck 63 = true := by decide

def tmFiber76ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber76Rows tmMaxParentDepth (listGetD tmFiber76Expected i 0) == 528

theorem tmFiber76Parent_0_ok : tmFiber76ParentCheck 0 = true := by decide
theorem tmFiber76Parent_1_ok : tmFiber76ParentCheck 1 = true := by decide
theorem tmFiber76Parent_2_ok : tmFiber76ParentCheck 2 = true := by decide
theorem tmFiber76Parent_3_ok : tmFiber76ParentCheck 3 = true := by decide
theorem tmFiber76Parent_4_ok : tmFiber76ParentCheck 4 = true := by decide
theorem tmFiber76Parent_5_ok : tmFiber76ParentCheck 5 = true := by decide
theorem tmFiber76Parent_6_ok : tmFiber76ParentCheck 6 = true := by decide
theorem tmFiber76Parent_7_ok : tmFiber76ParentCheck 7 = true := by decide
theorem tmFiber76Parent_8_ok : tmFiber76ParentCheck 8 = true := by decide
theorem tmFiber76Parent_9_ok : tmFiber76ParentCheck 9 = true := by decide
theorem tmFiber76Parent_10_ok : tmFiber76ParentCheck 10 = true := by decide
theorem tmFiber76Parent_11_ok : tmFiber76ParentCheck 11 = true := by decide
theorem tmFiber76Parent_12_ok : tmFiber76ParentCheck 12 = true := by decide
theorem tmFiber76Parent_13_ok : tmFiber76ParentCheck 13 = true := by decide
theorem tmFiber76Parent_14_ok : tmFiber76ParentCheck 14 = true := by decide
theorem tmFiber76Parent_15_ok : tmFiber76ParentCheck 15 = true := by decide
theorem tmFiber76Parent_16_ok : tmFiber76ParentCheck 16 = true := by decide
theorem tmFiber76Parent_17_ok : tmFiber76ParentCheck 17 = true := by decide
theorem tmFiber76Parent_18_ok : tmFiber76ParentCheck 18 = true := by decide
theorem tmFiber76Parent_19_ok : tmFiber76ParentCheck 19 = true := by decide
theorem tmFiber76Parent_20_ok : tmFiber76ParentCheck 20 = true := by decide
theorem tmFiber76Parent_21_ok : tmFiber76ParentCheck 21 = true := by decide
theorem tmFiber76Parent_22_ok : tmFiber76ParentCheck 22 = true := by decide
theorem tmFiber76Parent_23_ok : tmFiber76ParentCheck 23 = true := by decide
theorem tmFiber76Parent_24_ok : tmFiber76ParentCheck 24 = true := by decide
theorem tmFiber76Parent_25_ok : tmFiber76ParentCheck 25 = true := by decide
theorem tmFiber76Parent_26_ok : tmFiber76ParentCheck 26 = true := by decide
theorem tmFiber76Parent_27_ok : tmFiber76ParentCheck 27 = true := by decide
theorem tmFiber76Parent_28_ok : tmFiber76ParentCheck 28 = true := by decide
theorem tmFiber76Parent_29_ok : tmFiber76ParentCheck 29 = true := by decide
theorem tmFiber76Parent_30_ok : tmFiber76ParentCheck 30 = true := by decide
theorem tmFiber76Parent_31_ok : tmFiber76ParentCheck 31 = true := by decide
theorem tmFiber76Parent_32_ok : tmFiber76ParentCheck 32 = true := by decide
theorem tmFiber76Parent_33_ok : tmFiber76ParentCheck 33 = true := by decide
theorem tmFiber76Parent_34_ok : tmFiber76ParentCheck 34 = true := by decide
theorem tmFiber76Parent_35_ok : tmFiber76ParentCheck 35 = true := by decide
theorem tmFiber76Parent_36_ok : tmFiber76ParentCheck 36 = true := by decide
theorem tmFiber76Parent_37_ok : tmFiber76ParentCheck 37 = true := by decide
theorem tmFiber76Parent_38_ok : tmFiber76ParentCheck 38 = true := by decide
theorem tmFiber76Parent_39_ok : tmFiber76ParentCheck 39 = true := by decide
theorem tmFiber76Parent_40_ok : tmFiber76ParentCheck 40 = true := by decide
theorem tmFiber76Parent_41_ok : tmFiber76ParentCheck 41 = true := by decide
theorem tmFiber76Parent_42_ok : tmFiber76ParentCheck 42 = true := by decide
theorem tmFiber76Parent_43_ok : tmFiber76ParentCheck 43 = true := by decide
theorem tmFiber76Parent_44_ok : tmFiber76ParentCheck 44 = true := by decide
theorem tmFiber76Parent_45_ok : tmFiber76ParentCheck 45 = true := by decide
theorem tmFiber76Parent_46_ok : tmFiber76ParentCheck 46 = true := by decide
theorem tmFiber76Parent_47_ok : tmFiber76ParentCheck 47 = true := by decide
theorem tmFiber76Parent_48_ok : tmFiber76ParentCheck 48 = true := by decide
theorem tmFiber76Parent_49_ok : tmFiber76ParentCheck 49 = true := by decide
theorem tmFiber76Parent_50_ok : tmFiber76ParentCheck 50 = true := by decide
theorem tmFiber76Parent_51_ok : tmFiber76ParentCheck 51 = true := by decide
theorem tmFiber76Parent_52_ok : tmFiber76ParentCheck 52 = true := by decide
theorem tmFiber76Parent_53_ok : tmFiber76ParentCheck 53 = true := by decide
theorem tmFiber76Parent_54_ok : tmFiber76ParentCheck 54 = true := by decide
theorem tmFiber76Parent_55_ok : tmFiber76ParentCheck 55 = true := by decide
theorem tmFiber76Parent_56_ok : tmFiber76ParentCheck 56 = true := by decide
theorem tmFiber76Parent_57_ok : tmFiber76ParentCheck 57 = true := by decide
theorem tmFiber76Parent_58_ok : tmFiber76ParentCheck 58 = true := by decide
theorem tmFiber76Parent_59_ok : tmFiber76ParentCheck 59 = true := by decide
theorem tmFiber76Parent_60_ok : tmFiber76ParentCheck 60 = true := by decide
theorem tmFiber76Parent_61_ok : tmFiber76ParentCheck 61 = true := by decide
theorem tmFiber76Parent_62_ok : tmFiber76ParentCheck 62 = true := by decide
theorem tmFiber76Parent_63_ok : tmFiber76ParentCheck 63 = true := by decide

def tmFiber76CertificateAudit : Bool :=
  tmFiber76SourcesCheck &&
    tmFiber76RowCheck 0 &&
    tmFiber76RowCheck 1 &&
    tmFiber76RowCheck 2 &&
    tmFiber76RowCheck 3 &&
    tmFiber76RowCheck 4 &&
    tmFiber76RowCheck 5 &&
    tmFiber76RowCheck 6 &&
    tmFiber76RowCheck 7 &&
    tmFiber76RowCheck 8 &&
    tmFiber76RowCheck 9 &&
    tmFiber76RowCheck 10 &&
    tmFiber76RowCheck 11 &&
    tmFiber76RowCheck 12 &&
    tmFiber76RowCheck 13 &&
    tmFiber76RowCheck 14 &&
    tmFiber76RowCheck 15 &&
    tmFiber76RowCheck 16 &&
    tmFiber76RowCheck 17 &&
    tmFiber76RowCheck 18 &&
    tmFiber76RowCheck 19 &&
    tmFiber76RowCheck 20 &&
    tmFiber76RowCheck 21 &&
    tmFiber76RowCheck 22 &&
    tmFiber76RowCheck 23 &&
    tmFiber76RowCheck 24 &&
    tmFiber76RowCheck 25 &&
    tmFiber76RowCheck 26 &&
    tmFiber76RowCheck 27 &&
    tmFiber76RowCheck 28 &&
    tmFiber76RowCheck 29 &&
    tmFiber76RowCheck 30 &&
    tmFiber76RowCheck 31 &&
    tmFiber76RowCheck 32 &&
    tmFiber76RowCheck 33 &&
    tmFiber76RowCheck 34 &&
    tmFiber76RowCheck 35 &&
    tmFiber76RowCheck 36 &&
    tmFiber76RowCheck 37 &&
    tmFiber76RowCheck 38 &&
    tmFiber76RowCheck 39 &&
    tmFiber76RowCheck 40 &&
    tmFiber76RowCheck 41 &&
    tmFiber76RowCheck 42 &&
    tmFiber76RowCheck 43 &&
    tmFiber76RowCheck 44 &&
    tmFiber76RowCheck 45 &&
    tmFiber76RowCheck 46 &&
    tmFiber76RowCheck 47 &&
    tmFiber76RowCheck 48 &&
    tmFiber76RowCheck 49 &&
    tmFiber76RowCheck 50 &&
    tmFiber76RowCheck 51 &&
    tmFiber76RowCheck 52 &&
    tmFiber76RowCheck 53 &&
    tmFiber76RowCheck 54 &&
    tmFiber76RowCheck 55 &&
    tmFiber76RowCheck 56 &&
    tmFiber76RowCheck 57 &&
    tmFiber76RowCheck 58 &&
    tmFiber76RowCheck 59 &&
    tmFiber76RowCheck 60 &&
    tmFiber76RowCheck 61 &&
    tmFiber76RowCheck 62 &&
    tmFiber76RowCheck 63 &&
    tmFiber76ParentCheck 0 &&
    tmFiber76ParentCheck 1 &&
    tmFiber76ParentCheck 2 &&
    tmFiber76ParentCheck 3 &&
    tmFiber76ParentCheck 4 &&
    tmFiber76ParentCheck 5 &&
    tmFiber76ParentCheck 6 &&
    tmFiber76ParentCheck 7 &&
    tmFiber76ParentCheck 8 &&
    tmFiber76ParentCheck 9 &&
    tmFiber76ParentCheck 10 &&
    tmFiber76ParentCheck 11 &&
    tmFiber76ParentCheck 12 &&
    tmFiber76ParentCheck 13 &&
    tmFiber76ParentCheck 14 &&
    tmFiber76ParentCheck 15 &&
    tmFiber76ParentCheck 16 &&
    tmFiber76ParentCheck 17 &&
    tmFiber76ParentCheck 18 &&
    tmFiber76ParentCheck 19 &&
    tmFiber76ParentCheck 20 &&
    tmFiber76ParentCheck 21 &&
    tmFiber76ParentCheck 22 &&
    tmFiber76ParentCheck 23 &&
    tmFiber76ParentCheck 24 &&
    tmFiber76ParentCheck 25 &&
    tmFiber76ParentCheck 26 &&
    tmFiber76ParentCheck 27 &&
    tmFiber76ParentCheck 28 &&
    tmFiber76ParentCheck 29 &&
    tmFiber76ParentCheck 30 &&
    tmFiber76ParentCheck 31 &&
    tmFiber76ParentCheck 32 &&
    tmFiber76ParentCheck 33 &&
    tmFiber76ParentCheck 34 &&
    tmFiber76ParentCheck 35 &&
    tmFiber76ParentCheck 36 &&
    tmFiber76ParentCheck 37 &&
    tmFiber76ParentCheck 38 &&
    tmFiber76ParentCheck 39 &&
    tmFiber76ParentCheck 40 &&
    tmFiber76ParentCheck 41 &&
    tmFiber76ParentCheck 42 &&
    tmFiber76ParentCheck 43 &&
    tmFiber76ParentCheck 44 &&
    tmFiber76ParentCheck 45 &&
    tmFiber76ParentCheck 46 &&
    tmFiber76ParentCheck 47 &&
    tmFiber76ParentCheck 48 &&
    tmFiber76ParentCheck 49 &&
    tmFiber76ParentCheck 50 &&
    tmFiber76ParentCheck 51 &&
    tmFiber76ParentCheck 52 &&
    tmFiber76ParentCheck 53 &&
    tmFiber76ParentCheck 54 &&
    tmFiber76ParentCheck 55 &&
    tmFiber76ParentCheck 56 &&
    tmFiber76ParentCheck 57 &&
    tmFiber76ParentCheck 58 &&
    tmFiber76ParentCheck 59 &&
    tmFiber76ParentCheck 60 &&
    tmFiber76ParentCheck 61 &&
    tmFiber76ParentCheck 62 &&
    tmFiber76ParentCheck 63

theorem tmFiber76CertificateAudit_ok :
    tmFiber76CertificateAudit = true := by
  simp [tmFiber76CertificateAudit,
    tmFiber76SourcesCheck_ok,
    tmFiber76Row_0_ok,
    tmFiber76Row_1_ok,
    tmFiber76Row_2_ok,
    tmFiber76Row_3_ok,
    tmFiber76Row_4_ok,
    tmFiber76Row_5_ok,
    tmFiber76Row_6_ok,
    tmFiber76Row_7_ok,
    tmFiber76Row_8_ok,
    tmFiber76Row_9_ok,
    tmFiber76Row_10_ok,
    tmFiber76Row_11_ok,
    tmFiber76Row_12_ok,
    tmFiber76Row_13_ok,
    tmFiber76Row_14_ok,
    tmFiber76Row_15_ok,
    tmFiber76Row_16_ok,
    tmFiber76Row_17_ok,
    tmFiber76Row_18_ok,
    tmFiber76Row_19_ok,
    tmFiber76Row_20_ok,
    tmFiber76Row_21_ok,
    tmFiber76Row_22_ok,
    tmFiber76Row_23_ok,
    tmFiber76Row_24_ok,
    tmFiber76Row_25_ok,
    tmFiber76Row_26_ok,
    tmFiber76Row_27_ok,
    tmFiber76Row_28_ok,
    tmFiber76Row_29_ok,
    tmFiber76Row_30_ok,
    tmFiber76Row_31_ok,
    tmFiber76Row_32_ok,
    tmFiber76Row_33_ok,
    tmFiber76Row_34_ok,
    tmFiber76Row_35_ok,
    tmFiber76Row_36_ok,
    tmFiber76Row_37_ok,
    tmFiber76Row_38_ok,
    tmFiber76Row_39_ok,
    tmFiber76Row_40_ok,
    tmFiber76Row_41_ok,
    tmFiber76Row_42_ok,
    tmFiber76Row_43_ok,
    tmFiber76Row_44_ok,
    tmFiber76Row_45_ok,
    tmFiber76Row_46_ok,
    tmFiber76Row_47_ok,
    tmFiber76Row_48_ok,
    tmFiber76Row_49_ok,
    tmFiber76Row_50_ok,
    tmFiber76Row_51_ok,
    tmFiber76Row_52_ok,
    tmFiber76Row_53_ok,
    tmFiber76Row_54_ok,
    tmFiber76Row_55_ok,
    tmFiber76Row_56_ok,
    tmFiber76Row_57_ok,
    tmFiber76Row_58_ok,
    tmFiber76Row_59_ok,
    tmFiber76Row_60_ok,
    tmFiber76Row_61_ok,
    tmFiber76Row_62_ok,
    tmFiber76Row_63_ok,
    tmFiber76Parent_0_ok,
    tmFiber76Parent_1_ok,
    tmFiber76Parent_2_ok,
    tmFiber76Parent_3_ok,
    tmFiber76Parent_4_ok,
    tmFiber76Parent_5_ok,
    tmFiber76Parent_6_ok,
    tmFiber76Parent_7_ok,
    tmFiber76Parent_8_ok,
    tmFiber76Parent_9_ok,
    tmFiber76Parent_10_ok,
    tmFiber76Parent_11_ok,
    tmFiber76Parent_12_ok,
    tmFiber76Parent_13_ok,
    tmFiber76Parent_14_ok,
    tmFiber76Parent_15_ok,
    tmFiber76Parent_16_ok,
    tmFiber76Parent_17_ok,
    tmFiber76Parent_18_ok,
    tmFiber76Parent_19_ok,
    tmFiber76Parent_20_ok,
    tmFiber76Parent_21_ok,
    tmFiber76Parent_22_ok,
    tmFiber76Parent_23_ok,
    tmFiber76Parent_24_ok,
    tmFiber76Parent_25_ok,
    tmFiber76Parent_26_ok,
    tmFiber76Parent_27_ok,
    tmFiber76Parent_28_ok,
    tmFiber76Parent_29_ok,
    tmFiber76Parent_30_ok,
    tmFiber76Parent_31_ok,
    tmFiber76Parent_32_ok,
    tmFiber76Parent_33_ok,
    tmFiber76Parent_34_ok,
    tmFiber76Parent_35_ok,
    tmFiber76Parent_36_ok,
    tmFiber76Parent_37_ok,
    tmFiber76Parent_38_ok,
    tmFiber76Parent_39_ok,
    tmFiber76Parent_40_ok,
    tmFiber76Parent_41_ok,
    tmFiber76Parent_42_ok,
    tmFiber76Parent_43_ok,
    tmFiber76Parent_44_ok,
    tmFiber76Parent_45_ok,
    tmFiber76Parent_46_ok,
    tmFiber76Parent_47_ok,
    tmFiber76Parent_48_ok,
    tmFiber76Parent_49_ok,
    tmFiber76Parent_50_ok,
    tmFiber76Parent_51_ok,
    tmFiber76Parent_52_ok,
    tmFiber76Parent_53_ok,
    tmFiber76Parent_54_ok,
    tmFiber76Parent_55_ok,
    tmFiber76Parent_56_ok,
    tmFiber76Parent_57_ok,
    tmFiber76Parent_58_ok,
    tmFiber76Parent_59_ok,
    tmFiber76Parent_60_ok,
    tmFiber76Parent_61_ok,
    tmFiber76Parent_62_ok,
    tmFiber76Parent_63_ok]

def tmFiber77Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.p]

def tmFiber77Expected : List Nat :=
  [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]

def tmFiber77Rows : List DirectChainParentRow :=
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

def tmFiber77RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber77Rows i default

def tmFiber77SourcesCheck : Bool :=
  (tmFiber77Rows.map fun row => row.source) == tmFiber77Expected

theorem tmFiber77SourcesCheck_ok :
    tmFiber77SourcesCheck = true := by
  decide

def tmFiber77RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt i)

theorem tmFiber77Row_0_ok : tmFiber77RowCheck 0 = true := by decide
theorem tmFiber77Row_1_ok : tmFiber77RowCheck 1 = true := by decide
theorem tmFiber77Row_2_ok : tmFiber77RowCheck 2 = true := by decide
theorem tmFiber77Row_3_ok : tmFiber77RowCheck 3 = true := by decide
theorem tmFiber77Row_4_ok : tmFiber77RowCheck 4 = true := by decide
theorem tmFiber77Row_5_ok : tmFiber77RowCheck 5 = true := by decide
theorem tmFiber77Row_6_ok : tmFiber77RowCheck 6 = true := by decide
theorem tmFiber77Row_7_ok : tmFiber77RowCheck 7 = true := by decide
theorem tmFiber77Row_8_ok : tmFiber77RowCheck 8 = true := by decide
theorem tmFiber77Row_9_ok : tmFiber77RowCheck 9 = true := by decide
theorem tmFiber77Row_10_ok : tmFiber77RowCheck 10 = true := by decide
theorem tmFiber77Row_11_ok : tmFiber77RowCheck 11 = true := by decide
theorem tmFiber77Row_12_ok : tmFiber77RowCheck 12 = true := by decide
theorem tmFiber77Row_13_ok : tmFiber77RowCheck 13 = true := by decide
theorem tmFiber77Row_14_ok : tmFiber77RowCheck 14 = true := by decide
theorem tmFiber77Row_15_ok : tmFiber77RowCheck 15 = true := by decide

def tmFiber77ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber77Rows tmMaxParentDepth (listGetD tmFiber77Expected i 0) == 560

theorem tmFiber77Parent_0_ok : tmFiber77ParentCheck 0 = true := by decide
theorem tmFiber77Parent_1_ok : tmFiber77ParentCheck 1 = true := by decide
theorem tmFiber77Parent_2_ok : tmFiber77ParentCheck 2 = true := by decide
theorem tmFiber77Parent_3_ok : tmFiber77ParentCheck 3 = true := by decide
theorem tmFiber77Parent_4_ok : tmFiber77ParentCheck 4 = true := by decide
theorem tmFiber77Parent_5_ok : tmFiber77ParentCheck 5 = true := by decide
theorem tmFiber77Parent_6_ok : tmFiber77ParentCheck 6 = true := by decide
theorem tmFiber77Parent_7_ok : tmFiber77ParentCheck 7 = true := by decide
theorem tmFiber77Parent_8_ok : tmFiber77ParentCheck 8 = true := by decide
theorem tmFiber77Parent_9_ok : tmFiber77ParentCheck 9 = true := by decide
theorem tmFiber77Parent_10_ok : tmFiber77ParentCheck 10 = true := by decide
theorem tmFiber77Parent_11_ok : tmFiber77ParentCheck 11 = true := by decide
theorem tmFiber77Parent_12_ok : tmFiber77ParentCheck 12 = true := by decide
theorem tmFiber77Parent_13_ok : tmFiber77ParentCheck 13 = true := by decide
theorem tmFiber77Parent_14_ok : tmFiber77ParentCheck 14 = true := by decide
theorem tmFiber77Parent_15_ok : tmFiber77ParentCheck 15 = true := by decide

def tmFiber77CertificateAudit : Bool :=
  tmFiber77SourcesCheck &&
    tmFiber77RowCheck 0 &&
    tmFiber77RowCheck 1 &&
    tmFiber77RowCheck 2 &&
    tmFiber77RowCheck 3 &&
    tmFiber77RowCheck 4 &&
    tmFiber77RowCheck 5 &&
    tmFiber77RowCheck 6 &&
    tmFiber77RowCheck 7 &&
    tmFiber77RowCheck 8 &&
    tmFiber77RowCheck 9 &&
    tmFiber77RowCheck 10 &&
    tmFiber77RowCheck 11 &&
    tmFiber77RowCheck 12 &&
    tmFiber77RowCheck 13 &&
    tmFiber77RowCheck 14 &&
    tmFiber77RowCheck 15 &&
    tmFiber77ParentCheck 0 &&
    tmFiber77ParentCheck 1 &&
    tmFiber77ParentCheck 2 &&
    tmFiber77ParentCheck 3 &&
    tmFiber77ParentCheck 4 &&
    tmFiber77ParentCheck 5 &&
    tmFiber77ParentCheck 6 &&
    tmFiber77ParentCheck 7 &&
    tmFiber77ParentCheck 8 &&
    tmFiber77ParentCheck 9 &&
    tmFiber77ParentCheck 10 &&
    tmFiber77ParentCheck 11 &&
    tmFiber77ParentCheck 12 &&
    tmFiber77ParentCheck 13 &&
    tmFiber77ParentCheck 14 &&
    tmFiber77ParentCheck 15

theorem tmFiber77CertificateAudit_ok :
    tmFiber77CertificateAudit = true := by
  simp [tmFiber77CertificateAudit,
    tmFiber77SourcesCheck_ok,
    tmFiber77Row_0_ok,
    tmFiber77Row_1_ok,
    tmFiber77Row_2_ok,
    tmFiber77Row_3_ok,
    tmFiber77Row_4_ok,
    tmFiber77Row_5_ok,
    tmFiber77Row_6_ok,
    tmFiber77Row_7_ok,
    tmFiber77Row_8_ok,
    tmFiber77Row_9_ok,
    tmFiber77Row_10_ok,
    tmFiber77Row_11_ok,
    tmFiber77Row_12_ok,
    tmFiber77Row_13_ok,
    tmFiber77Row_14_ok,
    tmFiber77Row_15_ok,
    tmFiber77Parent_0_ok,
    tmFiber77Parent_1_ok,
    tmFiber77Parent_2_ok,
    tmFiber77Parent_3_ok,
    tmFiber77Parent_4_ok,
    tmFiber77Parent_5_ok,
    tmFiber77Parent_6_ok,
    tmFiber77Parent_7_ok,
    tmFiber77Parent_8_ok,
    tmFiber77Parent_9_ok,
    tmFiber77Parent_10_ok,
    tmFiber77Parent_11_ok,
    tmFiber77Parent_12_ok,
    tmFiber77Parent_13_ok,
    tmFiber77Parent_14_ok,
    tmFiber77Parent_15_ok]

def tmFiber78Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.r]

def tmFiber78Expected : List Nat :=
  []

def tmFiber78Rows : List DirectChainParentRow :=
  []

def tmFiber78RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber78Rows i default

def tmFiber78SourcesCheck : Bool :=
  (tmFiber78Rows.map fun row => row.source) == tmFiber78Expected

theorem tmFiber78SourcesCheck_ok :
    tmFiber78SourcesCheck = true := by
  decide

def tmFiber78RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber78Key tmFiber78Expected (tmFiber78RowAt i)

def tmFiber78ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber78Rows tmMaxParentDepth (listGetD tmFiber78Expected i 0) == 0

def tmFiber78CertificateAudit : Bool :=
  tmFiber78SourcesCheck

theorem tmFiber78CertificateAudit_ok :
    tmFiber78CertificateAudit = true := by
  simp [tmFiber78CertificateAudit,
    tmFiber78SourcesCheck_ok]

def tmFiber79Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.b]

def tmFiber79Expected : List Nat :=
  []

def tmFiber79Rows : List DirectChainParentRow :=
  []

def tmFiber79RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber79Rows i default

def tmFiber79SourcesCheck : Bool :=
  (tmFiber79Rows.map fun row => row.source) == tmFiber79Expected

theorem tmFiber79SourcesCheck_ok :
    tmFiber79SourcesCheck = true := by
  decide

def tmFiber79RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber79Key tmFiber79Expected (tmFiber79RowAt i)

def tmFiber79ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber79Rows tmMaxParentDepth (listGetD tmFiber79Expected i 0) == 0

def tmFiber79CertificateAudit : Bool :=
  tmFiber79SourcesCheck

theorem tmFiber79CertificateAudit_ok :
    tmFiber79CertificateAudit = true := by
  simp [tmFiber79CertificateAudit,
    tmFiber79SourcesCheck_ok]

def tmFiber80Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.p]

def tmFiber80Expected : List Nat :=
  []

def tmFiber80Rows : List DirectChainParentRow :=
  []

def tmFiber80RowAt (i : Nat) : DirectChainParentRow :=
  listGetD tmFiber80Rows i default

def tmFiber80SourcesCheck : Bool :=
  (tmFiber80Rows.map fun row => row.source) == tmFiber80Expected

theorem tmFiber80SourcesCheck_ok :
    tmFiber80SourcesCheck = true := by
  decide

def tmFiber80RowCheck (i : Nat) : Bool :=
  tmRowValid tmFiber80Key tmFiber80Expected (tmFiber80RowAt i)

def tmFiber80ParentCheck (i : Nat) : Bool :=
  directParentIter tmFiber80Rows tmMaxParentDepth (listGetD tmFiber80Expected i 0) == 0

def tmFiber80CertificateAudit : Bool :=
  tmFiber80SourcesCheck

theorem tmFiber80CertificateAudit_ok :
    tmFiber80CertificateAudit = true := by
  simp [tmFiber80CertificateAudit,
    tmFiber80SourcesCheck_ok]

def tmAllFiberCertificateAudit : Bool :=
  tmFiber0CertificateAudit &&
    tmFiber1CertificateAudit &&
    tmFiber2CertificateAudit &&
    tmFiber3CertificateAudit &&
    tmFiber4CertificateAudit &&
    tmFiber5CertificateAudit &&
    tmFiber6CertificateAudit &&
    tmFiber7CertificateAudit &&
    tmFiber8CertificateAudit &&
    tmFiber9CertificateAudit &&
    tmFiber10CertificateAudit &&
    tmFiber11CertificateAudit &&
    tmFiber12CertificateAudit &&
    tmFiber13CertificateAudit &&
    tmFiber14CertificateAudit &&
    tmFiber15CertificateAudit &&
    tmFiber16CertificateAudit &&
    tmFiber17CertificateAudit &&
    tmFiber18CertificateAudit &&
    tmFiber19CertificateAudit &&
    tmFiber20CertificateAudit &&
    tmFiber21CertificateAudit &&
    tmFiber22CertificateAudit &&
    tmFiber23CertificateAudit &&
    tmFiber24CertificateAudit &&
    tmFiber25CertificateAudit &&
    tmFiber26CertificateAudit &&
    tmFiber27CertificateAudit &&
    tmFiber28CertificateAudit &&
    tmFiber29CertificateAudit &&
    tmFiber30CertificateAudit &&
    tmFiber31CertificateAudit &&
    tmFiber32CertificateAudit &&
    tmFiber33CertificateAudit &&
    tmFiber34CertificateAudit &&
    tmFiber35CertificateAudit &&
    tmFiber36CertificateAudit &&
    tmFiber37CertificateAudit &&
    tmFiber38CertificateAudit &&
    tmFiber39CertificateAudit &&
    tmFiber40CertificateAudit &&
    tmFiber41CertificateAudit &&
    tmFiber42CertificateAudit &&
    tmFiber43CertificateAudit &&
    tmFiber44CertificateAudit &&
    tmFiber45CertificateAudit &&
    tmFiber46CertificateAudit &&
    tmFiber47CertificateAudit &&
    tmFiber48CertificateAudit &&
    tmFiber49CertificateAudit &&
    tmFiber50CertificateAudit &&
    tmFiber51CertificateAudit &&
    tmFiber52CertificateAudit &&
    tmFiber53CertificateAudit &&
    tmFiber54CertificateAudit &&
    tmFiber55CertificateAudit &&
    tmFiber56CertificateAudit &&
    tmFiber57CertificateAudit &&
    tmFiber58CertificateAudit &&
    tmFiber59CertificateAudit &&
    tmFiber60CertificateAudit &&
    tmFiber61CertificateAudit &&
    tmFiber62CertificateAudit &&
    tmFiber63CertificateAudit &&
    tmFiber64CertificateAudit &&
    tmFiber65CertificateAudit &&
    tmFiber66CertificateAudit &&
    tmFiber67CertificateAudit &&
    tmFiber68CertificateAudit &&
    tmFiber69CertificateAudit &&
    tmFiber70CertificateAudit &&
    tmFiber71CertificateAudit &&
    tmFiber72CertificateAudit &&
    tmFiber73CertificateAudit &&
    tmFiber74CertificateAudit &&
    tmFiber75CertificateAudit &&
    tmFiber76CertificateAudit &&
    tmFiber77CertificateAudit &&
    tmFiber78CertificateAudit &&
    tmFiber79CertificateAudit &&
    tmFiber80CertificateAudit

theorem tmAllFiberCertificateAudit_ok :
    tmAllFiberCertificateAudit = true := by
  simp [tmAllFiberCertificateAudit,
    tmFiber0CertificateAudit_ok,
    tmFiber1CertificateAudit_ok,
    tmFiber2CertificateAudit_ok,
    tmFiber3CertificateAudit_ok,
    tmFiber4CertificateAudit_ok,
    tmFiber5CertificateAudit_ok,
    tmFiber6CertificateAudit_ok,
    tmFiber7CertificateAudit_ok,
    tmFiber8CertificateAudit_ok,
    tmFiber9CertificateAudit_ok,
    tmFiber10CertificateAudit_ok,
    tmFiber11CertificateAudit_ok,
    tmFiber12CertificateAudit_ok,
    tmFiber13CertificateAudit_ok,
    tmFiber14CertificateAudit_ok,
    tmFiber15CertificateAudit_ok,
    tmFiber16CertificateAudit_ok,
    tmFiber17CertificateAudit_ok,
    tmFiber18CertificateAudit_ok,
    tmFiber19CertificateAudit_ok,
    tmFiber20CertificateAudit_ok,
    tmFiber21CertificateAudit_ok,
    tmFiber22CertificateAudit_ok,
    tmFiber23CertificateAudit_ok,
    tmFiber24CertificateAudit_ok,
    tmFiber25CertificateAudit_ok,
    tmFiber26CertificateAudit_ok,
    tmFiber27CertificateAudit_ok,
    tmFiber28CertificateAudit_ok,
    tmFiber29CertificateAudit_ok,
    tmFiber30CertificateAudit_ok,
    tmFiber31CertificateAudit_ok,
    tmFiber32CertificateAudit_ok,
    tmFiber33CertificateAudit_ok,
    tmFiber34CertificateAudit_ok,
    tmFiber35CertificateAudit_ok,
    tmFiber36CertificateAudit_ok,
    tmFiber37CertificateAudit_ok,
    tmFiber38CertificateAudit_ok,
    tmFiber39CertificateAudit_ok,
    tmFiber40CertificateAudit_ok,
    tmFiber41CertificateAudit_ok,
    tmFiber42CertificateAudit_ok,
    tmFiber43CertificateAudit_ok,
    tmFiber44CertificateAudit_ok,
    tmFiber45CertificateAudit_ok,
    tmFiber46CertificateAudit_ok,
    tmFiber47CertificateAudit_ok,
    tmFiber48CertificateAudit_ok,
    tmFiber49CertificateAudit_ok,
    tmFiber50CertificateAudit_ok,
    tmFiber51CertificateAudit_ok,
    tmFiber52CertificateAudit_ok,
    tmFiber53CertificateAudit_ok,
    tmFiber54CertificateAudit_ok,
    tmFiber55CertificateAudit_ok,
    tmFiber56CertificateAudit_ok,
    tmFiber57CertificateAudit_ok,
    tmFiber58CertificateAudit_ok,
    tmFiber59CertificateAudit_ok,
    tmFiber60CertificateAudit_ok,
    tmFiber61CertificateAudit_ok,
    tmFiber62CertificateAudit_ok,
    tmFiber63CertificateAudit_ok,
    tmFiber64CertificateAudit_ok,
    tmFiber65CertificateAudit_ok,
    tmFiber66CertificateAudit_ok,
    tmFiber67CertificateAudit_ok,
    tmFiber68CertificateAudit_ok,
    tmFiber69CertificateAudit_ok,
    tmFiber70CertificateAudit_ok,
    tmFiber71CertificateAudit_ok,
    tmFiber72CertificateAudit_ok,
    tmFiber73CertificateAudit_ok,
    tmFiber74CertificateAudit_ok,
    tmFiber75CertificateAudit_ok,
    tmFiber76CertificateAudit_ok,
    tmFiber77CertificateAudit_ok,
    tmFiber78CertificateAudit_ok,
    tmFiber79CertificateAudit_ok,
    tmFiber80CertificateAudit_ok]

end GoertzelLemma818TauMirrorCertificate

end Mettapedia.GraphTheory.FourColor
