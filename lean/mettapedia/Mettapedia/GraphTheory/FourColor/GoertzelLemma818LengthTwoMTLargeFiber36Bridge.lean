import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 36

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber36StateAt (i : Nat) : List TauState :=
  directStates (mtFiber36RowAt i).sourceLeft (mtFiber36RowAt i).sourceRight

def mtFiber36DirectStates : List (List TauState) :=
  [mtFiber36StateAt 0, mtFiber36StateAt 1, mtFiber36StateAt 2, mtFiber36StateAt 3, mtFiber36StateAt 4, mtFiber36StateAt 5, mtFiber36StateAt 6, mtFiber36StateAt 7, mtFiber36StateAt 8, mtFiber36StateAt 9, mtFiber36StateAt 10, mtFiber36StateAt 11, mtFiber36StateAt 12, mtFiber36StateAt 13, mtFiber36StateAt 14, mtFiber36StateAt 15, mtFiber36StateAt 16, mtFiber36StateAt 17, mtFiber36StateAt 18, mtFiber36StateAt 19, mtFiber36StateAt 20, mtFiber36StateAt 21, mtFiber36StateAt 22, mtFiber36StateAt 23, mtFiber36StateAt 24, mtFiber36StateAt 25, mtFiber36StateAt 26, mtFiber36StateAt 27, mtFiber36StateAt 28, mtFiber36StateAt 29, mtFiber36StateAt 30, mtFiber36StateAt 31, mtFiber36StateAt 32, mtFiber36StateAt 33, mtFiber36StateAt 34, mtFiber36StateAt 35, mtFiber36StateAt 36, mtFiber36StateAt 37, mtFiber36StateAt 38, mtFiber36StateAt 39, mtFiber36StateAt 40, mtFiber36StateAt 41, mtFiber36StateAt 42, mtFiber36StateAt 43, mtFiber36StateAt 44, mtFiber36StateAt 45, mtFiber36StateAt 46, mtFiber36StateAt 47, mtFiber36StateAt 48, mtFiber36StateAt 49, mtFiber36StateAt 50, mtFiber36StateAt 51, mtFiber36StateAt 52, mtFiber36StateAt 53, mtFiber36StateAt 54, mtFiber36StateAt 55, mtFiber36StateAt 56, mtFiber36StateAt 57, mtFiber36StateAt 58, mtFiber36StateAt 59, mtFiber36StateAt 60, mtFiber36StateAt 61, mtFiber36StateAt 62, mtFiber36StateAt 63]

theorem mtFiber36ReverseRow_1_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk0_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 0) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 1)
    (mtFiber36RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 1) (by decide) mtFiber36ReverseRow_1_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_2_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk1_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 2) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 2)
    (mtFiber36RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 2) (by decide) mtFiber36ReverseRow_2_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_3_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk1_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 2) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 3)
    (mtFiber36RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 3) (by decide) mtFiber36ReverseRow_3_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_4_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk2_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 4) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 4)
    (mtFiber36RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 4) (by decide) mtFiber36ReverseRow_4_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_5_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk2_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 4) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 5)
    (mtFiber36RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 5) (by decide) mtFiber36ReverseRow_5_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_6_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk3_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 6) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 6)
    (mtFiber36RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 6) (by decide) mtFiber36ReverseRow_6_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_7_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk3_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 6) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 7)
    (mtFiber36RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 7) (by decide) mtFiber36ReverseRow_7_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_8_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk4_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 8) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 8)
    (mtFiber36RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 8) (by decide) mtFiber36ReverseRow_8_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_9_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk4_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 8) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 9)
    (mtFiber36RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 9) (by decide) mtFiber36ReverseRow_9_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_10_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk5_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 10) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 2) (mtFiber36StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 2) (mtFiber36StateAt 10)
    (mtFiber36RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 10) (by decide) mtFiber36ReverseRow_10_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_11_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk5_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 10) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 11)
    (mtFiber36RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 11) (by decide) mtFiber36ReverseRow_11_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_12_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk6_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 12) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 12)
    (mtFiber36RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 12) (by decide) mtFiber36ReverseRow_12_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_13_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk6_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 12) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 5) (mtFiber36StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 5) (mtFiber36StateAt 13)
    (mtFiber36RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 13) (by decide) mtFiber36ReverseRow_13_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_14_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk7_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 14) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 6) (mtFiber36StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 6) (mtFiber36StateAt 14)
    (mtFiber36RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 14) (by decide) mtFiber36ReverseRow_14_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_15_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk7_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 14) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 7) (mtFiber36StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 7) (mtFiber36StateAt 15)
    (mtFiber36RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 15) (by decide) mtFiber36ReverseRow_15_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_16_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk8_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 16) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 16)
    (mtFiber36RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 16) (by decide) mtFiber36ReverseRow_16_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_17_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk8_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 16) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 17)
    (mtFiber36RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 17) (by decide) mtFiber36ReverseRow_17_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_18_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk9_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 18) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 2) (mtFiber36StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 2) (mtFiber36StateAt 18)
    (mtFiber36RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 18) (by decide) mtFiber36ReverseRow_18_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_19_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk9_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 18) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 19)
    (mtFiber36RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 19) (by decide) mtFiber36ReverseRow_19_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_20_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk10_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 20) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 20)
    (mtFiber36RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 20) (by decide) mtFiber36ReverseRow_20_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_21_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk10_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 20) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 5) (mtFiber36StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 5) (mtFiber36StateAt 21)
    (mtFiber36RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 21) (by decide) mtFiber36ReverseRow_21_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_22_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk11_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 22) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 6) (mtFiber36StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 6) (mtFiber36StateAt 22)
    (mtFiber36RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 22) (by decide) mtFiber36ReverseRow_22_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_23_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk11_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 22) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 7) (mtFiber36StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 7) (mtFiber36StateAt 23)
    (mtFiber36RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 23) (by decide) mtFiber36ReverseRow_23_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_24_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk12_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 24) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 8) (mtFiber36StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 8) (mtFiber36StateAt 24)
    (mtFiber36RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 24) (by decide) mtFiber36ReverseRow_24_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_25_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk12_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 24) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 9) (mtFiber36StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 9) (mtFiber36StateAt 25)
    (mtFiber36RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 25) (by decide) mtFiber36ReverseRow_25_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_26_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk13_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 26) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 10) (mtFiber36StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 10) (mtFiber36StateAt 26)
    (mtFiber36RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 26) (by decide) mtFiber36ReverseRow_26_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_27_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk13_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 26) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 11) (mtFiber36StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 11) (mtFiber36StateAt 27)
    (mtFiber36RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 27) (by decide) mtFiber36ReverseRow_27_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_28_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk14_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 28) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 12) (mtFiber36StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 12) (mtFiber36StateAt 28)
    (mtFiber36RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 28) (by decide) mtFiber36ReverseRow_28_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_29_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk14_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 28) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 13) (mtFiber36StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 13) (mtFiber36StateAt 29)
    (mtFiber36RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 29) (by decide) mtFiber36ReverseRow_29_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_30_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk15_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 30) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 14) (mtFiber36StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 14) (mtFiber36StateAt 30)
    (mtFiber36RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 30) (by decide) mtFiber36ReverseRow_30_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_31_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk15_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 30) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 15) (mtFiber36StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 15) (mtFiber36StateAt 31)
    (mtFiber36RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 31) (by decide) mtFiber36ReverseRow_31_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_32_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk16_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 32) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 36) (mtFiber36StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 36) (mtFiber36StateAt 32)
    (mtFiber36RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 32) (by decide) mtFiber36ReverseRow_32_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_33_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk16_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 32) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 37) (mtFiber36StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 37) (mtFiber36StateAt 33)
    (mtFiber36RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 33) (by decide) mtFiber36ReverseRow_33_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_34_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk17_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 34) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 20) (mtFiber36StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 20) (mtFiber36StateAt 34)
    (mtFiber36RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 34) (by decide) mtFiber36ReverseRow_34_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_35_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk17_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 34) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 21) (mtFiber36StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 21) (mtFiber36StateAt 35)
    (mtFiber36RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 35) (by decide) mtFiber36ReverseRow_35_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_36_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk18_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 36) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 16) (mtFiber36StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 16) (mtFiber36StateAt 36)
    (mtFiber36RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 36) (by decide) mtFiber36ReverseRow_36_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_37_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk18_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 36) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 17) (mtFiber36StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 17) (mtFiber36StateAt 37)
    (mtFiber36RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 37) (by decide) mtFiber36ReverseRow_37_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_38_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk19_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 38) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 18) (mtFiber36StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 18) (mtFiber36StateAt 38)
    (mtFiber36RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 38) (by decide) mtFiber36ReverseRow_38_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_39_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk19_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 38) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 19) (mtFiber36StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 19) (mtFiber36StateAt 39)
    (mtFiber36RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 39) (by decide) mtFiber36ReverseRow_39_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_40_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk20_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 40) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 44) (mtFiber36StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 44) (mtFiber36StateAt 40)
    (mtFiber36RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 40) (by decide) mtFiber36ReverseRow_40_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_41_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk20_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 40) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 45) (mtFiber36StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 45) (mtFiber36StateAt 41)
    (mtFiber36RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 41) (by decide) mtFiber36ReverseRow_41_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_42_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk21_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 42) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 58) (mtFiber36StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 58) (mtFiber36StateAt 42)
    (mtFiber36RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 42) (by decide) mtFiber36ReverseRow_42_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_43_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk21_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 42) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 59) (mtFiber36StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 59) (mtFiber36StateAt 43)
    (mtFiber36RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 43) (by decide) mtFiber36ReverseRow_43_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_44_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk22_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 44) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 60) (mtFiber36StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 60) (mtFiber36StateAt 44)
    (mtFiber36RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 44) (by decide) mtFiber36ReverseRow_44_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_45_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk22_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 44) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 61) (mtFiber36StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 61) (mtFiber36StateAt 45)
    (mtFiber36RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 45) (by decide) mtFiber36ReverseRow_45_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_46_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk23_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 46) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 62) (mtFiber36StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 62) (mtFiber36StateAt 46)
    (mtFiber36RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 46) (by decide) mtFiber36ReverseRow_46_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_47_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk23_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 46) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 63) (mtFiber36StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 63) (mtFiber36StateAt 47)
    (mtFiber36RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 47) (by decide) mtFiber36ReverseRow_47_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_48_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk24_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 48) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 52) (mtFiber36StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 52) (mtFiber36StateAt 48)
    (mtFiber36RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 48) (by decide) mtFiber36ReverseRow_48_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_49_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk24_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 48) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 53) (mtFiber36StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 53) (mtFiber36StateAt 49)
    (mtFiber36RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 49) (by decide) mtFiber36ReverseRow_49_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_50_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk25_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 50) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 12) (mtFiber36StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 12) (mtFiber36StateAt 50)
    (mtFiber36RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 50) (by decide) mtFiber36ReverseRow_50_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_51_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk25_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 50) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 13) (mtFiber36StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 13) (mtFiber36StateAt 51)
    (mtFiber36RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 51) (by decide) mtFiber36ReverseRow_51_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_52_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk26_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 52) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 8) (mtFiber36StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 8) (mtFiber36StateAt 52)
    (mtFiber36RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 52) (by decide) mtFiber36ReverseRow_52_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_53_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk26_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 52) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 9) (mtFiber36StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 9) (mtFiber36StateAt 53)
    (mtFiber36RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 53) (by decide) mtFiber36ReverseRow_53_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_54_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk27_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 54) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 10) (mtFiber36StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 10) (mtFiber36StateAt 54)
    (mtFiber36RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 54) (by decide) mtFiber36ReverseRow_54_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_55_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk27_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 54) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 11) (mtFiber36StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 11) (mtFiber36StateAt 55)
    (mtFiber36RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 55) (by decide) mtFiber36ReverseRow_55_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_56_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk28_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 56) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 60) (mtFiber36StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 60) (mtFiber36StateAt 56)
    (mtFiber36RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 56) (by decide) mtFiber36ReverseRow_56_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_57_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk28_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 56) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 61) (mtFiber36StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 61) (mtFiber36StateAt 57)
    (mtFiber36RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 57) (by decide) mtFiber36ReverseRow_57_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_58_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk29_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 58) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 4) (mtFiber36StateAt 58)
    (mtFiber36RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 58) (by decide) mtFiber36ReverseRow_58_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_59_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk29_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 58) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 5) (mtFiber36StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 5) (mtFiber36StateAt 59)
    (mtFiber36RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 59) (by decide) mtFiber36ReverseRow_59_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_60_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk30_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 60) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 0) (mtFiber36StateAt 60)
    (mtFiber36RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 60) (by decide) mtFiber36ReverseRow_60_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_61_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk30_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 60) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 1) (mtFiber36StateAt 61)
    (mtFiber36RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 61) (by decide) mtFiber36ReverseRow_61_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_62_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk31_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 62) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber36ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 2) (mtFiber36StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 2) (mtFiber36StateAt 62)
    (mtFiber36RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 62) (by decide) mtFiber36ReverseRow_62_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36ReverseRow_63_ok :
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber36Chunk31_ok
  change (mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 62) &&
    mtRowReverseValid mtFiber36Key mtFiber36Expected (mtFiber36RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber36ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber36StateAt 3) (mtFiber36StateAt 63)
    (mtFiber36RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber36Key mtFiber36Expected
        (mtFiber36RowAt 63) (by decide) mtFiber36ReverseRow_63_ok
      simpa [mtFiber36StateAt, mtFiber36RowAt, mtFiber36Rows, listGetD, directRow] using h)

theorem mtFiber36State0_in_close :
    mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  change mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 64 [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 0 64 [mtFiber36StateAt 0] (mtFiber36StateAt 0) (by simp [closeChainFiber])

theorem mtFiber36State1_in_close :
    mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  change mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates (1 + 63) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 1 63 [mtFiber36StateAt 0] (mtFiber36StateAt 1) h1

theorem mtFiber36State2_in_close :
    mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  change mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 2) h2

theorem mtFiber36State3_in_close :
    mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  change mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates (1 + 63) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 1 63 [mtFiber36StateAt 0] (mtFiber36StateAt 3) h1

theorem mtFiber36State4_in_close :
    mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  change mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates (1 + 63) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 1 63 [mtFiber36StateAt 0] (mtFiber36StateAt 4) h1

theorem mtFiber36State5_in_close :
    mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  change mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 5) h2

theorem mtFiber36State6_in_close :
    mtFiber36StateAt 6 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 6 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 6) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep6
  change mtFiber36StateAt 6 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 6) h2

theorem mtFiber36State7_in_close :
    mtFiber36StateAt 7 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 7 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 7) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep7
  change mtFiber36StateAt 7 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 7) h2

theorem mtFiber36State8_in_close :
    mtFiber36StateAt 8 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 8 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 8) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep8
  change mtFiber36StateAt 8 ∈ closeChainFiber mtWord mtFiber36DirectStates (1 + 63) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 1 63 [mtFiber36StateAt 0] (mtFiber36StateAt 8) h1

theorem mtFiber36State9_in_close :
    mtFiber36StateAt 9 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 9 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 9) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep9
  change mtFiber36StateAt 9 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 9) h2

theorem mtFiber36State10_in_close :
    mtFiber36StateAt 10 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  have h3 : mtFiber36StateAt 10 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 2) (mtFiber36StateAt 10) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep10
  change mtFiber36StateAt 10 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 10) h3

theorem mtFiber36State11_in_close :
    mtFiber36StateAt 11 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 11 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 11) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep11
  change mtFiber36StateAt 11 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 11) h2

theorem mtFiber36State12_in_close :
    mtFiber36StateAt 12 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 12 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 12) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep12
  change mtFiber36StateAt 12 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 12) h2

theorem mtFiber36State13_in_close :
    mtFiber36StateAt 13 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  have h3 : mtFiber36StateAt 13 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 5) (mtFiber36StateAt 13) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep13
  change mtFiber36StateAt 13 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 13) h3

theorem mtFiber36State14_in_close :
    mtFiber36StateAt 14 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 6 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 6) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep6
  have h3 : mtFiber36StateAt 14 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 6) (mtFiber36StateAt 14) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep14
  change mtFiber36StateAt 14 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 14) h3

theorem mtFiber36State15_in_close :
    mtFiber36StateAt 15 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 7 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 7) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep7
  have h3 : mtFiber36StateAt 15 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 7) (mtFiber36StateAt 15) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep15
  change mtFiber36StateAt 15 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 15) h3

theorem mtFiber36State16_in_close :
    mtFiber36StateAt 16 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 16 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 16) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep16
  change mtFiber36StateAt 16 ∈ closeChainFiber mtWord mtFiber36DirectStates (1 + 63) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 1 63 [mtFiber36StateAt 0] (mtFiber36StateAt 16) h1

theorem mtFiber36State17_in_close :
    mtFiber36StateAt 17 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 17 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 17) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep17
  change mtFiber36StateAt 17 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 17) h2

theorem mtFiber36State18_in_close :
    mtFiber36StateAt 18 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  have h3 : mtFiber36StateAt 18 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 2) (mtFiber36StateAt 18) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep18
  change mtFiber36StateAt 18 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 18) h3

theorem mtFiber36State19_in_close :
    mtFiber36StateAt 19 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 19 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 19) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep19
  change mtFiber36StateAt 19 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 19) h2

theorem mtFiber36State20_in_close :
    mtFiber36StateAt 20 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 20 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 20) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep20
  change mtFiber36StateAt 20 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 20) h2

theorem mtFiber36State21_in_close :
    mtFiber36StateAt 21 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  have h3 : mtFiber36StateAt 21 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 5) (mtFiber36StateAt 21) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep21
  change mtFiber36StateAt 21 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 21) h3

theorem mtFiber36State22_in_close :
    mtFiber36StateAt 22 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 6 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 6) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep6
  have h3 : mtFiber36StateAt 22 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 6) (mtFiber36StateAt 22) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep22
  change mtFiber36StateAt 22 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 22) h3

theorem mtFiber36State23_in_close :
    mtFiber36StateAt 23 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 7 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 7) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep7
  have h3 : mtFiber36StateAt 23 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 7) (mtFiber36StateAt 23) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep23
  change mtFiber36StateAt 23 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 23) h3

theorem mtFiber36State24_in_close :
    mtFiber36StateAt 24 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 8 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 8) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep8
  have h2 : mtFiber36StateAt 24 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 8) (mtFiber36StateAt 24) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep24
  change mtFiber36StateAt 24 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 24) h2

theorem mtFiber36State25_in_close :
    mtFiber36StateAt 25 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 9 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 9) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep9
  have h3 : mtFiber36StateAt 25 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 9) (mtFiber36StateAt 25) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep25
  change mtFiber36StateAt 25 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 25) h3

theorem mtFiber36State26_in_close :
    mtFiber36StateAt 26 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  have h3 : mtFiber36StateAt 10 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 2) (mtFiber36StateAt 10) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep10
  have h4 : mtFiber36StateAt 26 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 10) (mtFiber36StateAt 26) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep26
  change mtFiber36StateAt 26 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 26) h4

theorem mtFiber36State27_in_close :
    mtFiber36StateAt 27 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 11 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 11) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep11
  have h3 : mtFiber36StateAt 27 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 11) (mtFiber36StateAt 27) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep27
  change mtFiber36StateAt 27 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 27) h3

theorem mtFiber36State28_in_close :
    mtFiber36StateAt 28 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 12 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 12) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep12
  have h3 : mtFiber36StateAt 28 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 12) (mtFiber36StateAt 28) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep28
  change mtFiber36StateAt 28 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 28) h3

theorem mtFiber36State29_in_close :
    mtFiber36StateAt 29 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  have h3 : mtFiber36StateAt 13 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 5) (mtFiber36StateAt 13) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep13
  have h4 : mtFiber36StateAt 29 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 13) (mtFiber36StateAt 29) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep29
  change mtFiber36StateAt 29 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 29) h4

theorem mtFiber36State30_in_close :
    mtFiber36StateAt 30 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 6 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 6) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep6
  have h3 : mtFiber36StateAt 14 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 6) (mtFiber36StateAt 14) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep14
  have h4 : mtFiber36StateAt 30 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 14) (mtFiber36StateAt 30) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep30
  change mtFiber36StateAt 30 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 30) h4

theorem mtFiber36State31_in_close :
    mtFiber36StateAt 31 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 7 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 7) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep7
  have h3 : mtFiber36StateAt 15 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 7) (mtFiber36StateAt 15) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep15
  have h4 : mtFiber36StateAt 31 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 15) (mtFiber36StateAt 31) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep31
  change mtFiber36StateAt 31 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 31) h4

theorem mtFiber36State32_in_close :
    mtFiber36StateAt 32 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 16 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 16) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep16
  have h2 : mtFiber36StateAt 36 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 16) (mtFiber36StateAt 36) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep36
  have h3 : mtFiber36StateAt 32 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 36) (mtFiber36StateAt 32) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep32
  change mtFiber36StateAt 32 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 32) h3

theorem mtFiber36State33_in_close :
    mtFiber36StateAt 33 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 17 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 17) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep17
  have h3 : mtFiber36StateAt 37 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 17) (mtFiber36StateAt 37) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep37
  have h4 : mtFiber36StateAt 33 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 37) (mtFiber36StateAt 33) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep33
  change mtFiber36StateAt 33 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 33) h4

theorem mtFiber36State34_in_close :
    mtFiber36StateAt 34 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 20 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 20) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep20
  have h3 : mtFiber36StateAt 34 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 20) (mtFiber36StateAt 34) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep34
  change mtFiber36StateAt 34 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 34) h3

theorem mtFiber36State35_in_close :
    mtFiber36StateAt 35 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  have h3 : mtFiber36StateAt 21 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 5) (mtFiber36StateAt 21) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep21
  have h4 : mtFiber36StateAt 35 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 21) (mtFiber36StateAt 35) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep35
  change mtFiber36StateAt 35 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 35) h4

theorem mtFiber36State36_in_close :
    mtFiber36StateAt 36 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 16 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 16) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep16
  have h2 : mtFiber36StateAt 36 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 16) (mtFiber36StateAt 36) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep36
  change mtFiber36StateAt 36 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 36) h2

theorem mtFiber36State37_in_close :
    mtFiber36StateAt 37 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 17 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 17) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep17
  have h3 : mtFiber36StateAt 37 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 17) (mtFiber36StateAt 37) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep37
  change mtFiber36StateAt 37 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 37) h3

theorem mtFiber36State38_in_close :
    mtFiber36StateAt 38 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  have h3 : mtFiber36StateAt 18 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 2) (mtFiber36StateAt 18) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep18
  have h4 : mtFiber36StateAt 38 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 18) (mtFiber36StateAt 38) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep38
  change mtFiber36StateAt 38 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 38) h4

theorem mtFiber36State39_in_close :
    mtFiber36StateAt 39 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 19 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 19) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep19
  have h3 : mtFiber36StateAt 39 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 19) (mtFiber36StateAt 39) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep39
  change mtFiber36StateAt 39 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 39) h3

theorem mtFiber36State40_in_close :
    mtFiber36StateAt 40 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 60 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 60) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep60
  have h2 : mtFiber36StateAt 44 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 60) (mtFiber36StateAt 44) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep44
  have h3 : mtFiber36StateAt 40 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 44) (mtFiber36StateAt 40) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep40
  change mtFiber36StateAt 40 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 40) h3

theorem mtFiber36State41_in_close :
    mtFiber36StateAt 41 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 61 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 61) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep61
  have h3 : mtFiber36StateAt 45 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 61) (mtFiber36StateAt 45) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep45
  have h4 : mtFiber36StateAt 41 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 45) (mtFiber36StateAt 41) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep41
  change mtFiber36StateAt 41 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 41) h4

theorem mtFiber36State42_in_close :
    mtFiber36StateAt 42 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 58 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 58) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep58
  have h3 : mtFiber36StateAt 42 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 58) (mtFiber36StateAt 42) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep42
  change mtFiber36StateAt 42 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 42) h3

theorem mtFiber36State43_in_close :
    mtFiber36StateAt 43 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  have h3 : mtFiber36StateAt 59 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 5) (mtFiber36StateAt 59) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep59
  have h4 : mtFiber36StateAt 43 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 59) (mtFiber36StateAt 43) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep43
  change mtFiber36StateAt 43 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 43) h4

theorem mtFiber36State44_in_close :
    mtFiber36StateAt 44 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 60 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 60) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep60
  have h2 : mtFiber36StateAt 44 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 60) (mtFiber36StateAt 44) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep44
  change mtFiber36StateAt 44 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 44) h2

theorem mtFiber36State45_in_close :
    mtFiber36StateAt 45 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 61 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 61) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep61
  have h3 : mtFiber36StateAt 45 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 61) (mtFiber36StateAt 45) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep45
  change mtFiber36StateAt 45 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 45) h3

theorem mtFiber36State46_in_close :
    mtFiber36StateAt 46 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  have h3 : mtFiber36StateAt 62 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 2) (mtFiber36StateAt 62) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep62
  have h4 : mtFiber36StateAt 46 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 62) (mtFiber36StateAt 46) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep46
  change mtFiber36StateAt 46 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 46) h4

theorem mtFiber36State47_in_close :
    mtFiber36StateAt 47 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 63 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 63) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep63
  have h3 : mtFiber36StateAt 47 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 63) (mtFiber36StateAt 47) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep47
  change mtFiber36StateAt 47 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 47) h3

theorem mtFiber36State48_in_close :
    mtFiber36StateAt 48 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 8 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 8) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep8
  have h2 : mtFiber36StateAt 52 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 8) (mtFiber36StateAt 52) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep52
  have h3 : mtFiber36StateAt 48 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 52) (mtFiber36StateAt 48) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep48
  change mtFiber36StateAt 48 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 48) h3

theorem mtFiber36State49_in_close :
    mtFiber36StateAt 49 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 9 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 9) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep9
  have h3 : mtFiber36StateAt 53 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 9) (mtFiber36StateAt 53) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep53
  have h4 : mtFiber36StateAt 49 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 53) (mtFiber36StateAt 49) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep49
  change mtFiber36StateAt 49 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 49) h4

theorem mtFiber36State50_in_close :
    mtFiber36StateAt 50 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 12 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 12) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep12
  have h3 : mtFiber36StateAt 50 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 12) (mtFiber36StateAt 50) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep50
  change mtFiber36StateAt 50 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 50) h3

theorem mtFiber36State51_in_close :
    mtFiber36StateAt 51 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  have h3 : mtFiber36StateAt 13 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 5) (mtFiber36StateAt 13) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep13
  have h4 : mtFiber36StateAt 51 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 13) (mtFiber36StateAt 51) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep51
  change mtFiber36StateAt 51 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 51) h4

theorem mtFiber36State52_in_close :
    mtFiber36StateAt 52 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 8 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 8) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep8
  have h2 : mtFiber36StateAt 52 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 8) (mtFiber36StateAt 52) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep52
  change mtFiber36StateAt 52 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 52) h2

theorem mtFiber36State53_in_close :
    mtFiber36StateAt 53 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 9 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 9) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep9
  have h3 : mtFiber36StateAt 53 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 9) (mtFiber36StateAt 53) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep53
  change mtFiber36StateAt 53 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 53) h3

theorem mtFiber36State54_in_close :
    mtFiber36StateAt 54 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  have h3 : mtFiber36StateAt 10 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 2) (mtFiber36StateAt 10) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep10
  have h4 : mtFiber36StateAt 54 ∈ closeChainFiber mtWord mtFiber36DirectStates 4 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0]
      (mtFiber36StateAt 10) (mtFiber36StateAt 54) (by decide) h3 (by decide)
      mtFiber36ReverseSingleStep54
  change mtFiber36StateAt 54 ∈ closeChainFiber mtWord mtFiber36DirectStates (4 + 60) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 4 60 [mtFiber36StateAt 0] (mtFiber36StateAt 54) h4

theorem mtFiber36State55_in_close :
    mtFiber36StateAt 55 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 11 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 11) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep11
  have h3 : mtFiber36StateAt 55 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 11) (mtFiber36StateAt 55) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep55
  change mtFiber36StateAt 55 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 55) h3

theorem mtFiber36State56_in_close :
    mtFiber36StateAt 56 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 60 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 60) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep60
  have h2 : mtFiber36StateAt 56 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 60) (mtFiber36StateAt 56) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep56
  change mtFiber36StateAt 56 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 56) h2

theorem mtFiber36State57_in_close :
    mtFiber36StateAt 57 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 61 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 61) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep61
  have h3 : mtFiber36StateAt 57 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 61) (mtFiber36StateAt 57) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep57
  change mtFiber36StateAt 57 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 57) h3

theorem mtFiber36State58_in_close :
    mtFiber36StateAt 58 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 4 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 4) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep4
  have h2 : mtFiber36StateAt 58 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 4) (mtFiber36StateAt 58) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep58
  change mtFiber36StateAt 58 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 58) h2

theorem mtFiber36State59_in_close :
    mtFiber36StateAt 59 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 5 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 5) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep5
  have h3 : mtFiber36StateAt 59 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 5) (mtFiber36StateAt 59) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep59
  change mtFiber36StateAt 59 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 59) h3

theorem mtFiber36State60_in_close :
    mtFiber36StateAt 60 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 60 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 60) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep60
  change mtFiber36StateAt 60 ∈ closeChainFiber mtWord mtFiber36DirectStates (1 + 63) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 1 63 [mtFiber36StateAt 0] (mtFiber36StateAt 60) h1

theorem mtFiber36State61_in_close :
    mtFiber36StateAt 61 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 61 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 61) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep61
  change mtFiber36StateAt 61 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 61) h2

theorem mtFiber36State62_in_close :
    mtFiber36StateAt 62 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 1 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 1) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep1
  have h2 : mtFiber36StateAt 2 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 1) (mtFiber36StateAt 2) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep2
  have h3 : mtFiber36StateAt 62 ∈ closeChainFiber mtWord mtFiber36DirectStates 3 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0]
      (mtFiber36StateAt 2) (mtFiber36StateAt 62) (by decide) h2 (by decide)
      mtFiber36ReverseSingleStep62
  change mtFiber36StateAt 62 ∈ closeChainFiber mtWord mtFiber36DirectStates (3 + 61) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 3 61 [mtFiber36StateAt 0] (mtFiber36StateAt 62) h3

theorem mtFiber36State63_in_close :
    mtFiber36StateAt 63 ∈ closeChainFiber mtWord mtFiber36DirectStates mtFiber36DirectStates.length [mtFiber36StateAt 0] := by
  have h0 : mtFiber36StateAt 0 ∈ closeChainFiber mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber36StateAt 3 ∈ closeChainFiber mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 0 [mtFiber36StateAt 0]
      (mtFiber36StateAt 0) (mtFiber36StateAt 3) (by decide) h0 (by decide)
      mtFiber36ReverseSingleStep3
  have h2 : mtFiber36StateAt 63 ∈ closeChainFiber mtWord mtFiber36DirectStates 2 [mtFiber36StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber36DirectStates 1 [mtFiber36StateAt 0]
      (mtFiber36StateAt 3) (mtFiber36StateAt 63) (by decide) h1 (by decide)
      mtFiber36ReverseSingleStep63
  change mtFiber36StateAt 63 ∈ closeChainFiber mtWord mtFiber36DirectStates (2 + 62) [mtFiber36StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber36DirectStates 2 62 [mtFiber36StateAt 0] (mtFiber36StateAt 63) h2

theorem mtFiber36DirectConnected :
    chainFiberConnected mtWord mtFiber36DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber36DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber36State0_in_close
  · subst state
    exact mtFiber36State1_in_close
  · subst state
    exact mtFiber36State2_in_close
  · subst state
    exact mtFiber36State3_in_close
  · subst state
    exact mtFiber36State4_in_close
  · subst state
    exact mtFiber36State5_in_close
  · subst state
    exact mtFiber36State6_in_close
  · subst state
    exact mtFiber36State7_in_close
  · subst state
    exact mtFiber36State8_in_close
  · subst state
    exact mtFiber36State9_in_close
  · subst state
    exact mtFiber36State10_in_close
  · subst state
    exact mtFiber36State11_in_close
  · subst state
    exact mtFiber36State12_in_close
  · subst state
    exact mtFiber36State13_in_close
  · subst state
    exact mtFiber36State14_in_close
  · subst state
    exact mtFiber36State15_in_close
  · subst state
    exact mtFiber36State16_in_close
  · subst state
    exact mtFiber36State17_in_close
  · subst state
    exact mtFiber36State18_in_close
  · subst state
    exact mtFiber36State19_in_close
  · subst state
    exact mtFiber36State20_in_close
  · subst state
    exact mtFiber36State21_in_close
  · subst state
    exact mtFiber36State22_in_close
  · subst state
    exact mtFiber36State23_in_close
  · subst state
    exact mtFiber36State24_in_close
  · subst state
    exact mtFiber36State25_in_close
  · subst state
    exact mtFiber36State26_in_close
  · subst state
    exact mtFiber36State27_in_close
  · subst state
    exact mtFiber36State28_in_close
  · subst state
    exact mtFiber36State29_in_close
  · subst state
    exact mtFiber36State30_in_close
  · subst state
    exact mtFiber36State31_in_close
  · subst state
    exact mtFiber36State32_in_close
  · subst state
    exact mtFiber36State33_in_close
  · subst state
    exact mtFiber36State34_in_close
  · subst state
    exact mtFiber36State35_in_close
  · subst state
    exact mtFiber36State36_in_close
  · subst state
    exact mtFiber36State37_in_close
  · subst state
    exact mtFiber36State38_in_close
  · subst state
    exact mtFiber36State39_in_close
  · subst state
    exact mtFiber36State40_in_close
  · subst state
    exact mtFiber36State41_in_close
  · subst state
    exact mtFiber36State42_in_close
  · subst state
    exact mtFiber36State43_in_close
  · subst state
    exact mtFiber36State44_in_close
  · subst state
    exact mtFiber36State45_in_close
  · subst state
    exact mtFiber36State46_in_close
  · subst state
    exact mtFiber36State47_in_close
  · subst state
    exact mtFiber36State48_in_close
  · subst state
    exact mtFiber36State49_in_close
  · subst state
    exact mtFiber36State50_in_close
  · subst state
    exact mtFiber36State51_in_close
  · subst state
    exact mtFiber36State52_in_close
  · subst state
    exact mtFiber36State53_in_close
  · subst state
    exact mtFiber36State54_in_close
  · subst state
    exact mtFiber36State55_in_close
  · subst state
    exact mtFiber36State56_in_close
  · subst state
    exact mtFiber36State57_in_close
  · subst state
    exact mtFiber36State58_in_close
  · subst state
    exact mtFiber36State59_in_close
  · subst state
    exact mtFiber36State60_in_close
  · subst state
    exact mtFiber36State61_in_close
  · subst state
    exact mtFiber36State62_in_close
  · subst state
    exact mtFiber36State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
