import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 20

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber20StateAt (i : Nat) : List TauState :=
  directStates (mtFiber20RowAt i).sourceLeft (mtFiber20RowAt i).sourceRight

def mtFiber20DirectStates : List (List TauState) :=
  [mtFiber20StateAt 0, mtFiber20StateAt 1, mtFiber20StateAt 2, mtFiber20StateAt 3, mtFiber20StateAt 4, mtFiber20StateAt 5, mtFiber20StateAt 6, mtFiber20StateAt 7, mtFiber20StateAt 8, mtFiber20StateAt 9, mtFiber20StateAt 10, mtFiber20StateAt 11, mtFiber20StateAt 12, mtFiber20StateAt 13, mtFiber20StateAt 14, mtFiber20StateAt 15, mtFiber20StateAt 16, mtFiber20StateAt 17, mtFiber20StateAt 18, mtFiber20StateAt 19, mtFiber20StateAt 20, mtFiber20StateAt 21, mtFiber20StateAt 22, mtFiber20StateAt 23, mtFiber20StateAt 24, mtFiber20StateAt 25, mtFiber20StateAt 26, mtFiber20StateAt 27, mtFiber20StateAt 28, mtFiber20StateAt 29, mtFiber20StateAt 30, mtFiber20StateAt 31, mtFiber20StateAt 32, mtFiber20StateAt 33, mtFiber20StateAt 34, mtFiber20StateAt 35, mtFiber20StateAt 36, mtFiber20StateAt 37, mtFiber20StateAt 38, mtFiber20StateAt 39, mtFiber20StateAt 40, mtFiber20StateAt 41, mtFiber20StateAt 42, mtFiber20StateAt 43, mtFiber20StateAt 44, mtFiber20StateAt 45, mtFiber20StateAt 46, mtFiber20StateAt 47, mtFiber20StateAt 48, mtFiber20StateAt 49, mtFiber20StateAt 50, mtFiber20StateAt 51, mtFiber20StateAt 52, mtFiber20StateAt 53, mtFiber20StateAt 54, mtFiber20StateAt 55, mtFiber20StateAt 56, mtFiber20StateAt 57, mtFiber20StateAt 58, mtFiber20StateAt 59, mtFiber20StateAt 60, mtFiber20StateAt 61, mtFiber20StateAt 62, mtFiber20StateAt 63]

theorem mtFiber20ReverseRow_1_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk0_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 0) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 1)
    (mtFiber20RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 1) (by decide) mtFiber20ReverseRow_1_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_2_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk1_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 2) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 2)
    (mtFiber20RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 2) (by decide) mtFiber20ReverseRow_2_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_3_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk1_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 2) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 3)
    (mtFiber20RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 3) (by decide) mtFiber20ReverseRow_3_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_4_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk2_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 4) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 4)
    (mtFiber20RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 4) (by decide) mtFiber20ReverseRow_4_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_5_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk2_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 4) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 5)
    (mtFiber20RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 5) (by decide) mtFiber20ReverseRow_5_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_6_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk3_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 6) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 6)
    (mtFiber20RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 6) (by decide) mtFiber20ReverseRow_6_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_7_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk3_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 6) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 7)
    (mtFiber20RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 7) (by decide) mtFiber20ReverseRow_7_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_8_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk4_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 8) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 8)
    (mtFiber20RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 8) (by decide) mtFiber20ReverseRow_8_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_9_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk4_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 8) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 9)
    (mtFiber20RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 9) (by decide) mtFiber20ReverseRow_9_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_10_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk5_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 10) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 2) (mtFiber20StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 2) (mtFiber20StateAt 10)
    (mtFiber20RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 10) (by decide) mtFiber20ReverseRow_10_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_11_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk5_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 10) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 11)
    (mtFiber20RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 11) (by decide) mtFiber20ReverseRow_11_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_12_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk6_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 12) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 12)
    (mtFiber20RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 12) (by decide) mtFiber20ReverseRow_12_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_13_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk6_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 12) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 5) (mtFiber20StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 5) (mtFiber20StateAt 13)
    (mtFiber20RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 13) (by decide) mtFiber20ReverseRow_13_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_14_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk7_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 14) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 6) (mtFiber20StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 6) (mtFiber20StateAt 14)
    (mtFiber20RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 14) (by decide) mtFiber20ReverseRow_14_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_15_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk7_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 14) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 7) (mtFiber20StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 7) (mtFiber20StateAt 15)
    (mtFiber20RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 15) (by decide) mtFiber20ReverseRow_15_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_16_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk8_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 16) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 16)
    (mtFiber20RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 16) (by decide) mtFiber20ReverseRow_16_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_17_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk8_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 16) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 17)
    (mtFiber20RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 17) (by decide) mtFiber20ReverseRow_17_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_18_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk9_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 18) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 2) (mtFiber20StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 2) (mtFiber20StateAt 18)
    (mtFiber20RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 18) (by decide) mtFiber20ReverseRow_18_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_19_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk9_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 18) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 19)
    (mtFiber20RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 19) (by decide) mtFiber20ReverseRow_19_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_20_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk10_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 20) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 20)
    (mtFiber20RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 20) (by decide) mtFiber20ReverseRow_20_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_21_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk10_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 20) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 5) (mtFiber20StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 5) (mtFiber20StateAt 21)
    (mtFiber20RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 21) (by decide) mtFiber20ReverseRow_21_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_22_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk11_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 22) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 6) (mtFiber20StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 6) (mtFiber20StateAt 22)
    (mtFiber20RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 22) (by decide) mtFiber20ReverseRow_22_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_23_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk11_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 22) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 7) (mtFiber20StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 7) (mtFiber20StateAt 23)
    (mtFiber20RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 23) (by decide) mtFiber20ReverseRow_23_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_24_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk12_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 24) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 8) (mtFiber20StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 8) (mtFiber20StateAt 24)
    (mtFiber20RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 24) (by decide) mtFiber20ReverseRow_24_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_25_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk12_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 24) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 9) (mtFiber20StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 9) (mtFiber20StateAt 25)
    (mtFiber20RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 25) (by decide) mtFiber20ReverseRow_25_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_26_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk13_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 26) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 10) (mtFiber20StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 10) (mtFiber20StateAt 26)
    (mtFiber20RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 26) (by decide) mtFiber20ReverseRow_26_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_27_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk13_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 26) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 11) (mtFiber20StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 11) (mtFiber20StateAt 27)
    (mtFiber20RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 27) (by decide) mtFiber20ReverseRow_27_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_28_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk14_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 28) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 12) (mtFiber20StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 12) (mtFiber20StateAt 28)
    (mtFiber20RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 28) (by decide) mtFiber20ReverseRow_28_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_29_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk14_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 28) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 13) (mtFiber20StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 13) (mtFiber20StateAt 29)
    (mtFiber20RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 29) (by decide) mtFiber20ReverseRow_29_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_30_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk15_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 30) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 14) (mtFiber20StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 14) (mtFiber20StateAt 30)
    (mtFiber20RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 30) (by decide) mtFiber20ReverseRow_30_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_31_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk15_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 30) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 15) (mtFiber20StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 15) (mtFiber20StateAt 31)
    (mtFiber20RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 31) (by decide) mtFiber20ReverseRow_31_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_32_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk16_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 32) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 0) (mtFiber20StateAt 32)
    (mtFiber20RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 32) (by decide) mtFiber20ReverseRow_32_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_33_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk16_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 32) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 1) (mtFiber20StateAt 33)
    (mtFiber20RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 33) (by decide) mtFiber20ReverseRow_33_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_34_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk17_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 34) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 32) (mtFiber20StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 32) (mtFiber20StateAt 34)
    (mtFiber20RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 34) (by decide) mtFiber20ReverseRow_34_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_35_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk17_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 34) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 3) (mtFiber20StateAt 35)
    (mtFiber20RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 35) (by decide) mtFiber20ReverseRow_35_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_36_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk18_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 36) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 4) (mtFiber20StateAt 36)
    (mtFiber20RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 36) (by decide) mtFiber20ReverseRow_36_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_37_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk18_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 36) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 5) (mtFiber20StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 5) (mtFiber20StateAt 37)
    (mtFiber20RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 37) (by decide) mtFiber20ReverseRow_37_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_38_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk19_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 38) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 33) (mtFiber20StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 33) (mtFiber20StateAt 38)
    (mtFiber20RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 38) (by decide) mtFiber20ReverseRow_38_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_39_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk19_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 38) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 32) (mtFiber20StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 32) (mtFiber20StateAt 39)
    (mtFiber20RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 39) (by decide) mtFiber20ReverseRow_39_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_40_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk20_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 40) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 8) (mtFiber20StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 8) (mtFiber20StateAt 40)
    (mtFiber20RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 40) (by decide) mtFiber20ReverseRow_40_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_41_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk20_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 40) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 9) (mtFiber20StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 9) (mtFiber20StateAt 41)
    (mtFiber20RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 41) (by decide) mtFiber20ReverseRow_41_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_42_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk21_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 42) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 40) (mtFiber20StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 40) (mtFiber20StateAt 42)
    (mtFiber20RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 42) (by decide) mtFiber20ReverseRow_42_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_43_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk21_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 42) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 11) (mtFiber20StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 11) (mtFiber20StateAt 43)
    (mtFiber20RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 43) (by decide) mtFiber20ReverseRow_43_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_44_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk22_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 44) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 12) (mtFiber20StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 12) (mtFiber20StateAt 44)
    (mtFiber20RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 44) (by decide) mtFiber20ReverseRow_44_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_45_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk22_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 44) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 13) (mtFiber20StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 13) (mtFiber20StateAt 45)
    (mtFiber20RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 45) (by decide) mtFiber20ReverseRow_45_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_46_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk23_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 46) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 41) (mtFiber20StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 41) (mtFiber20StateAt 46)
    (mtFiber20RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 46) (by decide) mtFiber20ReverseRow_46_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_47_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk23_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 46) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 40) (mtFiber20StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 40) (mtFiber20StateAt 47)
    (mtFiber20RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 47) (by decide) mtFiber20ReverseRow_47_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_48_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk24_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 48) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 16) (mtFiber20StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 16) (mtFiber20StateAt 48)
    (mtFiber20RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 48) (by decide) mtFiber20ReverseRow_48_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_49_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk24_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 48) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 17) (mtFiber20StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 17) (mtFiber20StateAt 49)
    (mtFiber20RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 49) (by decide) mtFiber20ReverseRow_49_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_50_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk25_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 50) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 48) (mtFiber20StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 48) (mtFiber20StateAt 50)
    (mtFiber20RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 50) (by decide) mtFiber20ReverseRow_50_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_51_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk25_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 50) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 19) (mtFiber20StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 19) (mtFiber20StateAt 51)
    (mtFiber20RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 51) (by decide) mtFiber20ReverseRow_51_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_52_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk26_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 52) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 20) (mtFiber20StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 20) (mtFiber20StateAt 52)
    (mtFiber20RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 52) (by decide) mtFiber20ReverseRow_52_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_53_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk26_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 52) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 21) (mtFiber20StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 21) (mtFiber20StateAt 53)
    (mtFiber20RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 53) (by decide) mtFiber20ReverseRow_53_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_54_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk27_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 54) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 49) (mtFiber20StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 49) (mtFiber20StateAt 54)
    (mtFiber20RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 54) (by decide) mtFiber20ReverseRow_54_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_55_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk27_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 54) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 48) (mtFiber20StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 48) (mtFiber20StateAt 55)
    (mtFiber20RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 55) (by decide) mtFiber20ReverseRow_55_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_56_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk28_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 56) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 32) (mtFiber20StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 32) (mtFiber20StateAt 56)
    (mtFiber20RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 56) (by decide) mtFiber20ReverseRow_56_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_57_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk28_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 56) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 33) (mtFiber20StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 33) (mtFiber20StateAt 57)
    (mtFiber20RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 57) (by decide) mtFiber20ReverseRow_57_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_58_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk29_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 58) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 34) (mtFiber20StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 34) (mtFiber20StateAt 58)
    (mtFiber20RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 58) (by decide) mtFiber20ReverseRow_58_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_59_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk29_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 58) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 35) (mtFiber20StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 35) (mtFiber20StateAt 59)
    (mtFiber20RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 59) (by decide) mtFiber20ReverseRow_59_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_60_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk30_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 60) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 36) (mtFiber20StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 36) (mtFiber20StateAt 60)
    (mtFiber20RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 60) (by decide) mtFiber20ReverseRow_60_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_61_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk30_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 60) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 37) (mtFiber20StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 37) (mtFiber20StateAt 61)
    (mtFiber20RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 61) (by decide) mtFiber20ReverseRow_61_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_62_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk31_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 62) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber20ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 38) (mtFiber20StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 38) (mtFiber20StateAt 62)
    (mtFiber20RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 62) (by decide) mtFiber20ReverseRow_62_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20ReverseRow_63_ok :
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber20Chunk31_ok
  change (mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 62) &&
    mtRowReverseValid mtFiber20Key mtFiber20Expected (mtFiber20RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber20ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber20StateAt 39) (mtFiber20StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber20StateAt 39) (mtFiber20StateAt 63)
    (mtFiber20RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber20Key mtFiber20Expected
        (mtFiber20RowAt 63) (by decide) mtFiber20ReverseRow_63_ok
      simpa [mtFiber20StateAt, mtFiber20RowAt, mtFiber20Rows, listGetD, directRow] using h)

theorem mtFiber20State0_in_close :
    mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  change mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 64 [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 0 64 [mtFiber20StateAt 0] (mtFiber20StateAt 0) (by simp [closeChainFiber])

theorem mtFiber20State1_in_close :
    mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  change mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates (1 + 63) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 1 63 [mtFiber20StateAt 0] (mtFiber20StateAt 1) h1

theorem mtFiber20State2_in_close :
    mtFiber20StateAt 2 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 2 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 2) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep2
  change mtFiber20StateAt 2 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 2) h2

theorem mtFiber20State3_in_close :
    mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  change mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates (1 + 63) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 1 63 [mtFiber20StateAt 0] (mtFiber20StateAt 3) h1

theorem mtFiber20State4_in_close :
    mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  change mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates (1 + 63) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 1 63 [mtFiber20StateAt 0] (mtFiber20StateAt 4) h1

theorem mtFiber20State5_in_close :
    mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  change mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 5) h2

theorem mtFiber20State6_in_close :
    mtFiber20StateAt 6 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 6 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 6) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep6
  change mtFiber20StateAt 6 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 6) h2

theorem mtFiber20State7_in_close :
    mtFiber20StateAt 7 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 7 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 7) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep7
  change mtFiber20StateAt 7 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 7) h2

theorem mtFiber20State8_in_close :
    mtFiber20StateAt 8 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 8 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 8) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep8
  change mtFiber20StateAt 8 ∈ closeChainFiber mtWord mtFiber20DirectStates (1 + 63) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 1 63 [mtFiber20StateAt 0] (mtFiber20StateAt 8) h1

theorem mtFiber20State9_in_close :
    mtFiber20StateAt 9 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 9 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 9) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep9
  change mtFiber20StateAt 9 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 9) h2

theorem mtFiber20State10_in_close :
    mtFiber20StateAt 10 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 2 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 2) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep2
  have h3 : mtFiber20StateAt 10 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 2) (mtFiber20StateAt 10) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep10
  change mtFiber20StateAt 10 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 10) h3

theorem mtFiber20State11_in_close :
    mtFiber20StateAt 11 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 11 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 11) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep11
  change mtFiber20StateAt 11 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 11) h2

theorem mtFiber20State12_in_close :
    mtFiber20StateAt 12 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 12 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 12) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep12
  change mtFiber20StateAt 12 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 12) h2

theorem mtFiber20State13_in_close :
    mtFiber20StateAt 13 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  have h3 : mtFiber20StateAt 13 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 5) (mtFiber20StateAt 13) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep13
  change mtFiber20StateAt 13 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 13) h3

theorem mtFiber20State14_in_close :
    mtFiber20StateAt 14 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 6 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 6) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep6
  have h3 : mtFiber20StateAt 14 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 6) (mtFiber20StateAt 14) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep14
  change mtFiber20StateAt 14 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 14) h3

theorem mtFiber20State15_in_close :
    mtFiber20StateAt 15 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 7 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 7) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep7
  have h3 : mtFiber20StateAt 15 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 7) (mtFiber20StateAt 15) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep15
  change mtFiber20StateAt 15 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 15) h3

theorem mtFiber20State16_in_close :
    mtFiber20StateAt 16 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 16 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 16) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep16
  change mtFiber20StateAt 16 ∈ closeChainFiber mtWord mtFiber20DirectStates (1 + 63) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 1 63 [mtFiber20StateAt 0] (mtFiber20StateAt 16) h1

theorem mtFiber20State17_in_close :
    mtFiber20StateAt 17 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 17 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 17) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep17
  change mtFiber20StateAt 17 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 17) h2

theorem mtFiber20State18_in_close :
    mtFiber20StateAt 18 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 2 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 2) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep2
  have h3 : mtFiber20StateAt 18 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 2) (mtFiber20StateAt 18) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep18
  change mtFiber20StateAt 18 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 18) h3

theorem mtFiber20State19_in_close :
    mtFiber20StateAt 19 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 19 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 19) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep19
  change mtFiber20StateAt 19 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 19) h2

theorem mtFiber20State20_in_close :
    mtFiber20StateAt 20 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 20 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 20) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep20
  change mtFiber20StateAt 20 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 20) h2

theorem mtFiber20State21_in_close :
    mtFiber20StateAt 21 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  have h3 : mtFiber20StateAt 21 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 5) (mtFiber20StateAt 21) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep21
  change mtFiber20StateAt 21 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 21) h3

theorem mtFiber20State22_in_close :
    mtFiber20StateAt 22 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 6 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 6) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep6
  have h3 : mtFiber20StateAt 22 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 6) (mtFiber20StateAt 22) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep22
  change mtFiber20StateAt 22 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 22) h3

theorem mtFiber20State23_in_close :
    mtFiber20StateAt 23 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 7 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 7) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep7
  have h3 : mtFiber20StateAt 23 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 7) (mtFiber20StateAt 23) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep23
  change mtFiber20StateAt 23 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 23) h3

theorem mtFiber20State24_in_close :
    mtFiber20StateAt 24 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 8 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 8) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep8
  have h2 : mtFiber20StateAt 24 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 8) (mtFiber20StateAt 24) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep24
  change mtFiber20StateAt 24 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 24) h2

theorem mtFiber20State25_in_close :
    mtFiber20StateAt 25 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 9 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 9) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep9
  have h3 : mtFiber20StateAt 25 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 9) (mtFiber20StateAt 25) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep25
  change mtFiber20StateAt 25 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 25) h3

theorem mtFiber20State26_in_close :
    mtFiber20StateAt 26 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 2 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 2) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep2
  have h3 : mtFiber20StateAt 10 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 2) (mtFiber20StateAt 10) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep10
  have h4 : mtFiber20StateAt 26 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 10) (mtFiber20StateAt 26) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep26
  change mtFiber20StateAt 26 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 26) h4

theorem mtFiber20State27_in_close :
    mtFiber20StateAt 27 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 11 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 11) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep11
  have h3 : mtFiber20StateAt 27 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 11) (mtFiber20StateAt 27) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep27
  change mtFiber20StateAt 27 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 27) h3

theorem mtFiber20State28_in_close :
    mtFiber20StateAt 28 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 12 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 12) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep12
  have h3 : mtFiber20StateAt 28 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 12) (mtFiber20StateAt 28) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep28
  change mtFiber20StateAt 28 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 28) h3

theorem mtFiber20State29_in_close :
    mtFiber20StateAt 29 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  have h3 : mtFiber20StateAt 13 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 5) (mtFiber20StateAt 13) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep13
  have h4 : mtFiber20StateAt 29 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 13) (mtFiber20StateAt 29) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep29
  change mtFiber20StateAt 29 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 29) h4

theorem mtFiber20State30_in_close :
    mtFiber20StateAt 30 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 6 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 6) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep6
  have h3 : mtFiber20StateAt 14 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 6) (mtFiber20StateAt 14) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep14
  have h4 : mtFiber20StateAt 30 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 14) (mtFiber20StateAt 30) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep30
  change mtFiber20StateAt 30 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 30) h4

theorem mtFiber20State31_in_close :
    mtFiber20StateAt 31 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 7 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 7) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep7
  have h3 : mtFiber20StateAt 15 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 7) (mtFiber20StateAt 15) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep15
  have h4 : mtFiber20StateAt 31 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 15) (mtFiber20StateAt 31) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep31
  change mtFiber20StateAt 31 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 31) h4

theorem mtFiber20State32_in_close :
    mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 32) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep32
  change mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates (1 + 63) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 1 63 [mtFiber20StateAt 0] (mtFiber20StateAt 32) h1

theorem mtFiber20State33_in_close :
    mtFiber20StateAt 33 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 33 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 33) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep33
  change mtFiber20StateAt 33 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 33) h2

theorem mtFiber20State34_in_close :
    mtFiber20StateAt 34 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 32) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep32
  have h2 : mtFiber20StateAt 34 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 32) (mtFiber20StateAt 34) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep34
  change mtFiber20StateAt 34 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 34) h2

theorem mtFiber20State35_in_close :
    mtFiber20StateAt 35 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 35 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 35) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep35
  change mtFiber20StateAt 35 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 35) h2

theorem mtFiber20State36_in_close :
    mtFiber20StateAt 36 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 36 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 36) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep36
  change mtFiber20StateAt 36 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 36) h2

theorem mtFiber20State37_in_close :
    mtFiber20StateAt 37 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  have h3 : mtFiber20StateAt 37 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 5) (mtFiber20StateAt 37) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep37
  change mtFiber20StateAt 37 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 37) h3

theorem mtFiber20State38_in_close :
    mtFiber20StateAt 38 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 33 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 33) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep33
  have h3 : mtFiber20StateAt 38 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 33) (mtFiber20StateAt 38) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep38
  change mtFiber20StateAt 38 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 38) h3

theorem mtFiber20State39_in_close :
    mtFiber20StateAt 39 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 32) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep32
  have h2 : mtFiber20StateAt 39 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 32) (mtFiber20StateAt 39) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep39
  change mtFiber20StateAt 39 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 39) h2

theorem mtFiber20State40_in_close :
    mtFiber20StateAt 40 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 8 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 8) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep8
  have h2 : mtFiber20StateAt 40 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 8) (mtFiber20StateAt 40) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep40
  change mtFiber20StateAt 40 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 40) h2

theorem mtFiber20State41_in_close :
    mtFiber20StateAt 41 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 9 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 9) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep9
  have h3 : mtFiber20StateAt 41 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 9) (mtFiber20StateAt 41) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep41
  change mtFiber20StateAt 41 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 41) h3

theorem mtFiber20State42_in_close :
    mtFiber20StateAt 42 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 8 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 8) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep8
  have h2 : mtFiber20StateAt 40 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 8) (mtFiber20StateAt 40) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep40
  have h3 : mtFiber20StateAt 42 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 40) (mtFiber20StateAt 42) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep42
  change mtFiber20StateAt 42 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 42) h3

theorem mtFiber20State43_in_close :
    mtFiber20StateAt 43 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 11 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 11) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep11
  have h3 : mtFiber20StateAt 43 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 11) (mtFiber20StateAt 43) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep43
  change mtFiber20StateAt 43 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 43) h3

theorem mtFiber20State44_in_close :
    mtFiber20StateAt 44 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 12 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 12) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep12
  have h3 : mtFiber20StateAt 44 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 12) (mtFiber20StateAt 44) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep44
  change mtFiber20StateAt 44 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 44) h3

theorem mtFiber20State45_in_close :
    mtFiber20StateAt 45 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  have h3 : mtFiber20StateAt 13 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 5) (mtFiber20StateAt 13) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep13
  have h4 : mtFiber20StateAt 45 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 13) (mtFiber20StateAt 45) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep45
  change mtFiber20StateAt 45 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 45) h4

theorem mtFiber20State46_in_close :
    mtFiber20StateAt 46 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 9 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 9) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep9
  have h3 : mtFiber20StateAt 41 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 9) (mtFiber20StateAt 41) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep41
  have h4 : mtFiber20StateAt 46 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 41) (mtFiber20StateAt 46) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep46
  change mtFiber20StateAt 46 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 46) h4

theorem mtFiber20State47_in_close :
    mtFiber20StateAt 47 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 8 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 8) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep8
  have h2 : mtFiber20StateAt 40 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 8) (mtFiber20StateAt 40) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep40
  have h3 : mtFiber20StateAt 47 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 40) (mtFiber20StateAt 47) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep47
  change mtFiber20StateAt 47 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 47) h3

theorem mtFiber20State48_in_close :
    mtFiber20StateAt 48 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 16 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 16) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep16
  have h2 : mtFiber20StateAt 48 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 16) (mtFiber20StateAt 48) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep48
  change mtFiber20StateAt 48 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 48) h2

theorem mtFiber20State49_in_close :
    mtFiber20StateAt 49 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 17 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 17) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep17
  have h3 : mtFiber20StateAt 49 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 17) (mtFiber20StateAt 49) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep49
  change mtFiber20StateAt 49 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 49) h3

theorem mtFiber20State50_in_close :
    mtFiber20StateAt 50 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 16 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 16) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep16
  have h2 : mtFiber20StateAt 48 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 16) (mtFiber20StateAt 48) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep48
  have h3 : mtFiber20StateAt 50 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 48) (mtFiber20StateAt 50) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep50
  change mtFiber20StateAt 50 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 50) h3

theorem mtFiber20State51_in_close :
    mtFiber20StateAt 51 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 19 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 19) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep19
  have h3 : mtFiber20StateAt 51 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 19) (mtFiber20StateAt 51) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep51
  change mtFiber20StateAt 51 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 51) h3

theorem mtFiber20State52_in_close :
    mtFiber20StateAt 52 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 20 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 20) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep20
  have h3 : mtFiber20StateAt 52 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 20) (mtFiber20StateAt 52) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep52
  change mtFiber20StateAt 52 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 52) h3

theorem mtFiber20State53_in_close :
    mtFiber20StateAt 53 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  have h3 : mtFiber20StateAt 21 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 5) (mtFiber20StateAt 21) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep21
  have h4 : mtFiber20StateAt 53 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 21) (mtFiber20StateAt 53) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep53
  change mtFiber20StateAt 53 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 53) h4

theorem mtFiber20State54_in_close :
    mtFiber20StateAt 54 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 17 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 17) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep17
  have h3 : mtFiber20StateAt 49 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 17) (mtFiber20StateAt 49) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep49
  have h4 : mtFiber20StateAt 54 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 49) (mtFiber20StateAt 54) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep54
  change mtFiber20StateAt 54 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 54) h4

theorem mtFiber20State55_in_close :
    mtFiber20StateAt 55 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 16 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 16) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep16
  have h2 : mtFiber20StateAt 48 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 16) (mtFiber20StateAt 48) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep48
  have h3 : mtFiber20StateAt 55 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 48) (mtFiber20StateAt 55) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep55
  change mtFiber20StateAt 55 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 55) h3

theorem mtFiber20State56_in_close :
    mtFiber20StateAt 56 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 32) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep32
  have h2 : mtFiber20StateAt 56 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 32) (mtFiber20StateAt 56) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep56
  change mtFiber20StateAt 56 ∈ closeChainFiber mtWord mtFiber20DirectStates (2 + 62) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 2 62 [mtFiber20StateAt 0] (mtFiber20StateAt 56) h2

theorem mtFiber20State57_in_close :
    mtFiber20StateAt 57 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 33 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 33) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep33
  have h3 : mtFiber20StateAt 57 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 33) (mtFiber20StateAt 57) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep57
  change mtFiber20StateAt 57 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 57) h3

theorem mtFiber20State58_in_close :
    mtFiber20StateAt 58 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 32) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep32
  have h2 : mtFiber20StateAt 34 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 32) (mtFiber20StateAt 34) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep34
  have h3 : mtFiber20StateAt 58 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 34) (mtFiber20StateAt 58) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep58
  change mtFiber20StateAt 58 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 58) h3

theorem mtFiber20State59_in_close :
    mtFiber20StateAt 59 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 3 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 3) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep3
  have h2 : mtFiber20StateAt 35 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 3) (mtFiber20StateAt 35) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep35
  have h3 : mtFiber20StateAt 59 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 35) (mtFiber20StateAt 59) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep59
  change mtFiber20StateAt 59 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 59) h3

theorem mtFiber20State60_in_close :
    mtFiber20StateAt 60 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 4 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 4) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep4
  have h2 : mtFiber20StateAt 36 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 4) (mtFiber20StateAt 36) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep36
  have h3 : mtFiber20StateAt 60 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 36) (mtFiber20StateAt 60) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep60
  change mtFiber20StateAt 60 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 60) h3

theorem mtFiber20State61_in_close :
    mtFiber20StateAt 61 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 5 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 5) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep5
  have h3 : mtFiber20StateAt 37 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 5) (mtFiber20StateAt 37) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep37
  have h4 : mtFiber20StateAt 61 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 37) (mtFiber20StateAt 61) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep61
  change mtFiber20StateAt 61 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 61) h4

theorem mtFiber20State62_in_close :
    mtFiber20StateAt 62 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 1 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 1) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep1
  have h2 : mtFiber20StateAt 33 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 1) (mtFiber20StateAt 33) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep33
  have h3 : mtFiber20StateAt 38 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 33) (mtFiber20StateAt 38) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep38
  have h4 : mtFiber20StateAt 62 ∈ closeChainFiber mtWord mtFiber20DirectStates 4 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0]
      (mtFiber20StateAt 38) (mtFiber20StateAt 62) (by decide) h3 (by decide)
      mtFiber20ReverseSingleStep62
  change mtFiber20StateAt 62 ∈ closeChainFiber mtWord mtFiber20DirectStates (4 + 60) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 4 60 [mtFiber20StateAt 0] (mtFiber20StateAt 62) h4

theorem mtFiber20State63_in_close :
    mtFiber20StateAt 63 ∈ closeChainFiber mtWord mtFiber20DirectStates mtFiber20DirectStates.length [mtFiber20StateAt 0] := by
  have h0 : mtFiber20StateAt 0 ∈ closeChainFiber mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber20StateAt 32 ∈ closeChainFiber mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 0 [mtFiber20StateAt 0]
      (mtFiber20StateAt 0) (mtFiber20StateAt 32) (by decide) h0 (by decide)
      mtFiber20ReverseSingleStep32
  have h2 : mtFiber20StateAt 39 ∈ closeChainFiber mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 1 [mtFiber20StateAt 0]
      (mtFiber20StateAt 32) (mtFiber20StateAt 39) (by decide) h1 (by decide)
      mtFiber20ReverseSingleStep39
  have h3 : mtFiber20StateAt 63 ∈ closeChainFiber mtWord mtFiber20DirectStates 3 [mtFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber20DirectStates 2 [mtFiber20StateAt 0]
      (mtFiber20StateAt 39) (mtFiber20StateAt 63) (by decide) h2 (by decide)
      mtFiber20ReverseSingleStep63
  change mtFiber20StateAt 63 ∈ closeChainFiber mtWord mtFiber20DirectStates (3 + 61) [mtFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber20DirectStates 3 61 [mtFiber20StateAt 0] (mtFiber20StateAt 63) h3

theorem mtFiber20DirectConnected :
    chainFiberConnected mtWord mtFiber20DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber20DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber20State0_in_close
  · subst state
    exact mtFiber20State1_in_close
  · subst state
    exact mtFiber20State2_in_close
  · subst state
    exact mtFiber20State3_in_close
  · subst state
    exact mtFiber20State4_in_close
  · subst state
    exact mtFiber20State5_in_close
  · subst state
    exact mtFiber20State6_in_close
  · subst state
    exact mtFiber20State7_in_close
  · subst state
    exact mtFiber20State8_in_close
  · subst state
    exact mtFiber20State9_in_close
  · subst state
    exact mtFiber20State10_in_close
  · subst state
    exact mtFiber20State11_in_close
  · subst state
    exact mtFiber20State12_in_close
  · subst state
    exact mtFiber20State13_in_close
  · subst state
    exact mtFiber20State14_in_close
  · subst state
    exact mtFiber20State15_in_close
  · subst state
    exact mtFiber20State16_in_close
  · subst state
    exact mtFiber20State17_in_close
  · subst state
    exact mtFiber20State18_in_close
  · subst state
    exact mtFiber20State19_in_close
  · subst state
    exact mtFiber20State20_in_close
  · subst state
    exact mtFiber20State21_in_close
  · subst state
    exact mtFiber20State22_in_close
  · subst state
    exact mtFiber20State23_in_close
  · subst state
    exact mtFiber20State24_in_close
  · subst state
    exact mtFiber20State25_in_close
  · subst state
    exact mtFiber20State26_in_close
  · subst state
    exact mtFiber20State27_in_close
  · subst state
    exact mtFiber20State28_in_close
  · subst state
    exact mtFiber20State29_in_close
  · subst state
    exact mtFiber20State30_in_close
  · subst state
    exact mtFiber20State31_in_close
  · subst state
    exact mtFiber20State32_in_close
  · subst state
    exact mtFiber20State33_in_close
  · subst state
    exact mtFiber20State34_in_close
  · subst state
    exact mtFiber20State35_in_close
  · subst state
    exact mtFiber20State36_in_close
  · subst state
    exact mtFiber20State37_in_close
  · subst state
    exact mtFiber20State38_in_close
  · subst state
    exact mtFiber20State39_in_close
  · subst state
    exact mtFiber20State40_in_close
  · subst state
    exact mtFiber20State41_in_close
  · subst state
    exact mtFiber20State42_in_close
  · subst state
    exact mtFiber20State43_in_close
  · subst state
    exact mtFiber20State44_in_close
  · subst state
    exact mtFiber20State45_in_close
  · subst state
    exact mtFiber20State46_in_close
  · subst state
    exact mtFiber20State47_in_close
  · subst state
    exact mtFiber20State48_in_close
  · subst state
    exact mtFiber20State49_in_close
  · subst state
    exact mtFiber20State50_in_close
  · subst state
    exact mtFiber20State51_in_close
  · subst state
    exact mtFiber20State52_in_close
  · subst state
    exact mtFiber20State53_in_close
  · subst state
    exact mtFiber20State54_in_close
  · subst state
    exact mtFiber20State55_in_close
  · subst state
    exact mtFiber20State56_in_close
  · subst state
    exact mtFiber20State57_in_close
  · subst state
    exact mtFiber20State58_in_close
  · subst state
    exact mtFiber20State59_in_close
  · subst state
    exact mtFiber20State60_in_close
  · subst state
    exact mtFiber20State61_in_close
  · subst state
    exact mtFiber20State62_in_close
  · subst state
    exact mtFiber20State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
