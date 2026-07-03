import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 60

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber60StateAt (i : Nat) : List TauState :=
  directStates (mtFiber60RowAt i).sourceLeft (mtFiber60RowAt i).sourceRight

def mtFiber60DirectStates : List (List TauState) :=
  [mtFiber60StateAt 0, mtFiber60StateAt 1, mtFiber60StateAt 2, mtFiber60StateAt 3, mtFiber60StateAt 4, mtFiber60StateAt 5, mtFiber60StateAt 6, mtFiber60StateAt 7, mtFiber60StateAt 8, mtFiber60StateAt 9, mtFiber60StateAt 10, mtFiber60StateAt 11, mtFiber60StateAt 12, mtFiber60StateAt 13, mtFiber60StateAt 14, mtFiber60StateAt 15, mtFiber60StateAt 16, mtFiber60StateAt 17, mtFiber60StateAt 18, mtFiber60StateAt 19, mtFiber60StateAt 20, mtFiber60StateAt 21, mtFiber60StateAt 22, mtFiber60StateAt 23, mtFiber60StateAt 24, mtFiber60StateAt 25, mtFiber60StateAt 26, mtFiber60StateAt 27, mtFiber60StateAt 28, mtFiber60StateAt 29, mtFiber60StateAt 30, mtFiber60StateAt 31, mtFiber60StateAt 32, mtFiber60StateAt 33, mtFiber60StateAt 34, mtFiber60StateAt 35, mtFiber60StateAt 36, mtFiber60StateAt 37, mtFiber60StateAt 38, mtFiber60StateAt 39, mtFiber60StateAt 40, mtFiber60StateAt 41, mtFiber60StateAt 42, mtFiber60StateAt 43, mtFiber60StateAt 44, mtFiber60StateAt 45, mtFiber60StateAt 46, mtFiber60StateAt 47, mtFiber60StateAt 48, mtFiber60StateAt 49, mtFiber60StateAt 50, mtFiber60StateAt 51, mtFiber60StateAt 52, mtFiber60StateAt 53, mtFiber60StateAt 54, mtFiber60StateAt 55, mtFiber60StateAt 56, mtFiber60StateAt 57, mtFiber60StateAt 58, mtFiber60StateAt 59, mtFiber60StateAt 60, mtFiber60StateAt 61, mtFiber60StateAt 62, mtFiber60StateAt 63]

theorem mtFiber60ReverseRow_1_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk0_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 0) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 1)
    (mtFiber60RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 1) (by decide) mtFiber60ReverseRow_1_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_2_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk1_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 2) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 2)
    (mtFiber60RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 2) (by decide) mtFiber60ReverseRow_2_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_3_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk1_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 2) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 3)
    (mtFiber60RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 3) (by decide) mtFiber60ReverseRow_3_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_4_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk2_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 4) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 4)
    (mtFiber60RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 4) (by decide) mtFiber60ReverseRow_4_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_5_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk2_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 4) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 5)
    (mtFiber60RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 5) (by decide) mtFiber60ReverseRow_5_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_6_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk3_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 6) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 6)
    (mtFiber60RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 6) (by decide) mtFiber60ReverseRow_6_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_7_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk3_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 6) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 7)
    (mtFiber60RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 7) (by decide) mtFiber60ReverseRow_7_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_8_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk4_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 8) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 8)
    (mtFiber60RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 8) (by decide) mtFiber60ReverseRow_8_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_9_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk4_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 8) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 9)
    (mtFiber60RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 9) (by decide) mtFiber60ReverseRow_9_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_10_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk5_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 10) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 10)
    (mtFiber60RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 10) (by decide) mtFiber60ReverseRow_10_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_11_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk5_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 10) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 3) (mtFiber60StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 3) (mtFiber60StateAt 11)
    (mtFiber60RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 11) (by decide) mtFiber60ReverseRow_11_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_12_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk6_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 12) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 4) (mtFiber60StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 4) (mtFiber60StateAt 12)
    (mtFiber60RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 12) (by decide) mtFiber60ReverseRow_12_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_13_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk6_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 12) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 5) (mtFiber60StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 5) (mtFiber60StateAt 13)
    (mtFiber60RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 13) (by decide) mtFiber60ReverseRow_13_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_14_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk7_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 14) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 6) (mtFiber60StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 6) (mtFiber60StateAt 14)
    (mtFiber60RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 14) (by decide) mtFiber60ReverseRow_14_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_15_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk7_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 14) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 15)
    (mtFiber60RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 15) (by decide) mtFiber60ReverseRow_15_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_16_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk8_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 16) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 8) (mtFiber60StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 8) (mtFiber60StateAt 16)
    (mtFiber60RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 16) (by decide) mtFiber60ReverseRow_16_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_17_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk8_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 16) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 9) (mtFiber60StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 9) (mtFiber60StateAt 17)
    (mtFiber60RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 17) (by decide) mtFiber60ReverseRow_17_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_18_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk9_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 18) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 10) (mtFiber60StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 10) (mtFiber60StateAt 18)
    (mtFiber60RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 18) (by decide) mtFiber60ReverseRow_18_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_19_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk9_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 18) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 11) (mtFiber60StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 11) (mtFiber60StateAt 19)
    (mtFiber60RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 19) (by decide) mtFiber60ReverseRow_19_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_20_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk10_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 20) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 12) (mtFiber60StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 12) (mtFiber60StateAt 20)
    (mtFiber60RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 20) (by decide) mtFiber60ReverseRow_20_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_21_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk10_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 20) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 13) (mtFiber60StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 13) (mtFiber60StateAt 21)
    (mtFiber60RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 21) (by decide) mtFiber60ReverseRow_21_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_22_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk11_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 22) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 14) (mtFiber60StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 14) (mtFiber60StateAt 22)
    (mtFiber60RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 22) (by decide) mtFiber60ReverseRow_22_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_23_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk11_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 22) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 15) (mtFiber60StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 15) (mtFiber60StateAt 23)
    (mtFiber60RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 23) (by decide) mtFiber60ReverseRow_23_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_24_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk12_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 24) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 24)
    (mtFiber60RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 24) (by decide) mtFiber60ReverseRow_24_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_25_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk12_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 24) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 25)
    (mtFiber60RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 25) (by decide) mtFiber60ReverseRow_25_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_26_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk13_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 26) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 26)
    (mtFiber60RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 26) (by decide) mtFiber60ReverseRow_26_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_27_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk13_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 26) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 3) (mtFiber60StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 3) (mtFiber60StateAt 27)
    (mtFiber60RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 27) (by decide) mtFiber60ReverseRow_27_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_28_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk14_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 28) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 4) (mtFiber60StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 4) (mtFiber60StateAt 28)
    (mtFiber60RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 28) (by decide) mtFiber60ReverseRow_28_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_29_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk14_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 28) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 5) (mtFiber60StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 5) (mtFiber60StateAt 29)
    (mtFiber60RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 29) (by decide) mtFiber60ReverseRow_29_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_30_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk15_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 30) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 6) (mtFiber60StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 6) (mtFiber60StateAt 30)
    (mtFiber60RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 30) (by decide) mtFiber60ReverseRow_30_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_31_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk15_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 30) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 31)
    (mtFiber60RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 31) (by decide) mtFiber60ReverseRow_31_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_32_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk16_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 32) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 0) (mtFiber60StateAt 32)
    (mtFiber60RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 32) (by decide) mtFiber60ReverseRow_32_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_33_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk16_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 32) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 1) (mtFiber60StateAt 33)
    (mtFiber60RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 33) (by decide) mtFiber60ReverseRow_33_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_34_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk17_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 34) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 2) (mtFiber60StateAt 34)
    (mtFiber60RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 34) (by decide) mtFiber60ReverseRow_34_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_35_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk17_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 34) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 3) (mtFiber60StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 3) (mtFiber60StateAt 35)
    (mtFiber60RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 35) (by decide) mtFiber60ReverseRow_35_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_36_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk18_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 36) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 32) (mtFiber60StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 32) (mtFiber60StateAt 36)
    (mtFiber60RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 36) (by decide) mtFiber60ReverseRow_36_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_37_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk18_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 36) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 33) (mtFiber60StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 33) (mtFiber60StateAt 37)
    (mtFiber60RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 37) (by decide) mtFiber60ReverseRow_37_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_38_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk19_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 38) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 6) (mtFiber60StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 6) (mtFiber60StateAt 38)
    (mtFiber60RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 38) (by decide) mtFiber60ReverseRow_38_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_39_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk19_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 38) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 7) (mtFiber60StateAt 39)
    (mtFiber60RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 39) (by decide) mtFiber60ReverseRow_39_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_40_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk20_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 40) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 8) (mtFiber60StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 8) (mtFiber60StateAt 40)
    (mtFiber60RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 40) (by decide) mtFiber60ReverseRow_40_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_41_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk20_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 40) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 9) (mtFiber60StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 9) (mtFiber60StateAt 41)
    (mtFiber60RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 41) (by decide) mtFiber60ReverseRow_41_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_42_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk21_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 42) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 10) (mtFiber60StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 10) (mtFiber60StateAt 42)
    (mtFiber60RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 42) (by decide) mtFiber60ReverseRow_42_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_43_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk21_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 42) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 11) (mtFiber60StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 11) (mtFiber60StateAt 43)
    (mtFiber60RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 43) (by decide) mtFiber60ReverseRow_43_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_44_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk22_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 44) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 40) (mtFiber60StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 40) (mtFiber60StateAt 44)
    (mtFiber60RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 44) (by decide) mtFiber60ReverseRow_44_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_45_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk22_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 44) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 41) (mtFiber60StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 41) (mtFiber60StateAt 45)
    (mtFiber60RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 45) (by decide) mtFiber60ReverseRow_45_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_46_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk23_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 46) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 14) (mtFiber60StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 14) (mtFiber60StateAt 46)
    (mtFiber60RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 46) (by decide) mtFiber60ReverseRow_46_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_47_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk23_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 46) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 15) (mtFiber60StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 15) (mtFiber60StateAt 47)
    (mtFiber60RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 47) (by decide) mtFiber60ReverseRow_47_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_48_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk24_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 48) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 32) (mtFiber60StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 32) (mtFiber60StateAt 48)
    (mtFiber60RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 48) (by decide) mtFiber60ReverseRow_48_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_49_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk24_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 48) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 33) (mtFiber60StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 33) (mtFiber60StateAt 49)
    (mtFiber60RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 49) (by decide) mtFiber60ReverseRow_49_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_50_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk25_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 50) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 34) (mtFiber60StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 34) (mtFiber60StateAt 50)
    (mtFiber60RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 50) (by decide) mtFiber60ReverseRow_50_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_51_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk25_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 50) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 35) (mtFiber60StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 35) (mtFiber60StateAt 51)
    (mtFiber60RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 51) (by decide) mtFiber60ReverseRow_51_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_52_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk26_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 52) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 36) (mtFiber60StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 36) (mtFiber60StateAt 52)
    (mtFiber60RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 52) (by decide) mtFiber60ReverseRow_52_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_53_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk26_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 52) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 37) (mtFiber60StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 37) (mtFiber60StateAt 53)
    (mtFiber60RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 53) (by decide) mtFiber60ReverseRow_53_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_54_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk27_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 54) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 38) (mtFiber60StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 38) (mtFiber60StateAt 54)
    (mtFiber60RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 54) (by decide) mtFiber60ReverseRow_54_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_55_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk27_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 54) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 39) (mtFiber60StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 39) (mtFiber60StateAt 55)
    (mtFiber60RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 55) (by decide) mtFiber60ReverseRow_55_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_56_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk28_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 56) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 24) (mtFiber60StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 24) (mtFiber60StateAt 56)
    (mtFiber60RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 56) (by decide) mtFiber60ReverseRow_56_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_57_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk28_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 56) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 25) (mtFiber60StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 25) (mtFiber60StateAt 57)
    (mtFiber60RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 57) (by decide) mtFiber60ReverseRow_57_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_58_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk29_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 58) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 26) (mtFiber60StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 26) (mtFiber60StateAt 58)
    (mtFiber60RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 58) (by decide) mtFiber60ReverseRow_58_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_59_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk29_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 58) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 27) (mtFiber60StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 27) (mtFiber60StateAt 59)
    (mtFiber60RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 59) (by decide) mtFiber60ReverseRow_59_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_60_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk30_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 60) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 56) (mtFiber60StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 56) (mtFiber60StateAt 60)
    (mtFiber60RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 60) (by decide) mtFiber60ReverseRow_60_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_61_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk30_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 60) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 57) (mtFiber60StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 57) (mtFiber60StateAt 61)
    (mtFiber60RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 61) (by decide) mtFiber60ReverseRow_61_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_62_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk31_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 62) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber60ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 30) (mtFiber60StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 30) (mtFiber60StateAt 62)
    (mtFiber60RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 62) (by decide) mtFiber60ReverseRow_62_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60ReverseRow_63_ok :
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber60Chunk31_ok
  change (mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 62) &&
    mtRowReverseValid mtFiber60Key mtFiber60Expected (mtFiber60RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber60ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber60StateAt 31) (mtFiber60StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber60StateAt 31) (mtFiber60StateAt 63)
    (mtFiber60RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber60Key mtFiber60Expected
        (mtFiber60RowAt 63) (by decide) mtFiber60ReverseRow_63_ok
      simpa [mtFiber60StateAt, mtFiber60RowAt, mtFiber60Rows, listGetD, directRow] using h)

theorem mtFiber60State0_in_close :
    mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  change mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 64 [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 0 64 [mtFiber60StateAt 0] (mtFiber60StateAt 0) (by simp [closeChainFiber])

theorem mtFiber60State1_in_close :
    mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  change mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates (1 + 63) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 1 63 [mtFiber60StateAt 0] (mtFiber60StateAt 1) h1

theorem mtFiber60State2_in_close :
    mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  change mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates (1 + 63) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 1 63 [mtFiber60StateAt 0] (mtFiber60StateAt 2) h1

theorem mtFiber60State3_in_close :
    mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  change mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 3) h2

theorem mtFiber60State4_in_close :
    mtFiber60StateAt 4 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 4 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 4) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep4
  change mtFiber60StateAt 4 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 4) h2

theorem mtFiber60State5_in_close :
    mtFiber60StateAt 5 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 5 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 5) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep5
  change mtFiber60StateAt 5 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 5) h2

theorem mtFiber60State6_in_close :
    mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  change mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 6) h2

theorem mtFiber60State7_in_close :
    mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  change mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates (1 + 63) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 1 63 [mtFiber60StateAt 0] (mtFiber60StateAt 7) h1

theorem mtFiber60State8_in_close :
    mtFiber60StateAt 8 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 8 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 8) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep8
  change mtFiber60StateAt 8 ∈ closeChainFiber mtWord mtFiber60DirectStates (1 + 63) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 1 63 [mtFiber60StateAt 0] (mtFiber60StateAt 8) h1

theorem mtFiber60State9_in_close :
    mtFiber60StateAt 9 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 9 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 9) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep9
  change mtFiber60StateAt 9 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 9) h2

theorem mtFiber60State10_in_close :
    mtFiber60StateAt 10 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 10 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 10) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep10
  change mtFiber60StateAt 10 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 10) h2

theorem mtFiber60State11_in_close :
    mtFiber60StateAt 11 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  have h3 : mtFiber60StateAt 11 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 3) (mtFiber60StateAt 11) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep11
  change mtFiber60StateAt 11 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 11) h3

theorem mtFiber60State12_in_close :
    mtFiber60StateAt 12 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 4 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 4) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep4
  have h3 : mtFiber60StateAt 12 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 4) (mtFiber60StateAt 12) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep12
  change mtFiber60StateAt 12 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 12) h3

theorem mtFiber60State13_in_close :
    mtFiber60StateAt 13 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 5 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 5) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep5
  have h3 : mtFiber60StateAt 13 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 5) (mtFiber60StateAt 13) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep13
  change mtFiber60StateAt 13 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 13) h3

theorem mtFiber60State14_in_close :
    mtFiber60StateAt 14 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  have h3 : mtFiber60StateAt 14 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 6) (mtFiber60StateAt 14) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep14
  change mtFiber60StateAt 14 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 14) h3

theorem mtFiber60State15_in_close :
    mtFiber60StateAt 15 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 15 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 15) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep15
  change mtFiber60StateAt 15 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 15) h2

theorem mtFiber60State16_in_close :
    mtFiber60StateAt 16 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 8 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 8) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep8
  have h2 : mtFiber60StateAt 16 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 8) (mtFiber60StateAt 16) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep16
  change mtFiber60StateAt 16 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 16) h2

theorem mtFiber60State17_in_close :
    mtFiber60StateAt 17 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 9 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 9) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep9
  have h3 : mtFiber60StateAt 17 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 9) (mtFiber60StateAt 17) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep17
  change mtFiber60StateAt 17 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 17) h3

theorem mtFiber60State18_in_close :
    mtFiber60StateAt 18 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 10 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 10) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep10
  have h3 : mtFiber60StateAt 18 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 10) (mtFiber60StateAt 18) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep18
  change mtFiber60StateAt 18 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 18) h3

theorem mtFiber60State19_in_close :
    mtFiber60StateAt 19 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  have h3 : mtFiber60StateAt 11 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 3) (mtFiber60StateAt 11) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep11
  have h4 : mtFiber60StateAt 19 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 11) (mtFiber60StateAt 19) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep19
  change mtFiber60StateAt 19 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 19) h4

theorem mtFiber60State20_in_close :
    mtFiber60StateAt 20 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 4 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 4) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep4
  have h3 : mtFiber60StateAt 12 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 4) (mtFiber60StateAt 12) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep12
  have h4 : mtFiber60StateAt 20 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 12) (mtFiber60StateAt 20) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep20
  change mtFiber60StateAt 20 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 20) h4

theorem mtFiber60State21_in_close :
    mtFiber60StateAt 21 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 5 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 5) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep5
  have h3 : mtFiber60StateAt 13 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 5) (mtFiber60StateAt 13) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep13
  have h4 : mtFiber60StateAt 21 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 13) (mtFiber60StateAt 21) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep21
  change mtFiber60StateAt 21 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 21) h4

theorem mtFiber60State22_in_close :
    mtFiber60StateAt 22 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  have h3 : mtFiber60StateAt 14 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 6) (mtFiber60StateAt 14) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep14
  have h4 : mtFiber60StateAt 22 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 14) (mtFiber60StateAt 22) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep22
  change mtFiber60StateAt 22 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 22) h4

theorem mtFiber60State23_in_close :
    mtFiber60StateAt 23 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 15 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 15) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep15
  have h3 : mtFiber60StateAt 23 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 15) (mtFiber60StateAt 23) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep23
  change mtFiber60StateAt 23 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 23) h3

theorem mtFiber60State24_in_close :
    mtFiber60StateAt 24 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 24 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 24) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep24
  change mtFiber60StateAt 24 ∈ closeChainFiber mtWord mtFiber60DirectStates (1 + 63) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 1 63 [mtFiber60StateAt 0] (mtFiber60StateAt 24) h1

theorem mtFiber60State25_in_close :
    mtFiber60StateAt 25 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 25 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 25) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep25
  change mtFiber60StateAt 25 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 25) h2

theorem mtFiber60State26_in_close :
    mtFiber60StateAt 26 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 26 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 26) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep26
  change mtFiber60StateAt 26 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 26) h2

theorem mtFiber60State27_in_close :
    mtFiber60StateAt 27 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  have h3 : mtFiber60StateAt 27 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 3) (mtFiber60StateAt 27) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep27
  change mtFiber60StateAt 27 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 27) h3

theorem mtFiber60State28_in_close :
    mtFiber60StateAt 28 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 4 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 4) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep4
  have h3 : mtFiber60StateAt 28 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 4) (mtFiber60StateAt 28) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep28
  change mtFiber60StateAt 28 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 28) h3

theorem mtFiber60State29_in_close :
    mtFiber60StateAt 29 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 5 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 5) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep5
  have h3 : mtFiber60StateAt 29 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 5) (mtFiber60StateAt 29) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep29
  change mtFiber60StateAt 29 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 29) h3

theorem mtFiber60State30_in_close :
    mtFiber60StateAt 30 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  have h3 : mtFiber60StateAt 30 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 6) (mtFiber60StateAt 30) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep30
  change mtFiber60StateAt 30 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 30) h3

theorem mtFiber60State31_in_close :
    mtFiber60StateAt 31 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 31 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 31) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep31
  change mtFiber60StateAt 31 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 31) h2

theorem mtFiber60State32_in_close :
    mtFiber60StateAt 32 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 32 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 32) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep32
  change mtFiber60StateAt 32 ∈ closeChainFiber mtWord mtFiber60DirectStates (1 + 63) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 1 63 [mtFiber60StateAt 0] (mtFiber60StateAt 32) h1

theorem mtFiber60State33_in_close :
    mtFiber60StateAt 33 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 33 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 33) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep33
  change mtFiber60StateAt 33 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 33) h2

theorem mtFiber60State34_in_close :
    mtFiber60StateAt 34 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 34 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 34) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep34
  change mtFiber60StateAt 34 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 34) h2

theorem mtFiber60State35_in_close :
    mtFiber60StateAt 35 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  have h3 : mtFiber60StateAt 35 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 3) (mtFiber60StateAt 35) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep35
  change mtFiber60StateAt 35 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 35) h3

theorem mtFiber60State36_in_close :
    mtFiber60StateAt 36 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 32 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 32) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep32
  have h2 : mtFiber60StateAt 36 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 32) (mtFiber60StateAt 36) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep36
  change mtFiber60StateAt 36 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 36) h2

theorem mtFiber60State37_in_close :
    mtFiber60StateAt 37 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 33 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 33) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep33
  have h3 : mtFiber60StateAt 37 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 33) (mtFiber60StateAt 37) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep37
  change mtFiber60StateAt 37 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 37) h3

theorem mtFiber60State38_in_close :
    mtFiber60StateAt 38 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  have h3 : mtFiber60StateAt 38 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 6) (mtFiber60StateAt 38) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep38
  change mtFiber60StateAt 38 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 38) h3

theorem mtFiber60State39_in_close :
    mtFiber60StateAt 39 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 39 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 39) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep39
  change mtFiber60StateAt 39 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 39) h2

theorem mtFiber60State40_in_close :
    mtFiber60StateAt 40 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 8 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 8) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep8
  have h2 : mtFiber60StateAt 40 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 8) (mtFiber60StateAt 40) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep40
  change mtFiber60StateAt 40 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 40) h2

theorem mtFiber60State41_in_close :
    mtFiber60StateAt 41 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 9 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 9) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep9
  have h3 : mtFiber60StateAt 41 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 9) (mtFiber60StateAt 41) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep41
  change mtFiber60StateAt 41 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 41) h3

theorem mtFiber60State42_in_close :
    mtFiber60StateAt 42 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 10 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 10) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep10
  have h3 : mtFiber60StateAt 42 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 10) (mtFiber60StateAt 42) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep42
  change mtFiber60StateAt 42 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 42) h3

theorem mtFiber60State43_in_close :
    mtFiber60StateAt 43 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  have h3 : mtFiber60StateAt 11 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 3) (mtFiber60StateAt 11) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep11
  have h4 : mtFiber60StateAt 43 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 11) (mtFiber60StateAt 43) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep43
  change mtFiber60StateAt 43 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 43) h4

theorem mtFiber60State44_in_close :
    mtFiber60StateAt 44 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 8 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 8) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep8
  have h2 : mtFiber60StateAt 40 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 8) (mtFiber60StateAt 40) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep40
  have h3 : mtFiber60StateAt 44 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 40) (mtFiber60StateAt 44) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep44
  change mtFiber60StateAt 44 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 44) h3

theorem mtFiber60State45_in_close :
    mtFiber60StateAt 45 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 9 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 9) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep9
  have h3 : mtFiber60StateAt 41 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 9) (mtFiber60StateAt 41) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep41
  have h4 : mtFiber60StateAt 45 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 41) (mtFiber60StateAt 45) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep45
  change mtFiber60StateAt 45 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 45) h4

theorem mtFiber60State46_in_close :
    mtFiber60StateAt 46 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  have h3 : mtFiber60StateAt 14 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 6) (mtFiber60StateAt 14) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep14
  have h4 : mtFiber60StateAt 46 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 14) (mtFiber60StateAt 46) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep46
  change mtFiber60StateAt 46 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 46) h4

theorem mtFiber60State47_in_close :
    mtFiber60StateAt 47 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 15 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 15) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep15
  have h3 : mtFiber60StateAt 47 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 15) (mtFiber60StateAt 47) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep47
  change mtFiber60StateAt 47 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 47) h3

theorem mtFiber60State48_in_close :
    mtFiber60StateAt 48 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 32 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 32) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep32
  have h2 : mtFiber60StateAt 48 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 32) (mtFiber60StateAt 48) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep48
  change mtFiber60StateAt 48 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 48) h2

theorem mtFiber60State49_in_close :
    mtFiber60StateAt 49 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 33 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 33) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep33
  have h3 : mtFiber60StateAt 49 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 33) (mtFiber60StateAt 49) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep49
  change mtFiber60StateAt 49 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 49) h3

theorem mtFiber60State50_in_close :
    mtFiber60StateAt 50 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 34 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 34) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep34
  have h3 : mtFiber60StateAt 50 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 34) (mtFiber60StateAt 50) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep50
  change mtFiber60StateAt 50 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 50) h3

theorem mtFiber60State51_in_close :
    mtFiber60StateAt 51 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  have h3 : mtFiber60StateAt 35 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 3) (mtFiber60StateAt 35) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep35
  have h4 : mtFiber60StateAt 51 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 35) (mtFiber60StateAt 51) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep51
  change mtFiber60StateAt 51 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 51) h4

theorem mtFiber60State52_in_close :
    mtFiber60StateAt 52 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 32 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 32) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep32
  have h2 : mtFiber60StateAt 36 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 32) (mtFiber60StateAt 36) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep36
  have h3 : mtFiber60StateAt 52 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 36) (mtFiber60StateAt 52) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep52
  change mtFiber60StateAt 52 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 52) h3

theorem mtFiber60State53_in_close :
    mtFiber60StateAt 53 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 33 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 33) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep33
  have h3 : mtFiber60StateAt 37 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 33) (mtFiber60StateAt 37) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep37
  have h4 : mtFiber60StateAt 53 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 37) (mtFiber60StateAt 53) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep53
  change mtFiber60StateAt 53 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 53) h4

theorem mtFiber60State54_in_close :
    mtFiber60StateAt 54 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  have h3 : mtFiber60StateAt 38 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 6) (mtFiber60StateAt 38) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep38
  have h4 : mtFiber60StateAt 54 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 38) (mtFiber60StateAt 54) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep54
  change mtFiber60StateAt 54 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 54) h4

theorem mtFiber60State55_in_close :
    mtFiber60StateAt 55 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 39 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 39) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep39
  have h3 : mtFiber60StateAt 55 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 39) (mtFiber60StateAt 55) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep55
  change mtFiber60StateAt 55 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 55) h3

theorem mtFiber60State56_in_close :
    mtFiber60StateAt 56 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 24 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 24) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep24
  have h2 : mtFiber60StateAt 56 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 24) (mtFiber60StateAt 56) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep56
  change mtFiber60StateAt 56 ∈ closeChainFiber mtWord mtFiber60DirectStates (2 + 62) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 2 62 [mtFiber60StateAt 0] (mtFiber60StateAt 56) h2

theorem mtFiber60State57_in_close :
    mtFiber60StateAt 57 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 25 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 25) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep25
  have h3 : mtFiber60StateAt 57 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 25) (mtFiber60StateAt 57) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep57
  change mtFiber60StateAt 57 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 57) h3

theorem mtFiber60State58_in_close :
    mtFiber60StateAt 58 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 2 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 2) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep2
  have h2 : mtFiber60StateAt 26 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 2) (mtFiber60StateAt 26) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep26
  have h3 : mtFiber60StateAt 58 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 26) (mtFiber60StateAt 58) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep58
  change mtFiber60StateAt 58 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 58) h3

theorem mtFiber60State59_in_close :
    mtFiber60StateAt 59 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 3 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 3) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep3
  have h3 : mtFiber60StateAt 27 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 3) (mtFiber60StateAt 27) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep27
  have h4 : mtFiber60StateAt 59 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 27) (mtFiber60StateAt 59) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep59
  change mtFiber60StateAt 59 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 59) h4

theorem mtFiber60State60_in_close :
    mtFiber60StateAt 60 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 24 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 24) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep24
  have h2 : mtFiber60StateAt 56 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 24) (mtFiber60StateAt 56) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep56
  have h3 : mtFiber60StateAt 60 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 56) (mtFiber60StateAt 60) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep60
  change mtFiber60StateAt 60 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 60) h3

theorem mtFiber60State61_in_close :
    mtFiber60StateAt 61 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 25 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 25) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep25
  have h3 : mtFiber60StateAt 57 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 25) (mtFiber60StateAt 57) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep57
  have h4 : mtFiber60StateAt 61 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 57) (mtFiber60StateAt 61) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep61
  change mtFiber60StateAt 61 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 61) h4

theorem mtFiber60State62_in_close :
    mtFiber60StateAt 62 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 1 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 1) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep1
  have h2 : mtFiber60StateAt 6 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 1) (mtFiber60StateAt 6) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep6
  have h3 : mtFiber60StateAt 30 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 6) (mtFiber60StateAt 30) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep30
  have h4 : mtFiber60StateAt 62 ∈ closeChainFiber mtWord mtFiber60DirectStates 4 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0]
      (mtFiber60StateAt 30) (mtFiber60StateAt 62) (by decide) h3 (by decide)
      mtFiber60ReverseSingleStep62
  change mtFiber60StateAt 62 ∈ closeChainFiber mtWord mtFiber60DirectStates (4 + 60) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 4 60 [mtFiber60StateAt 0] (mtFiber60StateAt 62) h4

theorem mtFiber60State63_in_close :
    mtFiber60StateAt 63 ∈ closeChainFiber mtWord mtFiber60DirectStates mtFiber60DirectStates.length [mtFiber60StateAt 0] := by
  have h0 : mtFiber60StateAt 0 ∈ closeChainFiber mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber60StateAt 7 ∈ closeChainFiber mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 0 [mtFiber60StateAt 0]
      (mtFiber60StateAt 0) (mtFiber60StateAt 7) (by decide) h0 (by decide)
      mtFiber60ReverseSingleStep7
  have h2 : mtFiber60StateAt 31 ∈ closeChainFiber mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 1 [mtFiber60StateAt 0]
      (mtFiber60StateAt 7) (mtFiber60StateAt 31) (by decide) h1 (by decide)
      mtFiber60ReverseSingleStep31
  have h3 : mtFiber60StateAt 63 ∈ closeChainFiber mtWord mtFiber60DirectStates 3 [mtFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber60DirectStates 2 [mtFiber60StateAt 0]
      (mtFiber60StateAt 31) (mtFiber60StateAt 63) (by decide) h2 (by decide)
      mtFiber60ReverseSingleStep63
  change mtFiber60StateAt 63 ∈ closeChainFiber mtWord mtFiber60DirectStates (3 + 61) [mtFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber60DirectStates 3 61 [mtFiber60StateAt 0] (mtFiber60StateAt 63) h3

theorem mtFiber60DirectConnected :
    chainFiberConnected mtWord mtFiber60DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber60DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber60State0_in_close
  · subst state
    exact mtFiber60State1_in_close
  · subst state
    exact mtFiber60State2_in_close
  · subst state
    exact mtFiber60State3_in_close
  · subst state
    exact mtFiber60State4_in_close
  · subst state
    exact mtFiber60State5_in_close
  · subst state
    exact mtFiber60State6_in_close
  · subst state
    exact mtFiber60State7_in_close
  · subst state
    exact mtFiber60State8_in_close
  · subst state
    exact mtFiber60State9_in_close
  · subst state
    exact mtFiber60State10_in_close
  · subst state
    exact mtFiber60State11_in_close
  · subst state
    exact mtFiber60State12_in_close
  · subst state
    exact mtFiber60State13_in_close
  · subst state
    exact mtFiber60State14_in_close
  · subst state
    exact mtFiber60State15_in_close
  · subst state
    exact mtFiber60State16_in_close
  · subst state
    exact mtFiber60State17_in_close
  · subst state
    exact mtFiber60State18_in_close
  · subst state
    exact mtFiber60State19_in_close
  · subst state
    exact mtFiber60State20_in_close
  · subst state
    exact mtFiber60State21_in_close
  · subst state
    exact mtFiber60State22_in_close
  · subst state
    exact mtFiber60State23_in_close
  · subst state
    exact mtFiber60State24_in_close
  · subst state
    exact mtFiber60State25_in_close
  · subst state
    exact mtFiber60State26_in_close
  · subst state
    exact mtFiber60State27_in_close
  · subst state
    exact mtFiber60State28_in_close
  · subst state
    exact mtFiber60State29_in_close
  · subst state
    exact mtFiber60State30_in_close
  · subst state
    exact mtFiber60State31_in_close
  · subst state
    exact mtFiber60State32_in_close
  · subst state
    exact mtFiber60State33_in_close
  · subst state
    exact mtFiber60State34_in_close
  · subst state
    exact mtFiber60State35_in_close
  · subst state
    exact mtFiber60State36_in_close
  · subst state
    exact mtFiber60State37_in_close
  · subst state
    exact mtFiber60State38_in_close
  · subst state
    exact mtFiber60State39_in_close
  · subst state
    exact mtFiber60State40_in_close
  · subst state
    exact mtFiber60State41_in_close
  · subst state
    exact mtFiber60State42_in_close
  · subst state
    exact mtFiber60State43_in_close
  · subst state
    exact mtFiber60State44_in_close
  · subst state
    exact mtFiber60State45_in_close
  · subst state
    exact mtFiber60State46_in_close
  · subst state
    exact mtFiber60State47_in_close
  · subst state
    exact mtFiber60State48_in_close
  · subst state
    exact mtFiber60State49_in_close
  · subst state
    exact mtFiber60State50_in_close
  · subst state
    exact mtFiber60State51_in_close
  · subst state
    exact mtFiber60State52_in_close
  · subst state
    exact mtFiber60State53_in_close
  · subst state
    exact mtFiber60State54_in_close
  · subst state
    exact mtFiber60State55_in_close
  · subst state
    exact mtFiber60State56_in_close
  · subst state
    exact mtFiber60State57_in_close
  · subst state
    exact mtFiber60State58_in_close
  · subst state
    exact mtFiber60State59_in_close
  · subst state
    exact mtFiber60State60_in_close
  · subst state
    exact mtFiber60State61_in_close
  · subst state
    exact mtFiber60State62_in_close
  · subst state
    exact mtFiber60State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
