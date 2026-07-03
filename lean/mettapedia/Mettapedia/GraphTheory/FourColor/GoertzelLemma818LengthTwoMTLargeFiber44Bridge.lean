import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 44

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber44StateAt (i : Nat) : List TauState :=
  directStates (mtFiber44RowAt i).sourceLeft (mtFiber44RowAt i).sourceRight

def mtFiber44DirectStates : List (List TauState) :=
  [mtFiber44StateAt 0, mtFiber44StateAt 1, mtFiber44StateAt 2, mtFiber44StateAt 3, mtFiber44StateAt 4, mtFiber44StateAt 5, mtFiber44StateAt 6, mtFiber44StateAt 7, mtFiber44StateAt 8, mtFiber44StateAt 9, mtFiber44StateAt 10, mtFiber44StateAt 11, mtFiber44StateAt 12, mtFiber44StateAt 13, mtFiber44StateAt 14, mtFiber44StateAt 15, mtFiber44StateAt 16, mtFiber44StateAt 17, mtFiber44StateAt 18, mtFiber44StateAt 19, mtFiber44StateAt 20, mtFiber44StateAt 21, mtFiber44StateAt 22, mtFiber44StateAt 23, mtFiber44StateAt 24, mtFiber44StateAt 25, mtFiber44StateAt 26, mtFiber44StateAt 27, mtFiber44StateAt 28, mtFiber44StateAt 29, mtFiber44StateAt 30, mtFiber44StateAt 31, mtFiber44StateAt 32, mtFiber44StateAt 33, mtFiber44StateAt 34, mtFiber44StateAt 35, mtFiber44StateAt 36, mtFiber44StateAt 37, mtFiber44StateAt 38, mtFiber44StateAt 39, mtFiber44StateAt 40, mtFiber44StateAt 41, mtFiber44StateAt 42, mtFiber44StateAt 43, mtFiber44StateAt 44, mtFiber44StateAt 45, mtFiber44StateAt 46, mtFiber44StateAt 47, mtFiber44StateAt 48, mtFiber44StateAt 49, mtFiber44StateAt 50, mtFiber44StateAt 51, mtFiber44StateAt 52, mtFiber44StateAt 53, mtFiber44StateAt 54, mtFiber44StateAt 55, mtFiber44StateAt 56, mtFiber44StateAt 57, mtFiber44StateAt 58, mtFiber44StateAt 59, mtFiber44StateAt 60, mtFiber44StateAt 61, mtFiber44StateAt 62, mtFiber44StateAt 63]

theorem mtFiber44ReverseRow_1_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk0_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 0) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 1)
    (mtFiber44RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 1) (by decide) mtFiber44ReverseRow_1_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_2_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk1_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 2) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 2)
    (mtFiber44RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 2) (by decide) mtFiber44ReverseRow_2_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_3_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk1_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 2) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 3)
    (mtFiber44RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 3) (by decide) mtFiber44ReverseRow_3_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_4_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk2_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 4) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 4)
    (mtFiber44RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 4) (by decide) mtFiber44ReverseRow_4_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_5_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk2_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 4) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 5)
    (mtFiber44RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 5) (by decide) mtFiber44ReverseRow_5_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_6_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk3_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 6) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 6)
    (mtFiber44RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 6) (by decide) mtFiber44ReverseRow_6_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_7_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk3_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 6) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 7)
    (mtFiber44RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 7) (by decide) mtFiber44ReverseRow_7_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_8_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk4_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 8) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 8)
    (mtFiber44RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 8) (by decide) mtFiber44ReverseRow_8_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_9_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk4_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 8) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 9)
    (mtFiber44RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 9) (by decide) mtFiber44ReverseRow_9_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_10_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk5_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 10) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 2) (mtFiber44StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 2) (mtFiber44StateAt 10)
    (mtFiber44RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 10) (by decide) mtFiber44ReverseRow_10_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_11_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk5_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 10) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 11)
    (mtFiber44RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 11) (by decide) mtFiber44ReverseRow_11_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_12_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk6_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 12) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 12)
    (mtFiber44RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 12) (by decide) mtFiber44ReverseRow_12_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_13_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk6_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 12) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 5) (mtFiber44StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 5) (mtFiber44StateAt 13)
    (mtFiber44RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 13) (by decide) mtFiber44ReverseRow_13_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_14_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk7_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 14) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 6) (mtFiber44StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 6) (mtFiber44StateAt 14)
    (mtFiber44RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 14) (by decide) mtFiber44ReverseRow_14_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_15_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk7_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 14) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 7) (mtFiber44StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 7) (mtFiber44StateAt 15)
    (mtFiber44RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 15) (by decide) mtFiber44ReverseRow_15_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_16_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk8_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 16) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 16)
    (mtFiber44RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 16) (by decide) mtFiber44ReverseRow_16_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_17_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk8_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 16) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 17)
    (mtFiber44RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 17) (by decide) mtFiber44ReverseRow_17_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_18_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk9_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 18) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 2) (mtFiber44StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 2) (mtFiber44StateAt 18)
    (mtFiber44RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 18) (by decide) mtFiber44ReverseRow_18_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_19_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk9_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 18) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 19)
    (mtFiber44RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 19) (by decide) mtFiber44ReverseRow_19_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_20_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk10_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 20) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 20)
    (mtFiber44RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 20) (by decide) mtFiber44ReverseRow_20_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_21_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk10_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 20) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 5) (mtFiber44StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 5) (mtFiber44StateAt 21)
    (mtFiber44RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 21) (by decide) mtFiber44ReverseRow_21_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_22_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk11_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 22) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 6) (mtFiber44StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 6) (mtFiber44StateAt 22)
    (mtFiber44RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 22) (by decide) mtFiber44ReverseRow_22_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_23_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk11_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 22) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 7) (mtFiber44StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 7) (mtFiber44StateAt 23)
    (mtFiber44RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 23) (by decide) mtFiber44ReverseRow_23_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_24_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk12_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 24) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 8) (mtFiber44StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 8) (mtFiber44StateAt 24)
    (mtFiber44RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 24) (by decide) mtFiber44ReverseRow_24_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_25_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk12_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 24) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 9) (mtFiber44StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 9) (mtFiber44StateAt 25)
    (mtFiber44RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 25) (by decide) mtFiber44ReverseRow_25_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_26_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk13_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 26) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 10) (mtFiber44StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 10) (mtFiber44StateAt 26)
    (mtFiber44RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 26) (by decide) mtFiber44ReverseRow_26_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_27_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk13_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 26) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 11) (mtFiber44StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 11) (mtFiber44StateAt 27)
    (mtFiber44RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 27) (by decide) mtFiber44ReverseRow_27_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_28_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk14_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 28) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 12) (mtFiber44StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 12) (mtFiber44StateAt 28)
    (mtFiber44RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 28) (by decide) mtFiber44ReverseRow_28_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_29_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk14_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 28) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 13) (mtFiber44StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 13) (mtFiber44StateAt 29)
    (mtFiber44RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 29) (by decide) mtFiber44ReverseRow_29_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_30_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk15_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 30) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 14) (mtFiber44StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 14) (mtFiber44StateAt 30)
    (mtFiber44RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 30) (by decide) mtFiber44ReverseRow_30_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_31_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk15_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 30) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 15) (mtFiber44StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 15) (mtFiber44StateAt 31)
    (mtFiber44RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 31) (by decide) mtFiber44ReverseRow_31_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_32_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk16_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 32) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 36) (mtFiber44StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 36) (mtFiber44StateAt 32)
    (mtFiber44RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 32) (by decide) mtFiber44ReverseRow_32_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_33_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk16_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 32) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 37) (mtFiber44StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 37) (mtFiber44StateAt 33)
    (mtFiber44RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 33) (by decide) mtFiber44ReverseRow_33_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_34_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk17_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 34) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 20) (mtFiber44StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 20) (mtFiber44StateAt 34)
    (mtFiber44RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 34) (by decide) mtFiber44ReverseRow_34_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_35_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk17_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 34) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 21) (mtFiber44StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 21) (mtFiber44StateAt 35)
    (mtFiber44RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 35) (by decide) mtFiber44ReverseRow_35_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_36_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk18_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 36) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 16) (mtFiber44StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 16) (mtFiber44StateAt 36)
    (mtFiber44RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 36) (by decide) mtFiber44ReverseRow_36_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_37_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk18_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 36) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 17) (mtFiber44StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 17) (mtFiber44StateAt 37)
    (mtFiber44RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 37) (by decide) mtFiber44ReverseRow_37_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_38_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk19_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 38) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 18) (mtFiber44StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 18) (mtFiber44StateAt 38)
    (mtFiber44RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 38) (by decide) mtFiber44ReverseRow_38_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_39_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk19_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 38) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 19) (mtFiber44StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 19) (mtFiber44StateAt 39)
    (mtFiber44RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 39) (by decide) mtFiber44ReverseRow_39_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_40_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk20_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 40) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 44) (mtFiber44StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 44) (mtFiber44StateAt 40)
    (mtFiber44RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 40) (by decide) mtFiber44ReverseRow_40_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_41_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk20_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 40) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 45) (mtFiber44StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 45) (mtFiber44StateAt 41)
    (mtFiber44RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 41) (by decide) mtFiber44ReverseRow_41_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_42_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk21_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 42) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 58) (mtFiber44StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 58) (mtFiber44StateAt 42)
    (mtFiber44RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 42) (by decide) mtFiber44ReverseRow_42_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_43_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk21_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 42) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 59) (mtFiber44StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 59) (mtFiber44StateAt 43)
    (mtFiber44RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 43) (by decide) mtFiber44ReverseRow_43_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_44_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk22_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 44) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 60) (mtFiber44StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 60) (mtFiber44StateAt 44)
    (mtFiber44RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 44) (by decide) mtFiber44ReverseRow_44_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_45_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk22_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 44) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 61) (mtFiber44StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 61) (mtFiber44StateAt 45)
    (mtFiber44RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 45) (by decide) mtFiber44ReverseRow_45_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_46_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk23_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 46) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 62) (mtFiber44StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 62) (mtFiber44StateAt 46)
    (mtFiber44RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 46) (by decide) mtFiber44ReverseRow_46_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_47_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk23_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 46) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 63) (mtFiber44StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 63) (mtFiber44StateAt 47)
    (mtFiber44RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 47) (by decide) mtFiber44ReverseRow_47_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_48_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk24_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 48) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 52) (mtFiber44StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 52) (mtFiber44StateAt 48)
    (mtFiber44RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 48) (by decide) mtFiber44ReverseRow_48_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_49_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk24_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 48) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 53) (mtFiber44StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 53) (mtFiber44StateAt 49)
    (mtFiber44RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 49) (by decide) mtFiber44ReverseRow_49_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_50_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk25_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 50) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 12) (mtFiber44StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 12) (mtFiber44StateAt 50)
    (mtFiber44RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 50) (by decide) mtFiber44ReverseRow_50_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_51_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk25_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 50) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 13) (mtFiber44StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 13) (mtFiber44StateAt 51)
    (mtFiber44RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 51) (by decide) mtFiber44ReverseRow_51_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_52_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk26_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 52) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 8) (mtFiber44StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 8) (mtFiber44StateAt 52)
    (mtFiber44RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 52) (by decide) mtFiber44ReverseRow_52_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_53_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk26_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 52) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 9) (mtFiber44StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 9) (mtFiber44StateAt 53)
    (mtFiber44RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 53) (by decide) mtFiber44ReverseRow_53_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_54_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk27_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 54) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 10) (mtFiber44StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 10) (mtFiber44StateAt 54)
    (mtFiber44RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 54) (by decide) mtFiber44ReverseRow_54_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_55_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk27_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 54) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 11) (mtFiber44StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 11) (mtFiber44StateAt 55)
    (mtFiber44RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 55) (by decide) mtFiber44ReverseRow_55_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_56_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk28_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 56) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 60) (mtFiber44StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 60) (mtFiber44StateAt 56)
    (mtFiber44RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 56) (by decide) mtFiber44ReverseRow_56_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_57_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk28_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 56) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 61) (mtFiber44StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 61) (mtFiber44StateAt 57)
    (mtFiber44RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 57) (by decide) mtFiber44ReverseRow_57_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_58_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk29_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 58) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 4) (mtFiber44StateAt 58)
    (mtFiber44RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 58) (by decide) mtFiber44ReverseRow_58_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_59_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk29_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 58) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 5) (mtFiber44StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 5) (mtFiber44StateAt 59)
    (mtFiber44RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 59) (by decide) mtFiber44ReverseRow_59_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_60_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk30_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 60) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 0) (mtFiber44StateAt 60)
    (mtFiber44RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 60) (by decide) mtFiber44ReverseRow_60_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_61_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk30_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 60) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 1) (mtFiber44StateAt 61)
    (mtFiber44RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 61) (by decide) mtFiber44ReverseRow_61_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_62_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk31_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 62) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber44ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 2) (mtFiber44StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 2) (mtFiber44StateAt 62)
    (mtFiber44RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 62) (by decide) mtFiber44ReverseRow_62_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44ReverseRow_63_ok :
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber44Chunk31_ok
  change (mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 62) &&
    mtRowReverseValid mtFiber44Key mtFiber44Expected (mtFiber44RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber44ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber44StateAt 3) (mtFiber44StateAt 63)
    (mtFiber44RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber44Key mtFiber44Expected
        (mtFiber44RowAt 63) (by decide) mtFiber44ReverseRow_63_ok
      simpa [mtFiber44StateAt, mtFiber44RowAt, mtFiber44Rows, listGetD, directRow] using h)

theorem mtFiber44State0_in_close :
    mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  change mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 64 [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 0 64 [mtFiber44StateAt 0] (mtFiber44StateAt 0) (by simp [closeChainFiber])

theorem mtFiber44State1_in_close :
    mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  change mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates (1 + 63) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 1 63 [mtFiber44StateAt 0] (mtFiber44StateAt 1) h1

theorem mtFiber44State2_in_close :
    mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  change mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 2) h2

theorem mtFiber44State3_in_close :
    mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  change mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates (1 + 63) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 1 63 [mtFiber44StateAt 0] (mtFiber44StateAt 3) h1

theorem mtFiber44State4_in_close :
    mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  change mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates (1 + 63) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 1 63 [mtFiber44StateAt 0] (mtFiber44StateAt 4) h1

theorem mtFiber44State5_in_close :
    mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  change mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 5) h2

theorem mtFiber44State6_in_close :
    mtFiber44StateAt 6 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 6 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 6) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep6
  change mtFiber44StateAt 6 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 6) h2

theorem mtFiber44State7_in_close :
    mtFiber44StateAt 7 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 7 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 7) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep7
  change mtFiber44StateAt 7 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 7) h2

theorem mtFiber44State8_in_close :
    mtFiber44StateAt 8 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 8 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 8) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep8
  change mtFiber44StateAt 8 ∈ closeChainFiber mtWord mtFiber44DirectStates (1 + 63) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 1 63 [mtFiber44StateAt 0] (mtFiber44StateAt 8) h1

theorem mtFiber44State9_in_close :
    mtFiber44StateAt 9 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 9 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 9) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep9
  change mtFiber44StateAt 9 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 9) h2

theorem mtFiber44State10_in_close :
    mtFiber44StateAt 10 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  have h3 : mtFiber44StateAt 10 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 2) (mtFiber44StateAt 10) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep10
  change mtFiber44StateAt 10 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 10) h3

theorem mtFiber44State11_in_close :
    mtFiber44StateAt 11 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 11 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 11) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep11
  change mtFiber44StateAt 11 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 11) h2

theorem mtFiber44State12_in_close :
    mtFiber44StateAt 12 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 12 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 12) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep12
  change mtFiber44StateAt 12 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 12) h2

theorem mtFiber44State13_in_close :
    mtFiber44StateAt 13 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  have h3 : mtFiber44StateAt 13 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 5) (mtFiber44StateAt 13) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep13
  change mtFiber44StateAt 13 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 13) h3

theorem mtFiber44State14_in_close :
    mtFiber44StateAt 14 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 6 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 6) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep6
  have h3 : mtFiber44StateAt 14 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 6) (mtFiber44StateAt 14) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep14
  change mtFiber44StateAt 14 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 14) h3

theorem mtFiber44State15_in_close :
    mtFiber44StateAt 15 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 7 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 7) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep7
  have h3 : mtFiber44StateAt 15 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 7) (mtFiber44StateAt 15) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep15
  change mtFiber44StateAt 15 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 15) h3

theorem mtFiber44State16_in_close :
    mtFiber44StateAt 16 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 16 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 16) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep16
  change mtFiber44StateAt 16 ∈ closeChainFiber mtWord mtFiber44DirectStates (1 + 63) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 1 63 [mtFiber44StateAt 0] (mtFiber44StateAt 16) h1

theorem mtFiber44State17_in_close :
    mtFiber44StateAt 17 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 17 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 17) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep17
  change mtFiber44StateAt 17 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 17) h2

theorem mtFiber44State18_in_close :
    mtFiber44StateAt 18 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  have h3 : mtFiber44StateAt 18 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 2) (mtFiber44StateAt 18) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep18
  change mtFiber44StateAt 18 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 18) h3

theorem mtFiber44State19_in_close :
    mtFiber44StateAt 19 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 19 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 19) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep19
  change mtFiber44StateAt 19 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 19) h2

theorem mtFiber44State20_in_close :
    mtFiber44StateAt 20 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 20 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 20) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep20
  change mtFiber44StateAt 20 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 20) h2

theorem mtFiber44State21_in_close :
    mtFiber44StateAt 21 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  have h3 : mtFiber44StateAt 21 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 5) (mtFiber44StateAt 21) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep21
  change mtFiber44StateAt 21 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 21) h3

theorem mtFiber44State22_in_close :
    mtFiber44StateAt 22 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 6 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 6) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep6
  have h3 : mtFiber44StateAt 22 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 6) (mtFiber44StateAt 22) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep22
  change mtFiber44StateAt 22 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 22) h3

theorem mtFiber44State23_in_close :
    mtFiber44StateAt 23 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 7 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 7) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep7
  have h3 : mtFiber44StateAt 23 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 7) (mtFiber44StateAt 23) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep23
  change mtFiber44StateAt 23 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 23) h3

theorem mtFiber44State24_in_close :
    mtFiber44StateAt 24 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 8 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 8) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep8
  have h2 : mtFiber44StateAt 24 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 8) (mtFiber44StateAt 24) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep24
  change mtFiber44StateAt 24 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 24) h2

theorem mtFiber44State25_in_close :
    mtFiber44StateAt 25 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 9 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 9) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep9
  have h3 : mtFiber44StateAt 25 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 9) (mtFiber44StateAt 25) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep25
  change mtFiber44StateAt 25 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 25) h3

theorem mtFiber44State26_in_close :
    mtFiber44StateAt 26 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  have h3 : mtFiber44StateAt 10 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 2) (mtFiber44StateAt 10) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep10
  have h4 : mtFiber44StateAt 26 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 10) (mtFiber44StateAt 26) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep26
  change mtFiber44StateAt 26 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 26) h4

theorem mtFiber44State27_in_close :
    mtFiber44StateAt 27 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 11 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 11) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep11
  have h3 : mtFiber44StateAt 27 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 11) (mtFiber44StateAt 27) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep27
  change mtFiber44StateAt 27 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 27) h3

theorem mtFiber44State28_in_close :
    mtFiber44StateAt 28 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 12 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 12) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep12
  have h3 : mtFiber44StateAt 28 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 12) (mtFiber44StateAt 28) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep28
  change mtFiber44StateAt 28 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 28) h3

theorem mtFiber44State29_in_close :
    mtFiber44StateAt 29 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  have h3 : mtFiber44StateAt 13 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 5) (mtFiber44StateAt 13) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep13
  have h4 : mtFiber44StateAt 29 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 13) (mtFiber44StateAt 29) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep29
  change mtFiber44StateAt 29 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 29) h4

theorem mtFiber44State30_in_close :
    mtFiber44StateAt 30 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 6 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 6) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep6
  have h3 : mtFiber44StateAt 14 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 6) (mtFiber44StateAt 14) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep14
  have h4 : mtFiber44StateAt 30 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 14) (mtFiber44StateAt 30) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep30
  change mtFiber44StateAt 30 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 30) h4

theorem mtFiber44State31_in_close :
    mtFiber44StateAt 31 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 7 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 7) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep7
  have h3 : mtFiber44StateAt 15 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 7) (mtFiber44StateAt 15) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep15
  have h4 : mtFiber44StateAt 31 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 15) (mtFiber44StateAt 31) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep31
  change mtFiber44StateAt 31 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 31) h4

theorem mtFiber44State32_in_close :
    mtFiber44StateAt 32 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 16 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 16) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep16
  have h2 : mtFiber44StateAt 36 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 16) (mtFiber44StateAt 36) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep36
  have h3 : mtFiber44StateAt 32 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 36) (mtFiber44StateAt 32) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep32
  change mtFiber44StateAt 32 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 32) h3

theorem mtFiber44State33_in_close :
    mtFiber44StateAt 33 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 17 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 17) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep17
  have h3 : mtFiber44StateAt 37 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 17) (mtFiber44StateAt 37) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep37
  have h4 : mtFiber44StateAt 33 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 37) (mtFiber44StateAt 33) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep33
  change mtFiber44StateAt 33 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 33) h4

theorem mtFiber44State34_in_close :
    mtFiber44StateAt 34 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 20 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 20) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep20
  have h3 : mtFiber44StateAt 34 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 20) (mtFiber44StateAt 34) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep34
  change mtFiber44StateAt 34 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 34) h3

theorem mtFiber44State35_in_close :
    mtFiber44StateAt 35 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  have h3 : mtFiber44StateAt 21 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 5) (mtFiber44StateAt 21) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep21
  have h4 : mtFiber44StateAt 35 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 21) (mtFiber44StateAt 35) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep35
  change mtFiber44StateAt 35 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 35) h4

theorem mtFiber44State36_in_close :
    mtFiber44StateAt 36 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 16 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 16) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep16
  have h2 : mtFiber44StateAt 36 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 16) (mtFiber44StateAt 36) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep36
  change mtFiber44StateAt 36 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 36) h2

theorem mtFiber44State37_in_close :
    mtFiber44StateAt 37 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 17 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 17) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep17
  have h3 : mtFiber44StateAt 37 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 17) (mtFiber44StateAt 37) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep37
  change mtFiber44StateAt 37 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 37) h3

theorem mtFiber44State38_in_close :
    mtFiber44StateAt 38 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  have h3 : mtFiber44StateAt 18 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 2) (mtFiber44StateAt 18) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep18
  have h4 : mtFiber44StateAt 38 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 18) (mtFiber44StateAt 38) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep38
  change mtFiber44StateAt 38 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 38) h4

theorem mtFiber44State39_in_close :
    mtFiber44StateAt 39 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 19 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 19) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep19
  have h3 : mtFiber44StateAt 39 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 19) (mtFiber44StateAt 39) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep39
  change mtFiber44StateAt 39 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 39) h3

theorem mtFiber44State40_in_close :
    mtFiber44StateAt 40 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 60 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 60) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep60
  have h2 : mtFiber44StateAt 44 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 60) (mtFiber44StateAt 44) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep44
  have h3 : mtFiber44StateAt 40 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 44) (mtFiber44StateAt 40) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep40
  change mtFiber44StateAt 40 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 40) h3

theorem mtFiber44State41_in_close :
    mtFiber44StateAt 41 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 61 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 61) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep61
  have h3 : mtFiber44StateAt 45 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 61) (mtFiber44StateAt 45) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep45
  have h4 : mtFiber44StateAt 41 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 45) (mtFiber44StateAt 41) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep41
  change mtFiber44StateAt 41 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 41) h4

theorem mtFiber44State42_in_close :
    mtFiber44StateAt 42 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 58 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 58) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep58
  have h3 : mtFiber44StateAt 42 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 58) (mtFiber44StateAt 42) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep42
  change mtFiber44StateAt 42 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 42) h3

theorem mtFiber44State43_in_close :
    mtFiber44StateAt 43 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  have h3 : mtFiber44StateAt 59 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 5) (mtFiber44StateAt 59) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep59
  have h4 : mtFiber44StateAt 43 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 59) (mtFiber44StateAt 43) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep43
  change mtFiber44StateAt 43 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 43) h4

theorem mtFiber44State44_in_close :
    mtFiber44StateAt 44 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 60 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 60) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep60
  have h2 : mtFiber44StateAt 44 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 60) (mtFiber44StateAt 44) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep44
  change mtFiber44StateAt 44 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 44) h2

theorem mtFiber44State45_in_close :
    mtFiber44StateAt 45 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 61 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 61) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep61
  have h3 : mtFiber44StateAt 45 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 61) (mtFiber44StateAt 45) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep45
  change mtFiber44StateAt 45 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 45) h3

theorem mtFiber44State46_in_close :
    mtFiber44StateAt 46 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  have h3 : mtFiber44StateAt 62 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 2) (mtFiber44StateAt 62) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep62
  have h4 : mtFiber44StateAt 46 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 62) (mtFiber44StateAt 46) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep46
  change mtFiber44StateAt 46 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 46) h4

theorem mtFiber44State47_in_close :
    mtFiber44StateAt 47 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 63 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 63) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep63
  have h3 : mtFiber44StateAt 47 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 63) (mtFiber44StateAt 47) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep47
  change mtFiber44StateAt 47 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 47) h3

theorem mtFiber44State48_in_close :
    mtFiber44StateAt 48 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 8 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 8) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep8
  have h2 : mtFiber44StateAt 52 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 8) (mtFiber44StateAt 52) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep52
  have h3 : mtFiber44StateAt 48 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 52) (mtFiber44StateAt 48) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep48
  change mtFiber44StateAt 48 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 48) h3

theorem mtFiber44State49_in_close :
    mtFiber44StateAt 49 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 9 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 9) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep9
  have h3 : mtFiber44StateAt 53 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 9) (mtFiber44StateAt 53) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep53
  have h4 : mtFiber44StateAt 49 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 53) (mtFiber44StateAt 49) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep49
  change mtFiber44StateAt 49 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 49) h4

theorem mtFiber44State50_in_close :
    mtFiber44StateAt 50 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 12 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 12) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep12
  have h3 : mtFiber44StateAt 50 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 12) (mtFiber44StateAt 50) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep50
  change mtFiber44StateAt 50 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 50) h3

theorem mtFiber44State51_in_close :
    mtFiber44StateAt 51 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  have h3 : mtFiber44StateAt 13 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 5) (mtFiber44StateAt 13) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep13
  have h4 : mtFiber44StateAt 51 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 13) (mtFiber44StateAt 51) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep51
  change mtFiber44StateAt 51 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 51) h4

theorem mtFiber44State52_in_close :
    mtFiber44StateAt 52 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 8 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 8) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep8
  have h2 : mtFiber44StateAt 52 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 8) (mtFiber44StateAt 52) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep52
  change mtFiber44StateAt 52 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 52) h2

theorem mtFiber44State53_in_close :
    mtFiber44StateAt 53 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 9 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 9) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep9
  have h3 : mtFiber44StateAt 53 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 9) (mtFiber44StateAt 53) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep53
  change mtFiber44StateAt 53 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 53) h3

theorem mtFiber44State54_in_close :
    mtFiber44StateAt 54 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  have h3 : mtFiber44StateAt 10 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 2) (mtFiber44StateAt 10) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep10
  have h4 : mtFiber44StateAt 54 ∈ closeChainFiber mtWord mtFiber44DirectStates 4 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0]
      (mtFiber44StateAt 10) (mtFiber44StateAt 54) (by decide) h3 (by decide)
      mtFiber44ReverseSingleStep54
  change mtFiber44StateAt 54 ∈ closeChainFiber mtWord mtFiber44DirectStates (4 + 60) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 4 60 [mtFiber44StateAt 0] (mtFiber44StateAt 54) h4

theorem mtFiber44State55_in_close :
    mtFiber44StateAt 55 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 11 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 11) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep11
  have h3 : mtFiber44StateAt 55 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 11) (mtFiber44StateAt 55) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep55
  change mtFiber44StateAt 55 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 55) h3

theorem mtFiber44State56_in_close :
    mtFiber44StateAt 56 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 60 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 60) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep60
  have h2 : mtFiber44StateAt 56 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 60) (mtFiber44StateAt 56) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep56
  change mtFiber44StateAt 56 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 56) h2

theorem mtFiber44State57_in_close :
    mtFiber44StateAt 57 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 61 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 61) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep61
  have h3 : mtFiber44StateAt 57 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 61) (mtFiber44StateAt 57) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep57
  change mtFiber44StateAt 57 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 57) h3

theorem mtFiber44State58_in_close :
    mtFiber44StateAt 58 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 4 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 4) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep4
  have h2 : mtFiber44StateAt 58 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 4) (mtFiber44StateAt 58) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep58
  change mtFiber44StateAt 58 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 58) h2

theorem mtFiber44State59_in_close :
    mtFiber44StateAt 59 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 5 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 5) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep5
  have h3 : mtFiber44StateAt 59 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 5) (mtFiber44StateAt 59) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep59
  change mtFiber44StateAt 59 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 59) h3

theorem mtFiber44State60_in_close :
    mtFiber44StateAt 60 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 60 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 60) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep60
  change mtFiber44StateAt 60 ∈ closeChainFiber mtWord mtFiber44DirectStates (1 + 63) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 1 63 [mtFiber44StateAt 0] (mtFiber44StateAt 60) h1

theorem mtFiber44State61_in_close :
    mtFiber44StateAt 61 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 61 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 61) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep61
  change mtFiber44StateAt 61 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 61) h2

theorem mtFiber44State62_in_close :
    mtFiber44StateAt 62 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 1 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 1) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep1
  have h2 : mtFiber44StateAt 2 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 1) (mtFiber44StateAt 2) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep2
  have h3 : mtFiber44StateAt 62 ∈ closeChainFiber mtWord mtFiber44DirectStates 3 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0]
      (mtFiber44StateAt 2) (mtFiber44StateAt 62) (by decide) h2 (by decide)
      mtFiber44ReverseSingleStep62
  change mtFiber44StateAt 62 ∈ closeChainFiber mtWord mtFiber44DirectStates (3 + 61) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 3 61 [mtFiber44StateAt 0] (mtFiber44StateAt 62) h3

theorem mtFiber44State63_in_close :
    mtFiber44StateAt 63 ∈ closeChainFiber mtWord mtFiber44DirectStates mtFiber44DirectStates.length [mtFiber44StateAt 0] := by
  have h0 : mtFiber44StateAt 0 ∈ closeChainFiber mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber44StateAt 3 ∈ closeChainFiber mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 0 [mtFiber44StateAt 0]
      (mtFiber44StateAt 0) (mtFiber44StateAt 3) (by decide) h0 (by decide)
      mtFiber44ReverseSingleStep3
  have h2 : mtFiber44StateAt 63 ∈ closeChainFiber mtWord mtFiber44DirectStates 2 [mtFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber44DirectStates 1 [mtFiber44StateAt 0]
      (mtFiber44StateAt 3) (mtFiber44StateAt 63) (by decide) h1 (by decide)
      mtFiber44ReverseSingleStep63
  change mtFiber44StateAt 63 ∈ closeChainFiber mtWord mtFiber44DirectStates (2 + 62) [mtFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber44DirectStates 2 62 [mtFiber44StateAt 0] (mtFiber44StateAt 63) h2

theorem mtFiber44DirectConnected :
    chainFiberConnected mtWord mtFiber44DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber44DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber44State0_in_close
  · subst state
    exact mtFiber44State1_in_close
  · subst state
    exact mtFiber44State2_in_close
  · subst state
    exact mtFiber44State3_in_close
  · subst state
    exact mtFiber44State4_in_close
  · subst state
    exact mtFiber44State5_in_close
  · subst state
    exact mtFiber44State6_in_close
  · subst state
    exact mtFiber44State7_in_close
  · subst state
    exact mtFiber44State8_in_close
  · subst state
    exact mtFiber44State9_in_close
  · subst state
    exact mtFiber44State10_in_close
  · subst state
    exact mtFiber44State11_in_close
  · subst state
    exact mtFiber44State12_in_close
  · subst state
    exact mtFiber44State13_in_close
  · subst state
    exact mtFiber44State14_in_close
  · subst state
    exact mtFiber44State15_in_close
  · subst state
    exact mtFiber44State16_in_close
  · subst state
    exact mtFiber44State17_in_close
  · subst state
    exact mtFiber44State18_in_close
  · subst state
    exact mtFiber44State19_in_close
  · subst state
    exact mtFiber44State20_in_close
  · subst state
    exact mtFiber44State21_in_close
  · subst state
    exact mtFiber44State22_in_close
  · subst state
    exact mtFiber44State23_in_close
  · subst state
    exact mtFiber44State24_in_close
  · subst state
    exact mtFiber44State25_in_close
  · subst state
    exact mtFiber44State26_in_close
  · subst state
    exact mtFiber44State27_in_close
  · subst state
    exact mtFiber44State28_in_close
  · subst state
    exact mtFiber44State29_in_close
  · subst state
    exact mtFiber44State30_in_close
  · subst state
    exact mtFiber44State31_in_close
  · subst state
    exact mtFiber44State32_in_close
  · subst state
    exact mtFiber44State33_in_close
  · subst state
    exact mtFiber44State34_in_close
  · subst state
    exact mtFiber44State35_in_close
  · subst state
    exact mtFiber44State36_in_close
  · subst state
    exact mtFiber44State37_in_close
  · subst state
    exact mtFiber44State38_in_close
  · subst state
    exact mtFiber44State39_in_close
  · subst state
    exact mtFiber44State40_in_close
  · subst state
    exact mtFiber44State41_in_close
  · subst state
    exact mtFiber44State42_in_close
  · subst state
    exact mtFiber44State43_in_close
  · subst state
    exact mtFiber44State44_in_close
  · subst state
    exact mtFiber44State45_in_close
  · subst state
    exact mtFiber44State46_in_close
  · subst state
    exact mtFiber44State47_in_close
  · subst state
    exact mtFiber44State48_in_close
  · subst state
    exact mtFiber44State49_in_close
  · subst state
    exact mtFiber44State50_in_close
  · subst state
    exact mtFiber44State51_in_close
  · subst state
    exact mtFiber44State52_in_close
  · subst state
    exact mtFiber44State53_in_close
  · subst state
    exact mtFiber44State54_in_close
  · subst state
    exact mtFiber44State55_in_close
  · subst state
    exact mtFiber44State56_in_close
  · subst state
    exact mtFiber44State57_in_close
  · subst state
    exact mtFiber44State58_in_close
  · subst state
    exact mtFiber44State59_in_close
  · subst state
    exact mtFiber44State60_in_close
  · subst state
    exact mtFiber44State61_in_close
  · subst state
    exact mtFiber44State62_in_close
  · subst state
    exact mtFiber44State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
