import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 10

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber10StateAt (i : Nat) : List TauState :=
  directStates (mtFiber10RowAt i).sourceLeft (mtFiber10RowAt i).sourceRight

def mtFiber10DirectStates : List (List TauState) :=
  [mtFiber10StateAt 0, mtFiber10StateAt 1, mtFiber10StateAt 2, mtFiber10StateAt 3, mtFiber10StateAt 4, mtFiber10StateAt 5, mtFiber10StateAt 6, mtFiber10StateAt 7, mtFiber10StateAt 8, mtFiber10StateAt 9, mtFiber10StateAt 10, mtFiber10StateAt 11, mtFiber10StateAt 12, mtFiber10StateAt 13, mtFiber10StateAt 14, mtFiber10StateAt 15, mtFiber10StateAt 16, mtFiber10StateAt 17, mtFiber10StateAt 18, mtFiber10StateAt 19, mtFiber10StateAt 20, mtFiber10StateAt 21, mtFiber10StateAt 22, mtFiber10StateAt 23, mtFiber10StateAt 24, mtFiber10StateAt 25, mtFiber10StateAt 26, mtFiber10StateAt 27, mtFiber10StateAt 28, mtFiber10StateAt 29, mtFiber10StateAt 30, mtFiber10StateAt 31, mtFiber10StateAt 32, mtFiber10StateAt 33, mtFiber10StateAt 34, mtFiber10StateAt 35, mtFiber10StateAt 36, mtFiber10StateAt 37, mtFiber10StateAt 38, mtFiber10StateAt 39, mtFiber10StateAt 40, mtFiber10StateAt 41, mtFiber10StateAt 42, mtFiber10StateAt 43, mtFiber10StateAt 44, mtFiber10StateAt 45, mtFiber10StateAt 46, mtFiber10StateAt 47, mtFiber10StateAt 48, mtFiber10StateAt 49, mtFiber10StateAt 50, mtFiber10StateAt 51, mtFiber10StateAt 52, mtFiber10StateAt 53, mtFiber10StateAt 54, mtFiber10StateAt 55, mtFiber10StateAt 56, mtFiber10StateAt 57, mtFiber10StateAt 58, mtFiber10StateAt 59, mtFiber10StateAt 60, mtFiber10StateAt 61, mtFiber10StateAt 62, mtFiber10StateAt 63]

theorem mtFiber10ReverseRow_1_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk0_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 0) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 1)
    (mtFiber10RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 1) (by decide) mtFiber10ReverseRow_1_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_2_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk1_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 2) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 2)
    (mtFiber10RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 2) (by decide) mtFiber10ReverseRow_2_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_3_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk1_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 2) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 3)
    (mtFiber10RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 3) (by decide) mtFiber10ReverseRow_3_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_4_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk2_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 4) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 4)
    (mtFiber10RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 4) (by decide) mtFiber10ReverseRow_4_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_5_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk2_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 4) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 5)
    (mtFiber10RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 5) (by decide) mtFiber10ReverseRow_5_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_6_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk3_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 6) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 6)
    (mtFiber10RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 6) (by decide) mtFiber10ReverseRow_6_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_7_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk3_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 6) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 7)
    (mtFiber10RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 7) (by decide) mtFiber10ReverseRow_7_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_8_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk4_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 8) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 8)
    (mtFiber10RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 8) (by decide) mtFiber10ReverseRow_8_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_9_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk4_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 8) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 9)
    (mtFiber10RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 9) (by decide) mtFiber10ReverseRow_9_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_10_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk5_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 10) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 2) (mtFiber10StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 2) (mtFiber10StateAt 10)
    (mtFiber10RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 10) (by decide) mtFiber10ReverseRow_10_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_11_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk5_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 10) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 11)
    (mtFiber10RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 11) (by decide) mtFiber10ReverseRow_11_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_12_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk6_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 12) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 12)
    (mtFiber10RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 12) (by decide) mtFiber10ReverseRow_12_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_13_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk6_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 12) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 5) (mtFiber10StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 5) (mtFiber10StateAt 13)
    (mtFiber10RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 13) (by decide) mtFiber10ReverseRow_13_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_14_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk7_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 14) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 6) (mtFiber10StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 6) (mtFiber10StateAt 14)
    (mtFiber10RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 14) (by decide) mtFiber10ReverseRow_14_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_15_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk7_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 14) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 7) (mtFiber10StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 7) (mtFiber10StateAt 15)
    (mtFiber10RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 15) (by decide) mtFiber10ReverseRow_15_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_16_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk8_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 16) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 16)
    (mtFiber10RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 16) (by decide) mtFiber10ReverseRow_16_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_17_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk8_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 16) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 17)
    (mtFiber10RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 17) (by decide) mtFiber10ReverseRow_17_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_18_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk9_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 18) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 2) (mtFiber10StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 2) (mtFiber10StateAt 18)
    (mtFiber10RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 18) (by decide) mtFiber10ReverseRow_18_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_19_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk9_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 18) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 19)
    (mtFiber10RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 19) (by decide) mtFiber10ReverseRow_19_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_20_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk10_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 20) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 20)
    (mtFiber10RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 20) (by decide) mtFiber10ReverseRow_20_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_21_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk10_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 20) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 5) (mtFiber10StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 5) (mtFiber10StateAt 21)
    (mtFiber10RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 21) (by decide) mtFiber10ReverseRow_21_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_22_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk11_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 22) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 6) (mtFiber10StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 6) (mtFiber10StateAt 22)
    (mtFiber10RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 22) (by decide) mtFiber10ReverseRow_22_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_23_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk11_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 22) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 7) (mtFiber10StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 7) (mtFiber10StateAt 23)
    (mtFiber10RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 23) (by decide) mtFiber10ReverseRow_23_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_24_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk12_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 24) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 8) (mtFiber10StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 8) (mtFiber10StateAt 24)
    (mtFiber10RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 24) (by decide) mtFiber10ReverseRow_24_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_25_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk12_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 24) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 9) (mtFiber10StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 9) (mtFiber10StateAt 25)
    (mtFiber10RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 25) (by decide) mtFiber10ReverseRow_25_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_26_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk13_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 26) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 10) (mtFiber10StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 10) (mtFiber10StateAt 26)
    (mtFiber10RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 26) (by decide) mtFiber10ReverseRow_26_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_27_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk13_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 26) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 11) (mtFiber10StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 11) (mtFiber10StateAt 27)
    (mtFiber10RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 27) (by decide) mtFiber10ReverseRow_27_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_28_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk14_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 28) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 12) (mtFiber10StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 12) (mtFiber10StateAt 28)
    (mtFiber10RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 28) (by decide) mtFiber10ReverseRow_28_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_29_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk14_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 28) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 13) (mtFiber10StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 13) (mtFiber10StateAt 29)
    (mtFiber10RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 29) (by decide) mtFiber10ReverseRow_29_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_30_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk15_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 30) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 14) (mtFiber10StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 14) (mtFiber10StateAt 30)
    (mtFiber10RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 30) (by decide) mtFiber10ReverseRow_30_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_31_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk15_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 30) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 15) (mtFiber10StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 15) (mtFiber10StateAt 31)
    (mtFiber10RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 31) (by decide) mtFiber10ReverseRow_31_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_32_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk16_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 32) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 0) (mtFiber10StateAt 32)
    (mtFiber10RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 32) (by decide) mtFiber10ReverseRow_32_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_33_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk16_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 32) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 1) (mtFiber10StateAt 33)
    (mtFiber10RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 33) (by decide) mtFiber10ReverseRow_33_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_34_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk17_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 34) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 32) (mtFiber10StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 32) (mtFiber10StateAt 34)
    (mtFiber10RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 34) (by decide) mtFiber10ReverseRow_34_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_35_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk17_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 34) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 3) (mtFiber10StateAt 35)
    (mtFiber10RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 35) (by decide) mtFiber10ReverseRow_35_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_36_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk18_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 36) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 4) (mtFiber10StateAt 36)
    (mtFiber10RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 36) (by decide) mtFiber10ReverseRow_36_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_37_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk18_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 36) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 5) (mtFiber10StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 5) (mtFiber10StateAt 37)
    (mtFiber10RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 37) (by decide) mtFiber10ReverseRow_37_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_38_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk19_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 38) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 33) (mtFiber10StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 33) (mtFiber10StateAt 38)
    (mtFiber10RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 38) (by decide) mtFiber10ReverseRow_38_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_39_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk19_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 38) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 32) (mtFiber10StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 32) (mtFiber10StateAt 39)
    (mtFiber10RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 39) (by decide) mtFiber10ReverseRow_39_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_40_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk20_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 40) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 8) (mtFiber10StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 8) (mtFiber10StateAt 40)
    (mtFiber10RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 40) (by decide) mtFiber10ReverseRow_40_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_41_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk20_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 40) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 9) (mtFiber10StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 9) (mtFiber10StateAt 41)
    (mtFiber10RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 41) (by decide) mtFiber10ReverseRow_41_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_42_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk21_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 42) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 40) (mtFiber10StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 40) (mtFiber10StateAt 42)
    (mtFiber10RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 42) (by decide) mtFiber10ReverseRow_42_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_43_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk21_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 42) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 11) (mtFiber10StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 11) (mtFiber10StateAt 43)
    (mtFiber10RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 43) (by decide) mtFiber10ReverseRow_43_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_44_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk22_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 44) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 12) (mtFiber10StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 12) (mtFiber10StateAt 44)
    (mtFiber10RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 44) (by decide) mtFiber10ReverseRow_44_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_45_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk22_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 44) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 13) (mtFiber10StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 13) (mtFiber10StateAt 45)
    (mtFiber10RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 45) (by decide) mtFiber10ReverseRow_45_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_46_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk23_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 46) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 41) (mtFiber10StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 41) (mtFiber10StateAt 46)
    (mtFiber10RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 46) (by decide) mtFiber10ReverseRow_46_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_47_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk23_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 46) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 40) (mtFiber10StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 40) (mtFiber10StateAt 47)
    (mtFiber10RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 47) (by decide) mtFiber10ReverseRow_47_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_48_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk24_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 48) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 16) (mtFiber10StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 16) (mtFiber10StateAt 48)
    (mtFiber10RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 48) (by decide) mtFiber10ReverseRow_48_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_49_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk24_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 48) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 17) (mtFiber10StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 17) (mtFiber10StateAt 49)
    (mtFiber10RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 49) (by decide) mtFiber10ReverseRow_49_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_50_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk25_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 50) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 48) (mtFiber10StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 48) (mtFiber10StateAt 50)
    (mtFiber10RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 50) (by decide) mtFiber10ReverseRow_50_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_51_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk25_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 50) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 19) (mtFiber10StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 19) (mtFiber10StateAt 51)
    (mtFiber10RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 51) (by decide) mtFiber10ReverseRow_51_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_52_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk26_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 52) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 20) (mtFiber10StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 20) (mtFiber10StateAt 52)
    (mtFiber10RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 52) (by decide) mtFiber10ReverseRow_52_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_53_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk26_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 52) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 21) (mtFiber10StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 21) (mtFiber10StateAt 53)
    (mtFiber10RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 53) (by decide) mtFiber10ReverseRow_53_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_54_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk27_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 54) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 49) (mtFiber10StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 49) (mtFiber10StateAt 54)
    (mtFiber10RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 54) (by decide) mtFiber10ReverseRow_54_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_55_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk27_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 54) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 48) (mtFiber10StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 48) (mtFiber10StateAt 55)
    (mtFiber10RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 55) (by decide) mtFiber10ReverseRow_55_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_56_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk28_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 56) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 32) (mtFiber10StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 32) (mtFiber10StateAt 56)
    (mtFiber10RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 56) (by decide) mtFiber10ReverseRow_56_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_57_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk28_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 56) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 33) (mtFiber10StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 33) (mtFiber10StateAt 57)
    (mtFiber10RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 57) (by decide) mtFiber10ReverseRow_57_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_58_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk29_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 58) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 34) (mtFiber10StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 34) (mtFiber10StateAt 58)
    (mtFiber10RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 58) (by decide) mtFiber10ReverseRow_58_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_59_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk29_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 58) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 35) (mtFiber10StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 35) (mtFiber10StateAt 59)
    (mtFiber10RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 59) (by decide) mtFiber10ReverseRow_59_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_60_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk30_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 60) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 36) (mtFiber10StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 36) (mtFiber10StateAt 60)
    (mtFiber10RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 60) (by decide) mtFiber10ReverseRow_60_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_61_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk30_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 60) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 37) (mtFiber10StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 37) (mtFiber10StateAt 61)
    (mtFiber10RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 61) (by decide) mtFiber10ReverseRow_61_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_62_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk31_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 62) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber10ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 38) (mtFiber10StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 38) (mtFiber10StateAt 62)
    (mtFiber10RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 62) (by decide) mtFiber10ReverseRow_62_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10ReverseRow_63_ok :
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber10Chunk31_ok
  change (mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 62) &&
    mtRowReverseValid mtFiber10Key mtFiber10Expected (mtFiber10RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber10ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber10StateAt 39) (mtFiber10StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber10StateAt 39) (mtFiber10StateAt 63)
    (mtFiber10RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber10Key mtFiber10Expected
        (mtFiber10RowAt 63) (by decide) mtFiber10ReverseRow_63_ok
      simpa [mtFiber10StateAt, mtFiber10RowAt, mtFiber10Rows, listGetD, directRow] using h)

theorem mtFiber10State0_in_close :
    mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  change mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 64 [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 0 64 [mtFiber10StateAt 0] (mtFiber10StateAt 0) (by simp [closeChainFiber])

theorem mtFiber10State1_in_close :
    mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  change mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates (1 + 63) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 1 63 [mtFiber10StateAt 0] (mtFiber10StateAt 1) h1

theorem mtFiber10State2_in_close :
    mtFiber10StateAt 2 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 2 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 2) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep2
  change mtFiber10StateAt 2 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 2) h2

theorem mtFiber10State3_in_close :
    mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  change mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates (1 + 63) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 1 63 [mtFiber10StateAt 0] (mtFiber10StateAt 3) h1

theorem mtFiber10State4_in_close :
    mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  change mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates (1 + 63) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 1 63 [mtFiber10StateAt 0] (mtFiber10StateAt 4) h1

theorem mtFiber10State5_in_close :
    mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  change mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 5) h2

theorem mtFiber10State6_in_close :
    mtFiber10StateAt 6 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 6 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 6) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep6
  change mtFiber10StateAt 6 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 6) h2

theorem mtFiber10State7_in_close :
    mtFiber10StateAt 7 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 7 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 7) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep7
  change mtFiber10StateAt 7 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 7) h2

theorem mtFiber10State8_in_close :
    mtFiber10StateAt 8 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 8 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 8) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep8
  change mtFiber10StateAt 8 ∈ closeChainFiber mtWord mtFiber10DirectStates (1 + 63) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 1 63 [mtFiber10StateAt 0] (mtFiber10StateAt 8) h1

theorem mtFiber10State9_in_close :
    mtFiber10StateAt 9 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 9 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 9) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep9
  change mtFiber10StateAt 9 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 9) h2

theorem mtFiber10State10_in_close :
    mtFiber10StateAt 10 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 2 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 2) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep2
  have h3 : mtFiber10StateAt 10 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 2) (mtFiber10StateAt 10) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep10
  change mtFiber10StateAt 10 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 10) h3

theorem mtFiber10State11_in_close :
    mtFiber10StateAt 11 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 11 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 11) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep11
  change mtFiber10StateAt 11 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 11) h2

theorem mtFiber10State12_in_close :
    mtFiber10StateAt 12 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 12 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 12) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep12
  change mtFiber10StateAt 12 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 12) h2

theorem mtFiber10State13_in_close :
    mtFiber10StateAt 13 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  have h3 : mtFiber10StateAt 13 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 5) (mtFiber10StateAt 13) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep13
  change mtFiber10StateAt 13 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 13) h3

theorem mtFiber10State14_in_close :
    mtFiber10StateAt 14 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 6 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 6) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep6
  have h3 : mtFiber10StateAt 14 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 6) (mtFiber10StateAt 14) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep14
  change mtFiber10StateAt 14 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 14) h3

theorem mtFiber10State15_in_close :
    mtFiber10StateAt 15 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 7 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 7) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep7
  have h3 : mtFiber10StateAt 15 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 7) (mtFiber10StateAt 15) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep15
  change mtFiber10StateAt 15 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 15) h3

theorem mtFiber10State16_in_close :
    mtFiber10StateAt 16 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 16 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 16) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep16
  change mtFiber10StateAt 16 ∈ closeChainFiber mtWord mtFiber10DirectStates (1 + 63) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 1 63 [mtFiber10StateAt 0] (mtFiber10StateAt 16) h1

theorem mtFiber10State17_in_close :
    mtFiber10StateAt 17 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 17 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 17) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep17
  change mtFiber10StateAt 17 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 17) h2

theorem mtFiber10State18_in_close :
    mtFiber10StateAt 18 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 2 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 2) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep2
  have h3 : mtFiber10StateAt 18 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 2) (mtFiber10StateAt 18) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep18
  change mtFiber10StateAt 18 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 18) h3

theorem mtFiber10State19_in_close :
    mtFiber10StateAt 19 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 19 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 19) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep19
  change mtFiber10StateAt 19 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 19) h2

theorem mtFiber10State20_in_close :
    mtFiber10StateAt 20 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 20 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 20) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep20
  change mtFiber10StateAt 20 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 20) h2

theorem mtFiber10State21_in_close :
    mtFiber10StateAt 21 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  have h3 : mtFiber10StateAt 21 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 5) (mtFiber10StateAt 21) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep21
  change mtFiber10StateAt 21 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 21) h3

theorem mtFiber10State22_in_close :
    mtFiber10StateAt 22 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 6 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 6) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep6
  have h3 : mtFiber10StateAt 22 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 6) (mtFiber10StateAt 22) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep22
  change mtFiber10StateAt 22 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 22) h3

theorem mtFiber10State23_in_close :
    mtFiber10StateAt 23 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 7 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 7) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep7
  have h3 : mtFiber10StateAt 23 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 7) (mtFiber10StateAt 23) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep23
  change mtFiber10StateAt 23 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 23) h3

theorem mtFiber10State24_in_close :
    mtFiber10StateAt 24 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 8 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 8) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep8
  have h2 : mtFiber10StateAt 24 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 8) (mtFiber10StateAt 24) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep24
  change mtFiber10StateAt 24 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 24) h2

theorem mtFiber10State25_in_close :
    mtFiber10StateAt 25 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 9 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 9) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep9
  have h3 : mtFiber10StateAt 25 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 9) (mtFiber10StateAt 25) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep25
  change mtFiber10StateAt 25 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 25) h3

theorem mtFiber10State26_in_close :
    mtFiber10StateAt 26 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 2 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 2) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep2
  have h3 : mtFiber10StateAt 10 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 2) (mtFiber10StateAt 10) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep10
  have h4 : mtFiber10StateAt 26 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 10) (mtFiber10StateAt 26) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep26
  change mtFiber10StateAt 26 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 26) h4

theorem mtFiber10State27_in_close :
    mtFiber10StateAt 27 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 11 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 11) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep11
  have h3 : mtFiber10StateAt 27 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 11) (mtFiber10StateAt 27) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep27
  change mtFiber10StateAt 27 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 27) h3

theorem mtFiber10State28_in_close :
    mtFiber10StateAt 28 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 12 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 12) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep12
  have h3 : mtFiber10StateAt 28 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 12) (mtFiber10StateAt 28) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep28
  change mtFiber10StateAt 28 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 28) h3

theorem mtFiber10State29_in_close :
    mtFiber10StateAt 29 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  have h3 : mtFiber10StateAt 13 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 5) (mtFiber10StateAt 13) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep13
  have h4 : mtFiber10StateAt 29 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 13) (mtFiber10StateAt 29) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep29
  change mtFiber10StateAt 29 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 29) h4

theorem mtFiber10State30_in_close :
    mtFiber10StateAt 30 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 6 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 6) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep6
  have h3 : mtFiber10StateAt 14 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 6) (mtFiber10StateAt 14) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep14
  have h4 : mtFiber10StateAt 30 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 14) (mtFiber10StateAt 30) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep30
  change mtFiber10StateAt 30 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 30) h4

theorem mtFiber10State31_in_close :
    mtFiber10StateAt 31 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 7 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 7) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep7
  have h3 : mtFiber10StateAt 15 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 7) (mtFiber10StateAt 15) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep15
  have h4 : mtFiber10StateAt 31 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 15) (mtFiber10StateAt 31) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep31
  change mtFiber10StateAt 31 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 31) h4

theorem mtFiber10State32_in_close :
    mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 32) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep32
  change mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates (1 + 63) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 1 63 [mtFiber10StateAt 0] (mtFiber10StateAt 32) h1

theorem mtFiber10State33_in_close :
    mtFiber10StateAt 33 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 33 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 33) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep33
  change mtFiber10StateAt 33 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 33) h2

theorem mtFiber10State34_in_close :
    mtFiber10StateAt 34 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 32) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep32
  have h2 : mtFiber10StateAt 34 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 32) (mtFiber10StateAt 34) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep34
  change mtFiber10StateAt 34 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 34) h2

theorem mtFiber10State35_in_close :
    mtFiber10StateAt 35 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 35 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 35) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep35
  change mtFiber10StateAt 35 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 35) h2

theorem mtFiber10State36_in_close :
    mtFiber10StateAt 36 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 36 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 36) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep36
  change mtFiber10StateAt 36 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 36) h2

theorem mtFiber10State37_in_close :
    mtFiber10StateAt 37 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  have h3 : mtFiber10StateAt 37 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 5) (mtFiber10StateAt 37) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep37
  change mtFiber10StateAt 37 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 37) h3

theorem mtFiber10State38_in_close :
    mtFiber10StateAt 38 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 33 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 33) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep33
  have h3 : mtFiber10StateAt 38 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 33) (mtFiber10StateAt 38) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep38
  change mtFiber10StateAt 38 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 38) h3

theorem mtFiber10State39_in_close :
    mtFiber10StateAt 39 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 32) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep32
  have h2 : mtFiber10StateAt 39 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 32) (mtFiber10StateAt 39) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep39
  change mtFiber10StateAt 39 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 39) h2

theorem mtFiber10State40_in_close :
    mtFiber10StateAt 40 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 8 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 8) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep8
  have h2 : mtFiber10StateAt 40 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 8) (mtFiber10StateAt 40) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep40
  change mtFiber10StateAt 40 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 40) h2

theorem mtFiber10State41_in_close :
    mtFiber10StateAt 41 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 9 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 9) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep9
  have h3 : mtFiber10StateAt 41 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 9) (mtFiber10StateAt 41) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep41
  change mtFiber10StateAt 41 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 41) h3

theorem mtFiber10State42_in_close :
    mtFiber10StateAt 42 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 8 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 8) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep8
  have h2 : mtFiber10StateAt 40 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 8) (mtFiber10StateAt 40) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep40
  have h3 : mtFiber10StateAt 42 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 40) (mtFiber10StateAt 42) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep42
  change mtFiber10StateAt 42 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 42) h3

theorem mtFiber10State43_in_close :
    mtFiber10StateAt 43 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 11 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 11) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep11
  have h3 : mtFiber10StateAt 43 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 11) (mtFiber10StateAt 43) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep43
  change mtFiber10StateAt 43 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 43) h3

theorem mtFiber10State44_in_close :
    mtFiber10StateAt 44 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 12 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 12) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep12
  have h3 : mtFiber10StateAt 44 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 12) (mtFiber10StateAt 44) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep44
  change mtFiber10StateAt 44 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 44) h3

theorem mtFiber10State45_in_close :
    mtFiber10StateAt 45 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  have h3 : mtFiber10StateAt 13 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 5) (mtFiber10StateAt 13) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep13
  have h4 : mtFiber10StateAt 45 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 13) (mtFiber10StateAt 45) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep45
  change mtFiber10StateAt 45 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 45) h4

theorem mtFiber10State46_in_close :
    mtFiber10StateAt 46 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 9 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 9) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep9
  have h3 : mtFiber10StateAt 41 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 9) (mtFiber10StateAt 41) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep41
  have h4 : mtFiber10StateAt 46 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 41) (mtFiber10StateAt 46) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep46
  change mtFiber10StateAt 46 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 46) h4

theorem mtFiber10State47_in_close :
    mtFiber10StateAt 47 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 8 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 8) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep8
  have h2 : mtFiber10StateAt 40 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 8) (mtFiber10StateAt 40) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep40
  have h3 : mtFiber10StateAt 47 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 40) (mtFiber10StateAt 47) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep47
  change mtFiber10StateAt 47 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 47) h3

theorem mtFiber10State48_in_close :
    mtFiber10StateAt 48 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 16 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 16) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep16
  have h2 : mtFiber10StateAt 48 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 16) (mtFiber10StateAt 48) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep48
  change mtFiber10StateAt 48 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 48) h2

theorem mtFiber10State49_in_close :
    mtFiber10StateAt 49 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 17 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 17) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep17
  have h3 : mtFiber10StateAt 49 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 17) (mtFiber10StateAt 49) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep49
  change mtFiber10StateAt 49 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 49) h3

theorem mtFiber10State50_in_close :
    mtFiber10StateAt 50 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 16 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 16) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep16
  have h2 : mtFiber10StateAt 48 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 16) (mtFiber10StateAt 48) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep48
  have h3 : mtFiber10StateAt 50 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 48) (mtFiber10StateAt 50) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep50
  change mtFiber10StateAt 50 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 50) h3

theorem mtFiber10State51_in_close :
    mtFiber10StateAt 51 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 19 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 19) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep19
  have h3 : mtFiber10StateAt 51 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 19) (mtFiber10StateAt 51) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep51
  change mtFiber10StateAt 51 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 51) h3

theorem mtFiber10State52_in_close :
    mtFiber10StateAt 52 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 20 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 20) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep20
  have h3 : mtFiber10StateAt 52 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 20) (mtFiber10StateAt 52) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep52
  change mtFiber10StateAt 52 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 52) h3

theorem mtFiber10State53_in_close :
    mtFiber10StateAt 53 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  have h3 : mtFiber10StateAt 21 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 5) (mtFiber10StateAt 21) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep21
  have h4 : mtFiber10StateAt 53 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 21) (mtFiber10StateAt 53) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep53
  change mtFiber10StateAt 53 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 53) h4

theorem mtFiber10State54_in_close :
    mtFiber10StateAt 54 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 17 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 17) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep17
  have h3 : mtFiber10StateAt 49 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 17) (mtFiber10StateAt 49) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep49
  have h4 : mtFiber10StateAt 54 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 49) (mtFiber10StateAt 54) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep54
  change mtFiber10StateAt 54 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 54) h4

theorem mtFiber10State55_in_close :
    mtFiber10StateAt 55 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 16 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 16) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep16
  have h2 : mtFiber10StateAt 48 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 16) (mtFiber10StateAt 48) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep48
  have h3 : mtFiber10StateAt 55 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 48) (mtFiber10StateAt 55) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep55
  change mtFiber10StateAt 55 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 55) h3

theorem mtFiber10State56_in_close :
    mtFiber10StateAt 56 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 32) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep32
  have h2 : mtFiber10StateAt 56 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 32) (mtFiber10StateAt 56) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep56
  change mtFiber10StateAt 56 ∈ closeChainFiber mtWord mtFiber10DirectStates (2 + 62) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 2 62 [mtFiber10StateAt 0] (mtFiber10StateAt 56) h2

theorem mtFiber10State57_in_close :
    mtFiber10StateAt 57 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 33 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 33) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep33
  have h3 : mtFiber10StateAt 57 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 33) (mtFiber10StateAt 57) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep57
  change mtFiber10StateAt 57 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 57) h3

theorem mtFiber10State58_in_close :
    mtFiber10StateAt 58 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 32) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep32
  have h2 : mtFiber10StateAt 34 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 32) (mtFiber10StateAt 34) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep34
  have h3 : mtFiber10StateAt 58 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 34) (mtFiber10StateAt 58) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep58
  change mtFiber10StateAt 58 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 58) h3

theorem mtFiber10State59_in_close :
    mtFiber10StateAt 59 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 3 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 3) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep3
  have h2 : mtFiber10StateAt 35 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 3) (mtFiber10StateAt 35) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep35
  have h3 : mtFiber10StateAt 59 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 35) (mtFiber10StateAt 59) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep59
  change mtFiber10StateAt 59 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 59) h3

theorem mtFiber10State60_in_close :
    mtFiber10StateAt 60 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 4 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 4) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep4
  have h2 : mtFiber10StateAt 36 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 4) (mtFiber10StateAt 36) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep36
  have h3 : mtFiber10StateAt 60 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 36) (mtFiber10StateAt 60) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep60
  change mtFiber10StateAt 60 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 60) h3

theorem mtFiber10State61_in_close :
    mtFiber10StateAt 61 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 5 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 5) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep5
  have h3 : mtFiber10StateAt 37 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 5) (mtFiber10StateAt 37) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep37
  have h4 : mtFiber10StateAt 61 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 37) (mtFiber10StateAt 61) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep61
  change mtFiber10StateAt 61 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 61) h4

theorem mtFiber10State62_in_close :
    mtFiber10StateAt 62 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 1 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 1) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep1
  have h2 : mtFiber10StateAt 33 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 1) (mtFiber10StateAt 33) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep33
  have h3 : mtFiber10StateAt 38 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 33) (mtFiber10StateAt 38) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep38
  have h4 : mtFiber10StateAt 62 ∈ closeChainFiber mtWord mtFiber10DirectStates 4 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0]
      (mtFiber10StateAt 38) (mtFiber10StateAt 62) (by decide) h3 (by decide)
      mtFiber10ReverseSingleStep62
  change mtFiber10StateAt 62 ∈ closeChainFiber mtWord mtFiber10DirectStates (4 + 60) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 4 60 [mtFiber10StateAt 0] (mtFiber10StateAt 62) h4

theorem mtFiber10State63_in_close :
    mtFiber10StateAt 63 ∈ closeChainFiber mtWord mtFiber10DirectStates mtFiber10DirectStates.length [mtFiber10StateAt 0] := by
  have h0 : mtFiber10StateAt 0 ∈ closeChainFiber mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber10StateAt 32 ∈ closeChainFiber mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 0 [mtFiber10StateAt 0]
      (mtFiber10StateAt 0) (mtFiber10StateAt 32) (by decide) h0 (by decide)
      mtFiber10ReverseSingleStep32
  have h2 : mtFiber10StateAt 39 ∈ closeChainFiber mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 1 [mtFiber10StateAt 0]
      (mtFiber10StateAt 32) (mtFiber10StateAt 39) (by decide) h1 (by decide)
      mtFiber10ReverseSingleStep39
  have h3 : mtFiber10StateAt 63 ∈ closeChainFiber mtWord mtFiber10DirectStates 3 [mtFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber10DirectStates 2 [mtFiber10StateAt 0]
      (mtFiber10StateAt 39) (mtFiber10StateAt 63) (by decide) h2 (by decide)
      mtFiber10ReverseSingleStep63
  change mtFiber10StateAt 63 ∈ closeChainFiber mtWord mtFiber10DirectStates (3 + 61) [mtFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber10DirectStates 3 61 [mtFiber10StateAt 0] (mtFiber10StateAt 63) h3

theorem mtFiber10DirectConnected :
    chainFiberConnected mtWord mtFiber10DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber10DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber10State0_in_close
  · subst state
    exact mtFiber10State1_in_close
  · subst state
    exact mtFiber10State2_in_close
  · subst state
    exact mtFiber10State3_in_close
  · subst state
    exact mtFiber10State4_in_close
  · subst state
    exact mtFiber10State5_in_close
  · subst state
    exact mtFiber10State6_in_close
  · subst state
    exact mtFiber10State7_in_close
  · subst state
    exact mtFiber10State8_in_close
  · subst state
    exact mtFiber10State9_in_close
  · subst state
    exact mtFiber10State10_in_close
  · subst state
    exact mtFiber10State11_in_close
  · subst state
    exact mtFiber10State12_in_close
  · subst state
    exact mtFiber10State13_in_close
  · subst state
    exact mtFiber10State14_in_close
  · subst state
    exact mtFiber10State15_in_close
  · subst state
    exact mtFiber10State16_in_close
  · subst state
    exact mtFiber10State17_in_close
  · subst state
    exact mtFiber10State18_in_close
  · subst state
    exact mtFiber10State19_in_close
  · subst state
    exact mtFiber10State20_in_close
  · subst state
    exact mtFiber10State21_in_close
  · subst state
    exact mtFiber10State22_in_close
  · subst state
    exact mtFiber10State23_in_close
  · subst state
    exact mtFiber10State24_in_close
  · subst state
    exact mtFiber10State25_in_close
  · subst state
    exact mtFiber10State26_in_close
  · subst state
    exact mtFiber10State27_in_close
  · subst state
    exact mtFiber10State28_in_close
  · subst state
    exact mtFiber10State29_in_close
  · subst state
    exact mtFiber10State30_in_close
  · subst state
    exact mtFiber10State31_in_close
  · subst state
    exact mtFiber10State32_in_close
  · subst state
    exact mtFiber10State33_in_close
  · subst state
    exact mtFiber10State34_in_close
  · subst state
    exact mtFiber10State35_in_close
  · subst state
    exact mtFiber10State36_in_close
  · subst state
    exact mtFiber10State37_in_close
  · subst state
    exact mtFiber10State38_in_close
  · subst state
    exact mtFiber10State39_in_close
  · subst state
    exact mtFiber10State40_in_close
  · subst state
    exact mtFiber10State41_in_close
  · subst state
    exact mtFiber10State42_in_close
  · subst state
    exact mtFiber10State43_in_close
  · subst state
    exact mtFiber10State44_in_close
  · subst state
    exact mtFiber10State45_in_close
  · subst state
    exact mtFiber10State46_in_close
  · subst state
    exact mtFiber10State47_in_close
  · subst state
    exact mtFiber10State48_in_close
  · subst state
    exact mtFiber10State49_in_close
  · subst state
    exact mtFiber10State50_in_close
  · subst state
    exact mtFiber10State51_in_close
  · subst state
    exact mtFiber10State52_in_close
  · subst state
    exact mtFiber10State53_in_close
  · subst state
    exact mtFiber10State54_in_close
  · subst state
    exact mtFiber10State55_in_close
  · subst state
    exact mtFiber10State56_in_close
  · subst state
    exact mtFiber10State57_in_close
  · subst state
    exact mtFiber10State58_in_close
  · subst state
    exact mtFiber10State59_in_close
  · subst state
    exact mtFiber10State60_in_close
  · subst state
    exact mtFiber10State61_in_close
  · subst state
    exact mtFiber10State62_in_close
  · subst state
    exact mtFiber10State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
