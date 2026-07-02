import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 50

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber50StateAt (i : Nat) : List TauState :=
  directStates (mtFiber50RowAt i).sourceLeft (mtFiber50RowAt i).sourceRight

def mtFiber50DirectStates : List (List TauState) :=
  [mtFiber50StateAt 0, mtFiber50StateAt 1, mtFiber50StateAt 2, mtFiber50StateAt 3, mtFiber50StateAt 4, mtFiber50StateAt 5, mtFiber50StateAt 6, mtFiber50StateAt 7, mtFiber50StateAt 8, mtFiber50StateAt 9, mtFiber50StateAt 10, mtFiber50StateAt 11, mtFiber50StateAt 12, mtFiber50StateAt 13, mtFiber50StateAt 14, mtFiber50StateAt 15, mtFiber50StateAt 16, mtFiber50StateAt 17, mtFiber50StateAt 18, mtFiber50StateAt 19, mtFiber50StateAt 20, mtFiber50StateAt 21, mtFiber50StateAt 22, mtFiber50StateAt 23, mtFiber50StateAt 24, mtFiber50StateAt 25, mtFiber50StateAt 26, mtFiber50StateAt 27, mtFiber50StateAt 28, mtFiber50StateAt 29, mtFiber50StateAt 30, mtFiber50StateAt 31, mtFiber50StateAt 32, mtFiber50StateAt 33, mtFiber50StateAt 34, mtFiber50StateAt 35, mtFiber50StateAt 36, mtFiber50StateAt 37, mtFiber50StateAt 38, mtFiber50StateAt 39, mtFiber50StateAt 40, mtFiber50StateAt 41, mtFiber50StateAt 42, mtFiber50StateAt 43, mtFiber50StateAt 44, mtFiber50StateAt 45, mtFiber50StateAt 46, mtFiber50StateAt 47, mtFiber50StateAt 48, mtFiber50StateAt 49, mtFiber50StateAt 50, mtFiber50StateAt 51, mtFiber50StateAt 52, mtFiber50StateAt 53, mtFiber50StateAt 54, mtFiber50StateAt 55, mtFiber50StateAt 56, mtFiber50StateAt 57, mtFiber50StateAt 58, mtFiber50StateAt 59, mtFiber50StateAt 60, mtFiber50StateAt 61, mtFiber50StateAt 62, mtFiber50StateAt 63]

theorem mtFiber50ReverseRow_1_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk0_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 0) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 1)
    (mtFiber50RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 1) (by decide) mtFiber50ReverseRow_1_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_2_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk1_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 2) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 2)
    (mtFiber50RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 2) (by decide) mtFiber50ReverseRow_2_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_3_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk1_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 2) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 3)
    (mtFiber50RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 3) (by decide) mtFiber50ReverseRow_3_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_4_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk2_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 4) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 4)
    (mtFiber50RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 4) (by decide) mtFiber50ReverseRow_4_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_5_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk2_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 4) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 5)
    (mtFiber50RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 5) (by decide) mtFiber50ReverseRow_5_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_6_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk3_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 6) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 6)
    (mtFiber50RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 6) (by decide) mtFiber50ReverseRow_6_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_7_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk3_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 6) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 7)
    (mtFiber50RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 7) (by decide) mtFiber50ReverseRow_7_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_8_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk4_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 8) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 8)
    (mtFiber50RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 8) (by decide) mtFiber50ReverseRow_8_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_9_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk4_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 8) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 9)
    (mtFiber50RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 9) (by decide) mtFiber50ReverseRow_9_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_10_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk5_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 10) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 2) (mtFiber50StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 2) (mtFiber50StateAt 10)
    (mtFiber50RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 10) (by decide) mtFiber50ReverseRow_10_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_11_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk5_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 10) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 11)
    (mtFiber50RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 11) (by decide) mtFiber50ReverseRow_11_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_12_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk6_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 12) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 12)
    (mtFiber50RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 12) (by decide) mtFiber50ReverseRow_12_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_13_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk6_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 12) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 5) (mtFiber50StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 5) (mtFiber50StateAt 13)
    (mtFiber50RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 13) (by decide) mtFiber50ReverseRow_13_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_14_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk7_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 14) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 6) (mtFiber50StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 6) (mtFiber50StateAt 14)
    (mtFiber50RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 14) (by decide) mtFiber50ReverseRow_14_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_15_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk7_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 14) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 7) (mtFiber50StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 7) (mtFiber50StateAt 15)
    (mtFiber50RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 15) (by decide) mtFiber50ReverseRow_15_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_16_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk8_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 16) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 16)
    (mtFiber50RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 16) (by decide) mtFiber50ReverseRow_16_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_17_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk8_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 16) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 17)
    (mtFiber50RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 17) (by decide) mtFiber50ReverseRow_17_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_18_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk9_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 18) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 2) (mtFiber50StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 2) (mtFiber50StateAt 18)
    (mtFiber50RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 18) (by decide) mtFiber50ReverseRow_18_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_19_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk9_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 18) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 19)
    (mtFiber50RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 19) (by decide) mtFiber50ReverseRow_19_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_20_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk10_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 20) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 20)
    (mtFiber50RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 20) (by decide) mtFiber50ReverseRow_20_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_21_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk10_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 20) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 5) (mtFiber50StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 5) (mtFiber50StateAt 21)
    (mtFiber50RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 21) (by decide) mtFiber50ReverseRow_21_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_22_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk11_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 22) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 6) (mtFiber50StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 6) (mtFiber50StateAt 22)
    (mtFiber50RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 22) (by decide) mtFiber50ReverseRow_22_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_23_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk11_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 22) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 7) (mtFiber50StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 7) (mtFiber50StateAt 23)
    (mtFiber50RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 23) (by decide) mtFiber50ReverseRow_23_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_24_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk12_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 24) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 8) (mtFiber50StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 8) (mtFiber50StateAt 24)
    (mtFiber50RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 24) (by decide) mtFiber50ReverseRow_24_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_25_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk12_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 24) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 9) (mtFiber50StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 9) (mtFiber50StateAt 25)
    (mtFiber50RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 25) (by decide) mtFiber50ReverseRow_25_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_26_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk13_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 26) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 10) (mtFiber50StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 10) (mtFiber50StateAt 26)
    (mtFiber50RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 26) (by decide) mtFiber50ReverseRow_26_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_27_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk13_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 26) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 11) (mtFiber50StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 11) (mtFiber50StateAt 27)
    (mtFiber50RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 27) (by decide) mtFiber50ReverseRow_27_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_28_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk14_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 28) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 12) (mtFiber50StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 12) (mtFiber50StateAt 28)
    (mtFiber50RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 28) (by decide) mtFiber50ReverseRow_28_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_29_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk14_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 28) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 13) (mtFiber50StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 13) (mtFiber50StateAt 29)
    (mtFiber50RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 29) (by decide) mtFiber50ReverseRow_29_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_30_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk15_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 30) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 14) (mtFiber50StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 14) (mtFiber50StateAt 30)
    (mtFiber50RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 30) (by decide) mtFiber50ReverseRow_30_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_31_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk15_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 30) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 15) (mtFiber50StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 15) (mtFiber50StateAt 31)
    (mtFiber50RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 31) (by decide) mtFiber50ReverseRow_31_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_32_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk16_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 32) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 36) (mtFiber50StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 36) (mtFiber50StateAt 32)
    (mtFiber50RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 32) (by decide) mtFiber50ReverseRow_32_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_33_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk16_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 32) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 37) (mtFiber50StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 37) (mtFiber50StateAt 33)
    (mtFiber50RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 33) (by decide) mtFiber50ReverseRow_33_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_34_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk17_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 34) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 20) (mtFiber50StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 20) (mtFiber50StateAt 34)
    (mtFiber50RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 34) (by decide) mtFiber50ReverseRow_34_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_35_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk17_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 34) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 21) (mtFiber50StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 21) (mtFiber50StateAt 35)
    (mtFiber50RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 35) (by decide) mtFiber50ReverseRow_35_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_36_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk18_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 36) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 16) (mtFiber50StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 16) (mtFiber50StateAt 36)
    (mtFiber50RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 36) (by decide) mtFiber50ReverseRow_36_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_37_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk18_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 36) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 17) (mtFiber50StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 17) (mtFiber50StateAt 37)
    (mtFiber50RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 37) (by decide) mtFiber50ReverseRow_37_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_38_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk19_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 38) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 18) (mtFiber50StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 18) (mtFiber50StateAt 38)
    (mtFiber50RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 38) (by decide) mtFiber50ReverseRow_38_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_39_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk19_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 38) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 19) (mtFiber50StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 19) (mtFiber50StateAt 39)
    (mtFiber50RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 39) (by decide) mtFiber50ReverseRow_39_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_40_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk20_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 40) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 44) (mtFiber50StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 44) (mtFiber50StateAt 40)
    (mtFiber50RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 40) (by decide) mtFiber50ReverseRow_40_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_41_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk20_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 40) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 45) (mtFiber50StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 45) (mtFiber50StateAt 41)
    (mtFiber50RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 41) (by decide) mtFiber50ReverseRow_41_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_42_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk21_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 42) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 58) (mtFiber50StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 58) (mtFiber50StateAt 42)
    (mtFiber50RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 42) (by decide) mtFiber50ReverseRow_42_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_43_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk21_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 42) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 59) (mtFiber50StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 59) (mtFiber50StateAt 43)
    (mtFiber50RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 43) (by decide) mtFiber50ReverseRow_43_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_44_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk22_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 44) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 60) (mtFiber50StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 60) (mtFiber50StateAt 44)
    (mtFiber50RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 44) (by decide) mtFiber50ReverseRow_44_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_45_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk22_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 44) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 61) (mtFiber50StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 61) (mtFiber50StateAt 45)
    (mtFiber50RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 45) (by decide) mtFiber50ReverseRow_45_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_46_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk23_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 46) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 62) (mtFiber50StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 62) (mtFiber50StateAt 46)
    (mtFiber50RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 46) (by decide) mtFiber50ReverseRow_46_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_47_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk23_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 46) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 63) (mtFiber50StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 63) (mtFiber50StateAt 47)
    (mtFiber50RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 47) (by decide) mtFiber50ReverseRow_47_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_48_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk24_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 48) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 52) (mtFiber50StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 52) (mtFiber50StateAt 48)
    (mtFiber50RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 48) (by decide) mtFiber50ReverseRow_48_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_49_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk24_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 48) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 53) (mtFiber50StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 53) (mtFiber50StateAt 49)
    (mtFiber50RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 49) (by decide) mtFiber50ReverseRow_49_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_50_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk25_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 50) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 12) (mtFiber50StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 12) (mtFiber50StateAt 50)
    (mtFiber50RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 50) (by decide) mtFiber50ReverseRow_50_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_51_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk25_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 50) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 13) (mtFiber50StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 13) (mtFiber50StateAt 51)
    (mtFiber50RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 51) (by decide) mtFiber50ReverseRow_51_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_52_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk26_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 52) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 8) (mtFiber50StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 8) (mtFiber50StateAt 52)
    (mtFiber50RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 52) (by decide) mtFiber50ReverseRow_52_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_53_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk26_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 52) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 9) (mtFiber50StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 9) (mtFiber50StateAt 53)
    (mtFiber50RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 53) (by decide) mtFiber50ReverseRow_53_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_54_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk27_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 54) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 10) (mtFiber50StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 10) (mtFiber50StateAt 54)
    (mtFiber50RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 54) (by decide) mtFiber50ReverseRow_54_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_55_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk27_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 54) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 11) (mtFiber50StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 11) (mtFiber50StateAt 55)
    (mtFiber50RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 55) (by decide) mtFiber50ReverseRow_55_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_56_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk28_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 56) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 60) (mtFiber50StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 60) (mtFiber50StateAt 56)
    (mtFiber50RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 56) (by decide) mtFiber50ReverseRow_56_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_57_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk28_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 56) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 61) (mtFiber50StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 61) (mtFiber50StateAt 57)
    (mtFiber50RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 57) (by decide) mtFiber50ReverseRow_57_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_58_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk29_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 58) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 4) (mtFiber50StateAt 58)
    (mtFiber50RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 58) (by decide) mtFiber50ReverseRow_58_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_59_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk29_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 58) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 5) (mtFiber50StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 5) (mtFiber50StateAt 59)
    (mtFiber50RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 59) (by decide) mtFiber50ReverseRow_59_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_60_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk30_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 60) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 0) (mtFiber50StateAt 60)
    (mtFiber50RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 60) (by decide) mtFiber50ReverseRow_60_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_61_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk30_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 60) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 1) (mtFiber50StateAt 61)
    (mtFiber50RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 61) (by decide) mtFiber50ReverseRow_61_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_62_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk31_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 62) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber50ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 2) (mtFiber50StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 2) (mtFiber50StateAt 62)
    (mtFiber50RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 62) (by decide) mtFiber50ReverseRow_62_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50ReverseRow_63_ok :
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber50Chunk31_ok
  change (mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 62) &&
    mtRowReverseValid mtFiber50Key mtFiber50Expected (mtFiber50RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber50ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber50StateAt 3) (mtFiber50StateAt 63)
    (mtFiber50RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber50Key mtFiber50Expected
        (mtFiber50RowAt 63) (by decide) mtFiber50ReverseRow_63_ok
      simpa [mtFiber50StateAt, mtFiber50RowAt, mtFiber50Rows, listGetD, directRow] using h)

theorem mtFiber50State0_in_close :
    mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  change mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 64 [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 0 64 [mtFiber50StateAt 0] (mtFiber50StateAt 0) (by simp [closeChainFiber])

theorem mtFiber50State1_in_close :
    mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  change mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates (1 + 63) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 1 63 [mtFiber50StateAt 0] (mtFiber50StateAt 1) h1

theorem mtFiber50State2_in_close :
    mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  change mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 2) h2

theorem mtFiber50State3_in_close :
    mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  change mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates (1 + 63) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 1 63 [mtFiber50StateAt 0] (mtFiber50StateAt 3) h1

theorem mtFiber50State4_in_close :
    mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  change mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates (1 + 63) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 1 63 [mtFiber50StateAt 0] (mtFiber50StateAt 4) h1

theorem mtFiber50State5_in_close :
    mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  change mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 5) h2

theorem mtFiber50State6_in_close :
    mtFiber50StateAt 6 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 6 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 6) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep6
  change mtFiber50StateAt 6 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 6) h2

theorem mtFiber50State7_in_close :
    mtFiber50StateAt 7 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 7 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 7) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep7
  change mtFiber50StateAt 7 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 7) h2

theorem mtFiber50State8_in_close :
    mtFiber50StateAt 8 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 8 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 8) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep8
  change mtFiber50StateAt 8 ∈ closeChainFiber mtWord mtFiber50DirectStates (1 + 63) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 1 63 [mtFiber50StateAt 0] (mtFiber50StateAt 8) h1

theorem mtFiber50State9_in_close :
    mtFiber50StateAt 9 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 9 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 9) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep9
  change mtFiber50StateAt 9 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 9) h2

theorem mtFiber50State10_in_close :
    mtFiber50StateAt 10 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  have h3 : mtFiber50StateAt 10 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 2) (mtFiber50StateAt 10) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep10
  change mtFiber50StateAt 10 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 10) h3

theorem mtFiber50State11_in_close :
    mtFiber50StateAt 11 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 11 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 11) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep11
  change mtFiber50StateAt 11 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 11) h2

theorem mtFiber50State12_in_close :
    mtFiber50StateAt 12 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 12 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 12) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep12
  change mtFiber50StateAt 12 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 12) h2

theorem mtFiber50State13_in_close :
    mtFiber50StateAt 13 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  have h3 : mtFiber50StateAt 13 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 5) (mtFiber50StateAt 13) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep13
  change mtFiber50StateAt 13 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 13) h3

theorem mtFiber50State14_in_close :
    mtFiber50StateAt 14 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 6 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 6) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep6
  have h3 : mtFiber50StateAt 14 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 6) (mtFiber50StateAt 14) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep14
  change mtFiber50StateAt 14 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 14) h3

theorem mtFiber50State15_in_close :
    mtFiber50StateAt 15 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 7 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 7) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep7
  have h3 : mtFiber50StateAt 15 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 7) (mtFiber50StateAt 15) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep15
  change mtFiber50StateAt 15 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 15) h3

theorem mtFiber50State16_in_close :
    mtFiber50StateAt 16 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 16 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 16) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep16
  change mtFiber50StateAt 16 ∈ closeChainFiber mtWord mtFiber50DirectStates (1 + 63) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 1 63 [mtFiber50StateAt 0] (mtFiber50StateAt 16) h1

theorem mtFiber50State17_in_close :
    mtFiber50StateAt 17 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 17 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 17) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep17
  change mtFiber50StateAt 17 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 17) h2

theorem mtFiber50State18_in_close :
    mtFiber50StateAt 18 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  have h3 : mtFiber50StateAt 18 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 2) (mtFiber50StateAt 18) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep18
  change mtFiber50StateAt 18 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 18) h3

theorem mtFiber50State19_in_close :
    mtFiber50StateAt 19 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 19 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 19) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep19
  change mtFiber50StateAt 19 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 19) h2

theorem mtFiber50State20_in_close :
    mtFiber50StateAt 20 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 20 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 20) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep20
  change mtFiber50StateAt 20 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 20) h2

theorem mtFiber50State21_in_close :
    mtFiber50StateAt 21 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  have h3 : mtFiber50StateAt 21 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 5) (mtFiber50StateAt 21) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep21
  change mtFiber50StateAt 21 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 21) h3

theorem mtFiber50State22_in_close :
    mtFiber50StateAt 22 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 6 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 6) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep6
  have h3 : mtFiber50StateAt 22 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 6) (mtFiber50StateAt 22) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep22
  change mtFiber50StateAt 22 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 22) h3

theorem mtFiber50State23_in_close :
    mtFiber50StateAt 23 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 7 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 7) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep7
  have h3 : mtFiber50StateAt 23 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 7) (mtFiber50StateAt 23) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep23
  change mtFiber50StateAt 23 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 23) h3

theorem mtFiber50State24_in_close :
    mtFiber50StateAt 24 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 8 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 8) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep8
  have h2 : mtFiber50StateAt 24 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 8) (mtFiber50StateAt 24) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep24
  change mtFiber50StateAt 24 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 24) h2

theorem mtFiber50State25_in_close :
    mtFiber50StateAt 25 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 9 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 9) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep9
  have h3 : mtFiber50StateAt 25 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 9) (mtFiber50StateAt 25) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep25
  change mtFiber50StateAt 25 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 25) h3

theorem mtFiber50State26_in_close :
    mtFiber50StateAt 26 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  have h3 : mtFiber50StateAt 10 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 2) (mtFiber50StateAt 10) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep10
  have h4 : mtFiber50StateAt 26 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 10) (mtFiber50StateAt 26) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep26
  change mtFiber50StateAt 26 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 26) h4

theorem mtFiber50State27_in_close :
    mtFiber50StateAt 27 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 11 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 11) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep11
  have h3 : mtFiber50StateAt 27 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 11) (mtFiber50StateAt 27) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep27
  change mtFiber50StateAt 27 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 27) h3

theorem mtFiber50State28_in_close :
    mtFiber50StateAt 28 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 12 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 12) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep12
  have h3 : mtFiber50StateAt 28 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 12) (mtFiber50StateAt 28) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep28
  change mtFiber50StateAt 28 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 28) h3

theorem mtFiber50State29_in_close :
    mtFiber50StateAt 29 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  have h3 : mtFiber50StateAt 13 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 5) (mtFiber50StateAt 13) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep13
  have h4 : mtFiber50StateAt 29 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 13) (mtFiber50StateAt 29) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep29
  change mtFiber50StateAt 29 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 29) h4

theorem mtFiber50State30_in_close :
    mtFiber50StateAt 30 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 6 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 6) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep6
  have h3 : mtFiber50StateAt 14 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 6) (mtFiber50StateAt 14) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep14
  have h4 : mtFiber50StateAt 30 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 14) (mtFiber50StateAt 30) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep30
  change mtFiber50StateAt 30 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 30) h4

theorem mtFiber50State31_in_close :
    mtFiber50StateAt 31 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 7 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 7) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep7
  have h3 : mtFiber50StateAt 15 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 7) (mtFiber50StateAt 15) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep15
  have h4 : mtFiber50StateAt 31 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 15) (mtFiber50StateAt 31) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep31
  change mtFiber50StateAt 31 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 31) h4

theorem mtFiber50State32_in_close :
    mtFiber50StateAt 32 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 16 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 16) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep16
  have h2 : mtFiber50StateAt 36 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 16) (mtFiber50StateAt 36) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep36
  have h3 : mtFiber50StateAt 32 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 36) (mtFiber50StateAt 32) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep32
  change mtFiber50StateAt 32 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 32) h3

theorem mtFiber50State33_in_close :
    mtFiber50StateAt 33 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 17 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 17) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep17
  have h3 : mtFiber50StateAt 37 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 17) (mtFiber50StateAt 37) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep37
  have h4 : mtFiber50StateAt 33 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 37) (mtFiber50StateAt 33) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep33
  change mtFiber50StateAt 33 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 33) h4

theorem mtFiber50State34_in_close :
    mtFiber50StateAt 34 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 20 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 20) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep20
  have h3 : mtFiber50StateAt 34 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 20) (mtFiber50StateAt 34) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep34
  change mtFiber50StateAt 34 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 34) h3

theorem mtFiber50State35_in_close :
    mtFiber50StateAt 35 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  have h3 : mtFiber50StateAt 21 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 5) (mtFiber50StateAt 21) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep21
  have h4 : mtFiber50StateAt 35 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 21) (mtFiber50StateAt 35) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep35
  change mtFiber50StateAt 35 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 35) h4

theorem mtFiber50State36_in_close :
    mtFiber50StateAt 36 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 16 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 16) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep16
  have h2 : mtFiber50StateAt 36 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 16) (mtFiber50StateAt 36) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep36
  change mtFiber50StateAt 36 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 36) h2

theorem mtFiber50State37_in_close :
    mtFiber50StateAt 37 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 17 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 17) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep17
  have h3 : mtFiber50StateAt 37 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 17) (mtFiber50StateAt 37) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep37
  change mtFiber50StateAt 37 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 37) h3

theorem mtFiber50State38_in_close :
    mtFiber50StateAt 38 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  have h3 : mtFiber50StateAt 18 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 2) (mtFiber50StateAt 18) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep18
  have h4 : mtFiber50StateAt 38 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 18) (mtFiber50StateAt 38) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep38
  change mtFiber50StateAt 38 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 38) h4

theorem mtFiber50State39_in_close :
    mtFiber50StateAt 39 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 19 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 19) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep19
  have h3 : mtFiber50StateAt 39 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 19) (mtFiber50StateAt 39) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep39
  change mtFiber50StateAt 39 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 39) h3

theorem mtFiber50State40_in_close :
    mtFiber50StateAt 40 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 60 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 60) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep60
  have h2 : mtFiber50StateAt 44 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 60) (mtFiber50StateAt 44) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep44
  have h3 : mtFiber50StateAt 40 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 44) (mtFiber50StateAt 40) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep40
  change mtFiber50StateAt 40 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 40) h3

theorem mtFiber50State41_in_close :
    mtFiber50StateAt 41 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 61 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 61) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep61
  have h3 : mtFiber50StateAt 45 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 61) (mtFiber50StateAt 45) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep45
  have h4 : mtFiber50StateAt 41 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 45) (mtFiber50StateAt 41) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep41
  change mtFiber50StateAt 41 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 41) h4

theorem mtFiber50State42_in_close :
    mtFiber50StateAt 42 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 58 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 58) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep58
  have h3 : mtFiber50StateAt 42 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 58) (mtFiber50StateAt 42) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep42
  change mtFiber50StateAt 42 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 42) h3

theorem mtFiber50State43_in_close :
    mtFiber50StateAt 43 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  have h3 : mtFiber50StateAt 59 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 5) (mtFiber50StateAt 59) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep59
  have h4 : mtFiber50StateAt 43 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 59) (mtFiber50StateAt 43) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep43
  change mtFiber50StateAt 43 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 43) h4

theorem mtFiber50State44_in_close :
    mtFiber50StateAt 44 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 60 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 60) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep60
  have h2 : mtFiber50StateAt 44 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 60) (mtFiber50StateAt 44) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep44
  change mtFiber50StateAt 44 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 44) h2

theorem mtFiber50State45_in_close :
    mtFiber50StateAt 45 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 61 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 61) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep61
  have h3 : mtFiber50StateAt 45 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 61) (mtFiber50StateAt 45) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep45
  change mtFiber50StateAt 45 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 45) h3

theorem mtFiber50State46_in_close :
    mtFiber50StateAt 46 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  have h3 : mtFiber50StateAt 62 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 2) (mtFiber50StateAt 62) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep62
  have h4 : mtFiber50StateAt 46 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 62) (mtFiber50StateAt 46) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep46
  change mtFiber50StateAt 46 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 46) h4

theorem mtFiber50State47_in_close :
    mtFiber50StateAt 47 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 63 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 63) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep63
  have h3 : mtFiber50StateAt 47 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 63) (mtFiber50StateAt 47) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep47
  change mtFiber50StateAt 47 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 47) h3

theorem mtFiber50State48_in_close :
    mtFiber50StateAt 48 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 8 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 8) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep8
  have h2 : mtFiber50StateAt 52 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 8) (mtFiber50StateAt 52) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep52
  have h3 : mtFiber50StateAt 48 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 52) (mtFiber50StateAt 48) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep48
  change mtFiber50StateAt 48 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 48) h3

theorem mtFiber50State49_in_close :
    mtFiber50StateAt 49 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 9 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 9) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep9
  have h3 : mtFiber50StateAt 53 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 9) (mtFiber50StateAt 53) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep53
  have h4 : mtFiber50StateAt 49 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 53) (mtFiber50StateAt 49) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep49
  change mtFiber50StateAt 49 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 49) h4

theorem mtFiber50State50_in_close :
    mtFiber50StateAt 50 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 12 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 12) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep12
  have h3 : mtFiber50StateAt 50 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 12) (mtFiber50StateAt 50) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep50
  change mtFiber50StateAt 50 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 50) h3

theorem mtFiber50State51_in_close :
    mtFiber50StateAt 51 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  have h3 : mtFiber50StateAt 13 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 5) (mtFiber50StateAt 13) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep13
  have h4 : mtFiber50StateAt 51 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 13) (mtFiber50StateAt 51) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep51
  change mtFiber50StateAt 51 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 51) h4

theorem mtFiber50State52_in_close :
    mtFiber50StateAt 52 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 8 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 8) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep8
  have h2 : mtFiber50StateAt 52 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 8) (mtFiber50StateAt 52) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep52
  change mtFiber50StateAt 52 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 52) h2

theorem mtFiber50State53_in_close :
    mtFiber50StateAt 53 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 9 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 9) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep9
  have h3 : mtFiber50StateAt 53 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 9) (mtFiber50StateAt 53) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep53
  change mtFiber50StateAt 53 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 53) h3

theorem mtFiber50State54_in_close :
    mtFiber50StateAt 54 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  have h3 : mtFiber50StateAt 10 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 2) (mtFiber50StateAt 10) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep10
  have h4 : mtFiber50StateAt 54 ∈ closeChainFiber mtWord mtFiber50DirectStates 4 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0]
      (mtFiber50StateAt 10) (mtFiber50StateAt 54) (by decide) h3 (by decide)
      mtFiber50ReverseSingleStep54
  change mtFiber50StateAt 54 ∈ closeChainFiber mtWord mtFiber50DirectStates (4 + 60) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 4 60 [mtFiber50StateAt 0] (mtFiber50StateAt 54) h4

theorem mtFiber50State55_in_close :
    mtFiber50StateAt 55 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 11 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 11) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep11
  have h3 : mtFiber50StateAt 55 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 11) (mtFiber50StateAt 55) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep55
  change mtFiber50StateAt 55 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 55) h3

theorem mtFiber50State56_in_close :
    mtFiber50StateAt 56 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 60 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 60) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep60
  have h2 : mtFiber50StateAt 56 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 60) (mtFiber50StateAt 56) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep56
  change mtFiber50StateAt 56 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 56) h2

theorem mtFiber50State57_in_close :
    mtFiber50StateAt 57 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 61 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 61) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep61
  have h3 : mtFiber50StateAt 57 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 61) (mtFiber50StateAt 57) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep57
  change mtFiber50StateAt 57 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 57) h3

theorem mtFiber50State58_in_close :
    mtFiber50StateAt 58 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 4 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 4) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep4
  have h2 : mtFiber50StateAt 58 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 4) (mtFiber50StateAt 58) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep58
  change mtFiber50StateAt 58 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 58) h2

theorem mtFiber50State59_in_close :
    mtFiber50StateAt 59 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 5 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 5) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep5
  have h3 : mtFiber50StateAt 59 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 5) (mtFiber50StateAt 59) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep59
  change mtFiber50StateAt 59 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 59) h3

theorem mtFiber50State60_in_close :
    mtFiber50StateAt 60 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 60 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 60) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep60
  change mtFiber50StateAt 60 ∈ closeChainFiber mtWord mtFiber50DirectStates (1 + 63) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 1 63 [mtFiber50StateAt 0] (mtFiber50StateAt 60) h1

theorem mtFiber50State61_in_close :
    mtFiber50StateAt 61 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 61 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 61) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep61
  change mtFiber50StateAt 61 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 61) h2

theorem mtFiber50State62_in_close :
    mtFiber50StateAt 62 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 1 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 1) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep1
  have h2 : mtFiber50StateAt 2 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 1) (mtFiber50StateAt 2) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep2
  have h3 : mtFiber50StateAt 62 ∈ closeChainFiber mtWord mtFiber50DirectStates 3 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0]
      (mtFiber50StateAt 2) (mtFiber50StateAt 62) (by decide) h2 (by decide)
      mtFiber50ReverseSingleStep62
  change mtFiber50StateAt 62 ∈ closeChainFiber mtWord mtFiber50DirectStates (3 + 61) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 3 61 [mtFiber50StateAt 0] (mtFiber50StateAt 62) h3

theorem mtFiber50State63_in_close :
    mtFiber50StateAt 63 ∈ closeChainFiber mtWord mtFiber50DirectStates mtFiber50DirectStates.length [mtFiber50StateAt 0] := by
  have h0 : mtFiber50StateAt 0 ∈ closeChainFiber mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber50StateAt 3 ∈ closeChainFiber mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 0 [mtFiber50StateAt 0]
      (mtFiber50StateAt 0) (mtFiber50StateAt 3) (by decide) h0 (by decide)
      mtFiber50ReverseSingleStep3
  have h2 : mtFiber50StateAt 63 ∈ closeChainFiber mtWord mtFiber50DirectStates 2 [mtFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber50DirectStates 1 [mtFiber50StateAt 0]
      (mtFiber50StateAt 3) (mtFiber50StateAt 63) (by decide) h1 (by decide)
      mtFiber50ReverseSingleStep63
  change mtFiber50StateAt 63 ∈ closeChainFiber mtWord mtFiber50DirectStates (2 + 62) [mtFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber50DirectStates 2 62 [mtFiber50StateAt 0] (mtFiber50StateAt 63) h2

theorem mtFiber50DirectConnected :
    chainFiberConnected mtWord mtFiber50DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber50DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber50State0_in_close
  · subst state
    exact mtFiber50State1_in_close
  · subst state
    exact mtFiber50State2_in_close
  · subst state
    exact mtFiber50State3_in_close
  · subst state
    exact mtFiber50State4_in_close
  · subst state
    exact mtFiber50State5_in_close
  · subst state
    exact mtFiber50State6_in_close
  · subst state
    exact mtFiber50State7_in_close
  · subst state
    exact mtFiber50State8_in_close
  · subst state
    exact mtFiber50State9_in_close
  · subst state
    exact mtFiber50State10_in_close
  · subst state
    exact mtFiber50State11_in_close
  · subst state
    exact mtFiber50State12_in_close
  · subst state
    exact mtFiber50State13_in_close
  · subst state
    exact mtFiber50State14_in_close
  · subst state
    exact mtFiber50State15_in_close
  · subst state
    exact mtFiber50State16_in_close
  · subst state
    exact mtFiber50State17_in_close
  · subst state
    exact mtFiber50State18_in_close
  · subst state
    exact mtFiber50State19_in_close
  · subst state
    exact mtFiber50State20_in_close
  · subst state
    exact mtFiber50State21_in_close
  · subst state
    exact mtFiber50State22_in_close
  · subst state
    exact mtFiber50State23_in_close
  · subst state
    exact mtFiber50State24_in_close
  · subst state
    exact mtFiber50State25_in_close
  · subst state
    exact mtFiber50State26_in_close
  · subst state
    exact mtFiber50State27_in_close
  · subst state
    exact mtFiber50State28_in_close
  · subst state
    exact mtFiber50State29_in_close
  · subst state
    exact mtFiber50State30_in_close
  · subst state
    exact mtFiber50State31_in_close
  · subst state
    exact mtFiber50State32_in_close
  · subst state
    exact mtFiber50State33_in_close
  · subst state
    exact mtFiber50State34_in_close
  · subst state
    exact mtFiber50State35_in_close
  · subst state
    exact mtFiber50State36_in_close
  · subst state
    exact mtFiber50State37_in_close
  · subst state
    exact mtFiber50State38_in_close
  · subst state
    exact mtFiber50State39_in_close
  · subst state
    exact mtFiber50State40_in_close
  · subst state
    exact mtFiber50State41_in_close
  · subst state
    exact mtFiber50State42_in_close
  · subst state
    exact mtFiber50State43_in_close
  · subst state
    exact mtFiber50State44_in_close
  · subst state
    exact mtFiber50State45_in_close
  · subst state
    exact mtFiber50State46_in_close
  · subst state
    exact mtFiber50State47_in_close
  · subst state
    exact mtFiber50State48_in_close
  · subst state
    exact mtFiber50State49_in_close
  · subst state
    exact mtFiber50State50_in_close
  · subst state
    exact mtFiber50State51_in_close
  · subst state
    exact mtFiber50State52_in_close
  · subst state
    exact mtFiber50State53_in_close
  · subst state
    exact mtFiber50State54_in_close
  · subst state
    exact mtFiber50State55_in_close
  · subst state
    exact mtFiber50State56_in_close
  · subst state
    exact mtFiber50State57_in_close
  · subst state
    exact mtFiber50State58_in_close
  · subst state
    exact mtFiber50State59_in_close
  · subst state
    exact mtFiber50State60_in_close
  · subst state
    exact mtFiber50State61_in_close
  · subst state
    exact mtFiber50State62_in_close
  · subst state
    exact mtFiber50State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
