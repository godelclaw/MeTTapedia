import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 72

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber72StateAt (i : Nat) : List TauState :=
  directStates (mtFiber72RowAt i).sourceLeft (mtFiber72RowAt i).sourceRight

def mtFiber72DirectStates : List (List TauState) :=
  [mtFiber72StateAt 0, mtFiber72StateAt 1, mtFiber72StateAt 2, mtFiber72StateAt 3, mtFiber72StateAt 4, mtFiber72StateAt 5, mtFiber72StateAt 6, mtFiber72StateAt 7, mtFiber72StateAt 8, mtFiber72StateAt 9, mtFiber72StateAt 10, mtFiber72StateAt 11, mtFiber72StateAt 12, mtFiber72StateAt 13, mtFiber72StateAt 14, mtFiber72StateAt 15, mtFiber72StateAt 16, mtFiber72StateAt 17, mtFiber72StateAt 18, mtFiber72StateAt 19, mtFiber72StateAt 20, mtFiber72StateAt 21, mtFiber72StateAt 22, mtFiber72StateAt 23, mtFiber72StateAt 24, mtFiber72StateAt 25, mtFiber72StateAt 26, mtFiber72StateAt 27, mtFiber72StateAt 28, mtFiber72StateAt 29, mtFiber72StateAt 30, mtFiber72StateAt 31, mtFiber72StateAt 32, mtFiber72StateAt 33, mtFiber72StateAt 34, mtFiber72StateAt 35, mtFiber72StateAt 36, mtFiber72StateAt 37, mtFiber72StateAt 38, mtFiber72StateAt 39, mtFiber72StateAt 40, mtFiber72StateAt 41, mtFiber72StateAt 42, mtFiber72StateAt 43, mtFiber72StateAt 44, mtFiber72StateAt 45, mtFiber72StateAt 46, mtFiber72StateAt 47, mtFiber72StateAt 48, mtFiber72StateAt 49, mtFiber72StateAt 50, mtFiber72StateAt 51, mtFiber72StateAt 52, mtFiber72StateAt 53, mtFiber72StateAt 54, mtFiber72StateAt 55, mtFiber72StateAt 56, mtFiber72StateAt 57, mtFiber72StateAt 58, mtFiber72StateAt 59, mtFiber72StateAt 60, mtFiber72StateAt 61, mtFiber72StateAt 62, mtFiber72StateAt 63]

theorem mtFiber72ReverseRow_1_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk0_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 0) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 1)
    (mtFiber72RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 1) (by decide) mtFiber72ReverseRow_1_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_2_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk1_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 2) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 2)
    (mtFiber72RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 2) (by decide) mtFiber72ReverseRow_2_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_3_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk1_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 2) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 3)
    (mtFiber72RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 3) (by decide) mtFiber72ReverseRow_3_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_4_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk2_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 4) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 4)
    (mtFiber72RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 4) (by decide) mtFiber72ReverseRow_4_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_5_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk2_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 4) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 5)
    (mtFiber72RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 5) (by decide) mtFiber72ReverseRow_5_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_6_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk3_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 6) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 6)
    (mtFiber72RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 6) (by decide) mtFiber72ReverseRow_6_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_7_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk3_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 6) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 7)
    (mtFiber72RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 7) (by decide) mtFiber72ReverseRow_7_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_8_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk4_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 8) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 8)
    (mtFiber72RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 8) (by decide) mtFiber72ReverseRow_8_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_9_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk4_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 8) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 9)
    (mtFiber72RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 9) (by decide) mtFiber72ReverseRow_9_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_10_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk5_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 10) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 10)
    (mtFiber72RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 10) (by decide) mtFiber72ReverseRow_10_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_11_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk5_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 10) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 3) (mtFiber72StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 3) (mtFiber72StateAt 11)
    (mtFiber72RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 11) (by decide) mtFiber72ReverseRow_11_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_12_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk6_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 12) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 4) (mtFiber72StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 4) (mtFiber72StateAt 12)
    (mtFiber72RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 12) (by decide) mtFiber72ReverseRow_12_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_13_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk6_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 12) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 5) (mtFiber72StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 5) (mtFiber72StateAt 13)
    (mtFiber72RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 13) (by decide) mtFiber72ReverseRow_13_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_14_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk7_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 14) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 6) (mtFiber72StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 6) (mtFiber72StateAt 14)
    (mtFiber72RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 14) (by decide) mtFiber72ReverseRow_14_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_15_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk7_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 14) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 15)
    (mtFiber72RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 15) (by decide) mtFiber72ReverseRow_15_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_16_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk8_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 16) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 8) (mtFiber72StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 8) (mtFiber72StateAt 16)
    (mtFiber72RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 16) (by decide) mtFiber72ReverseRow_16_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_17_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk8_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 16) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 9) (mtFiber72StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 9) (mtFiber72StateAt 17)
    (mtFiber72RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 17) (by decide) mtFiber72ReverseRow_17_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_18_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk9_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 18) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 10) (mtFiber72StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 10) (mtFiber72StateAt 18)
    (mtFiber72RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 18) (by decide) mtFiber72ReverseRow_18_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_19_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk9_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 18) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 11) (mtFiber72StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 11) (mtFiber72StateAt 19)
    (mtFiber72RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 19) (by decide) mtFiber72ReverseRow_19_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_20_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk10_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 20) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 12) (mtFiber72StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 12) (mtFiber72StateAt 20)
    (mtFiber72RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 20) (by decide) mtFiber72ReverseRow_20_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_21_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk10_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 20) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 13) (mtFiber72StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 13) (mtFiber72StateAt 21)
    (mtFiber72RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 21) (by decide) mtFiber72ReverseRow_21_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_22_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk11_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 22) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 14) (mtFiber72StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 14) (mtFiber72StateAt 22)
    (mtFiber72RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 22) (by decide) mtFiber72ReverseRow_22_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_23_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk11_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 22) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 15) (mtFiber72StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 15) (mtFiber72StateAt 23)
    (mtFiber72RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 23) (by decide) mtFiber72ReverseRow_23_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_24_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk12_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 24) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 24)
    (mtFiber72RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 24) (by decide) mtFiber72ReverseRow_24_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_25_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk12_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 24) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 25)
    (mtFiber72RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 25) (by decide) mtFiber72ReverseRow_25_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_26_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk13_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 26) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 26)
    (mtFiber72RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 26) (by decide) mtFiber72ReverseRow_26_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_27_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk13_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 26) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 3) (mtFiber72StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 3) (mtFiber72StateAt 27)
    (mtFiber72RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 27) (by decide) mtFiber72ReverseRow_27_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_28_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk14_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 28) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 4) (mtFiber72StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 4) (mtFiber72StateAt 28)
    (mtFiber72RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 28) (by decide) mtFiber72ReverseRow_28_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_29_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk14_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 28) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 5) (mtFiber72StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 5) (mtFiber72StateAt 29)
    (mtFiber72RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 29) (by decide) mtFiber72ReverseRow_29_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_30_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk15_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 30) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 6) (mtFiber72StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 6) (mtFiber72StateAt 30)
    (mtFiber72RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 30) (by decide) mtFiber72ReverseRow_30_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_31_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk15_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 30) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 31)
    (mtFiber72RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 31) (by decide) mtFiber72ReverseRow_31_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_32_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk16_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 32) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 0) (mtFiber72StateAt 32)
    (mtFiber72RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 32) (by decide) mtFiber72ReverseRow_32_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_33_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk16_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 32) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 1) (mtFiber72StateAt 33)
    (mtFiber72RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 33) (by decide) mtFiber72ReverseRow_33_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_34_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk17_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 34) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 2) (mtFiber72StateAt 34)
    (mtFiber72RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 34) (by decide) mtFiber72ReverseRow_34_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_35_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk17_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 34) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 3) (mtFiber72StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 3) (mtFiber72StateAt 35)
    (mtFiber72RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 35) (by decide) mtFiber72ReverseRow_35_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_36_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk18_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 36) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 32) (mtFiber72StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 32) (mtFiber72StateAt 36)
    (mtFiber72RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 36) (by decide) mtFiber72ReverseRow_36_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_37_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk18_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 36) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 33) (mtFiber72StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 33) (mtFiber72StateAt 37)
    (mtFiber72RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 37) (by decide) mtFiber72ReverseRow_37_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_38_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk19_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 38) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 6) (mtFiber72StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 6) (mtFiber72StateAt 38)
    (mtFiber72RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 38) (by decide) mtFiber72ReverseRow_38_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_39_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk19_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 38) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 7) (mtFiber72StateAt 39)
    (mtFiber72RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 39) (by decide) mtFiber72ReverseRow_39_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_40_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk20_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 40) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 8) (mtFiber72StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 8) (mtFiber72StateAt 40)
    (mtFiber72RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 40) (by decide) mtFiber72ReverseRow_40_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_41_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk20_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 40) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 9) (mtFiber72StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 9) (mtFiber72StateAt 41)
    (mtFiber72RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 41) (by decide) mtFiber72ReverseRow_41_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_42_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk21_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 42) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 10) (mtFiber72StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 10) (mtFiber72StateAt 42)
    (mtFiber72RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 42) (by decide) mtFiber72ReverseRow_42_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_43_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk21_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 42) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 11) (mtFiber72StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 11) (mtFiber72StateAt 43)
    (mtFiber72RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 43) (by decide) mtFiber72ReverseRow_43_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_44_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk22_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 44) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 40) (mtFiber72StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 40) (mtFiber72StateAt 44)
    (mtFiber72RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 44) (by decide) mtFiber72ReverseRow_44_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_45_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk22_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 44) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 41) (mtFiber72StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 41) (mtFiber72StateAt 45)
    (mtFiber72RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 45) (by decide) mtFiber72ReverseRow_45_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_46_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk23_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 46) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 14) (mtFiber72StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 14) (mtFiber72StateAt 46)
    (mtFiber72RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 46) (by decide) mtFiber72ReverseRow_46_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_47_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk23_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 46) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 15) (mtFiber72StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 15) (mtFiber72StateAt 47)
    (mtFiber72RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 47) (by decide) mtFiber72ReverseRow_47_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_48_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk24_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 48) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 32) (mtFiber72StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 32) (mtFiber72StateAt 48)
    (mtFiber72RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 48) (by decide) mtFiber72ReverseRow_48_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_49_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk24_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 48) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 33) (mtFiber72StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 33) (mtFiber72StateAt 49)
    (mtFiber72RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 49) (by decide) mtFiber72ReverseRow_49_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_50_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk25_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 50) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 34) (mtFiber72StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 34) (mtFiber72StateAt 50)
    (mtFiber72RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 50) (by decide) mtFiber72ReverseRow_50_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_51_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk25_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 50) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 35) (mtFiber72StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 35) (mtFiber72StateAt 51)
    (mtFiber72RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 51) (by decide) mtFiber72ReverseRow_51_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_52_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk26_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 52) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 36) (mtFiber72StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 36) (mtFiber72StateAt 52)
    (mtFiber72RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 52) (by decide) mtFiber72ReverseRow_52_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_53_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk26_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 52) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 37) (mtFiber72StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 37) (mtFiber72StateAt 53)
    (mtFiber72RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 53) (by decide) mtFiber72ReverseRow_53_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_54_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk27_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 54) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 38) (mtFiber72StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 38) (mtFiber72StateAt 54)
    (mtFiber72RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 54) (by decide) mtFiber72ReverseRow_54_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_55_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk27_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 54) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 39) (mtFiber72StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 39) (mtFiber72StateAt 55)
    (mtFiber72RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 55) (by decide) mtFiber72ReverseRow_55_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_56_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk28_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 56) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 24) (mtFiber72StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 24) (mtFiber72StateAt 56)
    (mtFiber72RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 56) (by decide) mtFiber72ReverseRow_56_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_57_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk28_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 56) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 25) (mtFiber72StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 25) (mtFiber72StateAt 57)
    (mtFiber72RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 57) (by decide) mtFiber72ReverseRow_57_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_58_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk29_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 58) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 26) (mtFiber72StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 26) (mtFiber72StateAt 58)
    (mtFiber72RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 58) (by decide) mtFiber72ReverseRow_58_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_59_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk29_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 58) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 27) (mtFiber72StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 27) (mtFiber72StateAt 59)
    (mtFiber72RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 59) (by decide) mtFiber72ReverseRow_59_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_60_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk30_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 60) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 56) (mtFiber72StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 56) (mtFiber72StateAt 60)
    (mtFiber72RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 60) (by decide) mtFiber72ReverseRow_60_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_61_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk30_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 60) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 57) (mtFiber72StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 57) (mtFiber72StateAt 61)
    (mtFiber72RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 61) (by decide) mtFiber72ReverseRow_61_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_62_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk31_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 62) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber72ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 30) (mtFiber72StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 30) (mtFiber72StateAt 62)
    (mtFiber72RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 62) (by decide) mtFiber72ReverseRow_62_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72ReverseRow_63_ok :
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber72Chunk31_ok
  change (mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 62) &&
    mtRowReverseValid mtFiber72Key mtFiber72Expected (mtFiber72RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber72ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber72StateAt 31) (mtFiber72StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber72StateAt 31) (mtFiber72StateAt 63)
    (mtFiber72RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber72Key mtFiber72Expected
        (mtFiber72RowAt 63) (by decide) mtFiber72ReverseRow_63_ok
      simpa [mtFiber72StateAt, mtFiber72RowAt, mtFiber72Rows, listGetD, directRow] using h)

theorem mtFiber72State0_in_close :
    mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  change mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 64 [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 0 64 [mtFiber72StateAt 0] (mtFiber72StateAt 0) (by simp [closeChainFiber])

theorem mtFiber72State1_in_close :
    mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  change mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates (1 + 63) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 1 63 [mtFiber72StateAt 0] (mtFiber72StateAt 1) h1

theorem mtFiber72State2_in_close :
    mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  change mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates (1 + 63) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 1 63 [mtFiber72StateAt 0] (mtFiber72StateAt 2) h1

theorem mtFiber72State3_in_close :
    mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  change mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 3) h2

theorem mtFiber72State4_in_close :
    mtFiber72StateAt 4 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 4 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 4) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep4
  change mtFiber72StateAt 4 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 4) h2

theorem mtFiber72State5_in_close :
    mtFiber72StateAt 5 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 5 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 5) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep5
  change mtFiber72StateAt 5 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 5) h2

theorem mtFiber72State6_in_close :
    mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  change mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 6) h2

theorem mtFiber72State7_in_close :
    mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  change mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates (1 + 63) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 1 63 [mtFiber72StateAt 0] (mtFiber72StateAt 7) h1

theorem mtFiber72State8_in_close :
    mtFiber72StateAt 8 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 8 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 8) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep8
  change mtFiber72StateAt 8 ∈ closeChainFiber mtWord mtFiber72DirectStates (1 + 63) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 1 63 [mtFiber72StateAt 0] (mtFiber72StateAt 8) h1

theorem mtFiber72State9_in_close :
    mtFiber72StateAt 9 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 9 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 9) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep9
  change mtFiber72StateAt 9 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 9) h2

theorem mtFiber72State10_in_close :
    mtFiber72StateAt 10 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 10 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 10) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep10
  change mtFiber72StateAt 10 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 10) h2

theorem mtFiber72State11_in_close :
    mtFiber72StateAt 11 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  have h3 : mtFiber72StateAt 11 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 3) (mtFiber72StateAt 11) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep11
  change mtFiber72StateAt 11 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 11) h3

theorem mtFiber72State12_in_close :
    mtFiber72StateAt 12 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 4 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 4) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep4
  have h3 : mtFiber72StateAt 12 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 4) (mtFiber72StateAt 12) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep12
  change mtFiber72StateAt 12 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 12) h3

theorem mtFiber72State13_in_close :
    mtFiber72StateAt 13 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 5 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 5) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep5
  have h3 : mtFiber72StateAt 13 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 5) (mtFiber72StateAt 13) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep13
  change mtFiber72StateAt 13 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 13) h3

theorem mtFiber72State14_in_close :
    mtFiber72StateAt 14 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  have h3 : mtFiber72StateAt 14 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 6) (mtFiber72StateAt 14) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep14
  change mtFiber72StateAt 14 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 14) h3

theorem mtFiber72State15_in_close :
    mtFiber72StateAt 15 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 15 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 15) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep15
  change mtFiber72StateAt 15 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 15) h2

theorem mtFiber72State16_in_close :
    mtFiber72StateAt 16 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 8 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 8) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep8
  have h2 : mtFiber72StateAt 16 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 8) (mtFiber72StateAt 16) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep16
  change mtFiber72StateAt 16 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 16) h2

theorem mtFiber72State17_in_close :
    mtFiber72StateAt 17 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 9 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 9) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep9
  have h3 : mtFiber72StateAt 17 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 9) (mtFiber72StateAt 17) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep17
  change mtFiber72StateAt 17 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 17) h3

theorem mtFiber72State18_in_close :
    mtFiber72StateAt 18 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 10 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 10) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep10
  have h3 : mtFiber72StateAt 18 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 10) (mtFiber72StateAt 18) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep18
  change mtFiber72StateAt 18 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 18) h3

theorem mtFiber72State19_in_close :
    mtFiber72StateAt 19 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  have h3 : mtFiber72StateAt 11 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 3) (mtFiber72StateAt 11) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep11
  have h4 : mtFiber72StateAt 19 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 11) (mtFiber72StateAt 19) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep19
  change mtFiber72StateAt 19 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 19) h4

theorem mtFiber72State20_in_close :
    mtFiber72StateAt 20 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 4 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 4) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep4
  have h3 : mtFiber72StateAt 12 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 4) (mtFiber72StateAt 12) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep12
  have h4 : mtFiber72StateAt 20 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 12) (mtFiber72StateAt 20) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep20
  change mtFiber72StateAt 20 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 20) h4

theorem mtFiber72State21_in_close :
    mtFiber72StateAt 21 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 5 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 5) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep5
  have h3 : mtFiber72StateAt 13 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 5) (mtFiber72StateAt 13) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep13
  have h4 : mtFiber72StateAt 21 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 13) (mtFiber72StateAt 21) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep21
  change mtFiber72StateAt 21 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 21) h4

theorem mtFiber72State22_in_close :
    mtFiber72StateAt 22 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  have h3 : mtFiber72StateAt 14 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 6) (mtFiber72StateAt 14) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep14
  have h4 : mtFiber72StateAt 22 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 14) (mtFiber72StateAt 22) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep22
  change mtFiber72StateAt 22 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 22) h4

theorem mtFiber72State23_in_close :
    mtFiber72StateAt 23 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 15 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 15) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep15
  have h3 : mtFiber72StateAt 23 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 15) (mtFiber72StateAt 23) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep23
  change mtFiber72StateAt 23 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 23) h3

theorem mtFiber72State24_in_close :
    mtFiber72StateAt 24 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 24 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 24) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep24
  change mtFiber72StateAt 24 ∈ closeChainFiber mtWord mtFiber72DirectStates (1 + 63) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 1 63 [mtFiber72StateAt 0] (mtFiber72StateAt 24) h1

theorem mtFiber72State25_in_close :
    mtFiber72StateAt 25 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 25 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 25) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep25
  change mtFiber72StateAt 25 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 25) h2

theorem mtFiber72State26_in_close :
    mtFiber72StateAt 26 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 26 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 26) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep26
  change mtFiber72StateAt 26 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 26) h2

theorem mtFiber72State27_in_close :
    mtFiber72StateAt 27 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  have h3 : mtFiber72StateAt 27 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 3) (mtFiber72StateAt 27) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep27
  change mtFiber72StateAt 27 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 27) h3

theorem mtFiber72State28_in_close :
    mtFiber72StateAt 28 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 4 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 4) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep4
  have h3 : mtFiber72StateAt 28 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 4) (mtFiber72StateAt 28) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep28
  change mtFiber72StateAt 28 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 28) h3

theorem mtFiber72State29_in_close :
    mtFiber72StateAt 29 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 5 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 5) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep5
  have h3 : mtFiber72StateAt 29 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 5) (mtFiber72StateAt 29) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep29
  change mtFiber72StateAt 29 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 29) h3

theorem mtFiber72State30_in_close :
    mtFiber72StateAt 30 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  have h3 : mtFiber72StateAt 30 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 6) (mtFiber72StateAt 30) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep30
  change mtFiber72StateAt 30 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 30) h3

theorem mtFiber72State31_in_close :
    mtFiber72StateAt 31 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 31 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 31) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep31
  change mtFiber72StateAt 31 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 31) h2

theorem mtFiber72State32_in_close :
    mtFiber72StateAt 32 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 32 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 32) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep32
  change mtFiber72StateAt 32 ∈ closeChainFiber mtWord mtFiber72DirectStates (1 + 63) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 1 63 [mtFiber72StateAt 0] (mtFiber72StateAt 32) h1

theorem mtFiber72State33_in_close :
    mtFiber72StateAt 33 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 33 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 33) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep33
  change mtFiber72StateAt 33 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 33) h2

theorem mtFiber72State34_in_close :
    mtFiber72StateAt 34 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 34 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 34) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep34
  change mtFiber72StateAt 34 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 34) h2

theorem mtFiber72State35_in_close :
    mtFiber72StateAt 35 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  have h3 : mtFiber72StateAt 35 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 3) (mtFiber72StateAt 35) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep35
  change mtFiber72StateAt 35 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 35) h3

theorem mtFiber72State36_in_close :
    mtFiber72StateAt 36 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 32 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 32) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep32
  have h2 : mtFiber72StateAt 36 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 32) (mtFiber72StateAt 36) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep36
  change mtFiber72StateAt 36 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 36) h2

theorem mtFiber72State37_in_close :
    mtFiber72StateAt 37 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 33 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 33) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep33
  have h3 : mtFiber72StateAt 37 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 33) (mtFiber72StateAt 37) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep37
  change mtFiber72StateAt 37 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 37) h3

theorem mtFiber72State38_in_close :
    mtFiber72StateAt 38 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  have h3 : mtFiber72StateAt 38 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 6) (mtFiber72StateAt 38) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep38
  change mtFiber72StateAt 38 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 38) h3

theorem mtFiber72State39_in_close :
    mtFiber72StateAt 39 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 39 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 39) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep39
  change mtFiber72StateAt 39 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 39) h2

theorem mtFiber72State40_in_close :
    mtFiber72StateAt 40 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 8 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 8) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep8
  have h2 : mtFiber72StateAt 40 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 8) (mtFiber72StateAt 40) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep40
  change mtFiber72StateAt 40 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 40) h2

theorem mtFiber72State41_in_close :
    mtFiber72StateAt 41 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 9 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 9) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep9
  have h3 : mtFiber72StateAt 41 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 9) (mtFiber72StateAt 41) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep41
  change mtFiber72StateAt 41 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 41) h3

theorem mtFiber72State42_in_close :
    mtFiber72StateAt 42 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 10 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 10) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep10
  have h3 : mtFiber72StateAt 42 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 10) (mtFiber72StateAt 42) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep42
  change mtFiber72StateAt 42 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 42) h3

theorem mtFiber72State43_in_close :
    mtFiber72StateAt 43 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  have h3 : mtFiber72StateAt 11 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 3) (mtFiber72StateAt 11) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep11
  have h4 : mtFiber72StateAt 43 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 11) (mtFiber72StateAt 43) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep43
  change mtFiber72StateAt 43 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 43) h4

theorem mtFiber72State44_in_close :
    mtFiber72StateAt 44 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 8 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 8) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep8
  have h2 : mtFiber72StateAt 40 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 8) (mtFiber72StateAt 40) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep40
  have h3 : mtFiber72StateAt 44 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 40) (mtFiber72StateAt 44) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep44
  change mtFiber72StateAt 44 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 44) h3

theorem mtFiber72State45_in_close :
    mtFiber72StateAt 45 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 9 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 9) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep9
  have h3 : mtFiber72StateAt 41 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 9) (mtFiber72StateAt 41) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep41
  have h4 : mtFiber72StateAt 45 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 41) (mtFiber72StateAt 45) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep45
  change mtFiber72StateAt 45 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 45) h4

theorem mtFiber72State46_in_close :
    mtFiber72StateAt 46 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  have h3 : mtFiber72StateAt 14 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 6) (mtFiber72StateAt 14) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep14
  have h4 : mtFiber72StateAt 46 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 14) (mtFiber72StateAt 46) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep46
  change mtFiber72StateAt 46 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 46) h4

theorem mtFiber72State47_in_close :
    mtFiber72StateAt 47 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 15 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 15) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep15
  have h3 : mtFiber72StateAt 47 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 15) (mtFiber72StateAt 47) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep47
  change mtFiber72StateAt 47 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 47) h3

theorem mtFiber72State48_in_close :
    mtFiber72StateAt 48 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 32 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 32) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep32
  have h2 : mtFiber72StateAt 48 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 32) (mtFiber72StateAt 48) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep48
  change mtFiber72StateAt 48 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 48) h2

theorem mtFiber72State49_in_close :
    mtFiber72StateAt 49 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 33 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 33) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep33
  have h3 : mtFiber72StateAt 49 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 33) (mtFiber72StateAt 49) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep49
  change mtFiber72StateAt 49 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 49) h3

theorem mtFiber72State50_in_close :
    mtFiber72StateAt 50 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 34 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 34) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep34
  have h3 : mtFiber72StateAt 50 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 34) (mtFiber72StateAt 50) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep50
  change mtFiber72StateAt 50 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 50) h3

theorem mtFiber72State51_in_close :
    mtFiber72StateAt 51 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  have h3 : mtFiber72StateAt 35 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 3) (mtFiber72StateAt 35) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep35
  have h4 : mtFiber72StateAt 51 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 35) (mtFiber72StateAt 51) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep51
  change mtFiber72StateAt 51 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 51) h4

theorem mtFiber72State52_in_close :
    mtFiber72StateAt 52 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 32 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 32) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep32
  have h2 : mtFiber72StateAt 36 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 32) (mtFiber72StateAt 36) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep36
  have h3 : mtFiber72StateAt 52 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 36) (mtFiber72StateAt 52) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep52
  change mtFiber72StateAt 52 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 52) h3

theorem mtFiber72State53_in_close :
    mtFiber72StateAt 53 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 33 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 33) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep33
  have h3 : mtFiber72StateAt 37 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 33) (mtFiber72StateAt 37) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep37
  have h4 : mtFiber72StateAt 53 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 37) (mtFiber72StateAt 53) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep53
  change mtFiber72StateAt 53 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 53) h4

theorem mtFiber72State54_in_close :
    mtFiber72StateAt 54 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  have h3 : mtFiber72StateAt 38 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 6) (mtFiber72StateAt 38) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep38
  have h4 : mtFiber72StateAt 54 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 38) (mtFiber72StateAt 54) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep54
  change mtFiber72StateAt 54 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 54) h4

theorem mtFiber72State55_in_close :
    mtFiber72StateAt 55 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 39 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 39) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep39
  have h3 : mtFiber72StateAt 55 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 39) (mtFiber72StateAt 55) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep55
  change mtFiber72StateAt 55 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 55) h3

theorem mtFiber72State56_in_close :
    mtFiber72StateAt 56 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 24 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 24) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep24
  have h2 : mtFiber72StateAt 56 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 24) (mtFiber72StateAt 56) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep56
  change mtFiber72StateAt 56 ∈ closeChainFiber mtWord mtFiber72DirectStates (2 + 62) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 2 62 [mtFiber72StateAt 0] (mtFiber72StateAt 56) h2

theorem mtFiber72State57_in_close :
    mtFiber72StateAt 57 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 25 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 25) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep25
  have h3 : mtFiber72StateAt 57 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 25) (mtFiber72StateAt 57) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep57
  change mtFiber72StateAt 57 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 57) h3

theorem mtFiber72State58_in_close :
    mtFiber72StateAt 58 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 2 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 2) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep2
  have h2 : mtFiber72StateAt 26 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 2) (mtFiber72StateAt 26) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep26
  have h3 : mtFiber72StateAt 58 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 26) (mtFiber72StateAt 58) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep58
  change mtFiber72StateAt 58 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 58) h3

theorem mtFiber72State59_in_close :
    mtFiber72StateAt 59 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 3 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 3) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep3
  have h3 : mtFiber72StateAt 27 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 3) (mtFiber72StateAt 27) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep27
  have h4 : mtFiber72StateAt 59 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 27) (mtFiber72StateAt 59) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep59
  change mtFiber72StateAt 59 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 59) h4

theorem mtFiber72State60_in_close :
    mtFiber72StateAt 60 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 24 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 24) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep24
  have h2 : mtFiber72StateAt 56 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 24) (mtFiber72StateAt 56) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep56
  have h3 : mtFiber72StateAt 60 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 56) (mtFiber72StateAt 60) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep60
  change mtFiber72StateAt 60 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 60) h3

theorem mtFiber72State61_in_close :
    mtFiber72StateAt 61 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 25 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 25) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep25
  have h3 : mtFiber72StateAt 57 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 25) (mtFiber72StateAt 57) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep57
  have h4 : mtFiber72StateAt 61 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 57) (mtFiber72StateAt 61) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep61
  change mtFiber72StateAt 61 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 61) h4

theorem mtFiber72State62_in_close :
    mtFiber72StateAt 62 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 1 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 1) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep1
  have h2 : mtFiber72StateAt 6 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 1) (mtFiber72StateAt 6) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep6
  have h3 : mtFiber72StateAt 30 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 6) (mtFiber72StateAt 30) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep30
  have h4 : mtFiber72StateAt 62 ∈ closeChainFiber mtWord mtFiber72DirectStates 4 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0]
      (mtFiber72StateAt 30) (mtFiber72StateAt 62) (by decide) h3 (by decide)
      mtFiber72ReverseSingleStep62
  change mtFiber72StateAt 62 ∈ closeChainFiber mtWord mtFiber72DirectStates (4 + 60) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 4 60 [mtFiber72StateAt 0] (mtFiber72StateAt 62) h4

theorem mtFiber72State63_in_close :
    mtFiber72StateAt 63 ∈ closeChainFiber mtWord mtFiber72DirectStates mtFiber72DirectStates.length [mtFiber72StateAt 0] := by
  have h0 : mtFiber72StateAt 0 ∈ closeChainFiber mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber72StateAt 7 ∈ closeChainFiber mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 0 [mtFiber72StateAt 0]
      (mtFiber72StateAt 0) (mtFiber72StateAt 7) (by decide) h0 (by decide)
      mtFiber72ReverseSingleStep7
  have h2 : mtFiber72StateAt 31 ∈ closeChainFiber mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 1 [mtFiber72StateAt 0]
      (mtFiber72StateAt 7) (mtFiber72StateAt 31) (by decide) h1 (by decide)
      mtFiber72ReverseSingleStep31
  have h3 : mtFiber72StateAt 63 ∈ closeChainFiber mtWord mtFiber72DirectStates 3 [mtFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber72DirectStates 2 [mtFiber72StateAt 0]
      (mtFiber72StateAt 31) (mtFiber72StateAt 63) (by decide) h2 (by decide)
      mtFiber72ReverseSingleStep63
  change mtFiber72StateAt 63 ∈ closeChainFiber mtWord mtFiber72DirectStates (3 + 61) [mtFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber72DirectStates 3 61 [mtFiber72StateAt 0] (mtFiber72StateAt 63) h3

theorem mtFiber72DirectConnected :
    chainFiberConnected mtWord mtFiber72DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber72DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber72State0_in_close
  · subst state
    exact mtFiber72State1_in_close
  · subst state
    exact mtFiber72State2_in_close
  · subst state
    exact mtFiber72State3_in_close
  · subst state
    exact mtFiber72State4_in_close
  · subst state
    exact mtFiber72State5_in_close
  · subst state
    exact mtFiber72State6_in_close
  · subst state
    exact mtFiber72State7_in_close
  · subst state
    exact mtFiber72State8_in_close
  · subst state
    exact mtFiber72State9_in_close
  · subst state
    exact mtFiber72State10_in_close
  · subst state
    exact mtFiber72State11_in_close
  · subst state
    exact mtFiber72State12_in_close
  · subst state
    exact mtFiber72State13_in_close
  · subst state
    exact mtFiber72State14_in_close
  · subst state
    exact mtFiber72State15_in_close
  · subst state
    exact mtFiber72State16_in_close
  · subst state
    exact mtFiber72State17_in_close
  · subst state
    exact mtFiber72State18_in_close
  · subst state
    exact mtFiber72State19_in_close
  · subst state
    exact mtFiber72State20_in_close
  · subst state
    exact mtFiber72State21_in_close
  · subst state
    exact mtFiber72State22_in_close
  · subst state
    exact mtFiber72State23_in_close
  · subst state
    exact mtFiber72State24_in_close
  · subst state
    exact mtFiber72State25_in_close
  · subst state
    exact mtFiber72State26_in_close
  · subst state
    exact mtFiber72State27_in_close
  · subst state
    exact mtFiber72State28_in_close
  · subst state
    exact mtFiber72State29_in_close
  · subst state
    exact mtFiber72State30_in_close
  · subst state
    exact mtFiber72State31_in_close
  · subst state
    exact mtFiber72State32_in_close
  · subst state
    exact mtFiber72State33_in_close
  · subst state
    exact mtFiber72State34_in_close
  · subst state
    exact mtFiber72State35_in_close
  · subst state
    exact mtFiber72State36_in_close
  · subst state
    exact mtFiber72State37_in_close
  · subst state
    exact mtFiber72State38_in_close
  · subst state
    exact mtFiber72State39_in_close
  · subst state
    exact mtFiber72State40_in_close
  · subst state
    exact mtFiber72State41_in_close
  · subst state
    exact mtFiber72State42_in_close
  · subst state
    exact mtFiber72State43_in_close
  · subst state
    exact mtFiber72State44_in_close
  · subst state
    exact mtFiber72State45_in_close
  · subst state
    exact mtFiber72State46_in_close
  · subst state
    exact mtFiber72State47_in_close
  · subst state
    exact mtFiber72State48_in_close
  · subst state
    exact mtFiber72State49_in_close
  · subst state
    exact mtFiber72State50_in_close
  · subst state
    exact mtFiber72State51_in_close
  · subst state
    exact mtFiber72State52_in_close
  · subst state
    exact mtFiber72State53_in_close
  · subst state
    exact mtFiber72State54_in_close
  · subst state
    exact mtFiber72State55_in_close
  · subst state
    exact mtFiber72State56_in_close
  · subst state
    exact mtFiber72State57_in_close
  · subst state
    exact mtFiber72State58_in_close
  · subst state
    exact mtFiber72State59_in_close
  · subst state
    exact mtFiber72State60_in_close
  · subst state
    exact mtFiber72State61_in_close
  · subst state
    exact mtFiber72State62_in_close
  · subst state
    exact mtFiber72State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
