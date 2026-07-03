import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 30

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber30StateAt (i : Nat) : List TauState :=
  directStates (mtFiber30RowAt i).sourceLeft (mtFiber30RowAt i).sourceRight

def mtFiber30DirectStates : List (List TauState) :=
  [mtFiber30StateAt 0, mtFiber30StateAt 1, mtFiber30StateAt 2, mtFiber30StateAt 3, mtFiber30StateAt 4, mtFiber30StateAt 5, mtFiber30StateAt 6, mtFiber30StateAt 7, mtFiber30StateAt 8, mtFiber30StateAt 9, mtFiber30StateAt 10, mtFiber30StateAt 11, mtFiber30StateAt 12, mtFiber30StateAt 13, mtFiber30StateAt 14, mtFiber30StateAt 15, mtFiber30StateAt 16, mtFiber30StateAt 17, mtFiber30StateAt 18, mtFiber30StateAt 19, mtFiber30StateAt 20, mtFiber30StateAt 21, mtFiber30StateAt 22, mtFiber30StateAt 23, mtFiber30StateAt 24, mtFiber30StateAt 25, mtFiber30StateAt 26, mtFiber30StateAt 27, mtFiber30StateAt 28, mtFiber30StateAt 29, mtFiber30StateAt 30, mtFiber30StateAt 31, mtFiber30StateAt 32, mtFiber30StateAt 33, mtFiber30StateAt 34, mtFiber30StateAt 35, mtFiber30StateAt 36, mtFiber30StateAt 37, mtFiber30StateAt 38, mtFiber30StateAt 39, mtFiber30StateAt 40, mtFiber30StateAt 41, mtFiber30StateAt 42, mtFiber30StateAt 43, mtFiber30StateAt 44, mtFiber30StateAt 45, mtFiber30StateAt 46, mtFiber30StateAt 47, mtFiber30StateAt 48, mtFiber30StateAt 49, mtFiber30StateAt 50, mtFiber30StateAt 51, mtFiber30StateAt 52, mtFiber30StateAt 53, mtFiber30StateAt 54, mtFiber30StateAt 55, mtFiber30StateAt 56, mtFiber30StateAt 57, mtFiber30StateAt 58, mtFiber30StateAt 59, mtFiber30StateAt 60, mtFiber30StateAt 61, mtFiber30StateAt 62, mtFiber30StateAt 63]

theorem mtFiber30ReverseRow_1_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk0_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 0) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 1)
    (mtFiber30RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 1) (by decide) mtFiber30ReverseRow_1_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_2_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk1_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 2) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 2)
    (mtFiber30RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 2) (by decide) mtFiber30ReverseRow_2_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_3_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk1_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 2) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 3)
    (mtFiber30RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 3) (by decide) mtFiber30ReverseRow_3_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_4_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk2_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 4) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 4)
    (mtFiber30RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 4) (by decide) mtFiber30ReverseRow_4_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_5_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk2_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 4) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 5)
    (mtFiber30RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 5) (by decide) mtFiber30ReverseRow_5_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_6_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk3_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 6) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 6)
    (mtFiber30RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 6) (by decide) mtFiber30ReverseRow_6_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_7_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk3_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 6) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 7)
    (mtFiber30RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 7) (by decide) mtFiber30ReverseRow_7_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_8_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk4_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 8) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 8)
    (mtFiber30RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 8) (by decide) mtFiber30ReverseRow_8_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_9_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk4_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 8) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 9)
    (mtFiber30RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 9) (by decide) mtFiber30ReverseRow_9_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_10_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk5_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 10) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 2) (mtFiber30StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 2) (mtFiber30StateAt 10)
    (mtFiber30RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 10) (by decide) mtFiber30ReverseRow_10_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_11_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk5_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 10) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 11)
    (mtFiber30RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 11) (by decide) mtFiber30ReverseRow_11_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_12_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk6_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 12) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 12)
    (mtFiber30RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 12) (by decide) mtFiber30ReverseRow_12_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_13_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk6_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 12) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 5) (mtFiber30StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 5) (mtFiber30StateAt 13)
    (mtFiber30RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 13) (by decide) mtFiber30ReverseRow_13_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_14_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk7_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 14) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 6) (mtFiber30StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 6) (mtFiber30StateAt 14)
    (mtFiber30RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 14) (by decide) mtFiber30ReverseRow_14_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_15_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk7_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 14) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 7) (mtFiber30StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 7) (mtFiber30StateAt 15)
    (mtFiber30RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 15) (by decide) mtFiber30ReverseRow_15_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_16_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk8_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 16) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 16)
    (mtFiber30RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 16) (by decide) mtFiber30ReverseRow_16_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_17_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk8_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 16) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 17)
    (mtFiber30RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 17) (by decide) mtFiber30ReverseRow_17_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_18_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk9_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 18) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 2) (mtFiber30StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 2) (mtFiber30StateAt 18)
    (mtFiber30RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 18) (by decide) mtFiber30ReverseRow_18_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_19_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk9_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 18) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 19)
    (mtFiber30RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 19) (by decide) mtFiber30ReverseRow_19_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_20_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk10_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 20) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 20)
    (mtFiber30RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 20) (by decide) mtFiber30ReverseRow_20_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_21_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk10_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 20) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 5) (mtFiber30StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 5) (mtFiber30StateAt 21)
    (mtFiber30RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 21) (by decide) mtFiber30ReverseRow_21_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_22_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk11_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 22) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 6) (mtFiber30StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 6) (mtFiber30StateAt 22)
    (mtFiber30RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 22) (by decide) mtFiber30ReverseRow_22_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_23_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk11_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 22) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 7) (mtFiber30StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 7) (mtFiber30StateAt 23)
    (mtFiber30RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 23) (by decide) mtFiber30ReverseRow_23_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_24_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk12_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 24) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 8) (mtFiber30StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 8) (mtFiber30StateAt 24)
    (mtFiber30RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 24) (by decide) mtFiber30ReverseRow_24_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_25_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk12_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 24) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 9) (mtFiber30StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 9) (mtFiber30StateAt 25)
    (mtFiber30RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 25) (by decide) mtFiber30ReverseRow_25_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_26_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk13_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 26) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 10) (mtFiber30StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 10) (mtFiber30StateAt 26)
    (mtFiber30RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 26) (by decide) mtFiber30ReverseRow_26_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_27_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk13_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 26) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 11) (mtFiber30StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 11) (mtFiber30StateAt 27)
    (mtFiber30RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 27) (by decide) mtFiber30ReverseRow_27_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_28_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk14_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 28) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 12) (mtFiber30StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 12) (mtFiber30StateAt 28)
    (mtFiber30RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 28) (by decide) mtFiber30ReverseRow_28_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_29_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk14_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 28) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 13) (mtFiber30StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 13) (mtFiber30StateAt 29)
    (mtFiber30RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 29) (by decide) mtFiber30ReverseRow_29_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_30_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk15_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 30) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 14) (mtFiber30StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 14) (mtFiber30StateAt 30)
    (mtFiber30RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 30) (by decide) mtFiber30ReverseRow_30_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_31_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk15_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 30) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 15) (mtFiber30StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 15) (mtFiber30StateAt 31)
    (mtFiber30RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 31) (by decide) mtFiber30ReverseRow_31_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_32_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk16_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 32) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 36) (mtFiber30StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 36) (mtFiber30StateAt 32)
    (mtFiber30RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 32) (by decide) mtFiber30ReverseRow_32_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_33_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk16_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 32) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 37) (mtFiber30StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 37) (mtFiber30StateAt 33)
    (mtFiber30RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 33) (by decide) mtFiber30ReverseRow_33_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_34_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk17_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 34) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 20) (mtFiber30StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 20) (mtFiber30StateAt 34)
    (mtFiber30RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 34) (by decide) mtFiber30ReverseRow_34_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_35_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk17_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 34) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 21) (mtFiber30StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 21) (mtFiber30StateAt 35)
    (mtFiber30RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 35) (by decide) mtFiber30ReverseRow_35_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_36_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk18_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 36) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 16) (mtFiber30StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 16) (mtFiber30StateAt 36)
    (mtFiber30RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 36) (by decide) mtFiber30ReverseRow_36_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_37_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk18_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 36) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 17) (mtFiber30StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 17) (mtFiber30StateAt 37)
    (mtFiber30RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 37) (by decide) mtFiber30ReverseRow_37_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_38_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk19_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 38) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 18) (mtFiber30StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 18) (mtFiber30StateAt 38)
    (mtFiber30RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 38) (by decide) mtFiber30ReverseRow_38_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_39_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk19_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 38) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 19) (mtFiber30StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 19) (mtFiber30StateAt 39)
    (mtFiber30RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 39) (by decide) mtFiber30ReverseRow_39_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_40_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk20_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 40) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 44) (mtFiber30StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 44) (mtFiber30StateAt 40)
    (mtFiber30RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 40) (by decide) mtFiber30ReverseRow_40_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_41_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk20_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 40) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 45) (mtFiber30StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 45) (mtFiber30StateAt 41)
    (mtFiber30RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 41) (by decide) mtFiber30ReverseRow_41_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_42_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk21_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 42) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 58) (mtFiber30StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 58) (mtFiber30StateAt 42)
    (mtFiber30RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 42) (by decide) mtFiber30ReverseRow_42_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_43_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk21_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 42) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 59) (mtFiber30StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 59) (mtFiber30StateAt 43)
    (mtFiber30RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 43) (by decide) mtFiber30ReverseRow_43_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_44_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk22_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 44) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 60) (mtFiber30StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 60) (mtFiber30StateAt 44)
    (mtFiber30RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 44) (by decide) mtFiber30ReverseRow_44_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_45_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk22_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 44) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 61) (mtFiber30StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 61) (mtFiber30StateAt 45)
    (mtFiber30RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 45) (by decide) mtFiber30ReverseRow_45_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_46_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk23_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 46) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 62) (mtFiber30StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 62) (mtFiber30StateAt 46)
    (mtFiber30RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 46) (by decide) mtFiber30ReverseRow_46_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_47_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk23_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 46) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 63) (mtFiber30StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 63) (mtFiber30StateAt 47)
    (mtFiber30RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 47) (by decide) mtFiber30ReverseRow_47_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_48_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk24_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 48) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 52) (mtFiber30StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 52) (mtFiber30StateAt 48)
    (mtFiber30RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 48) (by decide) mtFiber30ReverseRow_48_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_49_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk24_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 48) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 53) (mtFiber30StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 53) (mtFiber30StateAt 49)
    (mtFiber30RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 49) (by decide) mtFiber30ReverseRow_49_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_50_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk25_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 50) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 12) (mtFiber30StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 12) (mtFiber30StateAt 50)
    (mtFiber30RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 50) (by decide) mtFiber30ReverseRow_50_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_51_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk25_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 50) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 13) (mtFiber30StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 13) (mtFiber30StateAt 51)
    (mtFiber30RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 51) (by decide) mtFiber30ReverseRow_51_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_52_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk26_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 52) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 8) (mtFiber30StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 8) (mtFiber30StateAt 52)
    (mtFiber30RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 52) (by decide) mtFiber30ReverseRow_52_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_53_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk26_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 52) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 9) (mtFiber30StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 9) (mtFiber30StateAt 53)
    (mtFiber30RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 53) (by decide) mtFiber30ReverseRow_53_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_54_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk27_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 54) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 10) (mtFiber30StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 10) (mtFiber30StateAt 54)
    (mtFiber30RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 54) (by decide) mtFiber30ReverseRow_54_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_55_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk27_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 54) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 11) (mtFiber30StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 11) (mtFiber30StateAt 55)
    (mtFiber30RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 55) (by decide) mtFiber30ReverseRow_55_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_56_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk28_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 56) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 60) (mtFiber30StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 60) (mtFiber30StateAt 56)
    (mtFiber30RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 56) (by decide) mtFiber30ReverseRow_56_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_57_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk28_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 56) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 61) (mtFiber30StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 61) (mtFiber30StateAt 57)
    (mtFiber30RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 57) (by decide) mtFiber30ReverseRow_57_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_58_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk29_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 58) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 4) (mtFiber30StateAt 58)
    (mtFiber30RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 58) (by decide) mtFiber30ReverseRow_58_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_59_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk29_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 58) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 5) (mtFiber30StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 5) (mtFiber30StateAt 59)
    (mtFiber30RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 59) (by decide) mtFiber30ReverseRow_59_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_60_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk30_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 60) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 0) (mtFiber30StateAt 60)
    (mtFiber30RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 60) (by decide) mtFiber30ReverseRow_60_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_61_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk30_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 60) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 1) (mtFiber30StateAt 61)
    (mtFiber30RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 61) (by decide) mtFiber30ReverseRow_61_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_62_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk31_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 62) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber30ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 2) (mtFiber30StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 2) (mtFiber30StateAt 62)
    (mtFiber30RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 62) (by decide) mtFiber30ReverseRow_62_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30ReverseRow_63_ok :
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber30Chunk31_ok
  change (mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 62) &&
    mtRowReverseValid mtFiber30Key mtFiber30Expected (mtFiber30RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber30ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber30StateAt 3) (mtFiber30StateAt 63)
    (mtFiber30RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber30Key mtFiber30Expected
        (mtFiber30RowAt 63) (by decide) mtFiber30ReverseRow_63_ok
      simpa [mtFiber30StateAt, mtFiber30RowAt, mtFiber30Rows, listGetD, directRow] using h)

theorem mtFiber30State0_in_close :
    mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  change mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 64 [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 0 64 [mtFiber30StateAt 0] (mtFiber30StateAt 0) (by simp [closeChainFiber])

theorem mtFiber30State1_in_close :
    mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  change mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates (1 + 63) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 1 63 [mtFiber30StateAt 0] (mtFiber30StateAt 1) h1

theorem mtFiber30State2_in_close :
    mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  change mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 2) h2

theorem mtFiber30State3_in_close :
    mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  change mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates (1 + 63) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 1 63 [mtFiber30StateAt 0] (mtFiber30StateAt 3) h1

theorem mtFiber30State4_in_close :
    mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  change mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates (1 + 63) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 1 63 [mtFiber30StateAt 0] (mtFiber30StateAt 4) h1

theorem mtFiber30State5_in_close :
    mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  change mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 5) h2

theorem mtFiber30State6_in_close :
    mtFiber30StateAt 6 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 6 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 6) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep6
  change mtFiber30StateAt 6 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 6) h2

theorem mtFiber30State7_in_close :
    mtFiber30StateAt 7 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 7 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 7) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep7
  change mtFiber30StateAt 7 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 7) h2

theorem mtFiber30State8_in_close :
    mtFiber30StateAt 8 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 8 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 8) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep8
  change mtFiber30StateAt 8 ∈ closeChainFiber mtWord mtFiber30DirectStates (1 + 63) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 1 63 [mtFiber30StateAt 0] (mtFiber30StateAt 8) h1

theorem mtFiber30State9_in_close :
    mtFiber30StateAt 9 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 9 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 9) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep9
  change mtFiber30StateAt 9 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 9) h2

theorem mtFiber30State10_in_close :
    mtFiber30StateAt 10 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  have h3 : mtFiber30StateAt 10 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 2) (mtFiber30StateAt 10) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep10
  change mtFiber30StateAt 10 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 10) h3

theorem mtFiber30State11_in_close :
    mtFiber30StateAt 11 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 11 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 11) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep11
  change mtFiber30StateAt 11 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 11) h2

theorem mtFiber30State12_in_close :
    mtFiber30StateAt 12 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 12 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 12) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep12
  change mtFiber30StateAt 12 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 12) h2

theorem mtFiber30State13_in_close :
    mtFiber30StateAt 13 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  have h3 : mtFiber30StateAt 13 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 5) (mtFiber30StateAt 13) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep13
  change mtFiber30StateAt 13 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 13) h3

theorem mtFiber30State14_in_close :
    mtFiber30StateAt 14 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 6 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 6) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep6
  have h3 : mtFiber30StateAt 14 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 6) (mtFiber30StateAt 14) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep14
  change mtFiber30StateAt 14 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 14) h3

theorem mtFiber30State15_in_close :
    mtFiber30StateAt 15 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 7 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 7) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep7
  have h3 : mtFiber30StateAt 15 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 7) (mtFiber30StateAt 15) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep15
  change mtFiber30StateAt 15 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 15) h3

theorem mtFiber30State16_in_close :
    mtFiber30StateAt 16 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 16 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 16) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep16
  change mtFiber30StateAt 16 ∈ closeChainFiber mtWord mtFiber30DirectStates (1 + 63) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 1 63 [mtFiber30StateAt 0] (mtFiber30StateAt 16) h1

theorem mtFiber30State17_in_close :
    mtFiber30StateAt 17 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 17 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 17) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep17
  change mtFiber30StateAt 17 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 17) h2

theorem mtFiber30State18_in_close :
    mtFiber30StateAt 18 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  have h3 : mtFiber30StateAt 18 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 2) (mtFiber30StateAt 18) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep18
  change mtFiber30StateAt 18 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 18) h3

theorem mtFiber30State19_in_close :
    mtFiber30StateAt 19 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 19 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 19) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep19
  change mtFiber30StateAt 19 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 19) h2

theorem mtFiber30State20_in_close :
    mtFiber30StateAt 20 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 20 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 20) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep20
  change mtFiber30StateAt 20 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 20) h2

theorem mtFiber30State21_in_close :
    mtFiber30StateAt 21 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  have h3 : mtFiber30StateAt 21 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 5) (mtFiber30StateAt 21) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep21
  change mtFiber30StateAt 21 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 21) h3

theorem mtFiber30State22_in_close :
    mtFiber30StateAt 22 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 6 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 6) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep6
  have h3 : mtFiber30StateAt 22 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 6) (mtFiber30StateAt 22) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep22
  change mtFiber30StateAt 22 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 22) h3

theorem mtFiber30State23_in_close :
    mtFiber30StateAt 23 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 7 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 7) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep7
  have h3 : mtFiber30StateAt 23 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 7) (mtFiber30StateAt 23) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep23
  change mtFiber30StateAt 23 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 23) h3

theorem mtFiber30State24_in_close :
    mtFiber30StateAt 24 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 8 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 8) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep8
  have h2 : mtFiber30StateAt 24 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 8) (mtFiber30StateAt 24) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep24
  change mtFiber30StateAt 24 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 24) h2

theorem mtFiber30State25_in_close :
    mtFiber30StateAt 25 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 9 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 9) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep9
  have h3 : mtFiber30StateAt 25 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 9) (mtFiber30StateAt 25) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep25
  change mtFiber30StateAt 25 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 25) h3

theorem mtFiber30State26_in_close :
    mtFiber30StateAt 26 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  have h3 : mtFiber30StateAt 10 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 2) (mtFiber30StateAt 10) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep10
  have h4 : mtFiber30StateAt 26 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 10) (mtFiber30StateAt 26) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep26
  change mtFiber30StateAt 26 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 26) h4

theorem mtFiber30State27_in_close :
    mtFiber30StateAt 27 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 11 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 11) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep11
  have h3 : mtFiber30StateAt 27 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 11) (mtFiber30StateAt 27) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep27
  change mtFiber30StateAt 27 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 27) h3

theorem mtFiber30State28_in_close :
    mtFiber30StateAt 28 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 12 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 12) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep12
  have h3 : mtFiber30StateAt 28 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 12) (mtFiber30StateAt 28) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep28
  change mtFiber30StateAt 28 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 28) h3

theorem mtFiber30State29_in_close :
    mtFiber30StateAt 29 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  have h3 : mtFiber30StateAt 13 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 5) (mtFiber30StateAt 13) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep13
  have h4 : mtFiber30StateAt 29 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 13) (mtFiber30StateAt 29) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep29
  change mtFiber30StateAt 29 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 29) h4

theorem mtFiber30State30_in_close :
    mtFiber30StateAt 30 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 6 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 6) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep6
  have h3 : mtFiber30StateAt 14 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 6) (mtFiber30StateAt 14) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep14
  have h4 : mtFiber30StateAt 30 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 14) (mtFiber30StateAt 30) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep30
  change mtFiber30StateAt 30 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 30) h4

theorem mtFiber30State31_in_close :
    mtFiber30StateAt 31 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 7 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 7) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep7
  have h3 : mtFiber30StateAt 15 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 7) (mtFiber30StateAt 15) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep15
  have h4 : mtFiber30StateAt 31 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 15) (mtFiber30StateAt 31) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep31
  change mtFiber30StateAt 31 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 31) h4

theorem mtFiber30State32_in_close :
    mtFiber30StateAt 32 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 16 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 16) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep16
  have h2 : mtFiber30StateAt 36 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 16) (mtFiber30StateAt 36) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep36
  have h3 : mtFiber30StateAt 32 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 36) (mtFiber30StateAt 32) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep32
  change mtFiber30StateAt 32 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 32) h3

theorem mtFiber30State33_in_close :
    mtFiber30StateAt 33 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 17 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 17) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep17
  have h3 : mtFiber30StateAt 37 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 17) (mtFiber30StateAt 37) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep37
  have h4 : mtFiber30StateAt 33 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 37) (mtFiber30StateAt 33) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep33
  change mtFiber30StateAt 33 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 33) h4

theorem mtFiber30State34_in_close :
    mtFiber30StateAt 34 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 20 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 20) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep20
  have h3 : mtFiber30StateAt 34 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 20) (mtFiber30StateAt 34) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep34
  change mtFiber30StateAt 34 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 34) h3

theorem mtFiber30State35_in_close :
    mtFiber30StateAt 35 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  have h3 : mtFiber30StateAt 21 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 5) (mtFiber30StateAt 21) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep21
  have h4 : mtFiber30StateAt 35 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 21) (mtFiber30StateAt 35) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep35
  change mtFiber30StateAt 35 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 35) h4

theorem mtFiber30State36_in_close :
    mtFiber30StateAt 36 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 16 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 16) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep16
  have h2 : mtFiber30StateAt 36 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 16) (mtFiber30StateAt 36) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep36
  change mtFiber30StateAt 36 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 36) h2

theorem mtFiber30State37_in_close :
    mtFiber30StateAt 37 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 17 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 17) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep17
  have h3 : mtFiber30StateAt 37 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 17) (mtFiber30StateAt 37) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep37
  change mtFiber30StateAt 37 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 37) h3

theorem mtFiber30State38_in_close :
    mtFiber30StateAt 38 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  have h3 : mtFiber30StateAt 18 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 2) (mtFiber30StateAt 18) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep18
  have h4 : mtFiber30StateAt 38 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 18) (mtFiber30StateAt 38) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep38
  change mtFiber30StateAt 38 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 38) h4

theorem mtFiber30State39_in_close :
    mtFiber30StateAt 39 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 19 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 19) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep19
  have h3 : mtFiber30StateAt 39 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 19) (mtFiber30StateAt 39) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep39
  change mtFiber30StateAt 39 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 39) h3

theorem mtFiber30State40_in_close :
    mtFiber30StateAt 40 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 60 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 60) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep60
  have h2 : mtFiber30StateAt 44 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 60) (mtFiber30StateAt 44) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep44
  have h3 : mtFiber30StateAt 40 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 44) (mtFiber30StateAt 40) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep40
  change mtFiber30StateAt 40 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 40) h3

theorem mtFiber30State41_in_close :
    mtFiber30StateAt 41 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 61 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 61) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep61
  have h3 : mtFiber30StateAt 45 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 61) (mtFiber30StateAt 45) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep45
  have h4 : mtFiber30StateAt 41 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 45) (mtFiber30StateAt 41) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep41
  change mtFiber30StateAt 41 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 41) h4

theorem mtFiber30State42_in_close :
    mtFiber30StateAt 42 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 58 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 58) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep58
  have h3 : mtFiber30StateAt 42 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 58) (mtFiber30StateAt 42) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep42
  change mtFiber30StateAt 42 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 42) h3

theorem mtFiber30State43_in_close :
    mtFiber30StateAt 43 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  have h3 : mtFiber30StateAt 59 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 5) (mtFiber30StateAt 59) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep59
  have h4 : mtFiber30StateAt 43 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 59) (mtFiber30StateAt 43) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep43
  change mtFiber30StateAt 43 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 43) h4

theorem mtFiber30State44_in_close :
    mtFiber30StateAt 44 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 60 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 60) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep60
  have h2 : mtFiber30StateAt 44 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 60) (mtFiber30StateAt 44) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep44
  change mtFiber30StateAt 44 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 44) h2

theorem mtFiber30State45_in_close :
    mtFiber30StateAt 45 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 61 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 61) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep61
  have h3 : mtFiber30StateAt 45 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 61) (mtFiber30StateAt 45) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep45
  change mtFiber30StateAt 45 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 45) h3

theorem mtFiber30State46_in_close :
    mtFiber30StateAt 46 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  have h3 : mtFiber30StateAt 62 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 2) (mtFiber30StateAt 62) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep62
  have h4 : mtFiber30StateAt 46 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 62) (mtFiber30StateAt 46) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep46
  change mtFiber30StateAt 46 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 46) h4

theorem mtFiber30State47_in_close :
    mtFiber30StateAt 47 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 63 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 63) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep63
  have h3 : mtFiber30StateAt 47 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 63) (mtFiber30StateAt 47) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep47
  change mtFiber30StateAt 47 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 47) h3

theorem mtFiber30State48_in_close :
    mtFiber30StateAt 48 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 8 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 8) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep8
  have h2 : mtFiber30StateAt 52 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 8) (mtFiber30StateAt 52) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep52
  have h3 : mtFiber30StateAt 48 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 52) (mtFiber30StateAt 48) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep48
  change mtFiber30StateAt 48 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 48) h3

theorem mtFiber30State49_in_close :
    mtFiber30StateAt 49 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 9 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 9) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep9
  have h3 : mtFiber30StateAt 53 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 9) (mtFiber30StateAt 53) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep53
  have h4 : mtFiber30StateAt 49 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 53) (mtFiber30StateAt 49) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep49
  change mtFiber30StateAt 49 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 49) h4

theorem mtFiber30State50_in_close :
    mtFiber30StateAt 50 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 12 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 12) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep12
  have h3 : mtFiber30StateAt 50 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 12) (mtFiber30StateAt 50) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep50
  change mtFiber30StateAt 50 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 50) h3

theorem mtFiber30State51_in_close :
    mtFiber30StateAt 51 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  have h3 : mtFiber30StateAt 13 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 5) (mtFiber30StateAt 13) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep13
  have h4 : mtFiber30StateAt 51 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 13) (mtFiber30StateAt 51) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep51
  change mtFiber30StateAt 51 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 51) h4

theorem mtFiber30State52_in_close :
    mtFiber30StateAt 52 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 8 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 8) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep8
  have h2 : mtFiber30StateAt 52 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 8) (mtFiber30StateAt 52) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep52
  change mtFiber30StateAt 52 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 52) h2

theorem mtFiber30State53_in_close :
    mtFiber30StateAt 53 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 9 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 9) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep9
  have h3 : mtFiber30StateAt 53 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 9) (mtFiber30StateAt 53) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep53
  change mtFiber30StateAt 53 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 53) h3

theorem mtFiber30State54_in_close :
    mtFiber30StateAt 54 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  have h3 : mtFiber30StateAt 10 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 2) (mtFiber30StateAt 10) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep10
  have h4 : mtFiber30StateAt 54 ∈ closeChainFiber mtWord mtFiber30DirectStates 4 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0]
      (mtFiber30StateAt 10) (mtFiber30StateAt 54) (by decide) h3 (by decide)
      mtFiber30ReverseSingleStep54
  change mtFiber30StateAt 54 ∈ closeChainFiber mtWord mtFiber30DirectStates (4 + 60) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 4 60 [mtFiber30StateAt 0] (mtFiber30StateAt 54) h4

theorem mtFiber30State55_in_close :
    mtFiber30StateAt 55 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 11 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 11) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep11
  have h3 : mtFiber30StateAt 55 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 11) (mtFiber30StateAt 55) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep55
  change mtFiber30StateAt 55 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 55) h3

theorem mtFiber30State56_in_close :
    mtFiber30StateAt 56 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 60 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 60) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep60
  have h2 : mtFiber30StateAt 56 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 60) (mtFiber30StateAt 56) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep56
  change mtFiber30StateAt 56 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 56) h2

theorem mtFiber30State57_in_close :
    mtFiber30StateAt 57 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 61 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 61) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep61
  have h3 : mtFiber30StateAt 57 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 61) (mtFiber30StateAt 57) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep57
  change mtFiber30StateAt 57 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 57) h3

theorem mtFiber30State58_in_close :
    mtFiber30StateAt 58 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 4 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 4) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep4
  have h2 : mtFiber30StateAt 58 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 4) (mtFiber30StateAt 58) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep58
  change mtFiber30StateAt 58 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 58) h2

theorem mtFiber30State59_in_close :
    mtFiber30StateAt 59 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 5 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 5) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep5
  have h3 : mtFiber30StateAt 59 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 5) (mtFiber30StateAt 59) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep59
  change mtFiber30StateAt 59 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 59) h3

theorem mtFiber30State60_in_close :
    mtFiber30StateAt 60 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 60 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 60) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep60
  change mtFiber30StateAt 60 ∈ closeChainFiber mtWord mtFiber30DirectStates (1 + 63) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 1 63 [mtFiber30StateAt 0] (mtFiber30StateAt 60) h1

theorem mtFiber30State61_in_close :
    mtFiber30StateAt 61 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 61 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 61) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep61
  change mtFiber30StateAt 61 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 61) h2

theorem mtFiber30State62_in_close :
    mtFiber30StateAt 62 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 1 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 1) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep1
  have h2 : mtFiber30StateAt 2 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 1) (mtFiber30StateAt 2) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep2
  have h3 : mtFiber30StateAt 62 ∈ closeChainFiber mtWord mtFiber30DirectStates 3 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0]
      (mtFiber30StateAt 2) (mtFiber30StateAt 62) (by decide) h2 (by decide)
      mtFiber30ReverseSingleStep62
  change mtFiber30StateAt 62 ∈ closeChainFiber mtWord mtFiber30DirectStates (3 + 61) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 3 61 [mtFiber30StateAt 0] (mtFiber30StateAt 62) h3

theorem mtFiber30State63_in_close :
    mtFiber30StateAt 63 ∈ closeChainFiber mtWord mtFiber30DirectStates mtFiber30DirectStates.length [mtFiber30StateAt 0] := by
  have h0 : mtFiber30StateAt 0 ∈ closeChainFiber mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber30StateAt 3 ∈ closeChainFiber mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 0 [mtFiber30StateAt 0]
      (mtFiber30StateAt 0) (mtFiber30StateAt 3) (by decide) h0 (by decide)
      mtFiber30ReverseSingleStep3
  have h2 : mtFiber30StateAt 63 ∈ closeChainFiber mtWord mtFiber30DirectStates 2 [mtFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber30DirectStates 1 [mtFiber30StateAt 0]
      (mtFiber30StateAt 3) (mtFiber30StateAt 63) (by decide) h1 (by decide)
      mtFiber30ReverseSingleStep63
  change mtFiber30StateAt 63 ∈ closeChainFiber mtWord mtFiber30DirectStates (2 + 62) [mtFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber30DirectStates 2 62 [mtFiber30StateAt 0] (mtFiber30StateAt 63) h2

theorem mtFiber30DirectConnected :
    chainFiberConnected mtWord mtFiber30DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber30DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber30State0_in_close
  · subst state
    exact mtFiber30State1_in_close
  · subst state
    exact mtFiber30State2_in_close
  · subst state
    exact mtFiber30State3_in_close
  · subst state
    exact mtFiber30State4_in_close
  · subst state
    exact mtFiber30State5_in_close
  · subst state
    exact mtFiber30State6_in_close
  · subst state
    exact mtFiber30State7_in_close
  · subst state
    exact mtFiber30State8_in_close
  · subst state
    exact mtFiber30State9_in_close
  · subst state
    exact mtFiber30State10_in_close
  · subst state
    exact mtFiber30State11_in_close
  · subst state
    exact mtFiber30State12_in_close
  · subst state
    exact mtFiber30State13_in_close
  · subst state
    exact mtFiber30State14_in_close
  · subst state
    exact mtFiber30State15_in_close
  · subst state
    exact mtFiber30State16_in_close
  · subst state
    exact mtFiber30State17_in_close
  · subst state
    exact mtFiber30State18_in_close
  · subst state
    exact mtFiber30State19_in_close
  · subst state
    exact mtFiber30State20_in_close
  · subst state
    exact mtFiber30State21_in_close
  · subst state
    exact mtFiber30State22_in_close
  · subst state
    exact mtFiber30State23_in_close
  · subst state
    exact mtFiber30State24_in_close
  · subst state
    exact mtFiber30State25_in_close
  · subst state
    exact mtFiber30State26_in_close
  · subst state
    exact mtFiber30State27_in_close
  · subst state
    exact mtFiber30State28_in_close
  · subst state
    exact mtFiber30State29_in_close
  · subst state
    exact mtFiber30State30_in_close
  · subst state
    exact mtFiber30State31_in_close
  · subst state
    exact mtFiber30State32_in_close
  · subst state
    exact mtFiber30State33_in_close
  · subst state
    exact mtFiber30State34_in_close
  · subst state
    exact mtFiber30State35_in_close
  · subst state
    exact mtFiber30State36_in_close
  · subst state
    exact mtFiber30State37_in_close
  · subst state
    exact mtFiber30State38_in_close
  · subst state
    exact mtFiber30State39_in_close
  · subst state
    exact mtFiber30State40_in_close
  · subst state
    exact mtFiber30State41_in_close
  · subst state
    exact mtFiber30State42_in_close
  · subst state
    exact mtFiber30State43_in_close
  · subst state
    exact mtFiber30State44_in_close
  · subst state
    exact mtFiber30State45_in_close
  · subst state
    exact mtFiber30State46_in_close
  · subst state
    exact mtFiber30State47_in_close
  · subst state
    exact mtFiber30State48_in_close
  · subst state
    exact mtFiber30State49_in_close
  · subst state
    exact mtFiber30State50_in_close
  · subst state
    exact mtFiber30State51_in_close
  · subst state
    exact mtFiber30State52_in_close
  · subst state
    exact mtFiber30State53_in_close
  · subst state
    exact mtFiber30State54_in_close
  · subst state
    exact mtFiber30State55_in_close
  · subst state
    exact mtFiber30State56_in_close
  · subst state
    exact mtFiber30State57_in_close
  · subst state
    exact mtFiber30State58_in_close
  · subst state
    exact mtFiber30State59_in_close
  · subst state
    exact mtFiber30State60_in_close
  · subst state
    exact mtFiber30State61_in_close
  · subst state
    exact mtFiber30State62_in_close
  · subst state
    exact mtFiber30State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
