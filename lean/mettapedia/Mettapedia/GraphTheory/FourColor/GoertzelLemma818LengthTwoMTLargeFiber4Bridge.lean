import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 4

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber4StateAt (i : Nat) : List TauState :=
  directStates (mtFiber4RowAt i).sourceLeft (mtFiber4RowAt i).sourceRight

def mtFiber4DirectStates : List (List TauState) :=
  [mtFiber4StateAt 0, mtFiber4StateAt 1, mtFiber4StateAt 2, mtFiber4StateAt 3, mtFiber4StateAt 4, mtFiber4StateAt 5, mtFiber4StateAt 6, mtFiber4StateAt 7, mtFiber4StateAt 8, mtFiber4StateAt 9, mtFiber4StateAt 10, mtFiber4StateAt 11, mtFiber4StateAt 12, mtFiber4StateAt 13, mtFiber4StateAt 14, mtFiber4StateAt 15, mtFiber4StateAt 16, mtFiber4StateAt 17, mtFiber4StateAt 18, mtFiber4StateAt 19, mtFiber4StateAt 20, mtFiber4StateAt 21, mtFiber4StateAt 22, mtFiber4StateAt 23, mtFiber4StateAt 24, mtFiber4StateAt 25, mtFiber4StateAt 26, mtFiber4StateAt 27, mtFiber4StateAt 28, mtFiber4StateAt 29, mtFiber4StateAt 30, mtFiber4StateAt 31, mtFiber4StateAt 32, mtFiber4StateAt 33, mtFiber4StateAt 34, mtFiber4StateAt 35, mtFiber4StateAt 36, mtFiber4StateAt 37, mtFiber4StateAt 38, mtFiber4StateAt 39, mtFiber4StateAt 40, mtFiber4StateAt 41, mtFiber4StateAt 42, mtFiber4StateAt 43, mtFiber4StateAt 44, mtFiber4StateAt 45, mtFiber4StateAt 46, mtFiber4StateAt 47, mtFiber4StateAt 48, mtFiber4StateAt 49, mtFiber4StateAt 50, mtFiber4StateAt 51, mtFiber4StateAt 52, mtFiber4StateAt 53, mtFiber4StateAt 54, mtFiber4StateAt 55, mtFiber4StateAt 56, mtFiber4StateAt 57, mtFiber4StateAt 58, mtFiber4StateAt 59, mtFiber4StateAt 60, mtFiber4StateAt 61, mtFiber4StateAt 62, mtFiber4StateAt 63]

theorem mtFiber4ReverseRow_1_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk0_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 0) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 1)
    (mtFiber4RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 1) (by decide) mtFiber4ReverseRow_1_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_2_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk1_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 2) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 2)
    (mtFiber4RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 2) (by decide) mtFiber4ReverseRow_2_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_3_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk1_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 2) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 3)
    (mtFiber4RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 3) (by decide) mtFiber4ReverseRow_3_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_4_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk2_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 4) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 4)
    (mtFiber4RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 4) (by decide) mtFiber4ReverseRow_4_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_5_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk2_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 4) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 5)
    (mtFiber4RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 5) (by decide) mtFiber4ReverseRow_5_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_6_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk3_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 6) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 6)
    (mtFiber4RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 6) (by decide) mtFiber4ReverseRow_6_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_7_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk3_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 6) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 7)
    (mtFiber4RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 7) (by decide) mtFiber4ReverseRow_7_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_8_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk4_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 8) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 8)
    (mtFiber4RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 8) (by decide) mtFiber4ReverseRow_8_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_9_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk4_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 8) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 9)
    (mtFiber4RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 9) (by decide) mtFiber4ReverseRow_9_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_10_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk5_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 10) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 2) (mtFiber4StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 2) (mtFiber4StateAt 10)
    (mtFiber4RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 10) (by decide) mtFiber4ReverseRow_10_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_11_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk5_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 10) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 11)
    (mtFiber4RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 11) (by decide) mtFiber4ReverseRow_11_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_12_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk6_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 12) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 12)
    (mtFiber4RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 12) (by decide) mtFiber4ReverseRow_12_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_13_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk6_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 12) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 5) (mtFiber4StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 5) (mtFiber4StateAt 13)
    (mtFiber4RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 13) (by decide) mtFiber4ReverseRow_13_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_14_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk7_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 14) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 6) (mtFiber4StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 6) (mtFiber4StateAt 14)
    (mtFiber4RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 14) (by decide) mtFiber4ReverseRow_14_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_15_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk7_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 14) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 7) (mtFiber4StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 7) (mtFiber4StateAt 15)
    (mtFiber4RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 15) (by decide) mtFiber4ReverseRow_15_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_16_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk8_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 16) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 16)
    (mtFiber4RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 16) (by decide) mtFiber4ReverseRow_16_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_17_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk8_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 16) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 17)
    (mtFiber4RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 17) (by decide) mtFiber4ReverseRow_17_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_18_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk9_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 18) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 2) (mtFiber4StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 2) (mtFiber4StateAt 18)
    (mtFiber4RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 18) (by decide) mtFiber4ReverseRow_18_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_19_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk9_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 18) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 19)
    (mtFiber4RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 19) (by decide) mtFiber4ReverseRow_19_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_20_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk10_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 20) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 20)
    (mtFiber4RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 20) (by decide) mtFiber4ReverseRow_20_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_21_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk10_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 20) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 5) (mtFiber4StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 5) (mtFiber4StateAt 21)
    (mtFiber4RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 21) (by decide) mtFiber4ReverseRow_21_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_22_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk11_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 22) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 6) (mtFiber4StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 6) (mtFiber4StateAt 22)
    (mtFiber4RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 22) (by decide) mtFiber4ReverseRow_22_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_23_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk11_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 22) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 7) (mtFiber4StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 7) (mtFiber4StateAt 23)
    (mtFiber4RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 23) (by decide) mtFiber4ReverseRow_23_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_24_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk12_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 24) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 8) (mtFiber4StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 8) (mtFiber4StateAt 24)
    (mtFiber4RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 24) (by decide) mtFiber4ReverseRow_24_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_25_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk12_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 24) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 9) (mtFiber4StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 9) (mtFiber4StateAt 25)
    (mtFiber4RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 25) (by decide) mtFiber4ReverseRow_25_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_26_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk13_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 26) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 10) (mtFiber4StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 10) (mtFiber4StateAt 26)
    (mtFiber4RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 26) (by decide) mtFiber4ReverseRow_26_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_27_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk13_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 26) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 11) (mtFiber4StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 11) (mtFiber4StateAt 27)
    (mtFiber4RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 27) (by decide) mtFiber4ReverseRow_27_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_28_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk14_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 28) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 12) (mtFiber4StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 12) (mtFiber4StateAt 28)
    (mtFiber4RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 28) (by decide) mtFiber4ReverseRow_28_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_29_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk14_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 28) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 13) (mtFiber4StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 13) (mtFiber4StateAt 29)
    (mtFiber4RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 29) (by decide) mtFiber4ReverseRow_29_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_30_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk15_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 30) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 14) (mtFiber4StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 14) (mtFiber4StateAt 30)
    (mtFiber4RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 30) (by decide) mtFiber4ReverseRow_30_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_31_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk15_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 30) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 15) (mtFiber4StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 15) (mtFiber4StateAt 31)
    (mtFiber4RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 31) (by decide) mtFiber4ReverseRow_31_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_32_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk16_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 32) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 0) (mtFiber4StateAt 32)
    (mtFiber4RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 32) (by decide) mtFiber4ReverseRow_32_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_33_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk16_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 32) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 1) (mtFiber4StateAt 33)
    (mtFiber4RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 33) (by decide) mtFiber4ReverseRow_33_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_34_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk17_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 34) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 32) (mtFiber4StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 32) (mtFiber4StateAt 34)
    (mtFiber4RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 34) (by decide) mtFiber4ReverseRow_34_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_35_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk17_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 34) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 3) (mtFiber4StateAt 35)
    (mtFiber4RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 35) (by decide) mtFiber4ReverseRow_35_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_36_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk18_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 36) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 4) (mtFiber4StateAt 36)
    (mtFiber4RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 36) (by decide) mtFiber4ReverseRow_36_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_37_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk18_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 36) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 5) (mtFiber4StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 5) (mtFiber4StateAt 37)
    (mtFiber4RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 37) (by decide) mtFiber4ReverseRow_37_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_38_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk19_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 38) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 33) (mtFiber4StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 33) (mtFiber4StateAt 38)
    (mtFiber4RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 38) (by decide) mtFiber4ReverseRow_38_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_39_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk19_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 38) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 32) (mtFiber4StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 32) (mtFiber4StateAt 39)
    (mtFiber4RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 39) (by decide) mtFiber4ReverseRow_39_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_40_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk20_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 40) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 8) (mtFiber4StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 8) (mtFiber4StateAt 40)
    (mtFiber4RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 40) (by decide) mtFiber4ReverseRow_40_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_41_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk20_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 40) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 9) (mtFiber4StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 9) (mtFiber4StateAt 41)
    (mtFiber4RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 41) (by decide) mtFiber4ReverseRow_41_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_42_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk21_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 42) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 40) (mtFiber4StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 40) (mtFiber4StateAt 42)
    (mtFiber4RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 42) (by decide) mtFiber4ReverseRow_42_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_43_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk21_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 42) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 11) (mtFiber4StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 11) (mtFiber4StateAt 43)
    (mtFiber4RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 43) (by decide) mtFiber4ReverseRow_43_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_44_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk22_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 44) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 12) (mtFiber4StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 12) (mtFiber4StateAt 44)
    (mtFiber4RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 44) (by decide) mtFiber4ReverseRow_44_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_45_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk22_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 44) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 13) (mtFiber4StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 13) (mtFiber4StateAt 45)
    (mtFiber4RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 45) (by decide) mtFiber4ReverseRow_45_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_46_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk23_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 46) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 41) (mtFiber4StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 41) (mtFiber4StateAt 46)
    (mtFiber4RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 46) (by decide) mtFiber4ReverseRow_46_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_47_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk23_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 46) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 40) (mtFiber4StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 40) (mtFiber4StateAt 47)
    (mtFiber4RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 47) (by decide) mtFiber4ReverseRow_47_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_48_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk24_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 48) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 16) (mtFiber4StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 16) (mtFiber4StateAt 48)
    (mtFiber4RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 48) (by decide) mtFiber4ReverseRow_48_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_49_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk24_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 48) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 17) (mtFiber4StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 17) (mtFiber4StateAt 49)
    (mtFiber4RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 49) (by decide) mtFiber4ReverseRow_49_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_50_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk25_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 50) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 48) (mtFiber4StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 48) (mtFiber4StateAt 50)
    (mtFiber4RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 50) (by decide) mtFiber4ReverseRow_50_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_51_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk25_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 50) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 19) (mtFiber4StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 19) (mtFiber4StateAt 51)
    (mtFiber4RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 51) (by decide) mtFiber4ReverseRow_51_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_52_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk26_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 52) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 20) (mtFiber4StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 20) (mtFiber4StateAt 52)
    (mtFiber4RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 52) (by decide) mtFiber4ReverseRow_52_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_53_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk26_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 52) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 21) (mtFiber4StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 21) (mtFiber4StateAt 53)
    (mtFiber4RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 53) (by decide) mtFiber4ReverseRow_53_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_54_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk27_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 54) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 49) (mtFiber4StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 49) (mtFiber4StateAt 54)
    (mtFiber4RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 54) (by decide) mtFiber4ReverseRow_54_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_55_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk27_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 54) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 48) (mtFiber4StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 48) (mtFiber4StateAt 55)
    (mtFiber4RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 55) (by decide) mtFiber4ReverseRow_55_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_56_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk28_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 56) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 32) (mtFiber4StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 32) (mtFiber4StateAt 56)
    (mtFiber4RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 56) (by decide) mtFiber4ReverseRow_56_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_57_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk28_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 56) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 33) (mtFiber4StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 33) (mtFiber4StateAt 57)
    (mtFiber4RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 57) (by decide) mtFiber4ReverseRow_57_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_58_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk29_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 58) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 34) (mtFiber4StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 34) (mtFiber4StateAt 58)
    (mtFiber4RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 58) (by decide) mtFiber4ReverseRow_58_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_59_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk29_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 58) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 35) (mtFiber4StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 35) (mtFiber4StateAt 59)
    (mtFiber4RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 59) (by decide) mtFiber4ReverseRow_59_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_60_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk30_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 60) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 36) (mtFiber4StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 36) (mtFiber4StateAt 60)
    (mtFiber4RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 60) (by decide) mtFiber4ReverseRow_60_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_61_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk30_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 60) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 37) (mtFiber4StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 37) (mtFiber4StateAt 61)
    (mtFiber4RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 61) (by decide) mtFiber4ReverseRow_61_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_62_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk31_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 62) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber4ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 38) (mtFiber4StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 38) (mtFiber4StateAt 62)
    (mtFiber4RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 62) (by decide) mtFiber4ReverseRow_62_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4ReverseRow_63_ok :
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber4Chunk31_ok
  change (mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 62) &&
    mtRowReverseValid mtFiber4Key mtFiber4Expected (mtFiber4RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber4ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber4StateAt 39) (mtFiber4StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber4StateAt 39) (mtFiber4StateAt 63)
    (mtFiber4RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber4Key mtFiber4Expected
        (mtFiber4RowAt 63) (by decide) mtFiber4ReverseRow_63_ok
      simpa [mtFiber4StateAt, mtFiber4RowAt, mtFiber4Rows, listGetD, directRow] using h)

theorem mtFiber4State0_in_close :
    mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  change mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 64 [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 0 64 [mtFiber4StateAt 0] (mtFiber4StateAt 0) (by simp [closeChainFiber])

theorem mtFiber4State1_in_close :
    mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  change mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates (1 + 63) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 1 63 [mtFiber4StateAt 0] (mtFiber4StateAt 1) h1

theorem mtFiber4State2_in_close :
    mtFiber4StateAt 2 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 2 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 2) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep2
  change mtFiber4StateAt 2 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 2) h2

theorem mtFiber4State3_in_close :
    mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  change mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates (1 + 63) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 1 63 [mtFiber4StateAt 0] (mtFiber4StateAt 3) h1

theorem mtFiber4State4_in_close :
    mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  change mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates (1 + 63) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 1 63 [mtFiber4StateAt 0] (mtFiber4StateAt 4) h1

theorem mtFiber4State5_in_close :
    mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  change mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 5) h2

theorem mtFiber4State6_in_close :
    mtFiber4StateAt 6 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 6 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 6) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep6
  change mtFiber4StateAt 6 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 6) h2

theorem mtFiber4State7_in_close :
    mtFiber4StateAt 7 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 7 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 7) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep7
  change mtFiber4StateAt 7 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 7) h2

theorem mtFiber4State8_in_close :
    mtFiber4StateAt 8 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 8 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 8) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep8
  change mtFiber4StateAt 8 ∈ closeChainFiber mtWord mtFiber4DirectStates (1 + 63) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 1 63 [mtFiber4StateAt 0] (mtFiber4StateAt 8) h1

theorem mtFiber4State9_in_close :
    mtFiber4StateAt 9 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 9 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 9) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep9
  change mtFiber4StateAt 9 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 9) h2

theorem mtFiber4State10_in_close :
    mtFiber4StateAt 10 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 2 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 2) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep2
  have h3 : mtFiber4StateAt 10 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 2) (mtFiber4StateAt 10) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep10
  change mtFiber4StateAt 10 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 10) h3

theorem mtFiber4State11_in_close :
    mtFiber4StateAt 11 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 11 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 11) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep11
  change mtFiber4StateAt 11 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 11) h2

theorem mtFiber4State12_in_close :
    mtFiber4StateAt 12 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 12 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 12) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep12
  change mtFiber4StateAt 12 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 12) h2

theorem mtFiber4State13_in_close :
    mtFiber4StateAt 13 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  have h3 : mtFiber4StateAt 13 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 5) (mtFiber4StateAt 13) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep13
  change mtFiber4StateAt 13 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 13) h3

theorem mtFiber4State14_in_close :
    mtFiber4StateAt 14 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 6 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 6) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep6
  have h3 : mtFiber4StateAt 14 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 6) (mtFiber4StateAt 14) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep14
  change mtFiber4StateAt 14 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 14) h3

theorem mtFiber4State15_in_close :
    mtFiber4StateAt 15 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 7 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 7) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep7
  have h3 : mtFiber4StateAt 15 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 7) (mtFiber4StateAt 15) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep15
  change mtFiber4StateAt 15 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 15) h3

theorem mtFiber4State16_in_close :
    mtFiber4StateAt 16 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 16 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 16) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep16
  change mtFiber4StateAt 16 ∈ closeChainFiber mtWord mtFiber4DirectStates (1 + 63) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 1 63 [mtFiber4StateAt 0] (mtFiber4StateAt 16) h1

theorem mtFiber4State17_in_close :
    mtFiber4StateAt 17 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 17 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 17) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep17
  change mtFiber4StateAt 17 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 17) h2

theorem mtFiber4State18_in_close :
    mtFiber4StateAt 18 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 2 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 2) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep2
  have h3 : mtFiber4StateAt 18 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 2) (mtFiber4StateAt 18) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep18
  change mtFiber4StateAt 18 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 18) h3

theorem mtFiber4State19_in_close :
    mtFiber4StateAt 19 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 19 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 19) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep19
  change mtFiber4StateAt 19 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 19) h2

theorem mtFiber4State20_in_close :
    mtFiber4StateAt 20 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 20 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 20) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep20
  change mtFiber4StateAt 20 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 20) h2

theorem mtFiber4State21_in_close :
    mtFiber4StateAt 21 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  have h3 : mtFiber4StateAt 21 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 5) (mtFiber4StateAt 21) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep21
  change mtFiber4StateAt 21 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 21) h3

theorem mtFiber4State22_in_close :
    mtFiber4StateAt 22 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 6 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 6) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep6
  have h3 : mtFiber4StateAt 22 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 6) (mtFiber4StateAt 22) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep22
  change mtFiber4StateAt 22 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 22) h3

theorem mtFiber4State23_in_close :
    mtFiber4StateAt 23 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 7 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 7) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep7
  have h3 : mtFiber4StateAt 23 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 7) (mtFiber4StateAt 23) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep23
  change mtFiber4StateAt 23 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 23) h3

theorem mtFiber4State24_in_close :
    mtFiber4StateAt 24 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 8 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 8) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep8
  have h2 : mtFiber4StateAt 24 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 8) (mtFiber4StateAt 24) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep24
  change mtFiber4StateAt 24 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 24) h2

theorem mtFiber4State25_in_close :
    mtFiber4StateAt 25 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 9 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 9) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep9
  have h3 : mtFiber4StateAt 25 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 9) (mtFiber4StateAt 25) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep25
  change mtFiber4StateAt 25 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 25) h3

theorem mtFiber4State26_in_close :
    mtFiber4StateAt 26 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 2 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 2) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep2
  have h3 : mtFiber4StateAt 10 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 2) (mtFiber4StateAt 10) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep10
  have h4 : mtFiber4StateAt 26 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 10) (mtFiber4StateAt 26) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep26
  change mtFiber4StateAt 26 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 26) h4

theorem mtFiber4State27_in_close :
    mtFiber4StateAt 27 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 11 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 11) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep11
  have h3 : mtFiber4StateAt 27 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 11) (mtFiber4StateAt 27) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep27
  change mtFiber4StateAt 27 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 27) h3

theorem mtFiber4State28_in_close :
    mtFiber4StateAt 28 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 12 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 12) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep12
  have h3 : mtFiber4StateAt 28 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 12) (mtFiber4StateAt 28) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep28
  change mtFiber4StateAt 28 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 28) h3

theorem mtFiber4State29_in_close :
    mtFiber4StateAt 29 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  have h3 : mtFiber4StateAt 13 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 5) (mtFiber4StateAt 13) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep13
  have h4 : mtFiber4StateAt 29 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 13) (mtFiber4StateAt 29) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep29
  change mtFiber4StateAt 29 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 29) h4

theorem mtFiber4State30_in_close :
    mtFiber4StateAt 30 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 6 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 6) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep6
  have h3 : mtFiber4StateAt 14 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 6) (mtFiber4StateAt 14) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep14
  have h4 : mtFiber4StateAt 30 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 14) (mtFiber4StateAt 30) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep30
  change mtFiber4StateAt 30 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 30) h4

theorem mtFiber4State31_in_close :
    mtFiber4StateAt 31 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 7 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 7) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep7
  have h3 : mtFiber4StateAt 15 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 7) (mtFiber4StateAt 15) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep15
  have h4 : mtFiber4StateAt 31 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 15) (mtFiber4StateAt 31) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep31
  change mtFiber4StateAt 31 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 31) h4

theorem mtFiber4State32_in_close :
    mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 32) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep32
  change mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates (1 + 63) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 1 63 [mtFiber4StateAt 0] (mtFiber4StateAt 32) h1

theorem mtFiber4State33_in_close :
    mtFiber4StateAt 33 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 33 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 33) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep33
  change mtFiber4StateAt 33 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 33) h2

theorem mtFiber4State34_in_close :
    mtFiber4StateAt 34 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 32) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep32
  have h2 : mtFiber4StateAt 34 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 32) (mtFiber4StateAt 34) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep34
  change mtFiber4StateAt 34 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 34) h2

theorem mtFiber4State35_in_close :
    mtFiber4StateAt 35 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 35 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 35) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep35
  change mtFiber4StateAt 35 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 35) h2

theorem mtFiber4State36_in_close :
    mtFiber4StateAt 36 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 36 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 36) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep36
  change mtFiber4StateAt 36 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 36) h2

theorem mtFiber4State37_in_close :
    mtFiber4StateAt 37 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  have h3 : mtFiber4StateAt 37 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 5) (mtFiber4StateAt 37) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep37
  change mtFiber4StateAt 37 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 37) h3

theorem mtFiber4State38_in_close :
    mtFiber4StateAt 38 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 33 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 33) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep33
  have h3 : mtFiber4StateAt 38 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 33) (mtFiber4StateAt 38) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep38
  change mtFiber4StateAt 38 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 38) h3

theorem mtFiber4State39_in_close :
    mtFiber4StateAt 39 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 32) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep32
  have h2 : mtFiber4StateAt 39 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 32) (mtFiber4StateAt 39) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep39
  change mtFiber4StateAt 39 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 39) h2

theorem mtFiber4State40_in_close :
    mtFiber4StateAt 40 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 8 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 8) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep8
  have h2 : mtFiber4StateAt 40 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 8) (mtFiber4StateAt 40) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep40
  change mtFiber4StateAt 40 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 40) h2

theorem mtFiber4State41_in_close :
    mtFiber4StateAt 41 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 9 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 9) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep9
  have h3 : mtFiber4StateAt 41 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 9) (mtFiber4StateAt 41) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep41
  change mtFiber4StateAt 41 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 41) h3

theorem mtFiber4State42_in_close :
    mtFiber4StateAt 42 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 8 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 8) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep8
  have h2 : mtFiber4StateAt 40 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 8) (mtFiber4StateAt 40) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep40
  have h3 : mtFiber4StateAt 42 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 40) (mtFiber4StateAt 42) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep42
  change mtFiber4StateAt 42 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 42) h3

theorem mtFiber4State43_in_close :
    mtFiber4StateAt 43 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 11 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 11) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep11
  have h3 : mtFiber4StateAt 43 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 11) (mtFiber4StateAt 43) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep43
  change mtFiber4StateAt 43 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 43) h3

theorem mtFiber4State44_in_close :
    mtFiber4StateAt 44 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 12 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 12) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep12
  have h3 : mtFiber4StateAt 44 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 12) (mtFiber4StateAt 44) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep44
  change mtFiber4StateAt 44 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 44) h3

theorem mtFiber4State45_in_close :
    mtFiber4StateAt 45 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  have h3 : mtFiber4StateAt 13 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 5) (mtFiber4StateAt 13) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep13
  have h4 : mtFiber4StateAt 45 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 13) (mtFiber4StateAt 45) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep45
  change mtFiber4StateAt 45 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 45) h4

theorem mtFiber4State46_in_close :
    mtFiber4StateAt 46 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 9 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 9) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep9
  have h3 : mtFiber4StateAt 41 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 9) (mtFiber4StateAt 41) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep41
  have h4 : mtFiber4StateAt 46 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 41) (mtFiber4StateAt 46) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep46
  change mtFiber4StateAt 46 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 46) h4

theorem mtFiber4State47_in_close :
    mtFiber4StateAt 47 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 8 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 8) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep8
  have h2 : mtFiber4StateAt 40 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 8) (mtFiber4StateAt 40) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep40
  have h3 : mtFiber4StateAt 47 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 40) (mtFiber4StateAt 47) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep47
  change mtFiber4StateAt 47 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 47) h3

theorem mtFiber4State48_in_close :
    mtFiber4StateAt 48 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 16 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 16) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep16
  have h2 : mtFiber4StateAt 48 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 16) (mtFiber4StateAt 48) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep48
  change mtFiber4StateAt 48 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 48) h2

theorem mtFiber4State49_in_close :
    mtFiber4StateAt 49 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 17 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 17) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep17
  have h3 : mtFiber4StateAt 49 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 17) (mtFiber4StateAt 49) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep49
  change mtFiber4StateAt 49 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 49) h3

theorem mtFiber4State50_in_close :
    mtFiber4StateAt 50 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 16 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 16) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep16
  have h2 : mtFiber4StateAt 48 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 16) (mtFiber4StateAt 48) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep48
  have h3 : mtFiber4StateAt 50 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 48) (mtFiber4StateAt 50) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep50
  change mtFiber4StateAt 50 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 50) h3

theorem mtFiber4State51_in_close :
    mtFiber4StateAt 51 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 19 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 19) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep19
  have h3 : mtFiber4StateAt 51 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 19) (mtFiber4StateAt 51) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep51
  change mtFiber4StateAt 51 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 51) h3

theorem mtFiber4State52_in_close :
    mtFiber4StateAt 52 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 20 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 20) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep20
  have h3 : mtFiber4StateAt 52 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 20) (mtFiber4StateAt 52) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep52
  change mtFiber4StateAt 52 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 52) h3

theorem mtFiber4State53_in_close :
    mtFiber4StateAt 53 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  have h3 : mtFiber4StateAt 21 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 5) (mtFiber4StateAt 21) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep21
  have h4 : mtFiber4StateAt 53 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 21) (mtFiber4StateAt 53) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep53
  change mtFiber4StateAt 53 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 53) h4

theorem mtFiber4State54_in_close :
    mtFiber4StateAt 54 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 17 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 17) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep17
  have h3 : mtFiber4StateAt 49 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 17) (mtFiber4StateAt 49) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep49
  have h4 : mtFiber4StateAt 54 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 49) (mtFiber4StateAt 54) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep54
  change mtFiber4StateAt 54 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 54) h4

theorem mtFiber4State55_in_close :
    mtFiber4StateAt 55 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 16 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 16) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep16
  have h2 : mtFiber4StateAt 48 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 16) (mtFiber4StateAt 48) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep48
  have h3 : mtFiber4StateAt 55 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 48) (mtFiber4StateAt 55) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep55
  change mtFiber4StateAt 55 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 55) h3

theorem mtFiber4State56_in_close :
    mtFiber4StateAt 56 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 32) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep32
  have h2 : mtFiber4StateAt 56 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 32) (mtFiber4StateAt 56) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep56
  change mtFiber4StateAt 56 ∈ closeChainFiber mtWord mtFiber4DirectStates (2 + 62) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 2 62 [mtFiber4StateAt 0] (mtFiber4StateAt 56) h2

theorem mtFiber4State57_in_close :
    mtFiber4StateAt 57 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 33 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 33) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep33
  have h3 : mtFiber4StateAt 57 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 33) (mtFiber4StateAt 57) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep57
  change mtFiber4StateAt 57 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 57) h3

theorem mtFiber4State58_in_close :
    mtFiber4StateAt 58 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 32) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep32
  have h2 : mtFiber4StateAt 34 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 32) (mtFiber4StateAt 34) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep34
  have h3 : mtFiber4StateAt 58 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 34) (mtFiber4StateAt 58) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep58
  change mtFiber4StateAt 58 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 58) h3

theorem mtFiber4State59_in_close :
    mtFiber4StateAt 59 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 3 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 3) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep3
  have h2 : mtFiber4StateAt 35 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 3) (mtFiber4StateAt 35) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep35
  have h3 : mtFiber4StateAt 59 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 35) (mtFiber4StateAt 59) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep59
  change mtFiber4StateAt 59 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 59) h3

theorem mtFiber4State60_in_close :
    mtFiber4StateAt 60 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 4 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 4) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep4
  have h2 : mtFiber4StateAt 36 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 4) (mtFiber4StateAt 36) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep36
  have h3 : mtFiber4StateAt 60 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 36) (mtFiber4StateAt 60) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep60
  change mtFiber4StateAt 60 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 60) h3

theorem mtFiber4State61_in_close :
    mtFiber4StateAt 61 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 5 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 5) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep5
  have h3 : mtFiber4StateAt 37 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 5) (mtFiber4StateAt 37) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep37
  have h4 : mtFiber4StateAt 61 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 37) (mtFiber4StateAt 61) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep61
  change mtFiber4StateAt 61 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 61) h4

theorem mtFiber4State62_in_close :
    mtFiber4StateAt 62 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 1 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 1) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep1
  have h2 : mtFiber4StateAt 33 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 1) (mtFiber4StateAt 33) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep33
  have h3 : mtFiber4StateAt 38 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 33) (mtFiber4StateAt 38) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep38
  have h4 : mtFiber4StateAt 62 ∈ closeChainFiber mtWord mtFiber4DirectStates 4 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0]
      (mtFiber4StateAt 38) (mtFiber4StateAt 62) (by decide) h3 (by decide)
      mtFiber4ReverseSingleStep62
  change mtFiber4StateAt 62 ∈ closeChainFiber mtWord mtFiber4DirectStates (4 + 60) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 4 60 [mtFiber4StateAt 0] (mtFiber4StateAt 62) h4

theorem mtFiber4State63_in_close :
    mtFiber4StateAt 63 ∈ closeChainFiber mtWord mtFiber4DirectStates mtFiber4DirectStates.length [mtFiber4StateAt 0] := by
  have h0 : mtFiber4StateAt 0 ∈ closeChainFiber mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber4StateAt 32 ∈ closeChainFiber mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 0 [mtFiber4StateAt 0]
      (mtFiber4StateAt 0) (mtFiber4StateAt 32) (by decide) h0 (by decide)
      mtFiber4ReverseSingleStep32
  have h2 : mtFiber4StateAt 39 ∈ closeChainFiber mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 1 [mtFiber4StateAt 0]
      (mtFiber4StateAt 32) (mtFiber4StateAt 39) (by decide) h1 (by decide)
      mtFiber4ReverseSingleStep39
  have h3 : mtFiber4StateAt 63 ∈ closeChainFiber mtWord mtFiber4DirectStates 3 [mtFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber4DirectStates 2 [mtFiber4StateAt 0]
      (mtFiber4StateAt 39) (mtFiber4StateAt 63) (by decide) h2 (by decide)
      mtFiber4ReverseSingleStep63
  change mtFiber4StateAt 63 ∈ closeChainFiber mtWord mtFiber4DirectStates (3 + 61) [mtFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber4DirectStates 3 61 [mtFiber4StateAt 0] (mtFiber4StateAt 63) h3

theorem mtFiber4DirectConnected :
    chainFiberConnected mtWord mtFiber4DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber4DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber4State0_in_close
  · subst state
    exact mtFiber4State1_in_close
  · subst state
    exact mtFiber4State2_in_close
  · subst state
    exact mtFiber4State3_in_close
  · subst state
    exact mtFiber4State4_in_close
  · subst state
    exact mtFiber4State5_in_close
  · subst state
    exact mtFiber4State6_in_close
  · subst state
    exact mtFiber4State7_in_close
  · subst state
    exact mtFiber4State8_in_close
  · subst state
    exact mtFiber4State9_in_close
  · subst state
    exact mtFiber4State10_in_close
  · subst state
    exact mtFiber4State11_in_close
  · subst state
    exact mtFiber4State12_in_close
  · subst state
    exact mtFiber4State13_in_close
  · subst state
    exact mtFiber4State14_in_close
  · subst state
    exact mtFiber4State15_in_close
  · subst state
    exact mtFiber4State16_in_close
  · subst state
    exact mtFiber4State17_in_close
  · subst state
    exact mtFiber4State18_in_close
  · subst state
    exact mtFiber4State19_in_close
  · subst state
    exact mtFiber4State20_in_close
  · subst state
    exact mtFiber4State21_in_close
  · subst state
    exact mtFiber4State22_in_close
  · subst state
    exact mtFiber4State23_in_close
  · subst state
    exact mtFiber4State24_in_close
  · subst state
    exact mtFiber4State25_in_close
  · subst state
    exact mtFiber4State26_in_close
  · subst state
    exact mtFiber4State27_in_close
  · subst state
    exact mtFiber4State28_in_close
  · subst state
    exact mtFiber4State29_in_close
  · subst state
    exact mtFiber4State30_in_close
  · subst state
    exact mtFiber4State31_in_close
  · subst state
    exact mtFiber4State32_in_close
  · subst state
    exact mtFiber4State33_in_close
  · subst state
    exact mtFiber4State34_in_close
  · subst state
    exact mtFiber4State35_in_close
  · subst state
    exact mtFiber4State36_in_close
  · subst state
    exact mtFiber4State37_in_close
  · subst state
    exact mtFiber4State38_in_close
  · subst state
    exact mtFiber4State39_in_close
  · subst state
    exact mtFiber4State40_in_close
  · subst state
    exact mtFiber4State41_in_close
  · subst state
    exact mtFiber4State42_in_close
  · subst state
    exact mtFiber4State43_in_close
  · subst state
    exact mtFiber4State44_in_close
  · subst state
    exact mtFiber4State45_in_close
  · subst state
    exact mtFiber4State46_in_close
  · subst state
    exact mtFiber4State47_in_close
  · subst state
    exact mtFiber4State48_in_close
  · subst state
    exact mtFiber4State49_in_close
  · subst state
    exact mtFiber4State50_in_close
  · subst state
    exact mtFiber4State51_in_close
  · subst state
    exact mtFiber4State52_in_close
  · subst state
    exact mtFiber4State53_in_close
  · subst state
    exact mtFiber4State54_in_close
  · subst state
    exact mtFiber4State55_in_close
  · subst state
    exact mtFiber4State56_in_close
  · subst state
    exact mtFiber4State57_in_close
  · subst state
    exact mtFiber4State58_in_close
  · subst state
    exact mtFiber4State59_in_close
  · subst state
    exact mtFiber4State60_in_close
  · subst state
    exact mtFiber4State61_in_close
  · subst state
    exact mtFiber4State62_in_close
  · subst state
    exact mtFiber4State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
